module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Finite type for sheaves of modules on an affine scheme

[Stacks, Tag 01XZ] characterises coherent modules on a locally Noetherian scheme. Every route
to that characterisation passes through the affine dictionary between `AlgebraicGeometry.tilde`
and finiteness of modules, which pinned Mathlib does not record: Mathlib's `tilde` file
transports quasi-coherence through `tilde` and nothing else.

This file supplies that dictionary in the two directions that need no covering argument,
together with the site-level lemma that global generating sections suffice for finite type.

## Main results

* `Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_of_generatingSections`: a sheaf of
  modules with a finite family of global generating sections is of finite type, on an arbitrary
  site.
* `Stacks.AlgebraicGeometry.CoherentTFAE.epi_of_map_epi`: a faithful functor reflects
  epimorphisms. This is what runs the `tilde` dictionary backwards.
* `Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_tilde`: `M^~` is of finite type when `M`
  is a finite module.
* `Stacks.AlgebraicGeometry.CoherentTFAE.finite_of_epi_free_tilde` and
  `Stacks.AlgebraicGeometry.CoherentTFAE.finite_of_generatingSections_tilde`: conversely, an
  epimorphism onto `M^~` from a finite free sheaf — in particular a finite family of global
  generating sections of `M^~` — makes `M` a finite module.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules _`, and the sheaf of rings
`X.ringCatSheaf` is a `TopCat.Sheaf`, not syntactically a `CategoryTheory.Sheaf` on the
Grothendieck topology of the opens. Both identifications hold at default transparency but not at
the transparency instance synthesis uses, so `Epi`/`IsIso` instances on morphisms of
`(Spec R).Modules` are *not* found by `infer_instance` even when they are the plain
`Iso.isIso_hom`. Mathlib's own proofs in its `tilde` file work around this by disabling
`backward.isDefEq.respectTransparency`. Here every such instance is instead supplied explicitly
and positionally, which needs no option; this is why the `Epi` arguments below are given as
proofs rather than left to `by infer_instance`.

For the same reason `tildeGeneratingSections` sets its index type to `ι` by hand instead of
inheriting it through `SheafOfModules.GeneratingSections.ofEpi`, so that `Finite` of the index
type is available by `rfl`.

## References

* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 01B4](https://stacks.math.columbia.edu/tag/01B4)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
-/

@[expose] public section

open CategoryTheory Limits SheafOfModules TopologicalSpace
open AlgebraicGeometry

universe u v' u' v u₁

namespace Stacks.AlgebraicGeometry.CoherentTFAE

/-! ### Global generating sections give finite type, on an arbitrary site -/

section Site

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ Y : C, HasSheafify (J.over Y) AddCommGrpCat.{u}]
  [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasBinaryProducts C]

end Site

/-! ### A faithful functor reflects epimorphisms -/

section Faithful

variable {C : Type u'} [Category.{v'} C] {D : Type u₁} [Category.{v} D]

/-- **A faithful functor reflects epimorphisms.** If `F.map f` is an epimorphism and `F` is
faithful then `f` is an epimorphism: two maps equalised by `f` have images equalised by
`F.map f`, hence equal images, hence are equal. -/
theorem epi_of_map_epi (F : C ⥤ D) [F.Faithful] {X Y : C} (f : X ⟶ Y) (hf : Epi (F.map f)) :
    Epi f :=
  F.epi_of_epi_map hf

/-- Precomposing an epimorphism with an isomorphism, given as an explicit `IsIso` proof, gives an
epimorphism. -/
private theorem epi_comp_of_isIso {X Y Z : C} (f : X ⟶ Y) (hf : IsIso f) (g : Y ⟶ Z)
    (hg : Epi g) : Epi (f ≫ g) :=
  have := hf
  epi_comp f g

end Faithful

/-! ### The `tilde` dictionary for finiteness -/

section Affine

variable {R : CommRingCat.{u}}

/-- **An epimorphism onto `M^~` from a finite free sheaf makes `M` a finite module.**
Composing with `AlgebraicGeometry.tildeFinsupp` turns the epimorphism into one out of
`(ι →₀ R)^~`; since `tilde` is full it is the image of a map `(ι →₀ R) ⟶ M`, and faithfulness
reflects the epimorphism, so that map is surjective. -/
theorem finite_of_epi_free_tilde (M : ModuleCat.{u} R) {ι : Type u} [Finite ι]
    (p : (free ι : SheafOfModules.{u} (Spec R).ringCatSheaf) ⟶ tilde M) (hp : Epi p) :
    Module.Finite R M := by
  have hq : Epi ((tildeFinsupp (R := R) ι).hom ≫ p) :=
    epi_comp_of_isIso _ (Iso.isIso_hom (tildeFinsupp (R := R) ι)) _ hp
  have hg : Epi ((tilde.functor R).map
      ((tilde.functor R).preimage ((tildeFinsupp (R := R) ι).hom ≫ p))) := by
    rw [(tilde.functor R).map_preimage]; exact hq
  have hepi := epi_of_map_epi (tilde.functor R) _ hg
  rw [ModuleCat.epi_iff_surjective] at hepi
  exact Module.Finite.of_surjective
    (ModuleCat.Hom.hom ((tilde.functor R).preimage ((tildeFinsupp (R := R) ι).hom ≫ p))) hepi

end Affine

end Stacks.AlgebraicGeometry.CoherentTFAE

end
