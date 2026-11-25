/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
public import WeilConjectures.EtaleCohomology.Purity.Smooth.SectionInvariant
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.SmoothProj
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.Etale.Derived.InvertibleLocal
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.ClosedImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion

/-!
# The section invariant and the family object lie in `Pic(D^b_{ctf})`

Blueprint `lemma-section-normal-bundle--1` and `definition-deformation-normal-bundle` place the
section invariant `𝒞(g, s) = Ls^* ω_g` and the family object `F = Ls̃^* ω_{g̃}` in
`Pic(D^b_{ctf}(-, Λ))`: they are ⊗-invertible and lie in `D^b_{ctf}`, since `ω_g` does and `Ls^*`
preserves both properties.

For `g` smooth of pure relative dimension `d`, `ω_g` is a shifted lisse rank-one sheaf. For `g`
merely smooth, its relative dimension is locally constant on `V`; on a noetherian source, `V` is
covered by finitely many opens on which it is constant, and invertibility and membership in
`D^b_{ctf}` are local on `V`.

## Main statements (in `AlgebraicGeometry.Etale`)

- `isInvertible_and_boundedConstructibleFiniteTor_sectionInvariant`,
  `isInvertible_and_boundedConstructibleFiniteTor_deformationFamilyObject`:
  constant relative dimension.
- `isInvertible_and_boundedConstructibleFiniteTor_dualizingComplex_of_smooth`
- `isInvertible_and_boundedConstructibleFiniteTor_sectionInvariant_of_smooth`,
  `isInvertible_and_boundedConstructibleFiniteTor_deformationFamilyObject_of_smooth`:
  smooth `g` of varying relative dimension.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {V B : Scheme.{u}} (d : ℕ)

/-- The dualizing complex `ω_g = Rg^! Λ_B` of a morphism `g` smooth of pure relative dimension
`d` lies in `D^b_{ctf}(V, Λ)`: it is `L[2d]` for a locally constant sheaf `L` whose stalks are
free of rank one (`AlgebraicGeometry.Etale.exists_dualizingComplex_iso_and_tensor`), so `L` is a
finite locally constant, hence constructible, flat sheaf. -/
theorem boundedConstructibleFiniteTor_dualizingComplex (g : V ⟶ B)
    [SmoothOfRelativeDimension d g] [HasCompactification g] [HasInvertibleExponent Λ V] :
    DerivedCategory.boundedConstructibleFiniteTor Λ V
      (dualizingComplex Λ g) := by
  obtain ⟨L, hL, hstalk, ⟨e⟩, -⟩ := exists_dualizingComplex_iso_and_tensor Λ g d
  have : IsFiniteSheaf L := ⟨fun Ω _ _ s ↦ (ModuleCat.isFinitelyGenerated_iff _).2
    (Module.Finite.equiv (hstalk Ω s).some.toLinearEquiv.symm)⟩
  have : IsFiniteLocallyConstantSheaf L := { }
  have : IsConstructibleSheaf L := IsFiniteLocallyConstantSheaf.isConstructibleSheaf ‹_›
  have hflat : ObjectProperty.flat L := (flat_iff_forall_flat_sheafFiber_obj L).2 fun s ↦
    ObjectProperty.prop_of_iso _
      ((((pointSmallEtale s).uliftSheafFiberIso (ModuleCat.{u + 1} Λ)).app L ≪≫
        (hstalk _ s).some).symm)
      ((ModuleCat.flat_iff_flat _).2 (inferInstanceAs (Module.Flat Λ Λ)))
  have hL : DerivedCategory.boundedConstructibleFiniteTor Λ V
      ((_root_.DerivedCategory.singleFunctor _ 0).obj L) :=
    ⟨Etale.DerivedCategory.boundedConstructible_singleFunctor_obj _ 0,
      ⟨0, 0, _root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat hflat⟩⟩
  have hL₂ := hL.shift (2 * d : ℤ)
  exact ⟨(DerivedCategory.boundedConstructible _ V).prop_of_iso e.symm hL₂.1,
    (DerivedCategory.finiteTorAmplitude _ V).prop_of_iso e.symm hL₂.2⟩

/-- Blueprint `lemma-section-normal-bundle--1`: Section invariant

For `g : V ⟶ B` smooth of pure relative dimension `d` and admitting a compactification, and a
section `s` of `g`, the section invariant `𝒞(g, s) = Ls^* ω_g = Ls^* Rg^! Λ_B` is an object of
`Pic(D^b_{ctf}(B, Λ))`: it is ⊗-invertible, and it lies in `D^b_{ctf}(B, Λ)` since `ω_g` does
and `Ls^*` preserves `D^b_{ctf}`. -/
theorem isInvertible_and_boundedConstructibleFiniteTor_sectionInvariant
    (g : V ⟶ B) [SmoothOfRelativeDimension d g] [HasCompactification g]
    [HasInvertibleExponent Λ V] (s : B ⟶ V) :
    DerivedCategory.isInvertible Λ B (sectionInvariant Λ g s) ∧
      DerivedCategory.boundedConstructibleFiniteTor Λ B (sectionInvariant Λ g s) :=
  ⟨isInvertible_sectionInvariant Λ d g s,
    constructibleFiniteTor_leftDerivedUpperStar (ModuleCat.{u + 1} Λ) s
      (boundedConstructibleFiniteTor_dualizingComplex Λ d g)⟩

/-- Blueprint `definition-deformation-normal-bundle`: Deformation space of a closed section

For `g : V ⟶ B` smooth of pure relative dimension `d` and a closed section `s` of `g`, the family
object `F = Ls̃^* ω_{g̃}` of the deformation to the normal cone of `s` is an object of
`Pic(D^b_{ctf}(𝔸¹_B, Λ))`: it lies in `D^b_{ctf}(𝔸¹_B, Λ)` and is ⊗-invertible. -/
theorem isInvertible_and_boundedConstructibleFiniteTor_deformationFamilyObject
    [HasInvertibleExponent Λ B] (g : V ⟶ B) [SmoothOfRelativeDimension d g] (s : B ⟶ V)
    [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B)
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)] :
    DerivedCategory.isInvertible Λ 𝔸(ULift.{u} (Fin 1); B) (deformationFamilyObject Λ g s) ∧
      DerivedCategory.boundedConstructibleFiniteTor Λ 𝔸(ULift.{u} (Fin 1); B)
        (deformationFamilyObject Λ g s) :=
  have := Scheme.Hom.smoothOfRelativeDimension_deformationSpaceProj d g s hs
  have : HasInvertibleExponent Λ s.ker.deformationSpace :=
    .of_hom (Scheme.Hom.deformationSpaceProj g s ≫ 𝔸(ULift.{u} (Fin 1); B) ↘ B)
  isInvertible_and_boundedConstructibleFiniteTor_sectionInvariant Λ d _ _

section Smooth

/-! ### Smooth morphisms of varying relative dimension

For `g` smooth, the relative dimension of `g` is only locally constant on the source. On a
noetherian source, `V` is covered by finitely many opens `W` on which `g` has constant relative
dimension; there `Lj_W^* ω_g ≅ ω_{g|W}` is invertible and in `D^b_{ctf}`, and both properties are
local (`AlgebraicGeometry.Etale.isInvertible_of_forall_isInvertible_leftDerivedUpperStar`,
`AlgebraicGeometry.Etale.boundedConstructible_of_openCover`,
`AlgebraicGeometry.Etale.torAmplitudeIn_of_openCover`). -/

variable {Λ}

-- Search the braiding of `ModuleCat Λ` through its symmetric structure, as in the generic
-- definitions of the derived tensor product: otherwise the monoidal structures found by instance
-- search differ from the ones in these definitions, and unifying them is very expensive.
attribute [local instance high] SymmetricCategory.toBraidedCategory

variable (Λ) in
/-- The dualizing complex restricts to open subschemes: for a quasi-compact open immersion
`j : U ⟶ V`, `Lj^* ω_g ≅ ω_{j ≫ g}`, since `Rj^! ≅ j^*` and `R(j ≫ g)^! ≅ Rj^! ∘ Rg^!`. -/
theorem nonempty_iso_leftDerivedUpperStar_dualizingComplex_of_isOpenImmersion {U : Scheme.{u}}
    (j : U ⟶ V) [IsOpenImmersion j] [QuasiCompact j] (g : V ⟶ B) [HasCompactification g]
    [HasCompactification (j ≫ g)] [QuasiCompact (j ≫ g)] :
    Nonempty ((L((j)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex Λ g) ≅
      dualizingComplex Λ (j ≫ g)) := by
  have := HasCompactification.comp_of_isOpenImmersion (𝟙 V) j
  have : HasCompactification j := .of_eq (Category.comp_id j)
  obtain ⟨c⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ j g
  exact ⟨(leftDerivedUpperStarIsoMapDerivedCategory _ j).app _ ≪≫
    ((rightDerivedUpperShriekIsoOfIsOpenImmersion Λ j).app _).symm ≪≫ (c.app _).symm⟩

/-- A morphism out of a scheme with noetherian underlying space is quasi-compact. -/
lemma quasiCompact_of_noetherianSpace {Y Z : Scheme.{u}} [TopologicalSpace.NoetherianSpace Y]
    (f : Y ⟶ Z) : QuasiCompact f :=
  ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩

variable (Λ) in
/-- Blueprint `proposition-exceptional-inverse-image-smooth-morphism`: Cohomological smoothness,
clause 1, for a smooth morphism whose relative dimension may vary.

For `g : V ⟶ B` smooth with a compactification, on a source with noetherian underlying space,
the dualizing complex `ω_g = Rg^! Λ_B` is ⊗-invertible and lies in `D^b_{ctf}(V, Λ)`: on each
member `W` of an open cover on which `g` has constant relative dimension, `Lj_W^* ω_g ≅ ω_{g|W}`
is (`AlgebraicGeometry.Etale.isInvertible_dualizingComplex`,
`AlgebraicGeometry.Etale.boundedConstructibleFiniteTor_dualizingComplex`), and both properties
are local on `V`. -/
theorem isInvertible_and_boundedConstructibleFiniteTor_dualizingComplex_of_smooth (g : V ⟶ B)
    [Smooth g] [HasCompactification g] [HasInvertibleExponent Λ V]
    [TopologicalSpace.NoetherianSpace V] :
    DerivedCategory.isInvertible Λ V (dualizingComplex Λ g) ∧
      DerivedCategory.boundedConstructibleFiniteTor Λ V
        (dualizingComplex Λ g) := by
  -- an open cover of `V` on which `g` has constant relative dimension
  have hchart (x : V) : ∃ W : V.Opens, x ∈ W ∧ ∃ e, SmoothOfRelativeDimension e (W.ι ≫ g) := by
    obtain ⟨U, W, -, -, hx, e, n, hn⟩ := Smooth.exists_smoothOfRelativeDimension_resLE g x
    refine ⟨W, hx, n, ?_⟩
    rw [← Scheme.Hom.resLE_comp_ι g e]
    exact inferInstanceAs (SmoothOfRelativeDimension (n + 0) _)
  choose W hxW n hn using hchart
  -- on each member of the cover, `Lj^* ω_g ≅ ω_{g|W}` is invertible and in `D^b_{ctf}`
  have hloc (x : V) :
      DerivedCategory.isInvertible Λ (W x)
          ((L(((W x).ι)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex _ g)) ∧
        DerivedCategory.boundedConstructibleFiniteTor Λ (W x)
          ((L(((W x).ι)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex _ g)) := by
    have : TopologicalSpace.NoetherianSpace (W x) :=
      (W x).ι.isOpenEmbedding.isInducing.noetherianSpace
    have := quasiCompact_of_noetherianSpace (W x).ι
    have := quasiCompact_of_noetherianSpace ((W x).ι ≫ g)
    have := HasCompactification.comp_of_isOpenImmersion g (W x).ι
    have : HasInvertibleExponent Λ (W x) := .of_hom (W x).ι
    have := hn x
    obtain ⟨e⟩ := nonempty_iso_leftDerivedUpperStar_dualizingComplex_of_isOpenImmersion Λ (W x).ι g
    have h := boundedConstructibleFiniteTor_dualizingComplex Λ (n x) ((W x).ι ≫ g)
    exact ⟨DerivedCategory.isInvertible.of_iso e.symm
        (isInvertible_dualizingComplex Λ (d := n x) ((W x).ι ≫ g)),
      (DerivedCategory.boundedConstructible _ (W x)).prop_of_iso e.symm h.1,
      (DerivedCategory.finiteTorAmplitude _ (W x)).prop_of_iso e.symm h.2⟩
  refine ⟨isInvertible_of_forall_isInvertible_leftDerivedUpperStar Λ (fun x ↦ (W x).ι)
    (fun x ↦ ⟨x, ⟨x, hxW x⟩, rfl⟩) fun x ↦ (hloc x).1, ?_⟩
  -- a finite subcover
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ ((W x : V.Opens) : Set V))
    (fun x ↦ (W x).isOpen) (fun x _ ↦ Set.mem_iUnion.2 ⟨x, hxW x⟩)
  let U (k : Fin t.card) : V.Opens := W (t.equivFin.symm k)
  have hU (y : V) : ∃ k, y ∈ U k := by
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact ⟨t.equivFin ⟨x, hx⟩, by simpa [U] using hy⟩
  have hctf (k : Fin t.card) :
      DerivedCategory.boundedConstructible _ (U k)
          (D(((U k).ι)^*[ModuleCat.{u + 1} Λ]).obj (dualizingComplex _ g)) ∧
        DerivedCategory.finiteTorAmplitude _ (U k)
          (D(((U k).ι)^*[ModuleCat.{u + 1} Λ]).obj (dualizingComplex _ g)) :=
    let e := (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) (U k).ι).app
      (dualizingComplex _ g)
    ⟨(DerivedCategory.boundedConstructible _ _).prop_of_iso e (hloc (t.equivFin.symm k)).2.1,
      (DerivedCategory.finiteTorAmplitude _ _).prop_of_iso e (hloc (t.equivFin.symm k)).2.2⟩
  refine ⟨boundedConstructible_of_openCover Λ U hU _ fun k ↦ (hctf k).1, ?_⟩
  choose a b hab using fun k ↦ (hctf k).2
  refine ⟨-∑ k, |a k|, ∑ k, |b k|,
    torAmplitudeIn_of_openCover (ModuleCat.{u + 1} Λ) U hU _ fun k ↦ ?_⟩
  have ha := Finset.single_le_sum (f := fun k ↦ |a k|) (fun _ _ ↦ abs_nonneg _)
    (Finset.mem_univ k)
  have hb := Finset.single_le_sum (f := fun k ↦ |b k|) (fun _ _ ↦ abs_nonneg _)
    (Finset.mem_univ k)
  exact _root_.DerivedCategory.torAmplitudeIn.mono
    (by have := neg_abs_le (a k); linarith)
    (by have := le_abs_self (b k); linarith) (hab k)

variable (Λ) in
/-- Blueprint `lemma-section-normal-bundle--1`: Section invariant

For `g : V ⟶ B` smooth (of locally constant relative dimension) admitting a compactification,
on a source with noetherian underlying space, and a section `s` of `g`, the section invariant
`𝒞(g, s) = Ls^* ω_g = Ls^* Rg^! Λ_B` is an object of `Pic(D^b_{ctf}(B, Λ))`: it is ⊗-invertible
and lies in `D^b_{ctf}(B, Λ)`, since `ω_g` does
(`isInvertible_and_boundedConstructibleFiniteTor_dualizingComplex_of_smooth`)
and `Ls^*` preserves both properties. -/
theorem isInvertible_and_boundedConstructibleFiniteTor_sectionInvariant_of_smooth (g : V ⟶ B)
    [Smooth g] [HasCompactification g] [HasInvertibleExponent Λ V]
    [TopologicalSpace.NoetherianSpace V] (s : B ⟶ V) :
    DerivedCategory.isInvertible Λ B (sectionInvariant Λ g s) ∧
      DerivedCategory.boundedConstructibleFiniteTor Λ B (sectionInvariant Λ g s) :=
  have h := isInvertible_and_boundedConstructibleFiniteTor_dualizingComplex_of_smooth Λ g
  ⟨DerivedCategory.isInvertible.leftDerivedUpperStar s h.1,
    constructibleFiniteTor_leftDerivedUpperStar (ModuleCat.{u + 1} Λ) s h.2⟩

variable (Λ) in
/-- Blueprint `definition-deformation-normal-bundle`: Deformation space of a closed section

For `g : V ⟶ B` smooth (of locally constant relative dimension) and quasi-compact over a
noetherian base, and a closed section `s` of `g`, the family object `F = Ls̃^* ω_{g̃}` of the
deformation to the normal cone of `s` is an object of `Pic(D^b_{ctf}(𝔸¹_B, Λ))`: `g̃` is again
smooth (`AlgebraicGeometry.Scheme.Hom.smooth_deformationSpaceProj`) and quasi-compact, so
`D_s V` is noetherian, and the section invariant of `(g̃, s̃)` lies in `Pic(D^b_{ctf})`. -/
theorem isInvertible_and_boundedConstructibleFiniteTor_deformationFamilyObject_of_smooth
    [HasInvertibleExponent Λ B] [IsNoetherian B] (g : V ⟶ B) [Smooth g] [QuasiCompact g]
    (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B)
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)] :
    DerivedCategory.isInvertible Λ 𝔸(ULift.{u} (Fin 1); B) (deformationFamilyObject Λ g s) ∧
      DerivedCategory.boundedConstructibleFiniteTor Λ 𝔸(ULift.{u} (Fin 1); B)
        (deformationFamilyObject Λ g s) := by
  have := Scheme.Hom.smooth_deformationSpaceProj g s hs
  have : HasInvertibleExponent Λ s.ker.deformationSpace :=
    .of_hom (Scheme.Hom.deformationSpaceProj g s ≫ 𝔸(ULift.{u} (Fin 1); B) ↘ B)
  have : IsLocallyNoetherian 𝔸(ULift.{u} (Fin 1); B) :=
    LocallyOfFiniteType.isLocallyNoetherian (𝔸(ULift.{u} (Fin 1); B) ↘ B)
  have : CompactSpace 𝔸(ULift.{u} (Fin 1); B) :=
    QuasiCompact.compactSpace_of_compactSpace (𝔸(ULift.{u} (Fin 1); B) ↘ B)
  have : IsLocallyNoetherian s.ker.deformationSpace :=
    LocallyOfFiniteType.isLocallyNoetherian (Scheme.Hom.deformationSpaceProj g s)
  have : CompactSpace s.ker.deformationSpace :=
    QuasiCompact.compactSpace_of_compactSpace (Scheme.Hom.deformationSpaceProj g s)
  have : IsNoetherian s.ker.deformationSpace := ⟨⟩
  exact isInvertible_and_boundedConstructibleFiniteTor_sectionInvariant_of_smooth Λ _ _

end Smooth

end Etale

end AlgebraicGeometry
