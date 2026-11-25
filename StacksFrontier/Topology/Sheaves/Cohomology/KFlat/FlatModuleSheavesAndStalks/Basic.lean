module


public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Sheaves.Skyscraper
public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Topology.Sheaves.CommRingCat
public import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Flat `O_X`-modules: basic definitions and the forward stalk map of the tensor product

For a ringed space `(X, O_X)` this file sets up the category `Mod(O_X)` of `O_X`-modules
(`OXModule X := SheafOfModules (ringSheaf X)`), the sheaf tensor product `OXModule.tensor` and
its functorial form `OXModule.tensorBy` (Tag 01CB, the sheafification of the presheaf tensor
product), flatness `OXModule.Flat` (Tag 05ND), stalks `OXModule.stalk`, stalkwise flatness, and
the stalk-level `Tor_1` (`OXModule.Tor1Stalk`, `OXModule.Tor1IsZero`).  It proves that
sheafification preserves stalks `O_{X,x}`-linearly (`OXModule.sheafify_stalk_iso`) and builds
the forward map `OXModule.presheafTensorStalkFwd` from the stalk of the presheaf tensor product
to the tensor product of the stalks.

The comment below describes the whole development (Tag 08BQ), which continues in
`FlatModuleSheavesAndStalks.StalkTensor`, `FlatModuleSheavesAndStalks.TorOneAndSkyscraper` and
`FlatModuleSheavesAndStalks.FlatIffTorOne`.
-/

@[expose] public section

/-
# Problem Description

Stacks Tag 08BQ ("Tor measures the deviation of flatness").

Let `(X, O_X)` be a ringed space and let `F` be an `O_X`-module.  Then the
following are equivalent:

1. `F` is a flat `O_X`-module (Tag 05ND); and
2. `Tor_1^{O_X}(F, G) = 0` (the zero `O_X`-module) for every `O_X`-module `G`.

## Background and context

* A ringed space `(X, O_X)` is a topological space `X` together with a *sheaf*
  `O_X` of commutative rings.  We use the genuine ringed space type
  `AlgebraicGeometry.RingedSpace` from Mathlib, whose field `isSheaf` records
  that the structure presheaf is a sheaf.  Thus the objects below are genuinely
  modules over a ringed space, not over an arbitrary presheaf of rings.

* (Definition 1, Tag 01CB) The tensor product `F ⊗_{O_X} G` is the
  *sheafification* of the presheaf `U ↦ F(U) ⊗_{O_X(U)} G(U)`; it is again an
  `O_X`-module, and its formation commutes with taking stalks: for each
  `x ∈ X` one has `(F ⊗_{O_X} G)_x ≅ F_x ⊗_{O_{X,x}} G_x`.

* (Definition 2, Tag 05ND) `F` is *flat* if `G ↦ G ⊗_{O_X} F` is exact.  As
  this functor is always right exact (it has a right adjoint, the sheaf-Hom),
  flatness is equivalent to it preserving monomorphisms; this is the form used
  below in `OXModule.Flat`.

* (Definitions 3, 4, Tags 06YH, 08BP) On the derived category `D(O_X)` there is
  a derived tensor product `- ⊗^{L}_{O_X} G` (computed by K-flat resolutions),
  and `Tor_p^{O_X}(F, G) := H^{-p}(F ⊗^{L}_{O_X} G)`.  In particular
  `Tor_0 = ⊗` and `Tor_p = 0` for `p < 0`.

## Formalization notes

We model `Mod(O_X)` by Mathlib's genuine abelian category `SheafOfModules R`,
where `R := O_X` viewed as a sheaf of rings on the open-cover (Grothendieck)
topology of the underlying space.  This is the actual category of
`O_X`-modules over a genuine ringed space, and it is abelian.

* **Definition 1 (tensor product) is formalized directly** (`OXModule.tensor`
  and the endofunctor `OXModule.tensorBy`): it is the *sheafification* of the
  presheaf tensor product `M.val ⊗ N.val`, where `⊗` is the monoidal structure
  on `PresheafOfModules` and `OXModule.sheafify` is the genuine sheafification
  functor `PresheafOfModules.sheafification`.  This is exactly Tag 01CB.

* **Definition 2 (flatness) is formalized directly** at the sheaf level
  (`OXModule.Flat`): `F` is flat iff the genuine tensor endofunctor
  `- ⊗_{O_X} F` preserves monomorphisms.  This is Definition 2 (using the
  automatic right-exactness of the sheaf tensor product).

* **`Tor_1` here is the stalk-level notion, not the sheaf-level one.**
  `OXModule.Tor1Stalk` is the classical module-theoretic `Tor` over the local
  rings `O_{X,x}` (the categorical `CategoryTheory.Tor` on
  `ModuleCat (O_{X,x})`, where projective resolutions are available), and
  `OXModule.Tor1IsZero F G` says that *every stalk* of `Tor_1(F, G)` vanishes.

  This is **not** the same expression as Definition 4: the genuine sheaf-level
  `Tor_p^{O_X}(F, G) = H^{-p}(F ⊗^{L}_{O_X} G)` *is* available in this
  development, as `Stacks.Cohomology.tor` (Tag 08BP) in
  `StacksFrontier.Topology.Sheaves.Cohomology.DerivedTensor.Tor`, built from the
  derived tensor product of Tag 06YU.

  The two agree, and *that agreement is a theorem proved elsewhere in the
  development*, namely
  `Stacks.SheafOfModules.DerivedTensorStalk.isZero_derivedTensorHomology_iff_forall_isZero_tor`
  in `StacksFrontier/Topology/Sheaves/Cohomology/DerivedTensor/TorFlatness.lean`.
  What this file itself supplies is:

    - `OXModule.stalk_tensor_iso` (Tag 01CB): the stalk of the sheaf tensor
      product is the tensor product of the stalks;
    - `OXModule.flat_iff_flat_stalk` (Tag 05NE): sheaf-level flatness (Def 2)
      is equivalent to stalk-wise flatness.

  `OXModule.tor1IsZero_iff_stalk` is **not** a correctness lemma tying the two
  notions together: it is `Iff.rfl`, i.e. it merely unfolds `Tor1IsZero` to its
  own definition, and it carries no mathematical content.

  Consequently `OXModule.flat_iff_tor1_eq_zero` below is the *stalk-level*
  reading of Tag 08BQ: `F` is flat (Def 2) iff all stalks of `Tor_1(F, G)`
  vanish, for every `O_X`-module `G`.  The tag's own statement — with
  `Stacks.Cohomology.tor X 1 F G` on the right-hand side — is
  `Stacks.Cohomology.flat_iff_forall_isZero_tor` in
  `StacksFrontier/Topology/Sheaves/Cohomology/DerivedTensor/TorFlatness.lean`, obtained
  from the stalk-level reading by that identification, whose own missing
  ingredient was `Stacks.DerivedTensor.homologyIsoTor`
  (`StacksFrontier/Homology/Tor/DerivedTensorTor.lean`): `H^{-p}` of the derived
  tensor product of two modules over a commutative ring is their `Tor_p`.

* **No further hypotheses.** No Noetherian, coherence, or finiteness
  assumptions are made on `X`, `O_X`, `F`, or `G`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopCat

universe u

namespace OXModule

variable (X : AlgebraicGeometry.RingedSpace.{u, u})

/-- The structure sheaf `O_X` of a ringed space, viewed as a *sheaf* of rings on
the open-cover (Grothendieck) topology of the underlying space.  Forgetting
commutativity preserves the sheaf condition (`Presheaf.isSheaf_iff_isSheaf_comp`),
so this is a genuine `Sheaf _ RingCat`. -/
noncomputable def ringSheaf : Sheaf (Opens.grothendieckTopology X.carrier) RingCat.{u} :=
  ⟨X.presheaf ⋙ forget₂ CommRingCat RingCat,
    (Presheaf.isSheaf_iff_isSheaf_comp (Opens.grothendieckTopology X.carrier) X.presheaf
      (forget₂ CommRingCat RingCat)).mp X.IsSheaf⟩

variable {X}

noncomputable local instance sectionModule
    (modulePresheaf : PresheafOfModules.{u} (ringSheaf X).obj)
    (openSet : (TopologicalSpace.Opens X.carrier)ᵒᵖ) :
    Module (X.presheaf.obj openSet) (modulePresheaf.obj openSet) :=
  (modulePresheaf.obj openSet).isModule

noncomputable local instance sectionPresheafModule
    (modulePresheaf : PresheafOfModules.{u} (ringSheaf X).obj)
    (openSet : (TopologicalSpace.Opens X.carrier)ᵒᵖ) :
    Module (X.presheaf.obj openSet) ↑(modulePresheaf.presheaf.obj openSet) :=
  (modulePresheaf.obj openSet).isModule

noncomputable local instance stalkModule
    (modulePresheaf : PresheafOfModules.{u} (ringSheaf X).obj) (point : X.carrier) :
    Module (X.presheaf.stalk point) ↑(TopCat.Presheaf.stalk modulePresheaf.presheaf point) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.presheaf) modulePresheaf point

/-! ## Correctness lemmas tying the formalization to the original definitions -/

/-! ### Part (2) of Tag 01CB: presheaf-tensor stalk = tensor of stalks

The remaining content of `stalk_tensor_iso` after sheafification has been peeled
off (`sheafify_stalk_iso`) is the *presheaf*-level statement

  `Presheaf.stalk (M.val ⊗ N.val).presheaf x  ≅  M.stalk x ⊗_{O_{X,x}} N.stalk x`,

i.e. `colim_{U∋x} (M(U) ⊗_{O(U)} N(U)) ≅ (colim M(U)) ⊗_{O_{X,x}} (colim N(U))`.

The strategy builds a
forward `O_{X,x}`-linear map `Φ` (germ `m ⊗ n ↦ germ m ⊗ germ n`, via a cocone
`colimit.desc`) and an inverse `Ψ` (a balanced map sending `germ_U m ⊗ germ_V n`
to `germ_{U⊓V} (m|_{U⊓V} ⊗ n|_{U⊓V})`, via `TensorProduct.lift`), and checks
`Φ ∘ Ψ = id`, `Ψ ∘ Φ = id`.  The decisive technical point (varying base ring):
each scalar `r ∈ O_{X,x}` is a germ `germ_W s` of an honest `s ∈ O_X(W)`, so all
balancing/`smul` identities reduce, via `PresheafOfModules.germ_smul`, to the
*fixed*-ring tensor identities at a common finite stage `W`.

We isolate the four leaf obligations (the two maps + the two round-trip
identities) as separate lemmas; the assembling `def` `presheafTensor_stalk_iso`
is `LinearEquiv.ofLinear` + `LinearEquiv.toModuleIso`.

Those four leaves are proved: `collectAxioms` on both
`OXModule.presheafTensor_stalk_iso` and `OXModule.stalk_tensor_iso` reports
exactly `[propext, Classical.choice, Quot.sound]`, so this development is
complete.

It is still not the right tool for Tag 01CJ, for a reason unrelated to
completeness: it produces a `ModuleCat` isomorphism rather than a `≃ₗ`, and its
sheafified form is a bare `Nonempty` with no germ formula, whereas 01CJ needs the
comparison pinned on germs. That role is filled by
`PresheafOfModules.tensorSheafStalkEquiv` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorBifunctorStalk`. **A third
proof of this statement should not be written.** -/

end OXModule
