import Langlands.AlgebraicGeometry.Picard.EulerPositivityPreparationStatement
import Langlands.AlgebraicGeometry.Modules.EulerCharacteristicBasicProof
import Langlands.AlgebraicGeometry.Modules.FiniteClosedSupportCohomologyProof
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Positive finite-support Euler characteristics and nonempty ample cuts -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.AlgebraicGeometry.Modules
open Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- Finite closed support reduces the actual Euler characteristic to H⁰. -/
theorem eulerCharacteristic_eq_finrank_of_finiteClosedSupport
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules)
    (hM : HasFiniteCohomology f M) (hS : HasFiniteClosedSupport M) :
    eulerCharacteristic f M hM =
      (Module.finrank K ((relativeCohomology f 0).obj M) : ℤ) := by
  apply (eulerCharacteristicBasic K X f).2.2.2.2 M hM
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact ((finiteClosedSupportCohomology X M hS).2.2 _ f).1 m

/-- A finite-cohomology sheaf with finite closed support has positive Euler
characteristic exactly when it is nonzero. -/
theorem eulerCharacteristic_pos_iff_of_finiteClosedSupport
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules)
    (hM : HasFiniteCohomology f M) (hS : HasFiniteClosedSupport M) :
    0 < eulerCharacteristic f M hM ↔ ¬ IsZero M := by
  let : Module.Finite K ((relativeCohomology f 0).obj M) := hM.1 0
  rw [eulerCharacteristic_eq_finrank_of_finiteClosedSupport f M hM hS,
    Int.natCast_pos, Module.finrank_pos_iff,
    ← not_subsingleton_iff_nontrivial, ← ModuleCat.isZero_iff_subsingleton,
    ((relativeCohomologyZeroIso f).app M).isZero_iff,
    ((finiteClosedSupportCohomology X M hS).2.2 _ f).2]

/-- A proper field scheme of positive topological dimension cannot be affine. -/
theorem not_isAffine_of_proper_of_pos_dimension
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) (hp : IsProper f)
    (hd : 0 < topologicalKrullDim X) : ¬ IsAffine X := by
  intro ha
  let : IsAffine X := ha
  let : IsProper f := hp
  let : IsFinite f :=
    IsFinite.iff_isProper_and_isAffineHom.mpr ⟨hp, inferInstance⟩
  let : IsLocallyArtinian X := IsLocallyArtinian.of_locallyQuasiFinite f
  exact (not_lt_of_ge (topologicalKrullDim_zero_of_discreteTopology X)) hd

/-- An affine open in a nonaffine scheme always has a point outside it. -/
theorem exists_notMem_of_isAffineOpen_of_not_isAffine
    {X : Scheme.{u}} (hn : ¬ IsAffine X) (U : X.Opens)
    (hU : IsAffineOpen U) : ∃ y : X, y ∉ U := by
  by_contra h
  have htop : U = ⊤ := by
    apply top_unique
    intro x _
    exact not_not.mp (fun hx => h ⟨x, hx⟩)
  apply hn
  rw [htop] at hU
  let : IsAffine (⊤ : X.Opens).toScheme := hU
  exact IsAffine.of_isIso X.topIso.inv

/-- The two preparations for dimension induction in ample Euler positivity. -/
theorem eulerPositivityPreparation : EulerPositivityPreparationStatement.{u} := by
  intro K _ X f
  refine ⟨fun M hM hS => ⟨?_, ?_⟩, ?_⟩
  · exact eulerCharacteristic_eq_finrank_of_finiteClosedSupport f M hM hS
  · exact eulerCharacteristic_pos_iff_of_finiteClosedSupport f M hM hS
  · intro hp hd
    have hn := not_isAffine_of_proper_of_pos_dimension f hp hd
    refine ⟨hn, ?_⟩
    intro L hL x
    obtain ⟨n, hpos, s, hx, ha⟩ := hL.exists_section x
    exact ⟨n, hpos, s, hx, ha,
      exists_notMem_of_isAffineOpen_of_not_isAffine hn (L.sectionOpen s) ha⟩

end Langlands.AlgebraicGeometry.Picard
