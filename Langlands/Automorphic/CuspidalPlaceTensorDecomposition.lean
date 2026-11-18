import Langlands.Automorphic.CuspidalArchimedeanDensityModels
import Langlands.Automorphic.FiniteFamilyGKTensor

/-! # Tensor decomposition at the actual infinite places of a cuspidal realization -/

noncomputable section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open scoped TensorProduct

namespace Langlands.Automorphic

open Langlands.Global InfinitePlaceFamily
open Langlands.Archimedean.FiniteFamilyTensor

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem tmul_nonzero
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {v : V} {w : W} (hv : v ≠ 0) (hw : w ≠ 0) : v ⊗ₜ[ℂ] w ≠ 0 := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one ℂ hv
  obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_eq_one ℂ hw
  intro hz
  have h := congrArg (TensorProduct.lift (φ.smulRight ψ)) hz
  simp [hφ, hψ] at h

private theorem tprod_nonzero
    {I : Type*} [Fintype I] {A : I → Type*}
    [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]
    (b : ∀ i, A i) (hb : ∀ i, b i ≠ 0) : PiTensorProduct.tprod ℂ b ≠ 0 := by
  classical
  choose φ hφ using fun i => Module.Projective.exists_dual_eq_one ℂ (hb i)
  let f : (⨂[ℂ] i, A i) →ₗ[ℂ] ℂ :=
    PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ I ℂ).compLinearMap φ)
  have hf : f (PiTensorProduct.tprod ℂ b) = 1 := by simp [f, hφ]
  intro hz
  rw [hz, map_zero] at hf
  exact zero_ne_one hf

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance placeTensorRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance placeTensorContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance placeTensorSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance placeTensorFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance placeTensorStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance placeTensorSpaceGroup (S : OperatorRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

namespace OperatorRealization.PlaceDensityModels

variable {S : OperatorRealization F n} (D : S.PlaceDensityModels)
  (A : Subrepresentation S.finiteRepresentation)

local instance placeTensorFactorGroup (i : Index F) : AddCommGroup (D.subspace i) :=
  Submodule.addCommGroup _
local instance placeTensorFiniteGroup : AddCommGroup A.toSubmodule :=
  Submodule.addCommGroup _

/-- The dependent tensor of the actual source models is the actual infinite multiplicity. -/
def multiplicityTensorEquiv
    (hS : S.IsIrreducible) (hne : A ≠ ⊥) (hA : A.toRepresentation.IsIrreducible)
    (ha : IsAdmissible A.toRepresentation) :
    {e : (⨂[ℂ] i, (D.subspace i : Type u)) ≃ₗ[ℂ] S.FiniteMultiplicity A //
      IsTensorEquivalence D.sourceCompact D.sourceLie
        (S.finiteMultiplicityPlaceCompact A) (S.finiteMultiplicityPlaceLie A) e} := by
  let h := tensorDecomposition.{u, 0, 0, u, u} (Index F) (Compact n) (Lie n)
    (fun i => (D.subspace i : Type u)) D.sourceCompact D.sourceLie D.densityHyp
    (S.FiniteMultiplicity A) (S.finiteMultiplicityPlaceCompact A)
    (S.finiteMultiplicityPlaceLie A)
    (S.finiteMultiplicityPlaceFamily_commutes A hne hA)
    (S.finiteMultiplicityPlaceFamily_irreducible A hS hne hA ha)
    (D.exists_nonzero_multiplicityHom A hS hne hA ha)
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

/-- Finite evaluation combined with all the infinite source models recovers the carrier. -/
def fullTensorEquiv
    (hS : S.IsIrreducible) (hne : A ≠ ⊥) (hA : A.toRepresentation.IsIrreducible)
    (ha : IsAdmissible A.toRepresentation) :
    A.toSubmodule ⊗[ℂ] (⨂[ℂ] i, (D.subspace i : Type u)) ≃ₗ[ℂ] S.Space :=
  (TensorProduct.congr (LinearEquiv.refl ℂ _)
    (D.multiplicityTensorEquiv A hS hne hA ha).val).trans
      (S.finiteMultiplicityEquiv A hS hne hA ha)

@[simp] theorem fullTensorEquiv_tmul
    (hS : S.IsIrreducible) (hne : A ≠ ⊥) (hA : A.toRepresentation.IsIrreducible)
    (ha : IsAdmissible A.toRepresentation) (a : A.toSubmodule)
    (t : ⨂[ℂ] i, (D.subspace i : Type u)) :
    D.fullTensorEquiv A hS hne hA ha (a ⊗ₜ[ℂ] t) =
      (D.multiplicityTensorEquiv A hS hne hA ha).val t a := rfl

/-- The full tensor equivalence intertwines the genuine finite adelic action. -/
theorem fullTensorEquiv_finite
    (hS : S.IsIrreducible) (hne : A ≠ ⊥) (hA : A.toRepresentation.IsIrreducible)
    (ha : IsAdmissible A.toRepresentation) (d : FiniteAdelicGL F n)
    (a : A.toSubmodule) (t : ⨂[ℂ] i, (D.subspace i : Type u)) :
    D.fullTensorEquiv A hS hne hA ha ((A.toRepresentation d a) ⊗ₜ[ℂ] t) =
      S.finiteRepresentation d (D.fullTensorEquiv A hS hne hA ha (a ⊗ₜ[ℂ] t)) :=
  S.finiteMultiplicityEvaluation_finite A d
    (a ⊗ₜ[ℂ] (D.multiplicityTensorEquiv A hS hne hA ha).val t)

/-- Each genuine local compact action acts on its own pure tensor component. -/
theorem fullTensorEquiv_compact
    (hS : S.IsIrreducible) (hne : A ≠ ⊥) (hA : A.toRepresentation.IsIrreducible)
    (ha : IsAdmissible A.toRepresentation) (i : Index F) (k : Compact n i)
    (a : A.toSubmodule) (b c : ∀ j, D.subspace j)
    (hother : ∀ j, j ≠ i → c j = b j) (hlocal : c i = D.sourceCompact i k (b i)) :
    D.fullTensorEquiv A hS hne hA ha (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ c) =
      S.placeCompactFamily i k
        (D.fullTensorEquiv A hS hne hA ha (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ b)) := by
  exact congrArg (fun f : S.FiniteMultiplicity A => f a)
    ((D.multiplicityTensorEquiv A hS hne hA ha).property.1 i k b c hother hlocal)

/-- Each genuine local Lie action acts on its own pure tensor component. -/
theorem fullTensorEquiv_lie
    (hS : S.IsIrreducible) (hne : A ≠ ⊥) (hA : A.toRepresentation.IsIrreducible)
    (ha : IsAdmissible A.toRepresentation) (i : Index F) (X : Lie n i)
    (a : A.toSubmodule) (b c : ∀ j, D.subspace j)
    (hother : ∀ j, j ≠ i → c j = b j) (hlocal : c i = D.sourceLie i X (b i)) :
    D.fullTensorEquiv A hS hne hA ha (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ c) =
      S.placeLieFamily i X
        (D.fullTensorEquiv A hS hne hA ha (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ b)) := by
  exact congrArg (fun f : S.FiniteMultiplicity A => f a)
    ((D.multiplicityTensorEquiv A hS hne hA ha).property.2 i X b c hother hlocal)

/-- Nonzero prescribed finite vectors and nonzero infinite tensors remain nonzero. -/
theorem fullTensorEquiv_tmul_ne_zero
    (hS : S.IsIrreducible) (hne : A ≠ ⊥) (hA : A.toRepresentation.IsIrreducible)
    (ha : IsAdmissible A.toRepresentation) (a : A.toSubmodule)
    (t : ⨂[ℂ] i, (D.subspace i : Type u)) (ha0 : a ≠ 0) (ht0 : t ≠ 0) :
    D.fullTensorEquiv A hS hne hA ha (a ⊗ₜ[ℂ] t) ≠ 0 := by
  intro hzero
  have hz : a ⊗ₜ[ℂ] t = 0 :=
    (D.fullTensorEquiv A hS hne hA ha).injective (hzero.trans (map_zero (D.fullTensorEquiv A hS hne hA ha).toLinearMap).symm)
  exact tmul_nonzero ha0 ht0 hz

/-- A nonzero pure infinite tensor may be combined with any prescribed nonzero finite vector. -/
theorem fullTensorEquiv_pure_ne_zero
    (hS : S.IsIrreducible) (hne : A ≠ ⊥) (hA : A.toRepresentation.IsIrreducible)
    (ha : IsAdmissible A.toRepresentation) (a : A.toSubmodule) (b : ∀ i, D.subspace i)
    (ha0 : a ≠ 0) (hb : ∀ i, b i ≠ 0) :
    D.fullTensorEquiv A hS hne hA ha (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ b) ≠ 0 := by
  let := Fintype.ofFinite (Index F)
  exact D.fullTensorEquiv_tmul_ne_zero A hS hne hA ha a _ ha0 (tprod_nonzero b hb)

end OperatorRealization.PlaceDensityModels

namespace CuspidalOperatorRealization

variable [CompactSpace (AdeleQuotient F)] {r : ℕ} (T : CuspidalOperatorRealization F r)

/-- The tensor decomposition at all actual places, using the chosen finite and infinite models. -/
def allPlaceTensorEquiv :
    T.finiteInfiniteDecomposition.finite.toSubmodule ⊗[ℂ]
      (⨂[ℂ] i, (T.placeDensityModels.subspace i : Type u)) ≃ₗ[ℂ] T.Space :=
  T.placeDensityModels.fullTensorEquiv T.finiteInfiniteDecomposition.finite
    T.irreducible T.finiteInfiniteDecomposition.nonzero
    T.finiteInfiniteDecomposition.irreducible T.finiteInfiniteDecomposition.admissible

/-- Actual cuspidal realizations admit the complete finite/infinite tensor decomposition. -/
def PlaceTensorDecompositionStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]
    (r : ℕ) (T : CuspidalOperatorRealization K r),
    let A := T.finiteInfiniteDecomposition
    let D := T.placeDensityModels
    ∃ E : (⨂[ℂ] i, (D.subspace i : Type u)) ≃ₗ[ℂ] A.InfiniteSpace,
      IsTensorEquivalence D.sourceCompact D.sourceLie
        (T.realization.finiteMultiplicityPlaceCompact A.finite)
        (T.realization.finiteMultiplicityPlaceLie A.finite) E ∧
      ∃ e : A.finite.toSubmodule ⊗[ℂ]
          (⨂[ℂ] i, (D.subspace i : Type u)) ≃ₗ[ℂ] T.Space,
        ∀ a t, e (a ⊗ₜ[ℂ] t) = E t a

/-- The actual-model specialization has no open theorem premise. -/
theorem placeTensorDecomposition : PlaceTensorDecompositionStatement.{u} := by
  intro K _ _ _ r T
  let A := T.finiteInfiniteDecomposition
  let D := T.placeDensityModels
  let E := D.multiplicityTensorEquiv A.finite T.irreducible A.nonzero
    A.irreducible A.admissible
  exact ⟨E.val, E.property, T.allPlaceTensorEquiv, fun _ _ => rfl⟩

end CuspidalOperatorRealization

end Langlands.Automorphic
