import Langlands.Global.Factors.CuspidalSupportEveryPlaceStatement
import Langlands.Automorphic.OperatorSubquotientPlaceComponentComplex
import Langlands.LinearAlgebra.TensorProductSubquotient
import Langlands.Representation.Archimedean.RealStandardModuleGKModule

/-! # Standard constituents of archimedean tensor subquotients -/

noncomputable section

open scoped TensorProduct Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u uM

namespace Langlands.Automorphic

open Langlands.Archimedean Langlands.Global Langlands.LocalFactor.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

section TensorMap

variable {R : Type*} [RCLike R] {n : ℕ}
  {V M H : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] [AddCommGroup H] [Module ℂ H]

local notation "K" => Matrix.unitaryGroup (Fin n) R
local notation "L" => Matrix (Fin n) (Fin n) R

/-- A map from a subspace of `V ⊗ M` intertwines the compact operators and the
Lie operators along real matrix directions, acting on `V` alone in the source.
The witnesses also give stability of the domain under these operators. -/
def IsPlaceTensorIntertwining
    (ρ : Representation ℂ K V) (π : (ℂ ⊗[ℝ] L) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (κ : Representation ℂ K H) (ψ : (ℂ ⊗[ℝ] L) →ₗ⁅ℂ⁆ Module.End ℂ H)
    {S : Submodule ℂ (V ⊗[ℂ] M)} (q : S →ₗ[ℂ] H) : Prop :=
  (∀ (k : K) (z : S), ∃ hz : TensorProduct.map (ρ k) LinearMap.id z.val ∈ S,
    q ⟨_, hz⟩ = κ k (q z)) ∧
  ∀ (X : L) (z : S), ∃ hz : TensorProduct.map (π (1 ⊗ₜ X)) LinearMap.id z.val ∈ S,
    q ⟨_, hz⟩ = ψ (1 ⊗ₜ X) (q z)

private theorem isStable_of_matrix_directions
    (κ : Representation ℂ K H) (ψ : (ℂ ⊗[ℝ] L) →ₗ⁅ℂ⁆ Module.End ℂ H)
    (U : Submodule ℂ H) (hκ : ∀ (k : K) x, x ∈ U → κ k x ∈ U)
    (hψ : ∀ (X : L) x, x ∈ U → ψ (1 ⊗ₜ X) x ∈ U) :
    PlaceComponent.IsStable κ ψ U := by
  refine ⟨hκ, fun Z x hx => ?_⟩
  induction Z using TensorProduct.inductionOn with
  | tmul c X =>
    have h : c ⊗ₜ[ℝ] X = c • (1 ⊗ₜ[ℝ] X) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h, map_smul, LinearMap.smul_apply]
    exact U.smul_mem c (hψ X x hx)
  | add X Y hX hY =>
    rw [map_add, LinearMap.add_apply]
    exact U.add_mem hX hY

private theorem standardConstituent_of_tensor
    (V : Submodule ℂ (Langlands.GeneralLinear n R → ℂ))
    (ρ : Representation ℂ K V) (π : (ℂ ⊗[ℝ] L) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (κ : Representation ℂ K H) (ψ : (ℂ ⊗[ℝ] L) →ₗ⁅ℂ⁆ Module.End ℂ H)
    (hρ : ∀ (k : K) (f : V), (ρ k f : Langlands.GeneralLinear n R → ℂ) =
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n R) (Unitary.toUnits k) f)
    (hπ : ∀ (X : L) (f : V), (π (1 ⊗ₜ X) f : Langlands.GeneralLinear n R → ℂ) =
      Archimedean.rightDerivative (Archimedean.matrixModel R n) X f)
    {S : Submodule ℂ (V ⊗[ℂ] M)} (q : S →ₗ[ℂ] H)
    (hq : IsPlaceTensorIntertwining ρ π κ ψ q)
    {J : Submodule ℂ H} (hJq : J ≤ LinearMap.range q)
    (hJ : PlaceComponent.IsIrreducible κ ψ J) :
    ∃ W : Submodule ℂ (Langlands.GeneralLinear n R → ℂ), W ≤ V ∧
    ∃ A : W →ₗ[ℂ] H,
      (∀ (k : Archimedean.unitaryCompact R n) (f : W),
        ∃ hf : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n R) k.val f ∈ W,
          A ⟨_, hf⟩ = κ ⟨((k.val : Langlands.GeneralLinear n R) : L), k.2⟩ (A f)) ∧
      (∀ (X : L) (f : W),
        ∃ hf : Archimedean.rightDerivative (Archimedean.matrixModel R n) X f ∈ W,
          A ⟨_, hf⟩ = ψ (1 ⊗ₜ X) (A f)) ∧
      LinearMap.range A ≠ ⊥ ∧
      ∀ U : Submodule ℂ H, U ≤ LinearMap.range A →
        (∀ (k : K) x, x ∈ U → κ k x ∈ U) →
        (∀ (X : L) x, x ∈ U → ψ (1 ⊗ₜ X) x ∈ U) →
        U = ⊥ ∨ U = LinearMap.range A := by
  let source : K ⊕ L → Module.End ℂ V := Sum.elim (fun k => ρ k) (fun X => π (1 ⊗ₜ X))
  let target : K ⊕ L → Module.End ℂ H := Sum.elim (fun k => κ k) (fun X => ψ (1 ⊗ₜ X))
  have hqOps (a : K ⊕ L) (z : S) :
      ∃ hz : TensorProduct.map (source a) LinearMap.id z.val ∈ S,
        q ⟨_, hz⟩ = target a (q z) := by
    cases a with
    | inl k => exact hq.1 k z
    | inr X => exact hq.2 X z
  have hS (a : K ⊕ L) (z : S) : TensorProduct.map (source a) LinearMap.id z.val ∈ S :=
    (hqOps a z).choose
  have hJStable (a : K ⊕ L) (x : H) (hx : x ∈ J) : target a x ∈ J := by
    cases a with
    | inl k => exact hJ.2.1.1 k x hx
    | inr X => exact hJ.2.1.2 (1 ⊗ₜ X) x hx
  obtain ⟨W, A, hA, hAOps⟩ := exists_subquotient_of_tensorProduct source target q hS
    (fun a z => (hqOps a z).choose_spec) hJq hJ.1 hJStable
    (fun U hU hUStable => hJ.2.2 U hU
      (isStable_of_matrix_directions κ ψ U
        (fun k => hUStable (.inl k)) (fun X => hUStable (.inr X))))
  let W' : Submodule ℂ (Langlands.GeneralLinear n R → ℂ) := W.map V.subtype
  let e : W ≃ₗ[ℂ] W' := Submodule.equivMapOfInjective V.subtype V.subtype_injective W
  let B : W' →ₗ[ℂ] H := A.comp e.symm.toLinearMap
  have hBA (x : W) : B (e x) = A x := by simp [B]
  have hB : LinearMap.range B = J :=
    (LinearMap.range_comp_of_range_eq_top A (LinearMap.range_eq_top.mpr e.symm.surjective)).trans hA
  refine ⟨W', V.map_subtype_le W, B, ?_, ?_, ?_, ?_⟩
  · intro k f
    obtain ⟨x, rfl⟩ := e.surjective f
    let k' : K := ⟨(k.val : L), k.2⟩
    obtain ⟨hx, hxA⟩ := hAOps (.inl k') x
    let y : W := ⟨ρ k' x.val, hx⟩
    have hy : (e y).val = Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n R) k.val
        (e x).val := by
      change (ρ k' x.val : Langlands.GeneralLinear n R → ℂ) =
        Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n R) k.val x.val
      rw [hρ, show (Unitary.toUnits k' : Langlands.GeneralLinear n R) = k.val from Units.ext rfl]
    have hf : _ ∈ W' := hy ▸ (e y).2
    refine ⟨hf, ?_⟩
    rw [show (⟨_, hf⟩ : W') = e y from Subtype.ext hy.symm, hBA, hBA]
    exact hxA
  · intro X f
    obtain ⟨x, rfl⟩ := e.surjective f
    obtain ⟨hx, hxA⟩ := hAOps (.inr X) x
    let y : W := ⟨π (1 ⊗ₜ X) x.val, hx⟩
    have hy : (e y).val = Archimedean.rightDerivative (Archimedean.matrixModel R n) X
        (e x).val := hπ X x.val
    have hf : _ ∈ W' := hy ▸ (e y).2
    refine ⟨hf, ?_⟩
    rw [show (⟨_, hf⟩ : W') = e y from Subtype.ext hy.symm, hBA, hBA]
    exact hxA
  · rw [hB]
    exact hJ.1
  · intro U hU hUK hUL
    rw [hB] at hU ⊢
    exact hJ.2.2 U hU (isStable_of_matrix_directions κ ψ U hUK hUL)

end TensorMap

section Places

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}
  {M : Type uM} [AddCommGroup M] [Module ℂ M]

local instance supportTensorRationalGroup : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance supportTensorContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance supportTensorFiniteSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance supportTensorFormGroup : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance supportTensorStableGroup : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance supportTensorRealizationGroup (T : OperatorRealization F n) : AddCommGroup T.Space := Submodule.addCommGroup _

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

/-- At a real or complex place, an irreducible place subspace of the image of a
map from a subspace of the standard module tensored with a multiplicity space
gives a constituent of the standard module at that place. -/
def ArchimedeanPlaceStandardConstituentOfTensorStatement
    (Q : OperatorSubquotient F n) (M : Type uM) [AddCommGroup M] [Module ℂ M] : Prop :=
  (∀ (v : RP) (ds : List RealBlock), realRank ds = n →
    ∀ {S : Submodule ℂ (realStandardKFinite n ds ⊗[ℂ] M)} (q : S →ₗ[ℂ] Q.Space),
    IsPlaceTensorIntertwining (realStandardRep n ds) (realStandardLie n ds)
      (Q.realPlaceCompactRepresentation v) (Q.realPlaceLieAction v) q →
    ∀ {J : Submodule ℂ Q.Space}, J ≤ LinearMap.range q →
    PlaceComponent.IsIrreducible (Q.realPlaceCompactRepresentation v) (Q.realPlaceLieAction v) J →
    Q.HasRealPlaceStandardConstituent v ds) ∧
  ∀ (v : CP) (ds : List ComplexCharacterData), ds.length = n →
    ∀ {S : Submodule ℂ (complexStandardKFinite n ds ⊗[ℂ] M)} (q : S →ₗ[ℂ] Q.Space),
    IsPlaceTensorIntertwining (complexStandardRep n ds) (complexStandardLie n ds)
      (Q.complexPlaceCompactRepresentation v) (Q.complexPlaceLieAction v) q →
    ∀ {J : Submodule ℂ Q.Space}, J ≤ LinearMap.range q →
    PlaceComponent.IsIrreducible (Q.complexPlaceCompactRepresentation v)
      (Q.complexPlaceLieAction v) J →
    Q.HasComplexPlaceStandardConstituent v ds

/-- Extract the same irreducible image from the standard module at either type of
archimedean place. -/
theorem archimedeanPlaceStandardConstituent_of_tensor (Q : OperatorSubquotient F n) :
    ArchimedeanPlaceStandardConstituentOfTensorStatement Q M := by
  constructor
  · intro v ds hn S q hq J hJq hJ
    exact ⟨hn, standardConstituent_of_tensor (realStandardKFinite n ds)
      (realStandardRep n ds) (realStandardLie n ds)
      (Q.realPlaceCompactRepresentation v) (Q.realPlaceLieAction v)
      (realStandardRep_apply_coe n ds) (realStandardLie_one_tmul_apply_coe n ds)
      q hq hJq hJ⟩
  · intro v ds hn S q hq J hJq hJ
    exact ⟨hn, standardConstituent_of_tensor (complexStandardKFinite n ds)
      (complexStandardRep n ds) (complexStandardLie n ds)
      (Q.complexPlaceCompactRepresentation v) (Q.complexPlaceLieAction v)
      (principalSeriesRep_apply_coe ℂ n (complexPositionCharacter ds))
      (principalSeriesLie_one_tmul_apply_coe ℂ n (complexPositionCharacter ds))
      q hq hJq hJ⟩

namespace OperatorSubquotient

variable (Q : OperatorSubquotient F n) [Nontrivial Q.Space]

/-- A surjective realization of an irreducible jointly admissible `Q` from a
tensor product with a real standard module gives a real place constituent. -/
theorem hasRealPlaceStandardConstituent_of_surjective_tensor
    (hQ : Q.IsIrreducible) (hAdm : Q.IsJointlyAdmissible)
    (v : RP) (ds : List RealBlock) (hn : realRank ds = n)
    {S : Submodule ℂ (realStandardKFinite n ds ⊗[ℂ] M)} (q : S →ₗ[ℂ] Q.Space)
    (hq : IsPlaceTensorIntertwining (realStandardRep n ds) (realStandardLie n ds)
      (Q.realPlaceCompactRepresentation v) (Q.realPlaceLieAction v) q)
    (hsurj : Function.Surjective q) :
    Q.HasRealPlaceStandardConstituent v ds := by
  obtain ⟨J, hJ, _⟩ := Q.exists_realPlaceComponent hQ hAdm v
  have hJq : J ≤ LinearMap.range q := by rw [LinearMap.range_eq_top.mpr hsurj]; exact le_top
  exact (archimedeanPlaceStandardConstituent_of_tensor (M := M) Q).1 v ds hn q hq hJq hJ

/-- A surjective realization of an irreducible jointly admissible `Q` from a
tensor product with a complex standard module gives a complex place constituent. -/
theorem hasComplexPlaceStandardConstituent_of_surjective_tensor
    (hQ : Q.IsIrreducible) (hAdm : Q.IsJointlyAdmissible)
    (v : CP) (ds : List ComplexCharacterData) (hn : ds.length = n)
    {S : Submodule ℂ (complexStandardKFinite n ds ⊗[ℂ] M)} (q : S →ₗ[ℂ] Q.Space)
    (hq : IsPlaceTensorIntertwining (complexStandardRep n ds) (complexStandardLie n ds)
      (Q.complexPlaceCompactRepresentation v) (Q.complexPlaceLieAction v) q)
    (hsurj : Function.Surjective q) :
    Q.HasComplexPlaceStandardConstituent v ds := by
  obtain ⟨J, hJ, _⟩ := Q.exists_complexPlaceComponent hQ hAdm v
  have hJq : J ≤ LinearMap.range q := by rw [LinearMap.range_eq_top.mpr hsurj]; exact le_top
  exact (archimedeanPlaceStandardConstituent_of_tensor (M := M) Q).2 v ds hn q hq hJq hJ

end OperatorSubquotient
end Places

end Langlands.Automorphic
