import Langlands.Automorphic.ArchimedeanStandardAdmissibleProof
import Langlands.Automorphic.CuspidalArchimedeanGenericComponentReduction
import Langlands.Global.Factors.CuspidalSupportArchimedeanTensor

/-! # Archimedean constituents from nonzero standard tensor maps -/

noncomputable section

open scoped Matrix.Norms.Operator TensorProduct

set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Archimedean Langlands.LocalFactor.Archimedean PlaceComponent

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem isAdmissible_range_of_compact_map
    {K L V W : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [LieRing L] [LieAlgebra ℂ L]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ K V} {π : L →ₗ⁅ℂ⁆ Module.End ℂ V}
    (κ : Representation ℂ K W) (hfin : IsLocallyFinite ρ) (hweak : IsWeaklyContinuous ρ)
    (hadm : IsAdmissibleGKModule ρ) {U : Submodule ℂ V} (hU : IsStable ρ π U)
    (p : U →ₗ[ℂ] W) (hp : ∀ k x, p (restrictCompact hU k x) = κ k (p x)) :
    PlaceComponent.IsAdmissible κ (LinearMap.range p) := by
  have hUA : PlaceComponent.IsAdmissible ρ U := by
    intro d τ hτ
    have := hadm d τ hτ
    exact Submodule.finiteDimensional_of_le
      (show intertwiners ρ U d τ ≤ gkIntertwiners ρ d τ from fun _ h => h.2)
  intro d τ hτ
  have := isAdmissibleGKModule_restrict hU hUA d τ hτ
  let push : gkIntertwiners (restrictCompact hU) d τ →ₗ[ℂ]
      intertwiners κ (LinearMap.range p) d τ :=
    { toFun := fun f => ⟨p.comp f.val, fun x => LinearMap.mem_range_self p (f.val x),
        fun k x => (congrArg p (f.property k x)).trans (hp k (f.val x))⟩
      map_add' := fun f g => Subtype.ext (LinearMap.comp_add f.val g.val p)
      map_smul' := fun a f => Subtype.ext (LinearMap.comp_smul p a f.val) }
  apply Module.Finite.of_surjective push
  intro f
  obtain ⟨g, hg, hpg⟩ := CompactMaschke.exists_lift_intertwiner (restrictCompact hU) κ
    (isLocallyFinite_restrict hfin hU.1) (isWeaklyContinuous_restrict hweak hU.1)
    p hp τ f.val f.property.2 f.property.1
  exact ⟨⟨g, hg⟩, Subtype.ext hpg⟩

section Tensor

variable {R : Type*} [RCLike R] {n : ℕ}
  {V M W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] [AddCommGroup W] [Module ℂ W]

local notation "K" => Matrix.unitaryGroup (Fin n) R
local notation "L" => Matrix (Fin n) (Fin n) R

private theorem stable_of_matrix_directions
    {H : Type*} [AddCommGroup H] [Module ℂ H]
    (κ : Representation ℂ K H) (ψ : (ℂ ⊗[ℝ] L) →ₗ⁅ℂ⁆ Module.End ℂ H)
    {U : Submodule ℂ H} (hκ : ∀ k x, x ∈ U → κ k x ∈ U)
    (hψ : ∀ (X : L) x, x ∈ U → ψ (1 ⊗ₜ X) x ∈ U) :
    IsStable κ ψ U := by
  refine ⟨hκ, fun Z x hx => ?_⟩
  induction Z using TensorProduct.inductionOn with
  | tmul a X =>
    have h : a ⊗ₜ[ℝ] X = a • (1 ⊗ₜ[ℝ] X) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h, map_smul, LinearMap.smul_apply]
    exact U.smul_mem a (hψ X x hx)
  | add X Y hX hY =>
    rw [map_add, LinearMap.add_apply]
    exact U.add_mem hX hY

private theorem exists_irreducible_in_tensor_image
    (ρ : Representation ℂ K V) (π : (ℂ ⊗[ℝ] L) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (κ : Representation ℂ K W) (ψ : (ℂ ⊗[ℝ] L) →ₗ⁅ℂ⁆ Module.End ℂ W)
    (hfin : ∀ x, FiniteVectors.IsFiniteVector ρ x)
    (hweak : ∀ x (μ : V →ₗ[ℂ] ℂ), Continuous fun k => μ (ρ k x))
    (hadm : IsAdmissibleGKModule ρ)
    {S : Submodule ℂ (V ⊗[ℂ] M)} (q : S →ₗ[ℂ] W)
    (hq : IsPlaceTensorIntertwining ρ π κ ψ q) (hq0 : LinearMap.range q ≠ ⊥)
    (hdet : ∃ (d : ℕ) (τ : K →* Matrix (Fin d) (Fin d) ℂ), Continuous τ ∧
      ∀ J : Submodule ℂ W, IsStable κ ψ J → J ≠ ⊥ → intertwiners κ J d τ ≠ ⊥) :
    ∃ J : Submodule ℂ W, J ≤ LinearMap.range q ∧ IsIrreducible κ ψ J := by
  let source : K ⊕ L → Module.End ℂ V := Sum.elim ρ fun X => π (1 ⊗ₜ X)
  let target : K ⊕ L → Module.End ℂ W := Sum.elim κ fun X => ψ (1 ⊗ₜ X)
  have hstep (a : K ⊕ L) (z : S) :
      ∃ hz : TensorProduct.map (source a) LinearMap.id z.val ∈ S,
        q ⟨_, hz⟩ = target a (q z) := by
    cases a with
    | inl k => exact hq.1 k z
    | inr X => exact hq.2 X z
  have hrange (a : K ⊕ L) (w : W) (hw : w ∈ LinearMap.range q) :
      target a w ∈ LinearMap.range q := by
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hw
    obtain ⟨hz, he⟩ := hstep a z
    exact ⟨⟨_, hz⟩, he⟩
  obtain ⟨U, p, hp_range, hp0, hact⟩ :=
    exists_nonzero_subquotient_of_tensorProduct source target q
      (fun a z => (hstep a z).choose) (fun a z => (hstep a z).choose_spec) le_rfl hq0 hrange
  have hUs : IsStable ρ π U := stable_of_matrix_directions ρ π
    (fun k x hx => (hact (.inl k) ⟨x, hx⟩).choose)
    (fun X x hx => (hact (.inr X) ⟨x, hx⟩).choose)
  have hpK (k : K) (x : U) : p (restrictCompact hUs k x) = κ k (p x) :=
    (hact (.inl k) x).choose_spec
  have hp_stable (a : K ⊕ L) (y : W) (hy : y ∈ LinearMap.range p) :
      target a y ∈ LinearMap.range p := by
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    obtain ⟨hx, he⟩ := hact a x
    exact ⟨⟨_, hx⟩, he⟩
  have hps : IsStable κ ψ (LinearMap.range p) := stable_of_matrix_directions κ ψ
    (fun k => hp_stable (.inl k)) (fun X => hp_stable (.inr X))
  have hρfin : IsLocallyFinite ρ := fun x =>
    ⟨FiniteVectors.orbitSpan ρ x, hfin x, FiniteVectors.self_mem_orbitSpan ρ x,
      fun k _ hy => (FiniteVectors.orbitSubrepresentation ρ x).apply_mem_toSubmodule k hy⟩
  have hpa := isAdmissible_range_of_compact_map κ hρfin (fun μ x => hweak x μ) hadm hUs p hpK
  obtain ⟨_, τ, hτ, hτdet⟩ := hdet
  obtain ⟨J, hJp, hJ, _⟩ := exists_isIrreducible_isAdmissible κ ψ hps hpa hp0 τ hτ
    (fun N _ hNs hNne => hτdet N hNs hNne)
  exact ⟨J, hJp.trans hp_range, hJ⟩

end Tensor

universe u uM

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}
  {M : Type uM} [AddCommGroup M] [Module ℂ M]

local instance : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance (T : OperatorRealization F n) : AddCommGroup T.Space := Submodule.addCommGroup _

local notation "RP" => {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}
local notation "CP" => {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

/-- A nonzero map from an invariant subspace of a standard module tensored with a
multiplicity space suffices for the archimedean constituent of an irreducible
operator subquotient. -/
def ArchimedeanPlaceStandardConstituentOfNonzeroTensorStatement
    (Q : OperatorSubquotient F n) (M : Type uM) [AddCommGroup M] [Module ℂ M] : Prop :=
  Q.IsIrreducible → Nontrivial Q.Space →
    (∀ (v : RP) (ds : List RealBlock), realRank ds = n →
      ∀ {S : Submodule ℂ (realStandardKFinite n ds ⊗[ℂ] M)} (q : S →ₗ[ℂ] Q.Space),
        IsPlaceTensorIntertwining (realStandardRep n ds) (realStandardLie n ds)
          (Q.realPlaceCompactRepresentation v) (Q.realPlaceLieAction v) q →
        LinearMap.range q ≠ ⊥ → Q.HasRealPlaceStandardConstituent v ds) ∧
    ∀ (v : CP) (ds : List ComplexCharacterData), ds.length = n →
      ∀ {S : Submodule ℂ (complexStandardKFinite n ds ⊗[ℂ] M)} (q : S →ₗ[ℂ] Q.Space),
        IsPlaceTensorIntertwining (complexStandardRep n ds) (complexStandardLie n ds)
          (Q.complexPlaceCompactRepresentation v) (Q.complexPlaceLieAction v) q →
        LinearMap.range q ≠ ⊥ → Q.HasComplexPlaceStandardConstituent v ds

/-- Use admissibility of the standard model and detection in the target to extract
the irreducible image needed by the place constituent adapters. -/
theorem archimedeanPlaceStandardConstituent_of_nonzero_tensor (Q : OperatorSubquotient F n) :
    ArchimedeanPlaceStandardConstituentOfNonzeroTensorStatement Q M := by
  intro hQ hNontrivial
  let : Nontrivial Q.Space := hNontrivial
  constructor
  · intro v ds hn S q hq hq0
    have hgk := isRealGKModule_realStandardModule n ds
    obtain ⟨J, hJq, hJ⟩ := exists_irreducible_in_tensor_image _ _ _ _ hgk.1 hgk.2.1
      (realStandardAdmissible n ds) q hq hq0 (Q.exists_realPlace_detection hQ v)
    exact (archimedeanPlaceStandardConstituent_of_tensor (M := M) Q).1 v ds hn q hq hJq hJ
  · intro v ds hn S q hq hq0
    have hgk := isComplexGKModule_complexStandardModule n ds
    obtain ⟨J, hJq, hJ⟩ := exists_irreducible_in_tensor_image _ _ _ _ hgk.1 hgk.2.1
      (complexStandardAdmissible n ds) q hq hq0 (Q.exists_complexPlace_detection hQ v)
    exact (archimedeanPlaceStandardConstituent_of_tensor (M := M) Q).2 v ds hn q hq hJq hJ

end Langlands.Automorphic
