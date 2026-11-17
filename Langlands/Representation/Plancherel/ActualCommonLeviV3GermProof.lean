import Langlands.Representation.Plancherel.ActualCommonLeviV3Statement
import Langlands.Representation.Plancherel.RationalUnramifiedScalarContinuation

/-! # Uniqueness of the actual common-Levi tensor germ -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

universe u uV uL uI uW

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure Topology
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel

namespace UnramifiedOperatorFamily

variable {L : Type uL} [Group L] [TopologicalSpace L]
  {I : Type uI} {ν : I → (L →* ℝ≥0ˣ)}
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Scalar linear tests determine a polynomial family on any open part of a
dense parameter set. No topology on the vector space is required. -/
theorem polynomial_eq_zero_on_open_of_dense
    {D U : Set (unramifiedCharacters ν)} (hD : Dense D) (hU : IsOpen U)
    (f : unramifiedCharacters ν → W)
    (hf : IsPolynomialOn Set.univ (fun z => f z.val))
    (hz : ∀ z ∈ D, z ∈ U → f z = 0) :
    ∀ z ∈ U, f z = 0 := by
  intro z hzU
  apply (Module.forall_dual_apply_eq_zero_iff ℂ (f z)).mp
  intro ℓ
  obtain ⟨a, ha⟩ := (isPolynomialOn_scalar_iff _).mp (hf.linearMap ℓ)
  have he : (fun x : U => a.val x.val) = (fun _ : U => (0 : ℂ)) := by
    apply Continuous.ext_on (hD.preimage hU.isOpenMap_subtype_val)
      ((continuous_unramifiedRegularFunction ν a).comp continuous_subtype_val)
      continuous_const
    intro x hx
    change a.val x.val = 0
    rw [← ha ⟨x.val, Set.mem_univ _⟩, hz x.val hx x.property, map_zero]
  rw [ha ⟨z, Set.mem_univ _⟩]
  exact congrFun he ⟨z, hzU⟩

/-- Equality on a dense set cross-multiplies any two polynomial operator
numerators on the intersection of their open domains. -/
theorem polynomial_operator_cross_eq_of_dense
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {D U U' : Set (unramifiedCharacters ν)}
    (hD : Dense D) (hU : IsOpen U) (hU' : IsOpen U')
    (J : D → V →ₗ[ℂ] W) (N N' : unramifiedCharacters ν → V →ₗ[ℂ] W)
    (b b' : unramifiedRegularFunctions ν)
    (hN : IsPolynomialOperatorOn Set.univ (fun z => N z.val))
    (hN' : IsPolynomialOperatorOn Set.univ (fun z => N' z.val))
    (he : ∀ z : D, z.val ∈ U → N z.val = b.val z.val • J z)
    (he' : ∀ z : D, z.val ∈ U' → N' z.val = b'.val z.val • J z) :
    ∀ z ∈ U ∩ U', b'.val z • N z = b.val z • N' z := by
  intro z hz
  apply LinearMap.ext
  intro v
  have hpoly := ((hN v).regular_smul b').sub ((hN' v).regular_smul b)
  have hz0 := polynomial_eq_zero_on_open_of_dense hD (hU.inter hU')
    (fun x => b'.val x • N x v - b.val x • N' x v) hpoly (by
      intro x hx hxU
      rw [he ⟨x, hx⟩ hxU.1, he' ⟨x, hx⟩ hxU.2]
      simp only [LinearMap.smul_apply, smul_smul]
      rw [mul_comm]
      exact sub_self _) z hz
  exact sub_eq_zero.mp hz0

private theorem inverse_smul_eq_of_cross {c d : ℂ} (hc : c ≠ 0) (hd : d ≠ 0)
    {v w : W} (he : d • v = c • w) :
    c⁻¹ • v = d⁻¹ • w := by
  have hcd : c⁻¹ * (d⁻¹ * c) = d⁻¹ := by
    field_simp
  calc
    c⁻¹ • v = c⁻¹ • (d⁻¹ • (d • v)) := by rw [inv_smul_smul₀ hd]
    _ = c⁻¹ • (d⁻¹ • (c • w)) := congrArg (fun x => c⁻¹ • (d⁻¹ • x)) he
    _ = d⁻¹ • w := by simp only [smul_smul, hcd]

end UnramifiedOperatorFamily

namespace ActualCommonLeviV3

open Aubert.General Induction StandardIntertwining DynamicOppositeStandardIntertwining
open DynamicCommonLeviComposition DynamicCommonLeviCompact DynamicCommonLeviContinuation
open ActualCommonLeviTensor ActualCommonLeviCompactTensor ActualCommonLeviRationalTensor
open UnramifiedOperatorFamily

attribute [local instance]
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsTopologicalGroup
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space2
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningLocallyCompactSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningNonarchimedeanGroup
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicCommonLeviContinuation.radicalMeasurable
  DynamicCommonLeviContinuation.radicalBorel
  DynamicCommonLeviContinuation.intersectionMeasurable
  DynamicCommonLeviContinuation.intersectionBorel
  DynamicCommonLeviContinuation.quotientMeasurable
  DynamicCommonLeviContinuation.quotientBorel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hG : IsConnectedReductive G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ : Dynamic.centralizer ψ = Dynamic.centralizer χ)
  (hψK : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ, ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hψ' : Dynamic.centralizer ψ' = Dynamic.centralizer χ)
  (hψ'K : ∀ g : RationalPoint F G.X, ∃ p : parabolic ψ', ∃ k : K,
    g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (p : ContinuedPair χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A)
  (q : ContinuedPair χ hG K hK ψ' hψ' hψ'K ψ hψ hψK A.contragredient)

local notation "X" => unramifiedCharacters (normCharacters χ)
local notation "Xu" => unitaryUnramifiedCharacters (normCharacters χ)
local notation "V₀" => compactFiber χ K ψ hψ A
local notation "V₁" => compactFiber χ K ψ' hψ' A
local notation "D" => genericLocus χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q
local notation "J" => compactComparison χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q

/-- Two whole-operator local representatives agree after cross-multiplication
on their overlap, even if their denominators differ. -/
theorem IsLocalRepresentative.cross_eq
    (hD : Dense D)
    {U U' : Set X} {N N' : X → V₀ →ₗ[ℂ] V₁}
    {b b' : unramifiedRegularFunctions (normCharacters χ)}
    (h : IsLocalRepresentative χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q U N b)
    (h' : IsLocalRepresentative χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q U' N' b') :
    ∀ z ∈ U ∩ U', b'.val z • N z = b.val z • N' z :=
  polynomial_operator_cross_eq_of_dense hD h.1 h'.1 J N N' b b'
    h.2.1 h'.2.1 h.2.2.2 h'.2.2.2

/-- Every local representative evaluates to the actual compact tensor at a
generic point in its open domain. -/
theorem IsLocalRepresentative.generic_value
    {U : Set X} {N : X → V₀ →ₗ[ℂ] V₁}
    {b : unramifiedRegularFunctions (normCharacters χ)}
    (h : IsLocalRepresentative χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q U N b)
    (z : D) (hz : z.val ∈ U) :
    (b.val z.val)⁻¹ • N z.val = J z := by
  exact (congrArg (fun M : V₀ →ₗ[ℂ] V₁ => (b.val z.val)⁻¹ • M)
    (h.2.2.2 z hz)).trans (inv_smul_smul₀ (h.2.2.1 z.val hz) (J z))

/-- Density of the genuine generic locus makes the actual rational germ
single-valued at every ambient point where a regular value exists. -/
theorem RegularGermAt.unique
    (hD : Dense D) {z : X} {L L' : V₀ →ₗ[ℂ] V₁}
    (h : RegularGermAt χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q z L)
    (h' : RegularGermAt χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q z L') :
    L = L' := by
  obtain ⟨U, N, b, hz, h, hL⟩ := h
  obtain ⟨U', N', b', hz', h', hL'⟩ := h'
  have he := h.cross_eq χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q hD h' z ⟨hz, hz'⟩
  exact hL.trans ((inverse_smul_eq_of_cross (W := V₀ →ₗ[ℂ] V₁)
    (v := N z) (w := N' z) (h.2.2.1 z hz) (h'.2.2.1 z hz') he).trans hL'.symm)

/-- Extract a compact operator from the existence of a regular representative.
Generic density makes this choice independent of the representative. -/
def regularGermValue (z : X)
    (h : ∃ L : V₀ →ₗ[ℂ] V₁,
      RegularGermAt χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q z L) :
    V₀ →ₗ[ℂ] V₁ :=
  Classical.choose h

theorem regularGermValue_spec (z : X)
    (h : ∃ L : V₀ →ₗ[ℂ] V₁,
      RegularGermAt χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q z L) :
    RegularGermAt χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q z
      (regularGermValue χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q z h) :=
  Classical.choose_spec h

theorem regularGermValue_eq
    (hD : Dense D) (z : X)
    (h : ∃ L : V₀ →ₗ[ℂ] V₁,
      RegularGermAt χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q z L)
    {L : V₀ →ₗ[ℂ] V₁}
    (hL : RegularGermAt χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q z L) :
    regularGermValue χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q z h = L :=
  (regularGermValue_spec χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q z h).unique
    χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q hD hL

/-- A regular extension supplies the actual rational germ at each unitary
point by specializing that point's local representative. -/
theorem IsRegularUnitaryExtension.regularGermAt
    {T : UnitaryComparisonFamily χ A ψ hψ ψ' hψ'}
    (hT : IsRegularUnitaryExtension χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q T)
    (z : Xu) :
    RegularGermAt χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q (unitaryParameter χ z)
      (compactValue χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K T z) := by
  obtain ⟨U, N, b, hz, hrep, he⟩ := hT z
  exact ⟨U, N, b, hz, hrep, he z hz⟩

/-- The rational-germ uniqueness clause of V.3.1 follows from ambient generic
density and regularity of the specified extension. -/
theorem IsRegularUnitaryExtension.isUniqueByRationalGerm
    (hD : Dense D) {T : UnitaryComparisonFamily χ A ψ hψ ψ' hψ'}
    (hT : IsRegularUnitaryExtension χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q T) :
    IsUniqueByRationalGerm χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q T := by
  intro z L hL
  exact hL.unique χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q hD
    (hT.regularGermAt χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q z)

private theorem conjugate_apply
    {V W Vc Wc : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup Vc] [Module ℂ Vc]
    [AddCommGroup Wc] [Module ℂ Wc]
    (E₀ : V ≃ₗ[ℂ] Vc) (E₁ : W ≃ₗ[ℂ] Wc) (T : V →ₗ[ℂ] W) (v : V) :
    (E₁.toLinearMap.comp (T.comp E₀.symm.toLinearMap)) (E₀ v) = E₁ (T v) := by
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply]

/-- Regularity of the specified unitary extension already forces agreement
with the actual generic coefficient-fiber comparison. -/
theorem IsRegularUnitaryExtension.agreesOnUnitaryGeneric
    {T : UnitaryComparisonFamily χ A ψ hψ ψ' hψ'}
    (hT : IsRegularUnitaryExtension χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q T) :
    AgreesOnUnitaryGeneric χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q T := by
  intro z hzD
  obtain ⟨U, N, b, hz, hrep, he⟩ := hT z
  have hval := (he z hz).trans
    (hrep.generic_value χ hG A K hK ψ hψ hψK ψ' hψ' hψ'K p q
      ⟨unitaryParameter χ z, hzD⟩ hz)
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  apply (compactTensorEquiv χ hG K hK ψ' hψ' hψ'K A (unitaryParameter χ z)).injective
  have hpoint := congrArg
    (fun M : V₀ →ₗ[ℂ] V₁ =>
      M (compactTensorEquiv χ hG K hK ψ hψ hψK A (unitaryParameter χ z) v)) hval
  have hc := conjugate_apply
    (compactTensorEquiv χ hG K hK ψ hψ hψK A (unitaryParameter χ z))
    (compactTensorEquiv χ hG K hK ψ' hψ' hψ'K A (unitaryParameter χ z))
    (T z).toLinearMap v
  exact (hc.symm.trans hpoint).trans
    (compactComparison_square χ hG K hK ψ hψ hψK ψ' hψ' hψ'K A p q
      ⟨unitaryParameter χ z, hzD⟩ v).symm

end ActualCommonLeviV3
end Langlands.Plancherel
