import Langlands.Representation.Character.CompactTypeAdmissibility
import Langlands.Representation.Compact.CompactGroupSmoothRepresentationProof
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Trace

/-! # Self-intertwining detected by a translated compact trace test -/

noncomputable section

namespace Langlands.Character

open Function HarmonicAnalysis
open Hecke.TestFunction (leftTranslate leftTranslate_apply pullback pullback_apply)

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]

/-- The conjugation map on the intersection `K ∩ y K₀ y⁻¹`, with values in `K₀`. -/
def conjugateIntersectionTransport (K₀ K : OpenSubgroup G) (y : G) :
    conjugateIntersection K₀ K y →* K₀ :=
  ((MulAut.conj y⁻¹).toMonoidHom.comp
    (K.toSubgroup.subtype.comp (conjugateIntersection K₀ K y).toSubgroup.subtype)).codRestrict
      K₀.toSubgroup (fun z => z.property)

private def weightedTraceTest {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] (τ : Representation ℂ K X) (hτ : IsSmooth τ) :
    Module.End ℂ X →ₗ[ℂ] SchwartzBruhat K where
  toFun B := ⟨fun k => LinearMap.trace ℂ X (B * τ k), by
    obtain ⟨N, _, hN⟩ := Renard.CompactRepresentation.exists_openNormal_trivial_of_finiteDimensional τ hτ
    apply (IsLocallyConstant.iff_exists_open _).mpr
    intro k
    refine ⟨(fun z => k⁻¹ * z) ⁻¹' (N : Set K), N.isOpen.preimage (continuous_const.mul continuous_id),
      by simp, ?_⟩
    intro z hz
    have hfix : τ (k⁻¹ * z) = 1 := LinearMap.ext (hN _ hz)
    have heq : τ z = τ k := calc
      _ = τ (k * (k⁻¹ * z)) := by rw [mul_inv_cancel_left]
      _ = _ := by rw [map_mul, hfix, mul_one]
    rw [heq], HasCompactSupport.of_compactSpace _⟩
  map_add' B C := Hecke.TestFunction.ext fun k => by
    change LinearMap.trace ℂ X ((B + C) * τ k) =
      LinearMap.trace ℂ X (B * τ k) + LinearMap.trace ℂ X (C * τ k)
    rw [add_mul, map_add]
  map_smul' d B := Hecke.TestFunction.ext fun k => by
    change LinearMap.trace ℂ X ((d • B) * τ k) = d • LinearMap.trace ℂ X (B * τ k)
    rw [smul_mul_assoc, map_smul]

private theorem weightedTraceTest_apply {K : Type*} [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] (τ : Representation ℂ K X) (hτ : IsSmooth τ)
    (B : Module.End ℂ X) (k : K) :
    weightedTraceTest τ hτ B k = LinearMap.trace ℂ X (B * τ k) := rfl

private def endTracePairing : LinearMap.BilinForm ℂ (Module.End ℂ X) :=
  LinearMap.mk₂ ℂ (fun A B : Module.End ℂ X => LinearMap.trace ℂ X (A * B))
    (fun A B C => by rw [add_mul, map_add]) (fun c A B => by rw [smul_mul_assoc, map_smul])
    (fun A B C => by rw [mul_add, map_add]) (fun c A B => by rw [mul_smul_comm, map_smul])

private theorem endTracePairing_injective :
    Injective (endTracePairing (X := X)) := by
  intro A B h
  let b := Module.finBasis ℂ X
  let M := LinearMap.toMatrix b b
  apply M.injective
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro C
  obtain ⟨D, rfl⟩ := M.surjective C
  have hD := congrArg (fun ℓ : Module.Dual ℂ (Module.End ℂ X) => ℓ D) h
  change LinearMap.trace ℂ X (A * D) = LinearMap.trace ℂ X (B * D) at hD
  simpa only [M, ← LinearMap.toMatrix_mul, ← LinearMap.trace_eq_matrix_trace ℂ b] using hD

variable [T2Space G]

/-- An invariant distribution that is nonzero on a translated compact trace test
detects a nonzero intertwiner of the compact type with its conjugate. -/
def CompactTraceSelfIntertwiningStatement
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (τ : Representation ℂ K X) (hτ : IsSmooth τ) (D : Distribution G) (y : G) : Prop :=
  Distribution.IsConjugationInvariant D →
  D (compactTraceCosetTest K hK τ hτ y) ≠ 0 →
  let J := conjugateIntersection K K y
  ∃ T : Representation.IntertwiningMap (τ.comp J.toSubgroup.subtype)
    (τ.comp (conjugateIntersectionTransport K K y)), T ≠ 0

theorem compactTraceSelfIntertwining (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (τ : Representation ℂ K X) (hτ : IsSmooth τ) (D : Distribution G) (y : G) :
    CompactTraceSelfIntertwiningStatement K hK τ hτ D y := by
  classical
  intro hD h
  let : IsTopologicalGroup K := inferInstanceAs (IsTopologicalGroup K.toSubgroup)
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let J := conjugateIntersection K K y
  let c := conjugateIntersectionTransport K K y
  let f := (leftTranslate y).toLinearMap.comp
    ((SchwartzBruhat.extendZero K.isOpen).comp (weightedTraceTest τ hτ))
  let Λ := D.comp f
  have hΛ : Λ 1 ≠ 0 := by
    have hOne : weightedTraceTest τ hτ 1 = compactTraceTest τ hτ :=
      Hecke.TestFunction.ext fun k => by rw [weightedTraceTest_apply, one_mul, compactTraceTest_apply]
    change D (leftTranslate y (SchwartzBruhat.extendZero K.isOpen (weightedTraceTest τ hτ 1))) ≠ 0
    rw [hOne]
    exact h
  have hAction (z : J) (B : Module.End ℂ X) :
      pullback (Distribution.conjugationHomeomorph (z.val : G)) (f B) =
        f (τ z.val⁻¹ * B * τ (c z)) := by
    let a := z.val
    let b := c z
    have hb : (b : G) = y⁻¹ * (a : G) * y := by
      change y⁻¹ * (a : G) * y⁻¹⁻¹ = _
      rw [inv_inv]
    apply Hecke.TestFunction.ext
    intro g
    have hg : y⁻¹ * ((a : G) * g * (a : G)⁻¹) =
        (b : G) * (y⁻¹ * g) * (a : G)⁻¹ := by rw [hb]; group
    change leftTranslate y (SchwartzBruhat.extendZero K.isOpen (weightedTraceTest τ hτ B))
        (Distribution.conjugationHomeomorph (a : G) g) =
      leftTranslate y (SchwartzBruhat.extendZero K.isOpen
        (weightedTraceTest τ hτ (τ a⁻¹ * B * τ b))) g
    simp only [leftTranslate_apply, Distribution.conjugationHomeomorph_apply, hg]
    by_cases hk : y⁻¹ * g ∈ K
    · let k : K := ⟨y⁻¹ * g, hk⟩
      change SchwartzBruhat.extendZero K.isOpen (weightedTraceTest τ hτ B)
          ((b * k * a⁻¹ : K) : G) =
        SchwartzBruhat.extendZero K.isOpen (weightedTraceTest τ hτ (τ a⁻¹ * B * τ b)) (k : G)
      simp only [SchwartzBruhat.extendZero_apply_subtype, weightedTraceTest_apply, map_mul]
      rw [← mul_assoc B (τ b * τ k) (τ a⁻¹), LinearMap.trace_mul_comm ℂ (B * (τ b * τ k))]
      simp only [mul_assoc]
    · have hn : (b : G) * (y⁻¹ * g) * (a : G)⁻¹ ∉ K := by
        change (b : G) * (y⁻¹ * g) * (a : G)⁻¹ ∉ K.toSubgroup
        rwa [K.toSubgroup.mul_mem_cancel_right (K.inv_mem a.property),
          K.toSubgroup.mul_mem_cancel_left b.property]
      rw [SchwartzBruhat.extendZero_apply_of_not_mem K.isOpen _ hn,
        SchwartzBruhat.extendZero_apply_of_not_mem K.isOpen _ hk]
  have hInv (z : J) (B : Module.End ℂ X) : Λ (τ z.val⁻¹ * B * τ (c z)) = Λ B := by
    change D (f (τ z.val⁻¹ * B * τ (c z))) = D (f B)
    rw [← hAction z B]
    exact (Distribution.isConjugationInvariant_iff D).mp hD (z.val : G) (f B)
  let P := endTracePairing (X := X)
  have hP : Injective P := endTracePairing_injective
  have hPs : Surjective P :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).mp hP
  obtain ⟨T, hT⟩ := hPs Λ
  have hEval (B : Module.End ℂ X) : LinearMap.trace ℂ X (T * B) = Λ B :=
    congrArg (fun ℓ : Module.Dual ℂ (Module.End ℂ X) => ℓ B) hT
  have hI (z : J) : T * τ z.val = τ (c z) * T := by
    have heq : τ (c z) * T * τ z.val⁻¹ = T := by
      apply hP
      apply LinearMap.ext
      intro B
      change LinearMap.trace ℂ X (τ (c z) * T * τ z.val⁻¹ * B) = LinearMap.trace ℂ X (T * B)
      calc
        _ = LinearMap.trace ℂ X (T * (τ z.val⁻¹ * B * τ (c z))) := by
          simp only [mul_assoc]
          rw [LinearMap.trace_mul_comm ℂ (τ (c z))]
          simp only [mul_assoc]
        _ = _ := by rw [hEval, hEval, hInv]
    calc
      _ = (τ (c z) * T * τ z.val⁻¹) * τ z.val := by rw [heq]
      _ = _ := by rw [mul_assoc (τ (c z) * T), ← map_mul, inv_mul_cancel, map_one, mul_one]
  let A : Representation.IntertwiningMap (τ.comp J.toSubgroup.subtype) (τ.comp c) :=
    { toLinearMap := T
      isIntertwining' := hI }
  refine ⟨A, fun hZero => hΛ ?_⟩
  have hT₀ : T = 0 := congrArg Representation.IntertwiningMap.toLinearMap hZero
  rw [← hEval, hT₀, zero_mul, map_zero]

end Langlands.Character
