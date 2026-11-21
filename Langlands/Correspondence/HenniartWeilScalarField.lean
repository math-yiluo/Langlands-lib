import Langlands.Correspondence.HenniartWeilUpperScalar
import Langlands.Weil.Local.IrreducibleReductionProof
import Langlands.LocalFactor.CommonClosure

/-! # A finite Galois scalar field for an irreducible Weil representation -/

noncomputable section

namespace Langlands.Henniart.Numerical

open FiniteRepresentation LocalClassField LocalFactor.CommonClosure Weil.Local
open VirtualRepresentation.LocalWeil.Ramification Ramification.Padic Ramification.HerbrandBridge

universe uK uW
variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)
variable (A : FiniteRepresentation.{0, uK, uW} ℂ (localWeilGroup K))

/-- An actual finite Galois field in the common closure with a scalar character
on its fixing Weil subgroup. Every nonnegative upper group acting by scalars
on `A` is contained in that fixing subgroup. -/
structure WeilScalarField where
  extension : Extension K
  galois : IsGalois K.Carrier extension.field
  character : weilSubgroup K extension →ₜ* ℂˣ
  scalar_act : ∀ w : weilSubgroup K extension,
    A.representation w = (character w : ℂ) • (1 : Module.End ℂ A)
  upper_le : ∀ {a : ℝ}, 0 ≤ a → HasUpperScalarAction K A a →
    upperGroup K a ≤ weilSubgroup K extension

private theorem scalar_eq_of_rep_equiv
    {B C : FiniteRepresentation.{0, uK, uW} ℂ (localWeilGroup K)}
    (e : FiniteRepresentation.Equiv B C) (w : localWeilGroup K) (z : ℂˣ)
    (h : B.representation w = (z : ℂ) • (1 : Module.End ℂ B)) :
    C.representation w = (z : ℂ) • (1 : Module.End ℂ C) := by
  ext v
  obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective v
  have he := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap w x
  change e.toLinearEquiv (B.representation w x) = C.representation w (e.toLinearEquiv x) at he
  rw [h, LinearMap.smul_apply, Module.End.one_apply, map_smul] at he
  simpa only [LinearMap.smul_apply, Module.End.one_apply] using he.symm

/-- Use the projective kernel of a finite-image unramified normalization to
obtain the field, and restore the unramified character on its Weil subgroup. -/
theorem exists_weilScalarField (hc : A.IsContinuous) (hi : A.IsIrreducible) :
    Nonempty (WeilScalarField K A) := by
  let : CharZero K.Carrier := Algebra.charZero_of_charZero (Padic p) K.Carrier
  let : IsGalois K.Carrier (AlgebraicClosure K.Carrier) := ⟨⟩
  let G := Field.absoluteGaloisGroup K.Carrier
  let := absoluteGaloisNonarchimedean K.Carrier
  obtain ⟨z, B, hcB, hiB, hfB, -, ⟨e⟩⟩ := (localWeilIrreducibleReductionFor K A hc hi).1
  obtain ⟨τ, ⟨hcτ, hτ⟩, -⟩ := (localWeilGaloisTypeFor K B).2 hcB hfB
  let χ := localUnramifiedCharacter K z
  have hτw (w : localWeilGroup K) : τ (localProjection K w) = B.representation w :=
    DFunLike.congr_fun hτ w
  let := B.carrierNormedAddCommGroup
  let := B.carrierNormedSpace
  have hker : IsOpen (τ.ker : Set G) :=
    Weil.open_kernel_of_continuous_nonarchimedean_representation τ
      ((FiniteRepresentation.isContinuous_of_iff τ).mp hcτ)
  let Z := Subgroup.center (Module.End ℂ B)ˣ
  let H := Z.comap τ.asGroupHom
  let hnormal : H.Normal := (inferInstance : Z.Normal).comap _
  have hle : τ.ker ≤ H := by
    intro g hg
    change τ.asGroupHom g ∈ Z
    have hg' : τ.asGroupHom g = 1 := Units.ext hg
    rw [hg']
    exact Z.one_mem
  have hH : IsOpen (H : Set G) := H.isOpen_of_openSubgroup (U := ⟨τ.ker, hker⟩) hle
  let M := IntermediateField.fixedField H
  have hfix : M.fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨H, Subgroup.isClosed_of_isOpen H hH⟩
  let : FiniteDimensional K.Carrier M :=
    (InfiniteGalois.isOpen_iff_finite M).mp (by rw [hfix]; exact hH)
  let L : Extension K := ⟨M, inferInstance⟩
  let W := weilSubgroup K L
  have hmem (w : localWeilGroup K) : w ∈ W ↔ localProjection K w ∈ H := by
    change localProjection K w ∈ M.fixingSubgroup ↔ _
    exact Iff.of_eq (congrArg (fun S : Subgroup G => localProjection K w ∈ S) hfix)
  have hscalar (w : W) : ∃ a : ℂˣ, B.representation w = (a : ℂ) • (1 : Module.End ℂ B) := by
    have hz : τ.asGroupHom (localProjection K w) ∈ Z := (hmem w).mp w.property
    obtain ⟨a, ha⟩ := Weil.UnramifiedReductionAux.scalar_of_commuting_unit B.representation hiB
      (τ.asGroupHom (localProjection K w)) (by
        intro u
        have h := congrArg Units.val ((Subgroup.mem_center_iff.mp hz) (τ.asGroupHom (localProjection K u)))
        change τ (localProjection K u) * τ (localProjection K w) =
          τ (localProjection K w) * τ (localProjection K u) at h
        rw [hτw u] at h
        exact h)
    exact ⟨a, (hτw w).symm.trans ha⟩
  have : Nontrivial B := Module.finrank_pos_iff.mp
    (Weil.UnramifiedReductionAux.finrank_pos_of_irreducible B.representation hiB)
  obtain ⟨v, hv⟩ := exists_ne (0 : B)
  let R := B.representation.comp W.subtype
  have hline (w : W) : w ∈ CyclicRestriction.eigenlineStabilizer R v := by
    obtain ⟨a, ha⟩ := hscalar w
    refine ⟨a, ?_⟩
    change B.representation w v = _
    rw [ha, LinearMap.smul_apply, Module.End.one_apply]
  let γ := CyclicRestriction.eigenlineCharacter hv hline
  have hγvec (w : W) : B.representation w v = (γ w : ℂ) • v :=
    CyclicRestriction.eigenlineCharacter_apply_smul hv hline w
  have hγ (w : W) : B.representation w = (γ w : ℂ) • (1 : Module.End ℂ B) := by
    obtain ⟨a, ha⟩ := hscalar w
    have h := hγvec w
    rw [ha, LinearMap.smul_apply, Module.End.one_apply] at h
    rw [← CyclicRestriction.eigenline_scalar_unique v hv h]
    exact ha
  let π : W →ₜ* G := (localProjection K).comp ⟨W.subtype, continuous_subtype_val⟩
  let N := τ.ker.comap π.toMonoidHom
  have hN : IsOpen (N : Set W) := hker.preimage π.continuous
  have hNγ : N ≤ γ.ker := by
    intro w hw
    have hw' : τ (localProjection K w) = 1 := hw
    rw [hτw] at hw'
    have h := hγvec w
    rw [hw', Module.End.one_apply] at h
    apply CyclicRestriction.eigenline_scalar_unique v hv
    simpa only [Units.val_one, one_smul] using h.symm
  have hcγ : Continuous γ := Weil.continuous_of_open_kernel γ
    (γ.ker.isOpen_of_openSubgroup (U := ⟨N, hN⟩) hNγ)
  let θ : W →ₜ* ℂˣ := χ.comp ⟨W.subtype, continuous_subtype_val⟩ * ⟨γ, hcγ⟩
  refine ⟨⟨L, IsGalois.of_fixedField_normal_subgroup H (hn := hnormal), θ, ?_, ?_⟩⟩
  · intro w
    apply scalar_eq_of_rep_equiv K e.symm
    change (χ (w : localWeilGroup K) : ℂ) • B.representation w =
      (↑(χ (w : localWeilGroup K) * γ w) : ℂ) • (1 : Module.End ℂ B)
    rw [hγ w, smul_smul, Units.val_mul]
  · intro a ha hS w hw
    obtain ⟨ξ, hξ⟩ := hS
    apply (hmem w).mpr
    have hiw : w ∈ localInertia K := by
      rw [localInertia_eq_comap K, ← absoluteUpperCanonicalInertia K]
      exact absoluteUpperRamificationGroup_antitone K ha hw
    have hact := scalar_eq_of_rep_equiv K e w (ξ ⟨w, hw⟩) (hξ ⟨w, hw⟩)
    change (χ w : ℂ) • B.representation w = _ at hact
    have hχw : χ w = 1 := unramifiedCharacter_on_kernel (localDegree K) z hiw
    rw [hχw, Units.val_one, one_smul] at hact
    change B.representation w = (ξ ⟨w, hw⟩ : ℂ) • (1 : Module.End ℂ B) at hact
    change τ.asGroupHom (localProjection K w) ∈ Z
    apply Subgroup.mem_center_iff.mpr
    intro U
    apply Units.ext
    change (U : Module.End ℂ B) * τ (localProjection K w) =
      τ (localProjection K w) * (U : Module.End ℂ B)
    rw [hτw, hact, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]

end Langlands.Henniart.Numerical
