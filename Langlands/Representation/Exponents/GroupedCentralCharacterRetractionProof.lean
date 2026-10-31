import Langlands.Representation.Exponents.GroupedCentralCharacterRetractionStatement
import Langlands.Representation.Exponents.FiniteActionSpectrumProof

/-! Equivariant primary projectors for finite full-central operator span. -/

noncomputable section

namespace Langlands

open FiniteActionSpectrum
open scoped IsMulCommutative

universe uG uV

/-- Finite full-central operator span splits every selected group of uniform
central-character spaces, preserving all generalized nilpotent directions. -/
theorem groupedCentralCharacterRetraction :
    GroupedCentralCharacterRetractionStatement.{uG,uV} := by
  intro G _ V _ _ ρ hfin P
  classical
  let ρc : Representation ℂ (Subgroup.center G) V :=
    ρ.comp (Subgroup.center G).subtype
  let S : Submodule ℂ (Module.End ℂ V) :=
    Submodule.span ℂ (Set.range ρc)
  have hcomm : ∀ (b : Module.End ℂ V), b ∈ S →
      ∀ g : G, b * ρ g = ρ g * b := by
    intro b hb g
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨z, rfl⟩ := hb
      change ρ (z : G) * ρ g = ρ g * ρ (z : G)
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp z.property g)]
    | zero => simp
    | add a b _ _ ha hb =>
      simp only [add_mul, mul_add, ha, hb]
    | smul c b _ hb =>
      rw [smul_mul_assoc, mul_smul_comm, hb]
  let B : Subalgebra ℂ (Module.End ℂ V) :=
    Algebra.adjoin ℂ (Set.range ρc)
  have hpair : (Set.range ρc).Pairwise Commute := by
    rintro _ ⟨z, rfl⟩ _ ⟨w, rfl⟩ _
    exact (Commute.all z w).map ρc
  let : IsMulCommutative B := Algebra.isMulCommutative_adjoin ℂ hpair
  let : CommRing B := inferInstance
  have hclosure : Submonoid.closure (Set.range ρc) ≤ MonoidHom.mrange ρc :=
    Submonoid.closure_le.mpr (fun _ hz => hz)
  have hBspan : B.toSubmodule = S :=
    Algebra.adjoin_eq_span_of_subset ℂ
      (fun _ hx => Submodule.subset_span (hclosure hx))
  let : Module.Finite ℂ B := by
    apply Subalgebra.finiteDimensional_toSubmodule.mp
    rw [hBspan]
    exact hfin
  let ι : B →ₐ[ℂ] Module.End ℂ V := B.val
  let ρ' : Subgroup.center G →* B :=
    ρc.codRestrict B (fun z => Algebra.subset_adjoin ⟨z, rfl⟩)
  have hι : ∀ z : Subgroup.center G, ι (ρ' z) = ρ (z : G) :=
    fun _ => rfl
  have hmem : ∀ b : B, ι b ∈ S := by
    intro b
    rw [← hBspan]
    exact b.property
  let op : B → ρ.IntertwiningMap ρ := fun b =>
    { toLinearMap := ι b
      isIntertwining' := fun g => hcomm (ι b) (hmem b) g }
  let : Finite (B →ₐ[ℂ] ℂ) := finite_algHom
  let : Fintype (B →ₐ[ℂ] ℂ) := Fintype.ofFinite _
  obtain ⟨N, h, hu, hann⟩ := exists_decomposition (R := B)
  let w : B := ((hu.unit⁻¹ : Bˣ) : B)
  have hdef : ∀ (φ : B →ₐ[ℂ] ℂ) (z : Subgroup.center G),
      ρ (z : G) - (algebraCharacter ρ' φ z : ℂ) • 1 =
        ι (ρ' z - algebraMap ℂ B (φ (ρ' z))) := by
    intro φ z
    rw [map_sub, AlgHom.commutes, hι, Algebra.algebraMap_eq_smul_one,
      algebraCharacter_apply]
  have hbound : ∀ (φ : B →ₐ[ℂ] ℂ) (z : Subgroup.center G) (v : V),
      ((ρ (z : G) - (algebraCharacter ρ' φ z : ℂ) • 1) ^ N)
        (ι (h φ) v) = 0 := by
    intro φ z v
    have hk : ρ' z - algebraMap ℂ B (φ (ρ' z)) ∈ RingHom.ker φ := by
      simp [RingHom.mem_ker]
    rw [hdef φ z, ← map_pow, ← Module.End.mul_apply, ← map_mul,
      hann φ _ (Ideal.pow_mem_pow hk N), map_zero, LinearMap.zero_apply]
  have hdecomp : ∀ v : V, v = ∑ φ, ι (h φ) (ι w v) := by
    intro v
    have h1 : (∑ φ, h φ) * w = 1 := hu.mul_val_inv
    calc v = ι ((∑ φ, h φ) * w) v := by
          rw [h1, map_one, Module.End.one_apply]
      _ = ∑ φ, ι (h φ) (ι w v) := by
          rw [map_mul, Module.End.mul_apply, map_sum, LinearMap.sum_apply]
  let piece : (B →ₐ[ℂ] ℂ) → ρ.IntertwiningMap ρ :=
    fun φ => (op (h φ)).comp (op w)
  have hpiece : ∀ (φ : B →ₐ[ℂ] ℂ) (v : V),
      piece φ v ∈ generalizedCentralCharacterSpace ρ (algebraCharacter ρ' φ) := by
    intro φ v
    exact (mem_generalizedCentralCharacterSpace ρ _ _).mpr
      ⟨N, fun z => hbound φ z (ι w v)⟩
  have hkill : ∀ (χ : Subgroup.center G →* ℂˣ) (φ : B →ₐ[ℂ] ℂ) (v : V),
      v ∈ generalizedCentralCharacterSpace ρ χ →
        algebraCharacter ρ' φ ≠ χ → piece φ v = 0 := by
    intro χ φ v hv hne
    obtain ⟨z, hz⟩ := DFunLike.ne_iff.mp hne
    obtain ⟨k, hk⟩ := (mem_generalizedCentralCharacterSpace ρ _ _).mp
      (map_mem_generalizedCentralCharacterSpace (piece φ) χ hv)
    exact eq_zero_of_pow_sub_smul (T := ρ (z : G))
      (fun heq => hz (Units.ext heq)) (hbound φ z (ι w v)) (hk z)
  let e : ρ.IntertwiningMap ρ :=
    ∑ φ : B →ₐ[ℂ] ℂ, if P (algebraCharacter ρ' φ) then piece φ else 0
  have heval : ∀ v : V, e v =
      ∑ φ : B →ₐ[ℂ] ℂ, if P (algebraCharacter ρ' φ) then piece φ v else 0 := by
    intro v
    dsimp only [e]
    rw [Representation.IntertwiningMap.sum_apply]
    apply Finset.sum_congr rfl
    intro φ _
    split_ifs <;> rfl
  have hemem : ∀ v : V, e v ∈ groupedCentralCharacterSpace ρ P := by
    intro v
    rw [heval]
    apply Submodule.sum_mem
    intro φ _
    by_cases hp : P (algebraCharacter ρ' φ)
    · simp only [hp, ↓reduceIte]
      exact generalizedCentralCharacterSpace_le_grouped ρ P _ hp (hpiece φ v)
    · simp only [hp, ↓reduceIte]
      exact Submodule.zero_mem _
  have hselected : ∀ (χ : Subgroup.center G →* ℂˣ), P χ →
      ∀ v : V, v ∈ generalizedCentralCharacterSpace ρ χ → e v = v := by
    intro χ hχ v hv
    calc
      e v = ∑ φ : B →ₐ[ℂ] ℂ, piece φ v := by
        rw [heval]
        apply Finset.sum_congr rfl
        intro φ _
        by_cases hp : P (algebraCharacter ρ' φ)
        · simp only [hp, ↓reduceIte]
        · simp only [hp, ↓reduceIte]
          exact (hkill χ φ v hv (fun heq => hp (heq.symm ▸ hχ))).symm
      _ = v := (hdecomp v).symm
  have hidentity : ∀ v : V, v ∈ groupedCentralCharacterSpace ρ P → e v = v := by
    intro v hv
    change v ∈ ⨆ χ : {χ : Subgroup.center G →* ℂˣ // P χ},
      (generalizedCentralCharacterSpace ρ χ.val).toSubmodule at hv
    refine Submodule.iSup_induction _ (motive := fun v => e v = v) hv ?_ ?_ ?_
    · intro χ v hv
      exact hselected χ.val χ.property v hv
    · exact map_zero e
    · intro v v' hv hv'
      rw [map_add, hv, hv']
  let r : ρ.IntertwiningMap (groupedCentralCharacterSpace ρ P).toRepresentation :=
    { toFun := fun v => ⟨e v, hemem v⟩
      map_add' := fun v v' => Subtype.ext (map_add e v v')
      map_smul' := fun c v => Subtype.ext (map_smul e c v)
      isIntertwining' := fun g => by
        apply LinearMap.ext
        intro v
        apply Subtype.ext
        exact Representation.IntertwiningMap.isIntertwining ρ ρ e g v }
  refine ⟨r, ?_, ?_⟩
  · intro v
    exact Subtype.ext (hidentity v v.property)
  · intro χ hnχ v hv
    apply Subtype.ext
    change e v = 0
    rw [heval]
    apply Finset.sum_eq_zero
    intro φ _
    by_cases hp : P (algebraCharacter ρ' φ)
    · simp only [hp, ↓reduceIte]
      exact hkill χ φ v hv (fun heq => hnχ (heq ▸ hp))
    · simp only [hp, ↓reduceIte]

end Langlands
