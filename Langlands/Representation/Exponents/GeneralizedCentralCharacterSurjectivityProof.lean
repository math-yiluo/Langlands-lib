import Langlands.Representation.Exponents.GeneralizedCentralCharacterSurjectivityStatement
import Langlands.Representation.Exponents.FiniteActionSpectrumProof

/-! # Surjectivity on uniform generalized central-character spaces -/

noncomputable section

namespace Langlands

namespace GeneralizedCentralSurjectivity

universe uG uV uW

variable {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

/-- The inverse image of every target subrepresentation is stable under the
source central operator span. In particular, the actual kernel is stable. -/
theorem preimage_stable (f : ρ.IntertwiningMap σ) (P : Subrepresentation σ)
    {T : Module.End ℂ V}
    (hT : T ∈ Submodule.span ℂ
      (Set.range (fun z : Subgroup.center G => ρ (z : G))))
    {v : V} (hv : f v ∈ P) : f (T v) ∈ P := by
  change f (T v) ∈ P.toSubmodule
  induction hT using Submodule.span_induction with
  | mem T hT =>
    obtain ⟨z, rfl⟩ := hT
    rw [Representation.IntertwiningMap.isIntertwining ρ σ f (z : G) v]
    exact P.apply_mem_toSubmodule (z : G) hv
  | zero => simp
  | add T U _ _ hT hU =>
    simpa only [LinearMap.add_apply, map_add] using P.toSubmodule.add_mem hT hU
  | smul c T _ hT =>
    simpa only [LinearMap.smul_apply, map_smul] using P.toSubmodule.smul_mem c hT

end GeneralizedCentralSurjectivity

open FiniteActionSpectrum in
/-- An onto intertwiner restricts to an onto map on each actual uniform
generalized central-character space when the source central span is finite. -/
theorem generalizedCentralCharacterSurjectivity.{uGroup,uSource,uTarget} :
    GeneralizedCentralCharacterSurjectivityStatement.{uGroup,uSource,uTarget} := by
  classical
  intro G _ V _ _ W _ _ ρ σ hfin f hf χ
  let : CommGroup (Subgroup.center G) :=
    { (inferInstance : Group (Subgroup.center G)) with
      mul_comm := fun z t => Subtype.ext (Subgroup.mem_center_iff.mp t.property z) }
  let ρc : Representation ℂ (Subgroup.center G) V :=
    ρ.comp (Subgroup.center G).subtype
  let S : Submodule ℂ (Module.End ℂ V) := Submodule.span ℂ (Set.range ρc)
  have hmem : ∀ z, ρc z ∈ S := fun z => Submodule.subset_span ⟨z, rfl⟩
  have hone : (1 : Module.End ℂ V) ∈ S := by simpa using hmem 1
  have hmulρ : ∀ z, ∀ x ∈ S, ρc z * x ∈ S ∧ x * ρc z = ρc z * x := by
    intro z x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨t, rfl⟩ := hy
      refine ⟨?_, ?_⟩
      · rw [← map_mul]
        exact hmem (z * t)
      · rw [← map_mul, ← map_mul, mul_comm]
    | zero => simp
    | add x y _ _ hx hy =>
      refine ⟨?_, ?_⟩
      · rw [mul_add]
        exact S.add_mem hx.1 hy.1
      · rw [mul_add, add_mul, hx.2, hy.2]
    | smul c x _ hx =>
      refine ⟨?_, ?_⟩
      · rw [mul_smul_comm]
        exact S.smul_mem c hx.1
      · rw [mul_smul_comm, smul_mul_assoc, hx.2]
  have hmul : ∀ x y, x ∈ S → y ∈ S → x * y ∈ S ∧ x * y = y * x := by
    intro x y hx hy
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨z, rfl⟩ := hz
      exact ⟨(hmulρ z y hy).1, (hmulρ z y hy).2.symm⟩
    | zero => simp
    | add x z _ _ hx hz =>
      refine ⟨?_, ?_⟩
      · rw [add_mul]
        exact S.add_mem hx.1 hz.1
      · rw [add_mul, mul_add, hx.2, hz.2]
    | smul c x _ hx =>
      refine ⟨?_, ?_⟩
      · rw [smul_mul_assoc]
        exact S.smul_mem c hx.1
      · rw [smul_mul_assoc, mul_smul_comm, hx.2]
  let B : Subalgebra ℂ (Module.End ℂ V) :=
    S.toSubalgebra hone (fun x y hx hy => (hmul x y hx hy).1)
  let : CommRing B :=
    { (inferInstance : Ring B) with
      mul_comm := fun x y => Subtype.ext (hmul x y x.2 y.2).2 }
  have : Module.Finite ℂ B := by
    have : Module.Finite ℂ (Subalgebra.toSubmodule B) := by
      rw [Submodule.toSubalgebra_toSubmodule]
      exact hfin
    exact Subalgebra.finiteDimensional_toSubmodule.mp this
  let ρ' : Subgroup.center G →* B := ρc.codRestrict B hmem
  let ι : B →ₐ[ℂ] Module.End ℂ V := B.val
  have hι : ∀ z, ι (ρ' z) = ρ (z : G) := fun _ => rfl
  have : Finite (B →ₐ[ℂ] ℂ) := finite_algHom
  let : Fintype (B →ₐ[ℂ] ℂ) := Fintype.ofFinite _
  obtain ⟨N, h, hu, hann⟩ := exists_decomposition (R := B)
  let a : B := ((hu.unit⁻¹ : Bˣ) : B)
  let p : (B →ₐ[ℂ] ℂ) → B := fun φ => h φ * a
  have hsum : ∑ φ, p φ = 1 := by
    dsimp only [p]
    rw [← Finset.sum_mul]
    exact hu.mul_val_inv
  have hpann : ∀ φ, ∀ y ∈ RingHom.ker φ ^ N, y * p φ = 0 := by
    intro φ y hy
    dsimp only [p]
    rw [← mul_assoc, hann φ y hy, zero_mul]
  have hdef : ∀ (φ : B →ₐ[ℂ] ℂ) (z : Subgroup.center G),
      ρ (z : G) - ((algebraCharacter ρ' φ z : ℂˣ) : ℂ) • 1 =
        ι (ρ' z - algebraMap ℂ B (φ (ρ' z))) := by
    intro φ z
    rw [map_sub, AlgHom.commutes, hι, Algebra.algebraMap_eq_smul_one,
      algebraCharacter_apply]
  have hbound : ∀ (φ : B →ₐ[ℂ] ℂ) (z : Subgroup.center G) (v : V),
      ((ρ (z : G) - ((algebraCharacter ρ' φ z : ℂˣ) : ℂ) • 1) ^ N)
        (ι (p φ) v) = 0 := by
    intro φ z v
    have hker : ρ' z - algebraMap ℂ B (φ (ρ' z)) ∈ RingHom.ker φ := by
      simp [RingHom.mem_ker]
    rw [hdef φ z, ← map_pow, ← Module.End.mul_apply, ← map_mul,
      hpann φ _ (Ideal.pow_mem_pow hker N), map_zero, LinearMap.zero_apply]
  have hgen : ∀ (φ : B →ₐ[ℂ] ℂ) (v : V),
      ι (p φ) v ∈ generalizedCentralCharacterSpace ρ (algebraCharacter ρ' φ) :=
    fun φ v => (mem_generalizedCentralCharacterSpace ρ _ _).mpr
      ⟨N, fun z => hbound φ z v⟩
  have hdecomp : ∀ v : V, v = ∑ φ, ι (p φ) v := by
    intro v
    calc v = ι (∑ φ, p φ) v := by rw [hsum, map_one, Module.End.one_apply]
      _ = ∑ φ, ι (p φ) v := by rw [map_sum, LinearMap.sum_apply]
  intro w
  obtain ⟨v, hv⟩ := hf (w : W)
  have htarget : ∀ φ : B →ₐ[ℂ] ℂ,
      f (ι (p φ) v) ∈ generalizedCentralCharacterSpace σ χ := by
    intro φ
    apply GeneralizedCentralSurjectivity.preimage_stable f
      (generalizedCentralCharacterSpace σ χ) (T := ι (p φ))
    · exact (p φ).property
    · change f v ∈ (generalizedCentralCharacterSpace σ χ).toSubmodule
      rw [hv]
      exact w.property
  have hkill : ∀ φ : B →ₐ[ℂ] ℂ, algebraCharacter ρ' φ ≠ χ →
      f (ι (p φ) v) = 0 := by
    intro φ hne
    obtain ⟨z, hz⟩ := DFunLike.ne_iff.mp hne
    obtain ⟨k, hk⟩ := (mem_generalizedCentralCharacterSpace σ χ _).mp (htarget φ)
    have hφ := map_mem_generalizedCentralCharacterSpace f _ (hgen φ v)
    obtain ⟨l, hl⟩ := (mem_generalizedCentralCharacterSpace σ _ _).mp hφ
    exact eq_zero_of_pow_sub_smul (T := σ (z : G))
      (fun heq => hz (Units.ext heq)) (hl z) (hk z)
  let vχ : V := ∑ φ : B →ₐ[ℂ] ℂ,
    if algebraCharacter ρ' φ = χ then ι (p φ) v else 0
  have hvχ : vχ ∈ generalizedCentralCharacterSpace ρ χ := by
    apply Submodule.sum_mem (generalizedCentralCharacterSpace ρ χ).toSubmodule
    intro φ _
    split_ifs with hφ
    · change ι (p φ) v ∈ generalizedCentralCharacterSpace ρ χ
      rw [← hφ]
      exact hgen φ v
    · exact Submodule.zero_mem _
  refine ⟨⟨vχ, hvχ⟩, ?_⟩
  apply Subtype.ext
  change f vχ = (w : W)
  rw [← hv, hdecomp v]
  dsimp only [vχ]
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro φ _
  by_cases hφ : algebraCharacter ρ' φ = χ
  · simp only [ite_eq_left hφ]
  · rw [ite_eq_right hφ, map_zero, hkill φ hφ]

end Langlands
