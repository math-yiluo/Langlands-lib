import Langlands.Representation.LanglandsClassification.LanglandsTriplet

/-! # Nonempty open coroot chambers

For integral reflection data on finitely many relative roots and a standard cocharacter `ζ`
of a simple-root index `J`, the real character `y = ∑_β ⟨β, ζ⟩ β` pairs with each coroot
`α^∨` as half of `⟨α, ζ⟩ ∑_β ⟨β, α^∨⟩²`. Hence its restriction lies in the open coroot
chamber of `J`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.GroupScheme

open RealTorusSpace

variable {k : Type u} [Field k] {A T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]

/-- The reflection of a root permutes the finite set of relative roots, so it can be used
to reindex a sum over them. -/
theorem sum_relativeRoots_weylAction (hfinite : (relativeRoots i).Finite)
    (n : normalizerPoints i) (g : characterLattice T → ℤ) :
    ∑ β ∈ hfinite.toFinset, g (weylAction i n β) = ∑ β ∈ hfinite.toFinset, g β := by
  classical
  let e : characterLattice T ≃ characterLattice T := (weylAction i n).toEquiv
  have hmap : hfinite.toFinset.map e.toEmbedding = hfinite.toFinset := by
    ext β
    simp only [Finset.mem_map, Set.Finite.mem_toFinset, Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact weylAction_mapsTo_relativeRoots i n hx
    · intro hβ
      rw [← weylAction_image_relativeRoots i n] at hβ
      obtain ⟨x, hx, rfl⟩ := hβ
      exact ⟨x, hx, rfl⟩
  calc ∑ β ∈ hfinite.toFinset, g (weylAction i n β)
      = ∑ β ∈ hfinite.toFinset.map e.toEmbedding, g β := by
        rw [Finset.sum_map]
        rfl
    _ = ∑ β ∈ hfinite.toFinset, g β := by rw [hmap]

/-- The pairing identity `2 ∑_β ⟨β, ζ⟩⟨β, α^∨⟩ = ⟨α, ζ⟩ ∑_β ⟨β, α^∨⟩²`. -/
theorem two_mul_sum_pairing_coroot (D : RelativeRootReflectionData i)
    (hfinite : (relativeRoots i).Finite) (ζ : cocharacterLattice T) (α : relativeRoots i) :
    2 * ∑ β ∈ hfinite.toFinset,
        latticePairing T β ζ * latticePairing T β (D.coroot α) =
      latticePairing T α.val ζ *
        ∑ β ∈ hfinite.toFinset, latticePairing T β (D.coroot α) ^ 2 := by
  have hre := sum_relativeRoots_weylAction i hfinite (D.representative α)
    (fun β => latticePairing T β ζ * latticePairing T β (D.coroot α))
  simp only [D.action, map_sub, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul, D.pair_self] at hre
  rw [two_mul]
  nth_rewrite 1 [← hre]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  ring

/-- The sum of squared coroot pairings over the roots is positive. -/
theorem sum_pairing_coroot_sq_pos (D : RelativeRootReflectionData i)
    (hfinite : (relativeRoots i).Finite) (α : relativeRoots i) :
    0 < ∑ β ∈ hfinite.toFinset, latticePairing T β (D.coroot α) ^ 2 := by
  have hα : α.val ∈ hfinite.toFinset := (Set.Finite.mem_toFinset hfinite).mpr α.property
  calc (0 : ℤ) < latticePairing T α.val (D.coroot α) ^ 2 := by rw [D.pair_self]; norm_num
    _ ≤ ∑ β ∈ hfinite.toFinset, latticePairing T β (D.coroot α) ^ 2 :=
      Finset.single_le_sum (f := fun β => latticePairing T β (D.coroot α) ^ 2)
        (fun β _ => sq_nonneg _) hα

/-- The open coroot chamber of a standard index is nonempty. -/
theorem restrictedCorootChamber_nonempty (ν : cocharacterLattice T)
    (J : Set (characterLattice T)) (f : A ⟶ T) (D : RelativeRootReflectionData i)
    (hfinite : (relativeRoots i).Finite) (ζ : cocharacterLattice T)
    (hζ : IsStandardCocharacter i ν J ζ) :
    (restrictedCorootChamber i ν J f D).Nonempty := by
  classical
  let y : Vstar T :=
    ∑ β ∈ hfinite.toFinset, ((latticePairing T β ζ : ℤ) : ℝ) ⊗ₜ[ℤ] β
  have hpair : ∀ α : relativeRoots i,
      pair T y ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) =
        ((∑ β ∈ hfinite.toFinset,
          latticePairing T β ζ * latticePairing T β (D.coroot α) : ℤ) : ℝ) := by
    intro α
    simp only [y, map_sum, LinearMap.sum_apply, pair_tmul_tmul]
    push_cast
    refine Finset.sum_congr rfl fun β _ => ?_
    ring
  refine ⟨rationalCharacterRestrictReal (CommGroupScheme.groupHom f) y, y, rfl, ?_, ?_⟩
  · intro α hαJ
    rw [hpair]
    have h2 := two_mul_sum_pairing_coroot i D hfinite ζ α
    rw [hζ.2.1 α.val hαJ, zero_mul] at h2
    have h0 : (∑ β ∈ hfinite.toFinset,
        latticePairing T β ζ * latticePairing T β (D.coroot α)) = 0 := by omega
    rw [h0]
    simp
  · intro α hαs hαJ
    rw [hpair]
    have h2 := two_mul_sum_pairing_coroot i D hfinite ζ α
    have hpos := hζ.2.2 α.val hαs hαJ
    have hsq := sum_pairing_coroot_sq_pos i D hfinite α
    have hprod := mul_pos hpos hsq
    have hS : 0 < (∑ β ∈ hfinite.toFinset,
        latticePairing T β ζ * latticePairing T β (D.coroot α)) := by omega
    exact_mod_cast hS

end Langlands.GroupScheme
