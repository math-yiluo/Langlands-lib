import Langlands.Representation.CuspidalSupport.JacquetInductionStatement
import Langlands.Representation.Geometric.WeylMinimalRepresentativeProof

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric

universe u

variable {n : ℕ} {R : Type u} [CommRing R]

theorem levi_mem_iff (B : BlockShape n) (g : GeneralLinear n R) :
    g ∈ B.leviSubgroup R ↔
      ∀ a b, blockIndex B a ≠ blockIndex B b → g a b = 0 := by
  constructor
  · rintro ⟨m, rfl⟩ a b hab
    obtain ⟨⟨i, x⟩, rfl⟩ := B.indexEquiv.surjective a
    obtain ⟨⟨j, y⟩, rfl⟩ := B.indexEquiv.surjective b
    apply B.leviEmbedding_apply_ne R m x y
    simpa [blockIndex] using hab
  · intro hg
    have hp : g ∈ B.parabolic R := by
      apply (B.mem_parabolic_iff R g).mpr
      intro i j a b hij
      exact hg _ _ (by simpa [blockIndex_index] using ne_of_gt hij)
    refine ⟨B.leviProjection R ⟨g, hp⟩, ?_⟩
    apply Units.ext
    ext a b
    obtain ⟨⟨i, x⟩, rfl⟩ := B.indexEquiv.surjective a
    obtain ⟨⟨j, y⟩, rfl⟩ := B.indexEquiv.surjective b
    change B.leviEmbedding R (B.leviProjection R ⟨g, hp⟩)
      (B.index i x) (B.index j y) = g (B.index i x) (B.index j y)
    by_cases hij : i = j
    · subst j
      simp
    · rw [B.leviEmbedding_apply_ne R _ x y hij]
      exact (hg _ _ (by simpa [blockIndex_index] using hij)).symm

/-- A permutation matrix lies in the actual embedded Levi exactly when its
permutation preserves every source block. -/
theorem permutation_mem_levi_iff [Nontrivial R] (B : BlockShape n)
    (w : Equiv.Perm (Fin n)) :
    permutation n R w ∈ B.leviSubgroup R ↔ w ∈ blockWeyl B := by
  rw [levi_mem_iff]
  constructor
  · intro h a
    by_contra ha
    have hz := h (w a) a ha
    simp [permutation_entry] at hz
  · intro h a b hab
    rw [permutation_entry]
    split_ifs with heq
    · exfalso
      apply hab
      rw [← heq]
      exact h b
    · rfl

private theorem map_conj_mul {G : Type*} [Group G] (H : Subgroup G) (x y : G) :
    H.map (MulAut.conj (x * y)).toMonoidHom =
      (H.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext g
  simp [MulAut.conj_apply, mul_assoc]

variable {F : Type u} [Field F] {B C D : BlockShape n}

theorem conjugatesLevi_mul {w v : Equiv.Perm (Fin n)}
    (hw : ConjugatesLevi (F := F) B C w)
    (hv : ConjugatesLevi (F := F) C D v) :
    ConjugatesLevi (F := F) B D (v * w) := by
  unfold ConjugatesLevi at *
  rw [map_mul, map_conj_mul, hw, hv]

private theorem conjugatesLevi_mem_iff {w : Equiv.Perm (Fin n)}
    (hw : ConjugatesLevi (F := F) B C w) (g : GeneralLinear n F) :
    permutation n F w * g * (permutation n F w)⁻¹ ∈ C.leviSubgroup F ↔
      g ∈ B.leviSubgroup F := by
  rw [← hw]
  exact Subgroup.mem_map_iff_mem (MulAut.conj (permutation n F w)).injective

theorem conjugatesLevi_inv {w : Equiv.Perm (Fin n)}
    (hw : ConjugatesLevi (F := F) B C w) :
    ConjugatesLevi (F := F) C B w⁻¹ := by
  apply Subgroup.ext
  intro g
  rw [Subgroup.mem_map_equiv]
  change ((permutation n F w⁻¹)⁻¹ * g * permutation n F w⁻¹ ∈ C.leviSubgroup F) ↔ _
  rw [map_inv, inv_inv]
  exact conjugatesLevi_mem_iff hw g

private theorem conjugatesLevi_self {w : Equiv.Perm (Fin n)}
    (hw : w ∈ blockWeyl B) : ConjugatesLevi (F := F) B B w := by
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mp
  apply (B.leviSubgroup F).le_normalizer
  exact (permutation_mem_levi_iff B w).mpr hw

/-- Actual Levi conjugation restricts to conjugation of their block Weyl groups. -/
theorem conjugatesLevi_weyl_mem {w b : Equiv.Perm (Fin n)}
    (hw : ConjugatesLevi (F := F) B C w) (hb : b ∈ blockWeyl B) :
    w * b * w⁻¹ ∈ blockWeyl C := by
  apply (permutation_mem_levi_iff (R := F) C _).mp
  simp only [map_mul, map_inv]
  exact (conjugatesLevi_mem_iff hw _).mpr ((permutation_mem_levi_iff B b).mpr hb)

private theorem conjugatesLevi_of_doubleCoset {w v : Equiv.Perm (Fin n)}
    (hw : ConjugatesLevi (F := F) B C w)
    (h : DoubleCoset.mk (blockWeyl C) (blockWeyl B) w =
      DoubleCoset.mk (blockWeyl C) (blockWeyl B) v) :
    ConjugatesLevi (F := F) B C v := by
  obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.eq.mp h
  simpa only [mul_assoc] using
    conjugatesLevi_mul (conjugatesLevi_mul (conjugatesLevi_self hb) hw)
      (conjugatesLevi_self ha)

private theorem right_factor_of_doubleCoset {w v : Equiv.Perm (Fin n)}
    (hv : ConjugatesLevi (F := F) B C v)
    (h : DoubleCoset.mk (blockWeyl C) (blockWeyl B) v =
      DoubleCoset.mk (blockWeyl C) (blockWeyl B) w) :
    ∃ b : blockWeyl B, w = v * b.val := by
  obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.eq.mp h
  have hc : v⁻¹ * a * v ∈ blockWeyl B := by
    simpa only [inv_inv] using conjugatesLevi_weyl_mem (conjugatesLevi_inv hv) ha
  refine ⟨⟨(v⁻¹ * a * v) * b, (blockWeyl B).mul_mem hc hb⟩, ?_⟩
  simp [mul_assoc]

/-- For every field and every rank, minimal conjugating permutations uniquely
represent the right cosets of the source block Weyl group. -/
theorem minimalConjugatingCosets
    (w : Equiv.Perm (Fin n)) (hw : ConjugatesLevi (F := F) B C w) :
    ∃! v : MinimalConjugatingPermutations (F := F) B C,
      ∃ b : blockWeyl B, w = v.val.val * b.val := by
  have hmin := weylDoubleCoset_bijective B C
  obtain ⟨v, hv⟩ := hmin.2 (DoubleCoset.mk (blockWeyl C) (blockWeyl B) w)
  have hvc : ConjugatesLevi (F := F) B C v.val :=
    conjugatesLevi_of_doubleCoset hw hv.symm
  refine ⟨⟨v, hvc⟩, right_factor_of_doubleCoset hvc hv, ?_⟩
  rintro u ⟨b, hb⟩
  apply Subtype.ext
  apply hmin.1
  change DoubleCoset.mk (blockWeyl C) (blockWeyl B) u.val.val = _
  rw [hv]
  apply DoubleCoset.eq.mpr
  exact ⟨1, (blockWeyl C).one_mem, b.val, b.property, by simpa using hb⟩

/-- The exact published p-adic, positive-rank statement. -/
theorem minimalConjugatingCosetsTheorem : MinimalConjugatingCosetsTheorem.{u} := by
  intro p hp F n hn B C w hw
  exact minimalConjugatingCosets w hw

end Langlands.CuspidalSupport
