import Langlands.Global.AdelicBlockCompactProjection

/-!
# Block diagonal inclusions for adelic compact slices

The block diagonal map embeds the product of the actual infinite compacts
in the infinite compact of the ambient group. Pairing the finite and
infinite Levi coordinates agrees with the ambient parabolic pairing.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v w

namespace Langlands.Global.AdelicBlockParabolic

open Langlands.GeneralLinear PrimitiveAdelicHeight

variable {n : ℕ} (B : BlockShape n)

private theorem leviEmbedding_map_mem_unitary {R : Type v} {A : Type w}
    [CommRing R] [CommRing A] [StarRing A] (f : R →+* A) (m : B.Levi R)
    (hm : ∀ i, (Matrix.GeneralLinearGroup.map f (m i)).val ∈
      Matrix.unitaryGroup (Fin (B.size i)) A) :
    (Matrix.GeneralLinearGroup.map f (B.leviEmbedding R m)).val ∈
      Matrix.unitaryGroup (Fin n) A := by
  let g := Matrix.GeneralLinearGroup.map f (B.leviEmbedding R m)
  have hg : (g⁻¹).val = star g.val := by
    have hginv : g⁻¹ = Matrix.GeneralLinearGroup.map f (B.leviEmbedding R m⁻¹) := by
      simp only [g, map_inv]
    rw [hginv]
    ext x y
    obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective x
    obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective y
    change f (B.leviEmbedding R m⁻¹ (B.index i a) (B.index j b)) =
      star (f (B.leviEmbedding R m (B.index j b) (B.index i a)))
    by_cases h : i = j
    · subst j
      simp only [B.leviEmbedding_apply_same, Pi.inv_apply]
      have hi : ((Matrix.GeneralLinearGroup.map f (m i))⁻¹).val =
          star (Matrix.GeneralLinearGroup.map f (m i)).val :=
        Units.inv_eq_of_mul_eq_one_right (Matrix.mem_unitaryGroup_iff.mp (hm i))
      rw [← map_inv] at hi
      exact congrArg (fun M : Matrix (Fin (B.size i)) (Fin (B.size i)) A => M a b) hi
    · rw [B.leviEmbedding_apply_ne R _ a b h,
        B.leviEmbedding_apply_ne R _ b a (Ne.symm h), map_zero, star_zero]
  change g.val ∈ Matrix.unitaryGroup (Fin n) A
  rw [Matrix.mem_unitaryGroup_iff, ← hg, ← Units.val_mul, mul_inv_cancel, Units.val_one]

variable (F : Type u) [Field F]

/-- Block diagonal inclusion of the actual infinite compact subgroups. -/
def infiniteLeviCompactInclusion :
    (∀ i : Fin B.length, standardInfiniteCompact F (B.size i)) →* standardInfiniteCompact F n where
  toFun k := ⟨B.leviEmbedding (InfiniteAdeles F) (fun i => (k i).val), by
    apply (mem_standardInfiniteCompact_iff F n _).mpr
    refine ⟨fun z => ?_, fun z => ?_⟩
    · exact leviEmbedding_map_mem_unitary B
        ((realCoord z).comp (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom)
        _ (fun i => ((mem_standardInfiniteCompact_iff F (B.size i) (k i).val).mp (k i).property).1 z)
    · exact leviEmbedding_map_mem_unitary B
        ((complexCoord z).comp (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom)
        _ (fun i => ((mem_standardInfiniteCompact_iff F (B.size i) (k i).val).mp (k i).property).2 z)⟩
  map_one' := Subtype.ext ((B.leviEmbedding (InfiniteAdeles F)).map_one)
  map_mul' k l := Subtype.ext ((B.leviEmbedding (InfiniteAdeles F)).map_mul
    (fun i => (k i).val) (fun i => (l i).val))

@[simp]
theorem infiniteLeviCompactInclusion_val
    (k : ∀ i : Fin B.length, standardInfiniteCompact F (B.size i)) :
    (infiniteLeviCompactInclusion B F k).val =
      B.leviEmbedding (InfiniteAdeles F) (fun i => (k i).val) := rfl

variable [NumberField F]

/-- The actual block diagonal parabolic section commutes with pairing. -/
theorem leviInParabolic_pair (a : InfiniteLevi F B) (b : FiniteLevi F B) :
    B.leviInParabolic (Adeles F) (leviPair F B a b) =
      AdelicBlockParabolic.pair F B (B.leviInParabolic (InfiniteAdeles F) a)
        (B.leviInParabolic (FiniteAdeles F) b) := by
  apply (split F B).injective
  apply Prod.ext
  · change infinite F B (B.leviInParabolic (Adeles F) (leviPair F B a b)) =
      infinite F B (AdelicBlockParabolic.pair F B _ _)
    rw [infinite_leviInParabolic, leviInfinite_pair, infinite_pair]
  · change finite F B (B.leviInParabolic (Adeles F) (leviPair F B a b)) =
      finite F B (AdelicBlockParabolic.pair F B _ _)
    rw [finite_leviInParabolic, leviFinite_pair, finite_pair]

/-- Embedding a pure archimedean Levi point agrees with first embedding in the
archimedean ambient group. -/
theorem leviEmbedding_infiniteOnly (a : InfiniteLevi F B) :
    B.leviEmbedding (Adeles F) (leviPair F B a 1) =
      AdelicGL.ofInfinite F n (B.leviEmbedding (InfiniteAdeles F) a) := by
  have h := congrArg Subtype.val (leviInParabolic_pair B F a (1 : FiniteLevi F B))
  rw [map_one, pair_val, B.leviInParabolic_val] at h
  exact h

/-- Embedding a pure finite Levi point agrees with first embedding in the
finite ambient group. -/
theorem leviEmbedding_finiteOnly (b : FiniteLevi F B) :
    B.leviEmbedding (Adeles F) (leviPair F B 1 b) =
      AdelicGL.ofFinite F n (B.leviEmbedding (FiniteAdeles F) b) := by
  have h := congrArg Subtype.val (leviInParabolic_pair B F (1 : InfiniteLevi F B) b)
  rw [map_one, pair_val, B.leviInParabolic_val] at h
  exact h

end Langlands.Global.AdelicBlockParabolic
