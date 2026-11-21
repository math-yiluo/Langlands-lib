import Langlands.Group.GL.Blocks
import Langlands.Representation.Archimedean.GeneralLinear

/-! # Compact block Levi coordinates over the real and complex fields -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanCompactBlocks

open _root_.Langlands.Archimedean (unitaryCompact)
open Matrix GeneralLinear

variable (𝕜 : Type*) [RCLike 𝕜] {n : ℕ} (B : BlockShape n)

private theorem inverse_val_eq_star {a : Langlands.GeneralLinear n 𝕜}
    (ha : a ∈ unitaryCompact 𝕜 n) : (a⁻¹).val = star a.val :=
  Units.inv_eq_of_mul_eq_one_right (Matrix.mem_unitaryGroup_iff.mp ha)

private theorem leviEmbedding_mem_unitaryCompact (q : ∀ i, unitaryCompact 𝕜 (B.size i)) :
    B.leviEmbedding 𝕜 (fun i => (q i).val) ∈ unitaryCompact 𝕜 n := by
  let a := B.leviEmbedding 𝕜 (fun i => (q i).val)
  have hinv : a⁻¹ = B.leviEmbedding 𝕜 (fun i => ((q i).val)⁻¹) := by
    rw [← map_inv]
    rfl
  have hstar : (a⁻¹).val = star a.val := by
    refine Matrix.ext fun x y => ?_
    obtain ⟨⟨i, s⟩, rfl⟩ := B.indexEquiv.surjective x
    obtain ⟨⟨j, t⟩, rfl⟩ := B.indexEquiv.surjective y
    change (a⁻¹).val (B.index i s) (B.index j t) = star (a.val (B.index j t) (B.index i s))
    rw [hinv]
    by_cases h : i = j
    · subst j
      change B.leviEmbedding 𝕜 (fun i => ((q i).val)⁻¹) (B.index i s) (B.index i t) =
        star (B.leviEmbedding 𝕜 (fun i => (q i).val) (B.index i t) (B.index i s))
      rw [B.leviEmbedding_apply_same, B.leviEmbedding_apply_same]
      exact congrArg (fun A : Matrix (Fin (B.size i)) (Fin (B.size i)) 𝕜 => A s t)
        (inverse_val_eq_star (n := B.size i) 𝕜 (q i).property)
    · change B.leviEmbedding 𝕜 (fun i => ((q i).val)⁻¹) (B.index i s) (B.index j t) =
        star (B.leviEmbedding 𝕜 (fun i => (q i).val) (B.index j t) (B.index i s))
      rw [B.leviEmbedding_apply_ne _ _ _ _ h, B.leviEmbedding_apply_ne _ _ _ _ (Ne.symm h), star_zero]
  change a.val ∈ Matrix.unitaryGroup (Fin n) 𝕜
  rw [Matrix.mem_unitaryGroup_iff, ← hstar, ← Units.val_mul, mul_inv_cancel, Units.val_one]

/-- The block diagonal embedding of the product of the compact block subgroups. -/
def compactLeviEmbedding : (∀ i, unitaryCompact 𝕜 (B.size i)) →* unitaryCompact 𝕜 n where
  toFun q := ⟨B.leviEmbedding 𝕜 (fun i => (q i).val), leviEmbedding_mem_unitaryCompact 𝕜 B q⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul (B.leviEmbedding 𝕜) (fun i => (x i).val) (fun i => (y i).val))

@[simp]
theorem compactLeviEmbedding_val (q : ∀ i, unitaryCompact 𝕜 (B.size i)) :
    (compactLeviEmbedding 𝕜 B q).val = B.leviEmbedding 𝕜 (fun i => (q i).val) := rfl

private theorem leviProjection_mem_unitaryCompact (p : B.parabolic 𝕜)
    (hp : p.val ∈ unitaryCompact 𝕜 n) (i : Fin B.length) :
    B.leviProjection 𝕜 p i ∈ unitaryCompact 𝕜 (B.size i) := by
  let a := B.leviProjection 𝕜 p i
  have h : a⁻¹ = B.leviProjection 𝕜 p⁻¹ i := by rw [map_inv, Pi.inv_apply]
  have ha : (a⁻¹).val = star a.val := by
    refine Matrix.ext fun s t => ?_
    rw [h]
    exact congrArg (fun M : Matrix (Fin n) (Fin n) 𝕜 => M (B.index i s) (B.index i t))
      (inverse_val_eq_star 𝕜 hp)
  change a.val ∈ Matrix.unitaryGroup (Fin (B.size i)) 𝕜
  rw [Matrix.mem_unitaryGroup_iff, ← ha, ← Units.val_mul, mul_inv_cancel, Units.val_one]

/-- The diagonal blocks of a compact parabolic element are compact. -/
def compactLeviProjection (p : B.parabolic 𝕜) (hp : p.val ∈ unitaryCompact 𝕜 n) :
    ∀ i, unitaryCompact 𝕜 (B.size i) :=
  fun i => ⟨B.leviProjection 𝕜 p i, leviProjection_mem_unitaryCompact 𝕜 B p hp i⟩

/-- In the archimedean compact parabolic intersection, the element is the
block diagonal embedding of its Levi projection. -/
theorem compactLeviEmbedding_projection (p : B.parabolic 𝕜)
    (hp : p.val ∈ unitaryCompact 𝕜 n) :
    compactLeviEmbedding 𝕜 B (compactLeviProjection 𝕜 B p hp) = ⟨p.val, hp⟩ := by
  apply Subtype.ext
  apply Units.ext
  refine Matrix.ext fun x y => ?_
  obtain ⟨⟨i, s⟩, rfl⟩ := B.indexEquiv.surjective x
  obtain ⟨⟨j, t⟩, rfl⟩ := B.indexEquiv.surjective y
  change B.leviEmbedding 𝕜 (B.leviProjection 𝕜 p) (B.index i s) (B.index j t) =
    p.val (B.index i s) (B.index j t)
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [B.leviEmbedding_apply_ne _ _ _ _ (ne_of_lt hij)]
    have hbelow := (B.mem_parabolic_iff 𝕜 (p⁻¹).val).mp (p⁻¹).property j i t s hij
    change (p.val⁻¹).val (B.index j t) (B.index i s) = 0 at hbelow
    rw [inverse_val_eq_star 𝕜 hp, Matrix.star_apply] at hbelow
    exact (star_eq_zero.mp hbelow).symm
  · rw [B.leviEmbedding_apply_same, B.leviProjection_apply]
  · rw [B.leviEmbedding_apply_ne _ _ _ _ (ne_of_gt hji)]
    exact ((B.mem_parabolic_iff 𝕜 p.val).mp p.property i j s t hji).symm

end Langlands.Global.ArchimedeanCompactBlocks
