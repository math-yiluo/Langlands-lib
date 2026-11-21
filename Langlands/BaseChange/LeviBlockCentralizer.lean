import Langlands.BaseChange.LeviNormDescent

/-! The regular ambient centralizer as the actual product of block centralizers. -/

namespace Langlands.BaseChange

open Langlands.GeneralLinear

universe u

variable {R : Type u} [Field R] {n : ℕ} (B : BlockShape n) (m : B.Levi R)

theorem leviEmbedding_mem_glCentralizer_iff (g : B.Levi R) :
    B.leviEmbedding R g ∈ glCentralizer (B.leviEmbedding R m) ↔
      ∀ i, g i ∈ glCentralizer (m i) := by
  simp_rw [glCentralizer_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h i
    have he : g * m = m * g := B.leviEmbedding_injective R (by
      simpa only [map_mul] using h)
    exact congrFun he i
  · intro h
    have he : g * m = m * g := funext h
    simpa only [map_mul] using congrArg (B.leviEmbedding R) he

variable (hCop : Pairwise fun i j => IsCoprime (m i).val.charpoly (m j).val.charpoly)

private def leviCentralizerCoordinate : glCentralizer (B.leviEmbedding R m) →* B.Levi R :=
  (B.leviEquiv R).symm.toMonoidHom.comp
    (Subgroup.inclusion (glCentralizer_le_leviSubgroup B m hCop))

private theorem leviEmbedding_leviCentralizerCoordinate
    (g : glCentralizer (B.leviEmbedding R m)) :
    B.leviEmbedding R (leviCentralizerCoordinate B m hCop g) = g.val :=
  congrArg Subtype.val ((B.leviEquiv R).apply_symm_apply
    (Subgroup.inclusion (glCentralizer_le_leviSubgroup B m hCop) g))

variable [TopologicalSpace R] [IsTopologicalRing R]

/-- For pairwise coprime block characteristic polynomials the ambient centralizer
is continuously isomorphic to the product of the actual block centralizers. -/
def glCentralizerLeviPiEquiv :
    glCentralizer (B.leviEmbedding R m) ≃ₜ* ∀ i, glCentralizer (m i) where
  toFun g i := ⟨leviCentralizerCoordinate B m hCop g i,
    (leviEmbedding_mem_glCentralizer_iff B m _).mp
      ((leviEmbedding_leviCentralizerCoordinate B m hCop g).symm ▸ g.property) i⟩
  invFun k := ⟨B.leviEmbedding R (fun i => (k i).val),
    (leviEmbedding_mem_glCentralizer_iff B m _).mpr (fun i => (k i).property)⟩
  left_inv g := Subtype.ext (leviEmbedding_leviCentralizerCoordinate B m hCop g)
  right_inv k := by
    let g : glCentralizer (B.leviEmbedding R m) :=
      ⟨B.leviEmbedding R (fun i => (k i).val),
        (leviEmbedding_mem_glCentralizer_iff B m _).mpr (fun i => (k i).property)⟩
    have hCoord : leviCentralizerCoordinate B m hCop g = fun i => (k i).val :=
      B.leviEmbedding_injective R (leviEmbedding_leviCentralizerCoordinate B m hCop g)
    exact funext fun i => Subtype.ext (congrFun hCoord i)
  map_mul' g g' := by
    funext i
    apply Subtype.ext
    exact congrFun ((leviCentralizerCoordinate B m hCop).map_mul g g') i
  continuous_toFun := by
    have hg : Continuous (leviCentralizerCoordinate B m hCop) :=
      (B.leviEquivContinuous R).symm.continuous.comp
        (continuous_subtype_val.subtype_mk _)
    exact continuous_pi fun i =>
      ((continuous_apply i).comp hg).subtype_mk _
  continuous_invFun :=
    ((B.leviEmbeddingContinuous R).continuous.comp
      (continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i))).subtype_mk _

@[simp] theorem glCentralizerLeviPiEquiv_symm_apply_val
    (g : ∀ i, glCentralizer (m i)) :
    ((glCentralizerLeviPiEquiv B m hCop).symm g).val =
      B.leviEmbedding R (fun i => (g i).val) := rfl

end Langlands.BaseChange
