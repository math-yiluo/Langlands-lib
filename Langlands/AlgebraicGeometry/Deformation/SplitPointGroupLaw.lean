import Langlands.AlgebraicGeometry.SplitInfinitesimalCoordinates
import Langlands.AbelianScheme.GroupScheme

/-! # The group law on split infinitesimal points at the identity is addition -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.AlgebraicGeometry.SplitInfinitesimalCoordinates

open SquareZeroAffinePairs
open scoped SquareZeroAffinePairs

variable {k : Type u} [Field k] {G : Langlands.GroupScheme (Spec (CommRingCat.of k))}
  (c : PointChart G.X (1 : test (k := k) k ⟶ G.X))
  {D : Type u} [CommRing D] [Algebra k D]
  {M : Type u} [AddCommGroup M] [Module D M] [Module k M] [IsScalarTower k D M]

/-- The pointwise product of two split infinitesimal points at the identity. -/
def PointChart.mul (v w : c.Points (D := D) (M := M)) : c.Points (D := D) (M := M) :=
  ⟨v.val * w.val, by
    rw [MonObj.comp_mul, v.property, w.property, ← MonObj.comp_mul, mul_one]⟩

theorem PointChart.mapPoints_mul {N : Type u} [AddCommGroup N] [Module D N] [Module k N]
    [IsScalarTower k D N] (g : M →ₗ[D] N) (v w : c.Points (D := D) (M := M)) :
    c.mapPoints (AlgHom.id k D) g (c.mul v w) =
      c.mul (c.mapPoints (AlgHom.id k D) g v) (c.mapPoints (AlgHom.id k D) g w) := by
  apply Subtype.ext
  exact MonObj.comp_mul _ _ _

theorem splitAlgMap_id_comp {N : Type u} [AddCommGroup N] [Module D N] [Module k N]
    [IsScalarTower k D N] {P : Type u} [AddCommGroup P] [Module D P] [Module k P]
    [IsScalarTower k D P] (g : N →ₗ[D] P) (h : M →ₗ[D] N) :
    (splitAlgMap (k := k) (AlgHom.id k D) g).comp (splitAlgMap (AlgHom.id k D) h) =
      splitAlgMap (AlgHom.id k D) (g.comp h) := by
  apply AlgHom.ext
  intro z
  exact TrivSqZeroExt.ext rfl rfl

theorem splitAlgMap_id_id :
    splitAlgMap (k := k) (AlgHom.id k D) (LinearMap.id : M →ₗ[D] M) = AlgHom.id k _ := by
  apply AlgHom.ext
  intro z
  exact TrivSqZeroExt.ext rfl rfl

theorem splitAlgMap_id_zero {N : Type u} [AddCommGroup N] [Module D N] [Module k N]
    [IsScalarTower k D N] :
    splitAlgMap (k := k) (AlgHom.id k D) (0 : M →ₗ[D] N) =
      (TrivSqZeroExt.inlAlgHom k D N).comp (TrivSqZeroExt.fstHom k D M) := by
  apply AlgHom.ext
  intro z
  exact TrivSqZeroExt.ext rfl rfl

theorem PointChart.mapPoints_comp {N : Type u} [AddCommGroup N] [Module D N] [Module k N]
    [IsScalarTower k D N] {P : Type u} [AddCommGroup P] [Module D P] [Module k P]
    [IsScalarTower k D P] (g : N →ₗ[D] P) (h : M →ₗ[D] N) (v : c.Points (D := D) (M := M)) :
    c.mapPoints (AlgHom.id k D) g (c.mapPoints (AlgHom.id k D) h v) =
      c.mapPoints (AlgHom.id k D) (g.comp h) v := by
  apply Subtype.ext
  change affineTestMap (splitAlgMap (AlgHom.id k D) g) ≫
      affineTestMap (splitAlgMap (AlgHom.id k D) h) ≫ v.val =
    affineTestMap (splitAlgMap (AlgHom.id k D) (g.comp h)) ≫ v.val
  rw [← Category.assoc, ← affineTestMap_comp, splitAlgMap_id_comp]

theorem PointChart.mapPoints_id (v : c.Points (D := D) (M := M)) :
    c.mapPoints (AlgHom.id k D) (LinearMap.id : M →ₗ[D] M) v = v := by
  apply Subtype.ext
  change affineTestMap (splitAlgMap (AlgHom.id k D) LinearMap.id) ≫ v.val = v.val
  rw [splitAlgMap_id_id]
  simp [affineTestMap]

theorem PointChart.mapPoints_zero {N : Type u} [AddCommGroup N] [Module D N] [Module k N]
    [IsScalarTower k D N] (v : c.Points (D := D) (M := M)) :
    (c.mapPoints (AlgHom.id k D) (0 : M →ₗ[D] N) v).val = 1 := by
  change affineTestMap (splitAlgMap (AlgHom.id k D) (0 : M →ₗ[D] N)) ≫ v.val = 1
  rw [splitAlgMap_id_zero, affineTestMap_comp, Category.assoc, v.property, MonObj.comp_one,
    MonObj.comp_one]

/-- On split infinitesimal points at the identity of a group scheme, the group law is the sum
of cotangent coordinates. -/
theorem PointChart.linearCoordinates_mul (v w : c.Points (D := D) (M := M)) :
    c.linearCoordinates (c.mul v w) = c.linearCoordinates v + c.linearCoordinates w := by
  let Q₁ : c.Points (D := D) (M := M × M) := c.mapPoints (AlgHom.id k D) (LinearMap.inl D M M) v
  let Q₂ : c.Points (D := D) (M := M × M) := c.mapPoints (AlgHom.id k D) (LinearMap.inr D M M) w
  let Q := c.mul Q₁ Q₂
  have h₁ : c.mapPoints (AlgHom.id k D) (LinearMap.fst D M M) Q = v := by
    apply Subtype.ext
    rw [c.mapPoints_mul]
    change (c.mapPoints _ _ Q₁).val * (c.mapPoints _ _ Q₂).val = v.val
    rw [c.mapPoints_comp, c.mapPoints_comp, LinearMap.fst_comp_inl, LinearMap.fst_comp_inr,
      c.mapPoints_id, c.mapPoints_zero, mul_one]
  have h₂ : c.mapPoints (AlgHom.id k D) (LinearMap.snd D M M) Q = w := by
    apply Subtype.ext
    rw [c.mapPoints_mul]
    change (c.mapPoints _ _ Q₁).val * (c.mapPoints _ _ Q₂).val = w.val
    rw [c.mapPoints_comp, c.mapPoints_comp, LinearMap.snd_comp_inl, LinearMap.snd_comp_inr,
      c.mapPoints_id, c.mapPoints_zero, one_mul]
  have h₃ : c.mapPoints (AlgHom.id k D) (LinearMap.fst D M M + LinearMap.snd D M M) Q =
      c.mul v w := by
    apply Subtype.ext
    rw [c.mapPoints_mul]
    change (c.mapPoints _ _ Q₁).val * (c.mapPoints _ _ Q₂).val = v.val * w.val
    rw [c.mapPoints_comp, c.mapPoints_comp, LinearMap.add_comp, LinearMap.add_comp,
      LinearMap.fst_comp_inl, LinearMap.snd_comp_inl, LinearMap.fst_comp_inr,
      LinearMap.snd_comp_inr, add_zero, zero_add, c.mapPoints_id, c.mapPoints_id]
  apply LinearMap.ext
  intro t
  have e₁ := c.linearCoordinates_mapPoints (AlgHom.id k D) (LinearMap.fst D M M) Q t
  have e₂ := c.linearCoordinates_mapPoints (AlgHom.id k D) (LinearMap.snd D M M) Q t
  have e₃ := c.linearCoordinates_mapPoints (AlgHom.id k D)
    (LinearMap.fst D M M + LinearMap.snd D M M) Q t
  rw [h₁] at e₁
  rw [h₂] at e₂
  rw [h₃] at e₃
  rw [LinearMap.add_apply, e₁, e₂, e₃]
  rfl

end Langlands.AlgebraicGeometry.SplitInfinitesimalCoordinates
