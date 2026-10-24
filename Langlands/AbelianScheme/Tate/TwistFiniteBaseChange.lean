import Langlands.AbelianScheme.Tate.TwistFiniteMonodromy
import Langlands.AlgebraicGeometry.FiniteEtale.Pullback

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u

namespace Langlands.GroupScheme.mu

variable {S S' : Scheme.{u}} (b : S' ⟶ S) (n : ℕ)

/-- The canonical comparison of actual root-kernel points, preserving the root coordinate. -/
def pointsBaseChangeEquiv (T : Over S') :
    (T ⟶ (mu S' n).X) ≃* ((Over.map b).obj T ⟶ (mu S n).X) :=
  (pointsEquiv S' n T).trans (pointsEquiv S n ((Over.map b).obj T)).symm

/-- The comparison is induced by the canonical group-scheme pullback isomorphism. -/
theorem pointsBaseChangeEquiv_eq_actual (T : Over S') (x : T ⟶ (mu S' n).X) :
    pointsBaseChangeEquiv b n T x =
      baseChangePointsEquiv b (mu S n).toGrp T (x ≫ (baseChangeIso b n).inv.hom.hom) := by
  apply (pointsEquiv S n ((Over.map b).obj T)).injective
  change (pointsEquiv S n ((Over.map b).obj T))
    ((pointsEquiv S n ((Over.map b).obj T)).symm (pointsEquiv S' n T x)) = _
  rw [MulEquiv.apply_symm_apply]
  exact (baseChangeRootsEquiv_baseChangeIso_inv b n T x).symm

/-- The underlying scheme map is the inverse canonical isomorphism and first projection. -/
theorem pointsBaseChangeEquiv_left (T : Over S') (x : T ⟶ (mu S' n).X) :
    (pointsBaseChangeEquiv b n T x).left =
      x.left ≫ (baseChangeIso b n).inv.hom.hom.left ≫ pullback.fst (mu S n).X.hom b := by
  rw [pointsBaseChangeEquiv_eq_actual, baseChangePointsEquiv_left]
  exact Category.assoc _ _ _

/-- The comparison on affine points leaves the actual root of unity unchanged. -/
@[simp] theorem levelEquiv_pointsBaseChangeEquiv {R : CommRingCat.{u}}
    (t : Spec R ⟶ S') (x : Additive (Over.mk t ⟶ (mu S' n).X)) :
    levelEquiv n (t ≫ b)
        (Additive.ofMul (pointsBaseChangeEquiv b n (Over.mk t) x.toMul)) =
      levelEquiv n t x := by
  change Additive.ofMul
    ((MulEquiv.restrictRootsOfUnity
      (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.toMulEquiv n)
      ((pointsEquiv S n ((Over.map b).obj (Over.mk t)))
        ((pointsEquiv S n ((Over.map b).obj (Over.mk t))).symm
          (pointsEquiv S' n (Over.mk t) x.toMul)))) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

open Langlands.AlgebraicGeometry.FiniteEtale
variable {Ω : Type u} [Field Ω] (t : Spec (.of Ω) ⟶ S')
  (ht : ∀ Y : Cover S', Finite (Fiber t Y))
  (hs : ∀ Y : Cover S, Finite (Fiber (t ≫ b) Y))
  [IsFinite (mu S n).X.hom] [Etale (mu S n).X.hom]
  [IsFinite (mu S' n).X.hom] [Etale (mu S' n).X.hom]

/-- Actual root-kernel points intertwine evaluation and the pointed fundamental-group map. -/
theorem pointsBaseChangeEquiv_act (g : FundamentalGroup t ht)
    (x : Over.mk t ⟶ (mu S' n).X) :
    pointsBaseChangeEquiv b n (Over.mk t) (act t ht (mu S' n).X g x) =
      act (t ≫ b) hs (mu S n).X (fundamentalGroupMap b t (t ≫ b) rfl ht hs g)
        (pointsBaseChangeEquiv b n (Over.mk t) x) := by
  let φ := (baseChangeIso b n).inv.hom.hom.left ≫ pullback.fst (mu S n).X.hom b
  have hφ : φ ≫ (mu S n).X.hom = (mu S' n).X.hom ≫ b := by
    dsimp [φ]
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    congr 1
    exact (baseChangeIso b n).inv.hom.hom.w
  apply Over.OverMorphism.ext
  rw [pointsBaseChangeEquiv_left]
  exact (fundamentalGroupMap_smul_left_of_comp b t (t ≫ b) rfl ht hs g
    (Y := ofOver (mu S n).X) (pointsBaseChangeEquiv b n (Over.mk t) x)
    (Y' := ofOver (mu S' n).X) x φ hφ
    (pointsBaseChangeEquiv_left b n (Over.mk t) x).symm).symm

end Langlands.GroupScheme.mu

namespace Langlands.TateTwist.Geometry
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme

variable {S S' : Scheme.{u}} (b : S' ⟶ S) {Ω : Type u} [Field Ω]
  (t : Spec (.of Ω) ⟶ S')
  (ht : ∀ Y : Cover S', Finite (Fiber t Y))
  (hs : ∀ Y : Cover S, Finite (Fiber (t ≫ b) Y))
  (n : ℕ)
  [IsFinite (mu S n).X.hom] [Etale (mu S n).X.hom]
  [IsFinite (mu S' n).X.hom] [Etale (mu S' n).X.hom]

/-- The same root has compatible geometric monodromy under pointed base change. -/
theorem levelMonodromy_baseChange (g : FundamentalGroup t ht) (x : Level Ω n) :
    levelMonodromy (t ≫ b) hs n (fundamentalGroupMap b t (t ≫ b) rfl ht hs g) x =
      levelMonodromy t ht n g x := by
  obtain ⟨y, rfl⟩ := (mu.levelEquiv n t).surjective x
  conv_lhs => rw [← mu.levelEquiv_pointsBaseChangeEquiv b n t y]
  rw [levelMonodromy_kernel, levelMonodromy_kernel]
  simp only [toMul_ofMul]
  rw [← mu.pointsBaseChangeEquiv_act b n t ht hs g y.toMul]
  exact mu.levelEquiv_pointsBaseChangeEquiv b n t _

/-- Restriction along the induced fundamental-group homomorphism recovers the root representation. -/
theorem levelRepresentation_baseChange :
    (levelRepresentation (t ≫ b) hs n).comp (fundamentalGroupMap b t (t ≫ b) rfl ht hs) =
      levelRepresentation t ht n := by
  apply MonoidHom.ext
  intro g
  apply LinearEquiv.ext
  intro x
  exact levelMonodromy_baseChange b t ht hs n g x

end Langlands.TateTwist.Geometry
