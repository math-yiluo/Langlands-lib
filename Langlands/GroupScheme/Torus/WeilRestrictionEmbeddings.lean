import Langlands.GroupScheme.Torus.WeilRestrictionDecomposition
import Langlands.Algebra.EmbeddingPermutation

/-! # Embedding coordinates for the Weil-restricted multiplicative group -/

set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.Algebra.SeparableTensor

namespace Langlands.GroupScheme.WeilGm


section Algebra

variable (k K Ω : Type u) [CommRing k] [CommRing K] [CommRing Ω]
  [Algebra k K] [Algebra k Ω]
  (h : Function.Bijective (embeddingEvaluation k K Ω))

/-- The canonical tensor evaluation, regarded as an equivalence using its bijectivity. -/
def embeddingDecomposition : Ω ⊗[k] K ≃ₐ[Ω] ((K →ₐ[k] Ω) → Ω) :=
  AlgEquiv.ofBijective (embeddingEvaluation k K Ω) h

@[simp] theorem embeddingDecomposition_tmul (c : Ω) (x : K) (τ : K →ₐ[k] Ω) :
    embeddingDecomposition k K Ω h (c ⊗ₜ x) τ = c * τ x := rfl

variable (R : Type u) [CommRing R] [Algebra Ω R] [Algebra k R] [IsScalarTower k Ω R]
  [Finite (K →ₐ[k] Ω)]

/-- The decomposition on a test algebra evaluates the original tensor at each embedding. -/
theorem embeddingDecompositionTensorEquiv_apply (x : K ⊗[k] R) (τ : K →ₐ[k] Ω) :
    decompositionTensorEquiv k Ω K R (K →ₐ[k] Ω) (embeddingDecomposition k K Ω h) x τ =
      tensorCoordinate (IsScalarTower.toAlgHom k Ω R) τ x := by
  induction x using TensorProduct.inductionOn with
  | tmul x r => simp [Algebra.smul_def]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

end Algebra

section Scheme

variable (k K Ω : Type u) [CommRing k] [CommRing K] [CommRing Ω]
  [Algebra k K] [Algebra k Ω] [Module.Finite k K] [Module.Projective k K]
  [Finite (K →ₐ[k] Ω)] (h : Function.Bijective (embeddingEvaluation k K Ω))

local notation "W_Ω" =>
  (Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k Ω))
    (commGroupScheme (CommRingCat.of k) K))

/-- Canonical evaluation splits the actual Weil restriction after base change. -/
def embeddingIso :
    (GroupScheme.baseChange (algebraBaseMap k Ω)).obj (groupScheme (CommRingCat.of k) K) ≅
      splitTorus (Spec (CommRingCat.of Ω)) (K →ₐ[k] Ω) :=
  decompositionIso (CommRingCat.of k) (CommRingCat.of Ω) K (K →ₐ[k] Ω)
    (embeddingDecomposition k K Ω h)

/-- The same splitting in the commutative category. -/
def embeddingCommIso :
    W_Ω ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of Ω)) (K →ₐ[k] Ω) :=
  commDecompositionIso (CommRingCat.of k) (CommRingCat.of Ω) K (K →ₐ[k] Ω)
    (embeddingDecomposition k K Ω h)

/-- Embedding coordinates on every test scheme. -/
def embeddingPointsEquiv (T : Over (Spec (CommRingCat.of Ω))) :
    (T ⟶ (W_Ω).X) ≃* ((K →ₐ[k] Ω) → (Γ(T.left, ⊤))ˣ) :=
  decompositionPointsEquiv (CommRingCat.of k) (CommRingCat.of Ω) K (K →ₐ[k] Ω)
    (embeddingDecomposition k K Ω h) T

/-- The coefficient map into the sections of a test scheme, as a `k`-algebra map. -/
def embeddingCoefficientMap (T : Over (Spec (CommRingCat.of Ω))) :
    Ω →ₐ[k] restrictedSections (CommRingCat.of k) (CommRingCat.of Ω) T :=
  letI := restrictedSectionsAlgebra (CommRingCat.of k) (CommRingCat.of Ω) T
  letI := restrictedSectionsScalarTower (CommRingCat.of k) (CommRingCat.of Ω) T
  IsScalarTower.toAlgHom (CommRingCat.of k) (CommRingCat.of Ω) _

/-- Coordinates are the unit maps of tensor evaluation on the original `k`-point. -/
theorem embeddingPointsEquiv_apply (T : Over (Spec (CommRingCat.of Ω)))
    (x : T ⟶ (W_Ω).X) (τ : K →ₐ[k] Ω) :
    embeddingPointsEquiv k K Ω h T x τ =
      Units.map (tensorCoordinate (embeddingCoefficientMap k Ω T) τ).toMonoidHom
        (pointsEquiv (CommRingCat.of k) K ((Over.map (algebraBaseMap k Ω)).obj T)
          (GroupScheme.baseChangePointsEquiv (algebraBaseMap k Ω)
            (groupScheme (CommRingCat.of k) K) T x)) := by
  let := restrictedSectionsAlgebra (CommRingCat.of k) (CommRingCat.of Ω) T
  let := restrictedSectionsScalarTower (CommRingCat.of k) (CommRingCat.of Ω) T
  apply Units.ext
  exact embeddingDecompositionTensorEquiv_apply (CommRingCat.of k) K (CommRingCat.of Ω) h
    (restrictedSections (CommRingCat.of k) (CommRingCat.of Ω) T) _ τ

theorem embeddingCommIso_hom_points (T : Over (Spec (CommRingCat.of Ω)))
    (x : T ⟶ (W_Ω).X) :
    splitTorus.pointsEquiv (K →ₐ[k] Ω) T
        (x ≫ (CommGroupScheme.groupHom (embeddingCommIso k K Ω h).hom).hom.hom) =
      embeddingPointsEquiv k K Ω h T x :=
  commDecompositionIso_hom_points (CommRingCat.of k) (CommRingCat.of Ω) K (K →ₐ[k] Ω)
    (embeddingDecomposition k K Ω h) T x

/-- Embedding coordinates are natural for every map of test schemes. -/
theorem embeddingPointsEquiv_naturality {T T' : Over (Spec (CommRingCat.of Ω))} (a : T' ⟶ T)
    (x : T ⟶ (W_Ω).X) :
    embeddingPointsEquiv k K Ω h T' (a ≫ x) =
      splitTorus.unitsRestrict (K →ₐ[k] Ω) a (embeddingPointsEquiv k K Ω h T x) :=
  decompositionPointsEquiv_naturality (CommRingCat.of k) (CommRingCat.of Ω) K (K →ₐ[k] Ω)
    (embeddingDecomposition k K Ω h) a x

/-- Changing the base structure by `Spec σ` twists the coefficient map by `σ`.
The intervening map of sections is the identity on the underlying scheme. -/
theorem embeddingCoefficientMap_descent (σ : Ω ≃ₐ[k] Ω)
    (T : Over (Spec (CommRingCat.of Ω))) (c : Ω) :
    embeddingCoefficientMap k Ω ((Over.map (galoisBaseMap k Ω σ)).obj T) c =
      ((algΓ (CommRingCat.of k)).map
        (descentTestIso (algebraBaseMap k Ω) (galoisBaseMap k Ω σ)
          (galoisBaseMap_over k Ω σ) T).inv).unop.hom
        (embeddingCoefficientMap k Ω T (σ c)) := by
  change (T.hom ≫ galoisBaseMap k Ω σ).appTop ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv c) =
    (𝟙 T.left : T.left ⟶ T.left).appTop
      (T.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv (σ c)))
  rw [Scheme.Hom.id_appTop, Scheme.Hom.comp_appTop]
  exact congrArg T.hom.appTop
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom σ.toRingHom)) c).symm

theorem embeddingCoefficientMap_descent_eq (σ : Ω ≃ₐ[k] Ω)
    (T : Over (Spec (CommRingCat.of Ω))) :
    embeddingCoefficientMap k Ω ((Over.map (galoisBaseMap k Ω σ)).obj T) =
      ((algΓ (CommRingCat.of k)).map
        (descentTestIso (algebraBaseMap k Ω) (galoisBaseMap k Ω σ)
          (galoisBaseMap_over k Ω σ) T).inv).unop.hom.comp
        ((embeddingCoefficientMap k Ω T).comp σ.toAlgHom) := by
  ext c
  exact embeddingCoefficientMap_descent k Ω σ T c

/-- The same original point, seen with its coefficient structure twisted by `σ`,
has its embedding coordinates permuted by postcomposition with `σ`. -/
theorem embeddingPointsEquiv_descentPoint (σ : Ω ≃ₐ[k] Ω)
    (T : Over (Spec (CommRingCat.of Ω))) (x : T ⟶ (W_Ω).X) (τ : K →ₐ[k] Ω) :
    embeddingPointsEquiv k K Ω h ((Over.map (galoisBaseMap k Ω σ)).obj T)
        (descentPoint (algebraBaseMap k Ω) (galoisBaseMap k Ω σ)
          (galoisBaseMap_over k Ω σ) (commGroupScheme (CommRingCat.of k) K).toGrp T x) τ =
      embeddingPointsEquiv k K Ω h T x (embeddingPermutation k K Ω σ τ) := by
  rw [embeddingPointsEquiv_apply, embeddingPointsEquiv_apply,
    baseChangePointsEquiv_descentPoint, pointsEquiv_naturality]
  apply Units.ext
  change tensorCoordinate _ τ (Algebra.TensorProduct.lTensor (S := K) K
    ((algΓ (CommRingCat.of k)).map
      (descentTestIso (algebraBaseMap k Ω) (galoisBaseMap k Ω σ)
        (galoisBaseMap_over k Ω σ) T).inv).unop.hom _) = _
  rw [embeddingCoefficientMap_descent_eq, tensorCoordinate_natural, tensorCoordinate_comp]
  change (𝟙 T.left : T.left ⟶ T.left).appTop.hom _ = _
  rw [Scheme.Hom.id_appTop]
  rfl

end Scheme

end Langlands.GroupScheme.WeilGm
