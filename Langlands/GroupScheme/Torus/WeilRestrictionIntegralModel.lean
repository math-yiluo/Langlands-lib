import Langlands.GroupScheme.Torus.WeilRestrictionBaseChange
import Langlands.GroupScheme.Torus.WeilRestrictionGaloisPoints
import Langlands.GroupScheme.CorepresentedAffineComparison
import Langlands.GroupScheme.IntegralModel.SplitIntegralPoints

/-! # Integral models of Weil restrictions of the multiplicative group -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.WeilGm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

/-- Global functions on the identity test scheme recover its base algebra. -/
def selfSectionsAlgEquiv (A : CommRingCat.{u}) :
    ((algΓ A).obj (Over.mk (𝟙 (Spec A)))).unop ≃ₐ[A] A :=
  { (Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv with
    commutes' := by
      intro r
      change (Scheme.ΓSpecIso A).hom ((𝟙 (Spec A) : Spec A ⟶ Spec A).appTop ((Scheme.ΓSpecIso A).inv r)) = r
      simp }

section Sections

variable (A : CommRingCat.{u}) (B : Type u) [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]

/-- Removing the global-functions tensor factor on the identity test scheme. -/
def sectionTensorEquiv :
    B ⊗[A] ((algΓ A).obj (Over.mk (𝟙 (Spec A)))).unop ≃+* B :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl (R := A) (A₁ := B))
      (selfSectionsAlgEquiv A)).toRingEquiv.trans
    (Algebra.TensorProduct.rid A B B).toRingEquiv

omit [Module.Finite A B] [Module.Projective A B] in
@[simp] theorem sectionTensorEquiv_tmul (b : B)
    (r : ((algΓ A).obj (Over.mk (𝟙 (Spec A)))).unop) :
    sectionTensorEquiv A B (b ⊗ₜ r) = (Scheme.ΓSpecIso A).hom r • b := by
  simp [sectionTensorEquiv, selfSectionsAlgEquiv]
  rfl

/-- Sections of `Res_{B/A} G_m` over `Spec A` are the units of `B`. -/
def sectionUnitsEquiv : rationalPoints (groupScheme A B) ≃* Bˣ :=
  (pointsEquiv A B (Over.mk (𝟙 (Spec A)))).trans
    (Units.mapEquiv (sectionTensorEquiv A B).toMulEquiv)

end Sections

/-- The general section comparison agrees with the published field-point comparison. -/
theorem rationalUnitsEquiv_eq_sectionUnitsEquiv (k : Type u) [Field k]
    (B : Type u) [CommRing B] [Algebra k B] [Module.Finite k B]
    (x : rationalPoints (groupScheme (CommRingCat.of k) B)) :
    rationalUnitsEquiv k B x = sectionUnitsEquiv (CommRingCat.of k) B x := by
  let A := CommRingCat.of k
  let T := (algSpec A).obj (op (CommAlgCat.of k k))
  let y := GaloisPointComparison.rationalCoeffEquiv k (groupScheme A B) x
  let a := (Langlands.AlgebraicGeometry.PointTopology.ringTestSelfIso k).hom
  let c := (Corepresented.affineSectionsIso (R := A) (CommAlgCat.of k k)).hom.hom
  have c_eq (s) : c s = (Scheme.ΓSpecIso A).hom s :=
    DFunLike.congr_fun (Corepresented.affineSectionsIso_hom_ringHom
      (R := A) (CommAlgCat.of k k)) s
  have hy : y = a ≫ x := rfl
  have hc := Corepresented.map_affineSectionsIso_pointsEquiv
    (functor A B) (corepresentableBy A B) (CommAlgCat.of k k) y
  change Units.map (Algebra.TensorProduct.lTensor (S := B) B c).toMonoidHom
      (pointsEquiv A B T y) = affineUnitsEquiv A B (CommAlgCat.of k k) y at hc
  apply Units.ext
  change Algebra.TensorProduct.rid k B B (affineUnitsEquiv A B (CommAlgCat.of k k) y) =
    sectionTensorEquiv A B (pointsEquiv A B (Over.mk (𝟙 (Spec A))) x)
  rw [← hc, hy, pointsEquiv_naturality]
  suffices h : ∀ z : B ⊗[A] ((algΓ A).obj (Over.mk (𝟙 (Spec A)))).unop,
      Algebra.TensorProduct.rid k B B
          (Algebra.TensorProduct.lTensor (S := B) B c
            (Algebra.TensorProduct.lTensor (S := B) B ((algΓ A).map a).unop.hom z)) =
        sectionTensorEquiv A B z by
    exact h _
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul b r =>
      simp only [Algebra.TensorProduct.lTensor, Algebra.TensorProduct.map_tmul,
        sectionTensorEquiv_tmul]
      rw [c_eq]
      change (Scheme.ΓSpecIso A).hom
        ((𝟙 (Spec A) : Spec A ⟶ Spec A).appTop r) • b = _
      simp
  | add z z' hz hz' => simp only [map_add, hz, hz']

section Model

variable (R K : Type u) [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  (B₀ : Type u) [CommRing B₀] [Algebra R B₀]
  [Module.Finite R B₀] [Module.Projective R B₀]
  (B : Type u) [CommRing B] [Algebra K B] [Module.Finite K B]
  (e : K ⊗[R] B₀ ≃ₐ[K] B)

/-- The integral Weil restriction with its supplied generic-fibre algebra identification. -/
def integralModel : IntegralModel R K (groupScheme (CommRingCat.of K) B) := by
  letI := smooth (CommRingCat.of R) B₀
  exact
    { group := groupScheme (CommRingCat.of R) B₀
      affine := by
        change IsAffineHom (Spec.map _)
        infer_instance
      genericIso := algebraBaseChangeIso (CommRingCat.of R) (CommRingCat.of K) B₀ ≪≫
        congrIso e }

/-- This integral model is smooth. -/
theorem integralModel_isSmooth : (integralModel R K B₀ B e).IsSmooth :=
  smooth (CommRingCat.of R) B₀

/-- Restricting a section sends its unit to `e (1 ⊗ u)` on the generic fibre. -/
theorem rationalUnitsEquiv_integralPointMap
    (x : (integralModel R K B₀ B e).integralSections) :
    (rationalUnitsEquiv K B ((integralModel R K B₀ B e).integralPointMap x) : B) =
      e (1 ⊗ₜ (sectionUnitsEquiv (CommRingCat.of R) B₀ x : B₀)) := by
  change rationalPoints (groupScheme (CommRingCat.of R) B₀) at x
  let A := CommRingCat.of R
  let A' := CommRingCat.of K
  let T := Over.mk (𝟙 (Spec A'))
  let a : (Over.map (baseMap A A')).obj T ⟶ Over.mk (𝟙 (Spec A)) :=
    Over.homMk (baseMap A A') (by simp [T])
  let : Algebra A' (restrictedSections A A' T) := restrictedSectionsAlgebra A A' T
  let : IsScalarTower A A' (restrictedSections A A' T) :=
    restrictedSectionsScalarTower A A' T
  rw [rationalUnitsEquiv_eq_sectionUnitsEquiv]
  change (sectionUnitsEquiv A' B
      (baseChangeSectionHom (baseMap A A') (groupScheme A B₀) x ≫
        (integralModel R K B₀ B e).genericIso.hom.hom.hom) : B) = _
  dsimp only [integralModel, Iso.trans_hom]
  rw [Grp.comp_hom_hom, ← Category.assoc]
  change sectionTensorEquiv A' B (pointsEquiv A' B T _) =
    e (1 ⊗ₜ sectionTensorEquiv A B₀ (pointsEquiv A B₀ (Over.mk (𝟙 (Spec A))) x))
  rw [congrIso_hom_points, algebraBaseChangeIso_hom_points A A' B₀ T,
    baseChangePointsEquiv_baseChangeSectionHom, pointsEquiv_naturality]
  suffices h : ∀ z : B₀ ⊗[A] ((algΓ A).obj (Over.mk (𝟙 (Spec A)))).unop,
      sectionTensorEquiv A' B
        (Algebra.TensorProduct.congr e (AlgEquiv.refl (R := A')
          (A₁ := ((algΓ A').obj T).unop))
          (baseChangeTensorEquiv A A' B₀ (restrictedSections A A' T)
            (Algebra.TensorProduct.lTensor (S := B₀) B₀ ((algΓ A).map a).unop.hom z))) =
        e (1 ⊗ₜ sectionTensorEquiv A B₀ z) by
    exact h _
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul b r =>
      simp only [Algebra.TensorProduct.lTensor, Algebra.TensorProduct.map_tmul,
        baseChangeTensorEquiv_tmul, Algebra.TensorProduct.congr_apply,
        sectionTensorEquiv_tmul]
      have hnat := ConcreteCategory.congr_hom
        (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R K))) r
      change (Scheme.ΓSpecIso A').hom ((baseMap A A').appTop r) =
        algebraMap R K ((Scheme.ΓSpecIso A).hom r) at hnat
      change (Scheme.ΓSpecIso A').hom ((baseMap A A').appTop r) • e (1 ⊗ₜ b) = _
      rw [hnat, ← map_smul e]
      congr 1
      rw [TensorProduct.tmul_smul, IsScalarTower.algebraMap_smul]
  | add z z' hz hz' =>
      simp only [map_add, TensorProduct.tmul_add, hz, hz']

/-- Integral points are exactly the images of units of the integral algebra. -/
theorem mem_integralModel_integralPoints_iff
    (y : rationalPoints (groupScheme (CommRingCat.of K) B)) :
    y ∈ (integralModel R K B₀ B e).integralPoints ↔
      ∃ u : B₀ˣ, (rationalUnitsEquiv K B y : B) = e (1 ⊗ₜ (u : B₀)) := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨sectionUnitsEquiv (CommRingCat.of R) B₀ x,
      rationalUnitsEquiv_integralPointMap R K B₀ B e x⟩
  · rintro ⟨u, hu⟩
    refine ⟨(sectionUnitsEquiv (CommRingCat.of R) B₀).symm u, ?_⟩
    apply (rationalUnitsEquiv K B).injective
    apply Units.ext
    rw [rationalUnitsEquiv_integralPointMap, MulEquiv.apply_symm_apply]
    exact hu.symm

end Model

end Langlands.GroupScheme.WeilGm
