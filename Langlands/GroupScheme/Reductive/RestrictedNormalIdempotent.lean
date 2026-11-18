import Langlands.GroupScheme.ConjugationEquivariantAffine
import Langlands.GroupScheme.RestrictedAffinePointPresentation
import Langlands.GroupScheme.Reductive.AffineNormalIdempotentDecomposition
import Langlands.GroupScheme.Reductive.AlmostSimpleGeometricBaseChange
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.AffineIdempotentPoints

/-! # The ring idempotent for a restricted natural normal idempotent -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

section PointRestriction

variable {R : Type u} [CommRing R] {H : GroupScheme (Spec (CommRingCat.of R))}
  (ψ : H ⟶ H) (A : CommAlgCat.{u} (CommRingCat.of R))

/-- Identity after coefficient base change gives identity on the original
coefficient points. -/
theorem affinePoints_comp_eq_of_baseChange_eq_id
    (hψ : (baseChange (Spec.map (CommRingCat.ofHom (algebraMap R A)))).map ψ =
      𝟙 ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj H))
    (p : H.affinePoints A) : p ≫ ψ.hom.hom = p := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let U : Over (Spec (CommRingCat.of A)) := Over.mk (𝟙 _)
  let x : (Over.map b).obj U ⟶ H.X :=
    Over.homMk p.left (by
      change p.left ≫ H.X.hom = 𝟙 _ ≫ b
      simpa only [Category.id_comp, algSpec_obj_hom] using p.w)
  let y := (baseChangePointsEquiv b H U).symm x
  have hy : y ≫ ((baseChange b).map ψ).hom.hom = y := by
    rw [hψ, Grp.id_hom_hom, Category.comp_id]
  have hx := congrArg (baseChangePointsEquiv b H U) hy
  rw [baseChangePointsEquiv_comp, MulEquiv.apply_symm_apply] at hx
  apply Over.OverMorphism.ext
  exact congrArg (fun f => f.left) hx

/-- Triviality after coefficient base change gives triviality on the
original coefficient points. -/
theorem affinePoints_comp_eq_one_of_baseChange_eq_zero
    (hψ : (baseChange (Spec.map (CommRingCat.ofHom (algebraMap R A)))).map ψ = 0)
    (p : H.affinePoints A) : p ≫ ψ.hom.hom = 1 := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let U : Over (Spec (CommRingCat.of A)) := Over.mk (𝟙 _)
  let x : (Over.map b).obj U ⟶ H.X :=
    Over.homMk p.left (by
      change p.left ≫ H.X.hom = 𝟙 _ ≫ b
      simpa only [Category.id_comp, algSpec_obj_hom] using p.w)
  let y := (baseChangePointsEquiv b H U).symm x
  have hy : y ≫ ((baseChange b).map ψ).hom.hom = 1 := by
    rw [hψ]
    exact MonObj.comp_one _
  have hx := congrArg (baseChangePointsEquiv b H U) hy
  rw [baseChangePointsEquiv_comp, MulEquiv.apply_symm_apply, map_one] at hx
  apply Over.OverMorphism.ext
  have hleft := congrArg (fun f => f.left) hx
  change p.left ≫ ψ.hom.hom.left = (𝟙 _ ≫ b) ≫ η[H.X].left at hleft
  simpa only [Category.id_comp, Hom.one_def, Over.comp_left, Over.toUnit_left,
    algSpec_obj_hom] using hleft

end PointRestriction

namespace RestrictedAffinePoints

private theorem naturality_app {C : Type*} [Category C] (F : C ⥤ GrpCat.{u})
    (α : F ⟶ F) {X Y : C} (f : X ⟶ Y) (x : F.obj X) :
    F.map f (α.app X x) = α.app Y (F.map f x) :=
  (congrArg (fun g : F.obj X ⟶ F.obj Y => g.hom x) (α.naturality f)).symm

variable {R : Type u} [CommRing R] (T : CommAlgCat.{u} (CommRingCat.of R))
  (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffine G.X.left]
  (θ : Under.forget T ⋙ G.affinePointFunctor ⟶
    Under.forget T ⋙ G.affinePointFunctor)

/-- The actual ring idempotent associated with the original restricted
natural normal idempotent, retaining all affine coefficient changes. -/
def ringDecomposition (hG : IsReductive G) (hAS : IsFibrewiseAlmostSimple G)
    (hidem : θ ≫ θ = θ)
    (hn : ∀ (X : Under T)
      (g x : (Under.forget T ⋙ G.affinePointFunctor).obj X),
      θ.app X (g * x * g⁻¹) = g * θ.app X x * g⁻¹) :
    RingIdempotentDecomposition (endomorphism T G θ) :=
  (normalIdempotentDecomposition (hG.baseChange (Spec.algebraMap R T))
    (hAS.baseChange (Spec.algebraMap R T)) (endomorphism T G θ)
    (endomorphism_idempotent T G θ hidem)
    (endomorphism_conjugationEquivariant T G θ hn).range_isNormal).toRingDecomposition

/-- The original transformation is the identity on a coefficient algebra
where the constructed ring idempotent becomes one. -/
theorem app_eq_self_of_element_eq_one (hG : IsReductive G)
    (hAS : IsFibrewiseAlmostSimple G) (hidem : θ ≫ θ = θ)
    (hn : ∀ (X : Under T)
      (g x : (Under.forget T ⋙ G.affinePointFunctor).obj X),
      θ.app X (g * x * g⁻¹) = g * θ.app X x * g⁻¹)
    (X : Under T)
    (hX : X.hom.hom (ringDecomposition T G θ hG hAS hidem hn).element = 1)
    (x : G.affinePoints X.right) : θ.app X x = x := by
  obtain ⟨p, rfl⟩ := (originalPointsEquiv T G X).surjective x
  rw [← endomorphism_originalPoints]
  congr 1
  exact affinePoints_comp_eq_of_baseChange_eq_id (endomorphism T G θ)
    (underAlgebra T X)
    ((ringDecomposition T G θ hG hAS hidem hn).identity_eq X.right
      X.hom.hom.toRingHom hX) p

/-- The original transformation is trivial on a coefficient algebra where
the constructed ring idempotent becomes zero. -/
theorem app_eq_one_of_element_eq_zero (hG : IsReductive G)
    (hAS : IsFibrewiseAlmostSimple G) (hidem : θ ≫ θ = θ)
    (hn : ∀ (X : Under T)
      (g x : (Under.forget T ⋙ G.affinePointFunctor).obj X),
      θ.app X (g * x * g⁻¹) = g * θ.app X x * g⁻¹)
    (X : Under T)
    (hX : X.hom.hom (ringDecomposition T G θ hG hAS hidem hn).element = 0)
    (x : G.affinePoints X.right) : θ.app X x = 1 := by
  obtain ⟨p, rfl⟩ := (originalPointsEquiv T G X).surjective x
  rw [← endomorphism_originalPoints,
    affinePoints_comp_eq_one_of_baseChange_eq_zero (endomorphism T G θ)
      (underAlgebra T X)
      ((ringDecomposition T G θ hG hAS hidem hn).zero_eq X.right
        X.hom.hom.toRingHom hX) p, map_one]

/-- A quotient of an original coefficient algebra, with the original
composite structure map from `T`. -/
def quotientUnder (X : Under T) (I : Ideal X.right) : Under T :=
  Under.mk (X.hom ≫ CommAlgCat.ofHom (Ideal.Quotient.mkₐ R I))

/-- The quotient map is a morphism under `T`. -/
def quotientMap (X : Under T) (I : Ideal X.right) : X ⟶ quotientUnder T X I :=
  Under.homMk (CommAlgCat.ofHom (Ideal.Quotient.mkₐ R I)) rfl

/-- An actual idempotent of `T` with the original universal quotient-point formulas. -/
structure ProjectionData where
  element : T
  idempotent : IsIdempotentElem element
  formula : ∀ (X : Under T) (x : G.affinePoints X.right),
    G.affinePointMap (CommAlgCat.ofHom (Ideal.Quotient.mkₐ R
        (Ideal.span {1 - X.hom.hom element}))) (θ.app X x) =
      G.affinePointMap (CommAlgCat.ofHom (Ideal.Quotient.mkₐ R
        (Ideal.span {1 - X.hom.hom element}))) x ∧
    G.affinePointMap (CommAlgCat.ofHom (Ideal.Quotient.mkₐ R
        (Ideal.span {X.hom.hom element}))) (θ.app X x) = 1

/-- The original restricted normal idempotent has the exact factor projection
formulas on every original coefficient algebra. -/
def projectionData (hG : IsReductive G) (hAS : IsFibrewiseAlmostSimple G)
    (hidem : θ ≫ θ = θ)
    (hn : ∀ (X : Under T)
      (g x : (Under.forget T ⋙ G.affinePointFunctor).obj X),
      θ.app X (g * x * g⁻¹) = g * θ.app X x * g⁻¹) : ProjectionData T G θ where
  element := (ringDecomposition T G θ hG hAS hidem hn).element
  idempotent := (ringDecomposition T G θ hG hAS hidem hn).idempotent
  formula X x := by
    let e := (ringDecomposition T G θ hG hAS hidem hn).element
    constructor
    · let I : Ideal X.right := Ideal.span {1 - X.hom.hom e}
      let Y := quotientUnder T X I
      have he : Y.hom.hom e = 1 := IdempotentPoints.mk_fst_self _
      change G.affinePointMap (quotientMap T X I).right (θ.app X x) =
        G.affinePointMap (quotientMap T X I).right x
      exact (naturality_app (Under.forget T ⋙ G.affinePointFunctor) θ
        (quotientMap T X I) x).trans
          (app_eq_self_of_element_eq_one T G θ hG hAS hidem hn Y he _)
    · let I : Ideal X.right := Ideal.span {X.hom.hom e}
      let Y := quotientUnder T X I
      have he : Y.hom.hom e = 0 := IdempotentPoints.mk_snd_self _
      change G.affinePointMap (quotientMap T X I).right (θ.app X x) = 1
      exact (naturality_app (Under.forget T ⋙ G.affinePointFunctor) θ
        (quotientMap T X I) x).trans
          (app_eq_one_of_element_eq_zero T G θ hG hAS hidem hn Y he _)

end RestrictedAffinePoints
end Langlands.GroupScheme
