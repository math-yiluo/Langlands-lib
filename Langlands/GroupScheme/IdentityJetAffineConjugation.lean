import Langlands.GroupScheme.IdentityJetAmbientPoints

/-! # Actual conjugation at the affine identity-jet point -/

noncomputable section
universe u
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IdentityJet

open AffineCoordinates Corepresented

private def affineCoordinatePoint {R : CommRingCat.{u}} {B : CommAlgCat R}
    {X : Scheme.{u}} (b : X ⟶ Spec R) (j : X ⟶ Spec (CommRingCat.of B))
    (hj : j ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) = b)
    (V : X.Opens) (hV : IsAffineOpen V) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b V
    (algSpec R).obj (op (CommAlgCat.of R Γ(X, V))) ⟶ (algSpec R).obj (op B) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom b V
  refine Over.homMk (hV.fromSpec ≫ j) ?_
  change (hV.fromSpec ≫ j) ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) = _
  rw [Category.assoc, hj]
  exact (spec_coordinateMap b V hV).symm

variable {R : CommRingCat.{u}} {S : Scheme.{u}}
  (G : GroupScheme (Spec R)) [IsAffine G.X.left] (b : S ⟶ Spec R)
  {H : GroupScheme S} [IsAffineHom H.X.hom]
  (h : H ⟶ (GroupScheme.baseChange b).obj G)
  (g : Over.mk (𝟙 S) ⟶ ((GroupScheme.baseChange b).obj G).X)

/-- The actual conjugating section in the fixed ambient coordinates. -/
def conjugatorProjection : S ⟶ Spec (CommRingCat.of (algebra G)) :=
  g.left ≫ Limits.pullback.fst G.X.hom b ≫ (groupSchemeIso G).inv.hom.hom.left

private theorem conjugatorProjection_over :
    conjugatorProjection G b g ≫ Spec.map (CommRingCat.ofHom (algebraMap R (algebra G))) = b := by
  change (g.left ≫ Limits.pullback.fst G.X.hom b ≫
    (groupSchemeIso G).inv.hom.hom.left) ≫
      (groupScheme (functor G) (corepresentation G)).X.hom = _
  rw [Category.assoc, Category.assoc, Over.w]
  rw [Limits.pullback.condition, ← Category.assoc]
  have hg : g.left ≫ Limits.pullback.snd G.X.hom b = 𝟙 S := Over.w g
  rw [hg]
  exact Category.id_comp b

/-- The actual conjugating section over an affine open of its parameter scheme. -/
def parameterAffinePoint (U : S.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    (algSpec R).obj (op (CommAlgCat.of R Γ(S, U))) ⟶
      (groupScheme (functor G) (corepresentation G)).X :=
  affineCoordinatePoint b (conjugatorProjection G b g)
    (conjugatorProjection_over G b g) U U.2

/-- The actual conjugator pulled back to the canonical affine jet chart. -/
def jetConjugatorPoint (n : ℕ) (U : S.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (projection H n ≫ b)
      (projection H n ⁻¹ᵁ U)
    (algSpec R).obj (op (CommAlgCat.of R Γ(scheme H n, projection H n ⁻¹ᵁ U))) ⟶
      (groupScheme (functor G) (corepresentation G)).X :=
  affineCoordinatePoint (projection H n ≫ b)
    (projection H n ≫ conjugatorProjection G b g)
    (by rw [Category.assoc, conjugatorProjection_over])
    (projection H n ⁻¹ᵁ U) (isAffineOpen_jetPreimage H n U)

/-- Pulling the parameter point to the jet chart is the actual projection's
section-ring map, with no unspecified coefficient map. -/
theorem jetConjugatorPoint_eq_parameterPullback (n : ℕ) (U : S.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (projection H n ≫ b)
      (projection H n ⁻¹ᵁ U)
    ∀ (φ : CommAlgCat.of R Γ(S, U) ⟶
      CommAlgCat.of R Γ(scheme H n, projection H n ⁻¹ᵁ U)),
      φ.hom.toRingHom = ((projection H n).app U).hom →
      jetConjugatorPoint G b (H := H) g n U =
        (algSpec R).map φ.op ≫ parameterAffinePoint G b g U := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom b U
  let := Scheme.TwoAffineOpenCover.algebraOfHom (projection H n ≫ b)
    (projection H n ⁻¹ᵁ U)
  intro φ hφ
  apply Over.OverMorphism.ext
  change (isAffineOpen_jetPreimage H n U).fromSpec ≫ projection H n ≫
      conjugatorProjection G b g =
    Spec.map (CommRingCat.ofHom φ.hom.toRingHom) ≫ U.2.fromSpec ≫ conjugatorProjection G b g
  rw [hφ]
  have hc : Spec.map ((projection H n).app U) ≫ U.2.fromSpec =
      (isAffineOpen_jetPreimage H n U).fromSpec ≫ projection H n := by
    rw [Scheme.Hom.app_eq_appLE]
    exact IsAffineOpen.SpecMap_appLE_fromSpec (projection H n) U.2
      (isAffineOpen_jetPreimage H n U) le_rfl
  rw [← Category.assoc, ← hc, Category.assoc]
  rfl

omit [IsAffineHom H.X.hom] in
private theorem point_inner {T : Over S}
    (x : T ⟶ H.X) :
    baseChangePointsEquiv b G T
        (x ≫ (h ≫ (((GroupScheme.baseChange b).obj G).innerIso g).hom).hom.hom) ≫
          (groupSchemeIso G).inv.hom.hom =
      (baseChangePointsEquiv b G T (((GroupScheme.baseChange b).obj G).constantPoint g T) ≫
        (groupSchemeIso G).inv.hom.hom) *
      (baseChangePointsEquiv b G T (x ≫ h.hom.hom) ≫ (groupSchemeIso G).inv.hom.hom) *
      (baseChangePointsEquiv b G T (((GroupScheme.baseChange b).obj G).constantPoint g T) ≫
        (groupSchemeIso G).inv.hom.hom)⁻¹ := by
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom]
  simp only [map_mul, map_inv, MonObj.mul_comp, GrpObj.inv_comp]

/-- The actual conjugate jet chart is conjugation of the actual original jet point. -/
theorem affineJetPoint_inner (n : ℕ) (U : S.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (projection H n ≫ b)
      (projection H n ⁻¹ᵁ U)
    affineJetPoint H (functor G) (corepresentation G) b
        (ambientProjection G b (h ≫ (((GroupScheme.baseChange b).obj G).innerIso g).hom))
        (ambientProjection_over G b _) n U =
      jetConjugatorPoint G b (H := H) g n U *
        affineJetPoint H (functor G) (corepresentation G) b (ambientProjection G b h)
          (ambientProjection_over G b h) n U *
        (jetConjugatorPoint G b (H := H) g n U)⁻¹ := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom (projection H n ≫ b)
    (projection H n ⁻¹ᵁ U)
  let V := projection H n ⁻¹ᵁ U
  let Z := CommAlgCat.of R Γ(scheme H n, V)
  let t : Spec (CommRingCat.of Z) ⟶ S :=
    (isAffineOpen_jetPreimage H n U).fromSpec ≫ projection H n
  let T : Over S := Over.mk t
  let x : T ⟶ H.X := Over.homMk
    ((isAffineOpen_jetPreimage H n U).fromSpec ≫ inclusion H n) (by
      change ((isAffineOpen_jetPreimage H n U).fromSpec ≫ inclusion H n) ≫ H.X.hom = t
      exact Category.assoc _ _ _)
  have hb : Spec.map (CommRingCat.ofHom (algebraMap R Z)) = t ≫ b :=
    spec_coordinateMap (projection H n ≫ b) V (isAffineOpen_jetPreimage H n U)
  let a : (algSpec R).obj (op Z) ⟶ (Over.map b).obj T :=
    Over.homMk (𝟙 _) ((Category.id_comp _).trans hb.symm)
  have hp (k : H ⟶ (GroupScheme.baseChange b).obj G) :
      affineJetPoint H (functor G) (corepresentation G) b (ambientProjection G b k)
        (ambientProjection_over G b k) n U =
      a ≫ baseChangePointsEquiv b G T (x ≫ k.hom.hom) ≫ (groupSchemeIso G).inv.hom.hom := by
    apply Over.OverMorphism.ext
    simp only [affineJetPoint_left, Over.comp_left, baseChangePointsEquiv_left,
      a, Over.homMk_left, x, ambientProjection, Category.assoc]
    exact (Category.id_comp _).symm
  have hg : jetConjugatorPoint G b (H := H) g n U =
      a ≫ baseChangePointsEquiv b G T (((GroupScheme.baseChange b).obj G).constantPoint g T) ≫
        (groupSchemeIso G).inv.hom.hom := by
    apply Over.OverMorphism.ext
    simp only [jetConjugatorPoint, affineCoordinatePoint, Over.homMk_left, Over.comp_left,
      baseChangePointsEquiv_left, a, GroupScheme.constantPoint,
      conjugatorProjection, T, Over.mk_hom, t, Category.assoc]
    exact (Category.id_comp _).symm
  rw [hp, hp, hg]
  simpa only [MonObj.comp_mul, GrpObj.comp_inv, Category.assoc] using
    congrArg (fun y => a ≫ y) (point_inner G b h g x)

end Langlands.GroupScheme.IdentityJet
