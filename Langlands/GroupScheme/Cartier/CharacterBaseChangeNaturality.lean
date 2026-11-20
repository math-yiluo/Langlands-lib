import Langlands.GroupScheme.Cartier.BaseChange

/-! # Evaluation and precomposition for Cartier characters under base change -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace Langlands.GroupScheme.Cartier

variable {S S' : Scheme.{u}} (b : S' ⟶ S) (T : Over S')

private theorem testBaseChangeAlongIso_inv_naturality {G' G : CommGroupScheme S} (f : G' ⟶ G) :
    (testBaseChangeAlongIso G' b T).inv ≫
        (CommGroupScheme.baseChange ((Over.map b).obj T).hom).map f =
      (CommGroupScheme.baseChange T.hom).map ((CommGroupScheme.baseChange b).map f) ≫
        (testBaseChangeAlongIso G b T).inv :=
  congrArg Additive.ofMul
    (((Functor.mapGrpNatIso (Over.pullbackComp T.hom b)) ≪≫ Functor.mapGrpCompIso).inv.naturality
      f.toMul).symm

/-- The base-change isomorphism of relative characters respects precomposition. -/
theorem charactersBaseChangeIso_precompose {G' G : CommGroupScheme S} (f : G' ⟶ G)
    (χ : RelativeHom G (Gm S) ((Over.map b).obj T)) :
    (charactersBaseChangeIso G' b).hom.app (.op T)
        (precompose (Gm S) f ((Over.map b).obj T) χ) =
      precompose (Gm S') ((CommGroupScheme.baseChange b).map f) T
        ((charactersBaseChangeIso G b).hom.app (.op T) χ) := by
  let e := (testBaseChangeAlongIso (Gm S) b T).hom
  let m := (CommGroupScheme.baseChange T.hom).map (Gm.commBaseChangeIso b).hom
  change ((testBaseChangeAlongIso G' b T).inv ≫
    ((CommGroupScheme.baseChange ((Over.map b).obj T).hom).map f ≫ χ) ≫ e) ≫ m =
    (CommGroupScheme.baseChange T.hom).map ((CommGroupScheme.baseChange b).map f) ≫
      (((testBaseChangeAlongIso G b T).inv ≫ χ ≫ e) ≫ m)
  simpa only [Category.assoc] using
    congrArg (fun k => k ≫ χ ≫ e ≫ m) (testBaseChangeAlongIso_inv_naturality b T f)

private theorem sectionPointsEquiv_compAlongInv (G : CommGroupScheme S)
    (x : Over.mk (𝟙 T.left) ⟶ (testBaseChange T ((CommGroupScheme.baseChange b).obj G)).X) :
    sectionPointsEquiv G ((Over.map b).obj T)
        (x ≫ (testBaseChangeAlongIso G b T).inv.toMul.hom.hom) =
      GroupScheme.baseChangePointsEquiv b G.toGrp T
        (sectionPointsEquiv ((CommGroupScheme.baseChange b).obj G) T x) := by
  apply Over.OverMorphism.ext
  simp only [sectionPointsEquiv_left, Over.comp_left]
  exact congrArg (x.left ≫ ·) (testBaseChangeAlongIso_inv_fst G b T)

/-- Evaluating a transported relative homomorphism is compatible with the pullback
point equivalences on source and target. -/
theorem evaluation_relativeHomBaseChangeEquiv {G H : CommGroupScheme S}
    (χ : RelativeHom G H ((Over.map b).obj T))
    (x : T ⟶ ((CommGroupScheme.baseChange b).obj G).X) :
    GroupScheme.baseChangePointsEquiv b H.toGrp T
        (evaluation (relativeHomBaseChangeEquiv G H b T χ) x) =
      evaluation χ (GroupScheme.baseChangePointsEquiv b G.toGrp T x) := by
  let x₀ := (sectionPointsEquiv ((CommGroupScheme.baseChange b).obj G) T).symm x
  have hx : (sectionPointsEquiv G ((Over.map b).obj T)).symm
      (GroupScheme.baseChangePointsEquiv b G.toGrp T x) =
        x₀ ≫ (testBaseChangeAlongIso G b T).inv.toMul.hom.hom := by
    apply (sectionPointsEquiv G ((Over.map b).obj T)).injective
    rw [MulEquiv.apply_symm_apply, sectionPointsEquiv_compAlongInv]
    exact congrArg (GroupScheme.baseChangePointsEquiv b G.toGrp T)
      ((sectionPointsEquiv ((CommGroupScheme.baseChange b).obj G) T).apply_symm_apply x).symm
  rw [evaluation_def, evaluation_def, ← sectionPointsEquiv_compAlongInv, hx]
  congr 1
  change (x₀ ≫
      (((testBaseChangeAlongIso G b T).inv ≫ χ ≫ (testBaseChangeAlongIso H b T).hom).toMul.hom.hom)) ≫
      (testBaseChangeAlongIso H b T).inv.toMul.hom.hom =
    (x₀ ≫ (testBaseChangeAlongIso G b T).inv.toMul.hom.hom) ≫ χ.toMul.hom.hom
  have hH := congrArg (fun f => f.toMul.hom.hom) (testBaseChangeAlongIso H b T).hom_inv_id
  change (testBaseChangeAlongIso H b T).hom.toMul.hom.hom ≫
    (testBaseChangeAlongIso H b T).inv.toMul.hom.hom = 𝟙 _ at hH
  change (x₀ ≫ (testBaseChangeAlongIso G b T).inv.toMul.hom.hom ≫ χ.toMul.hom.hom ≫
      (testBaseChangeAlongIso H b T).hom.toMul.hom.hom) ≫
    (testBaseChangeAlongIso H b T).inv.toMul.hom.hom = _
  simp only [Category.assoc, hH, Category.comp_id]

/-- The relative character evaluates to the same global unit after base change. -/
theorem charactersBaseChangeIso_evaluation (G : CommGroupScheme S)
    (χ : RelativeHom G (Gm S) ((Over.map b).obj T))
    (x : T ⟶ ((CommGroupScheme.baseChange b).obj G).X) :
    Gm.pointsEquiv S' T (evaluation ((charactersBaseChangeIso G b).hom.app (.op T) χ) x) =
      Gm.pointsEquiv S ((Over.map b).obj T)
        (evaluation χ (GroupScheme.baseChangePointsEquiv b G.toGrp T x)) := by
  erw [charactersBaseChangeIso_hom_app_apply G b T]
  rw [evaluation_postcompose]
  change Gm.pointsEquiv S' T
    (evaluation (relativeHomBaseChangeEquiv G (Gm S) b T χ) x ≫ (Gm.baseChangeIso b).hom.hom.hom) = _
  exact (Gm.pointsEquiv_baseChangeIso_hom b T _).trans
    (congrArg (Gm.pointsEquiv S ((Over.map b).obj T))
      (evaluation_relativeHomBaseChangeEquiv b T χ x))

end Langlands.GroupScheme.Cartier
