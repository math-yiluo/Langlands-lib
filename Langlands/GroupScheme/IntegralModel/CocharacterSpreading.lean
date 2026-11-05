import Langlands.GroupScheme.IntegralModel.Multiplicative
import Langlands.GroupScheme.Dynamic.BaseChange
import Langlands.GroupScheme.Descent.Data
import Langlands.GroupScheme.IntegralModel.ArithmeticHomSpreading

/-! # Canonical multiplicative comparisons for arithmetic cocharacter descent -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

private theorem gm_comparison {S T U : Scheme.{u}}
    (b : T ⟶ S) (a : U ⟶ T) (c : U ⟶ S) (h : a ≫ b = c) :
    (baseChange a).map (Gm.baseChangeIso b).hom ≫ (Gm.baseChangeIso a).hom =
      (Descent.pullbackComparison b a c h (Gm S).toGrp).hom ≫
        (Gm.baseChangeIso c).hom := by
  apply hom_ext_points
  intro V x
  apply (Gm.pointsEquiv U V).injective
  simp only [Grp.comp_hom_hom, ← Category.assoc]
  rw [Gm.pointsEquiv_baseChangeIso_hom, Gm.baseChangeUnitsEquiv_apply,
    baseChangePointsEquiv_comp, Gm.pointsEquiv_baseChangeIso_hom,
    Gm.baseChangeUnitsEquiv_apply, Gm.pointsEquiv_baseChangeIso_hom,
    Gm.baseChangeUnitsEquiv_apply]
  apply Units.ext
  simp only [Gm.pointsEquiv_val, baseChangePointsEquiv_left, Over.comp_left, Category.assoc]
  exact congrArg (fun k => (x.left ≫ k).appTop
    ((Scheme.ΓSpecIso Gm.laurentRing).inv (LaurentPolynomial.T 1)))
    (Descent.pullbackComparison_hom_fst_assoc b a c h (Gm S).toGrp
      (pullback.fst Gm.overSpecZ.hom (Gm.toSpecZ S))).symm

variable {R A K : Type u} [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
  [Field K] [Algebra R K] [IsFractionRing R K] [Algebra A K] [IsFractionRing A K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G)
  (b : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))
  (hb : Spec.algebraMap A K ≫ b = Spec.algebraMap R K)
  {χ : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ G}

/-- Turn a descended homomorphism with multiplicative source into an actual cocharacter. -/
def cocharacterOfHom
    (f : ((multiplicative R K).baseChangeModel b hb).Hom (M.baseChangeModel b hb) χ) :
    (Gm (Spec (CommRingCat.of A))).toGrp ⟶ (M.baseChangeModel b hb).group :=
  (Gm.baseChangeIso b).inv ≫ f.hom

/-- The cocharacter recovers the supplied generic map through the prescribed model isomorphism. -/
theorem cocharacterOfHom_generic
    (f : ((multiplicative R K).baseChangeModel b hb).Hom (M.baseChangeModel b hb) χ) :
    Dynamic.baseChangeCocharacter (Spec.algebraMap A K) (cocharacterOfHom M b hb f) ≫
      (M.baseChangeModel b hb).genericIso.hom = χ := by
  have hsrc : ((multiplicative R K).baseChangeModel b hb).genericIso.hom =
      (baseChange (Spec.algebraMap A K)).map (Gm.baseChangeIso b).hom ≫
        (Gm.baseChangeIso (Spec.algebraMap A K)).hom := by
    exact (gm_comparison b (Spec.algebraMap A K) (Spec.algebraMap R K) hb).symm
  change (Gm.baseChangeIso (Spec.algebraMap A K)).inv ≫
      (baseChange (Spec.algebraMap A K)).map ((Gm.baseChangeIso b).inv ≫ f.hom) ≫
        (M.baseChangeModel b hb).genericIso.hom = χ
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [f.generic_comm, hsrc]
  simp only [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
  rw [(baseChange (Spec.algebraMap A K)).map_id]
  simp only [Category.comp_id, Iso.inv_hom_id, Category.id_comp]

end Langlands.GroupScheme.IntegralModel

namespace Langlands.GroupScheme.IntegralModel.ArithmeticSpreading

open Langlands.Global
open scoped NumberField

variable (F : Type u) [Field F] [NumberField F]

/-- A cocharacter on the canonical finite enlargement of a prescribed model,
with exact recovery through its actual generic identification. -/
structure EnlargedCocharacterData (S : Finset (FinitePlace F))
    {G : GroupScheme (Spec (CommRingCat.of F))}
    (M : IntegralModel ((S : Set (FinitePlace F)).integer F) F G)
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) where
  places : Finset (FinitePlace F)
  contains : S ⊆ places
  cocharacter : (Gm (Spec (CommRingCat.of
    ((places : Set (FinitePlace F)).integer F)))).toGrp ⟶
      (enlargeModel F M contains).group
  generic_comm :
    Dynamic.baseChangeCocharacter
        (Spec.algebraMap ((places : Set (FinitePlace F)).integer F) F) cocharacter ≫
      (enlargeModel F M contains).genericIso.hom = χ

/-- Descend the supplied generic cocharacter to a finite canonical enlargement
of the supplied actual arithmetic model. -/
def enlargedCocharacterData (S : Finset (FinitePlace F))
    {G : GroupScheme (Spec (CommRingCat.of F))}
    (M : IntegralModel ((S : Set (FinitePlace F)).integer F) F G)
    [LocallyOfFinitePresentation M.group.X.hom]
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    EnlargedCocharacterData F S M χ :=
  let D := enlargedHomData F S
    (multiplicative ((S : Set (FinitePlace F)).integer F) F) M χ
  { places := D.places
    contains := D.contains
    cocharacter := cocharacterOfHom M
      (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap F D.contains)))
      (integerInclusion_generic F D.contains) D.hom
    generic_comm := cocharacterOfHom_generic M
      (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap F D.contains)))
      (integerInclusion_generic F D.contains) D.hom }

end Langlands.GroupScheme.IntegralModel.ArithmeticSpreading
