import Langlands.GroupScheme.Torus.LatticeGalois
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Langlands.GroupScheme.Cartier.Characters

/-! # Character restriction along test-scheme maps -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme
namespace characterLattice
variable {S : Scheme.{u}} (T : CommGroupScheme S)

/-- Relative homomorphisms to the pulled-back multiplicative group are actual characters. -/
abbrev relativeEquiv (Q : Over S) :
    Cartier.RelativeHom T (Gm S) Q ≃+ characterLattice (Cartier.testBaseChange Q T) :=
  Cartier.characterHomEquiv T Q

/-- Restriction of actual characters along a map between test schemes. -/
def restriction {Q Q' : Over S} (a : Q' ⟶ Q) :
    characterLattice (Cartier.testBaseChange Q T) →+
      characterLattice (Cartier.testBaseChange Q' T) :=
  ((Cartier.characterHomFunctor T).map a.op).hom

@[simp] theorem restriction_id (Q : Over S)
    (χ : characterLattice (Cartier.testBaseChange Q T)) : restriction T (𝟙 Q) χ = χ := by
  change relativeEquiv T Q (Cartier.restrict T (Gm S) (𝟙 Q) ((relativeEquiv T Q).symm χ)) = χ
  rw [Cartier.restrict_id, AddEquiv.apply_symm_apply]

@[simp] theorem restriction_comp {Q Q' Q'' : Over S} (a : Q'' ⟶ Q') (b : Q' ⟶ Q)
    (χ : characterLattice (Cartier.testBaseChange Q T)) :
    restriction T (a ≫ b) χ = restriction T a (restriction T b χ) := by
  change relativeEquiv T Q'' (Cartier.restrict T (Gm S) (a ≫ b) _) =
    relativeEquiv T Q'' (Cartier.restrict T (Gm S) a
      ((relativeEquiv T Q').symm (relativeEquiv T Q' _)))
  rw [AddEquiv.symm_apply_apply, Cartier.restrict_comp]
  rfl

/-- The multiplicative-group comparisons commute with successive pullback. -/
theorem gm_compIso {Q Q' : Over S} (a : Q' ⟶ Q) :
    (Cartier.baseChangeCompIso (Gm S) a).hom ≫
      (GroupScheme.baseChange a.left).map (Gm.baseChangeIso Q.hom).hom ≫
        (Gm.baseChangeIso a.left).hom = (Gm.baseChangeIso Q'.hom).hom :=
  Cartier.gmBaseChange_comp a

/-- The test-scheme comparison in the category of commutative group schemes. -/
def comparison {Q Q' : Over S} (a : Q' ⟶ Q) :
    Cartier.testBaseChange Q' T ≅
      (CommGroupScheme.baseChange a.left).obj (Cartier.testBaseChange Q T) :=
  CommGroupScheme.isoOfGroupIso (Cartier.baseChangeCompIso T a)

/-- Restriction is ordinary character pullback, followed by the canonical domain comparison. -/
theorem restriction_eq {Q Q' : Over S} (a : Q' ⟶ Q)
    (χ : characterLattice (Cartier.testBaseChange Q T)) :
    restriction T a χ = (comparison T a).hom ≫
      baseChange a.left (Cartier.testBaseChange Q T) χ := by
  have hg : (comparison (Gm S) a).hom ≫
      (CommGroupScheme.baseChange a.left).map (Gm.commBaseChangeIso Q.hom).hom ≫
        (Gm.commBaseChangeIso a.left).hom = (Gm.commBaseChangeIso Q'.hom).hom :=
    congrArg Additive.ofMul (gm_compIso a)
  change ((comparison T a).hom ≫
    (CommGroupScheme.baseChange a.left).map (χ ≫ (Gm.commBaseChangeIso Q.hom).inv) ≫
      (comparison (Gm S) a).inv) ≫
        (Gm.commBaseChangeIso Q'.hom).hom = _
  rw [Functor.map_comp]
  have hgm : (comparison (Gm S) a).inv ≫
      (Gm.commBaseChangeIso Q'.hom).hom =
      (CommGroupScheme.baseChange a.left).map (Gm.commBaseChangeIso Q.hom).hom ≫
        (Gm.commBaseChangeIso a.left).hom := by
    rw [← hg]
    simp only [Iso.inv_hom_id_assoc]
  simp only [Category.assoc]
  rw [hgm, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- Restriction between field-valued tests is bijective when the source torus is split. -/
theorem restriction_bijective {E M : Type u} [Field E] [Field M]
    {b : Spec (CommRingCat.of E) ⟶ S} {c : Spec (CommRingCat.of M) ⟶ S}
    (a : Over.mk c ⟶ Over.mk b)
    (hT : IsSplitTorus (Cartier.testBaseChange (Over.mk b) T).toGrp) :
    Function.Bijective (restriction T a) := by
  have h := (congr (comparison T a).symm).bijective.comp
    (hT.characterLattice_baseChange_bijective a.left (Cartier.testBaseChange (Over.mk b) T))
  change Function.Bijective (fun χ => (comparison T a).hom ≫
    baseChange a.left (Cartier.testBaseChange (Over.mk b) T) χ) at h
  have heq : (fun χ => (comparison T a).hom ≫
      baseChange a.left (Cartier.testBaseChange (Over.mk b) T) χ) = restriction T a :=
    funext fun χ => (restriction_eq T a χ).symm
  rw [heq] at h
  exact h

/-- For an endomorphism over the original base, the comparison is the descent comparison. -/
theorem comparison_endomorphism {B : Scheme.{u}} (b : B ⟶ S) (a : B ⟶ B)
    (ha : a ≫ b = b) :
    (Cartier.baseChangeCompIso T (Over.homMk a ha : Over.mk b ⟶ Over.mk b)).hom =
      (descentBaseChangeIso b a ha T.toGrp).inv := by
  apply (cancel_mono (descentBaseChangeIso b a ha T.toGrp).hom).1
  rw [Iso.inv_hom_id]
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change ((Cartier.baseChangeCompIso T (Over.homMk a ha : Over.mk b ⟶ Over.mk b)).hom.hom.hom.left ≫
      (descentBaseChangeIso b a ha T.toGrp).hom.hom.hom.left) ≫ pullback.fst T.X.hom b = _
    rw [Category.assoc, descentBaseChangeIso_hom_fst]
    change (Cartier.baseChangeCompIso T (Over.homMk a ha : Over.mk b ⟶ Over.mk b)).hom.hom.hom.left ≫
      pullback.fst (pullback.snd T.X.hom b) a ≫ pullback.fst T.X.hom b = _
    exact (congrArg (· ≫ pullback.fst T.X.hom b)
      (Cartier.baseChangeCompIso_hom_fst T
        (Over.homMk a ha : Over.mk b ⟶ Over.mk b))).trans
      ((Cartier.baseChangeProj_fst T (Over.homMk a ha : Over.mk b ⟶ Over.mk b)).trans
        (Category.id_comp _).symm)
  · exact (Over.w (((Cartier.baseChangeCompIso T
        (Over.homMk a ha : Over.mk b ⟶ Over.mk b)).hom ≫
          (descentBaseChangeIso b a ha T.toGrp).hom).hom.hom)).trans
        (Category.id_comp _).symm

/-- Character restriction along an endomorphism is the published character transport. -/
theorem restriction_endomorphism {B : Scheme.{u}} (b : B ⟶ S) (a : B ⟶ B)
    (ha : a ≫ b = b) (χ : characterLattice ((CommGroupScheme.baseChange b).obj T)) :
    restriction T (Over.homMk a ha : Over.mk b ⟶ Over.mk b) χ = transport b a ha T χ := by
  rw [restriction_eq]
  change Additive.ofMul ((Cartier.baseChangeCompIso T
    (Over.homMk a ha : Over.mk b ⟶ Over.mk b)).hom ≫
      (GroupScheme.baseChange a).map (CommGroupScheme.groupHom χ) ≫
        (Gm.baseChangeIso a).hom) = _
  rw [comparison_endomorphism]
  rfl

end characterLattice
end Langlands.GroupScheme
