import Langlands.GroupScheme.Absolute.CocharacterDescent
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace Langlands.GroupScheme.GaloisCocharacterDescent

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- Restriction of the extension-field Laurent test to the base-field Laurent test. -/
def extendTest :
    (Over.map (algebraBaseMap k K)).obj (Gm.relativeLaurent (CommRingCat.of K)) ⟶
      Gm.relativeLaurent (CommRingCat.of k) :=
  (laurentBaseIso k K).inv ≫
    (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom (extendAlg k K)).op ≫
      (laurentAffineIso k).hom

theorem extendTest_left :
    (extendTest k K).left =
      Spec.map (CommRingCat.ofHom (LaurentGaloisDescent.extend k K)) := by
  simp only [extendTest, Over.comp_left, laurentBaseIso, laurentAffineIso,
    Over.isoMk_inv_left, Over.isoMk_hom_left, Iso.refl_inv, Iso.refl_hom]
  rfl

/-- Extending coefficients preserves the universal Laurent unit. -/
theorem extendTest_universalUnit :
    Gm.pointsEquiv (Spec (CommRingCat.of k)) _ (extendTest k K ≫ Gm.laurentPoint k) =
      Gm.pointsEquiv (Spec (CommRingCat.of K)) _ (Gm.laurentPoint K) := by
  rw [Gm.pointsEquiv_naturality]
  apply Units.ext
  apply (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial K))).commRingCatIsoToRingEquiv.injective
  change ((extendTest k K).left.appTop ≫ (Scheme.ΓSpecIso _).hom) _ =
    (Scheme.ΓSpecIso _).hom _
  rw [extendTest_left, Scheme.ΓSpecIso_naturality]
  change LaurentGaloisDescent.extend k K
    (Gm.affinePointsEquiv (Gm.laurentStructure (CommRingCat.of k))
      (Gm.laurentPoint k) : LaurentPolynomial k) =
    (Gm.affinePointsEquiv (Gm.laurentStructure (CommRingCat.of K))
      (Gm.laurentPoint K) : LaurentPolynomial K)
  have hk : (Gm.affinePointsEquiv (Gm.laurentStructure (CommRingCat.of k))
      (Gm.laurentPoint k) : LaurentPolynomial k) = LaurentPolynomial.T 1 :=
    Gm.affinePointsEquiv_universalPoint (CommRingCat.of k)
  have hK : (Gm.affinePointsEquiv (Gm.laurentStructure (CommRingCat.of K))
      (Gm.laurentPoint K) : LaurentPolynomial K) = LaurentPolynomial.T 1 :=
    Gm.affinePointsEquiv_universalPoint (CommRingCat.of K)
  rw [hk, hK]
  exact AddMonoidAlgebra.mapRingHom_single (algebraMap k K) 1 1 |>.trans
    (by rw [map_one]; rfl)

/-- Base change of Gm identifies the same universal point after coefficient extension. -/
theorem baseChangeIso_universalProjection :
    baseChangePointsEquiv (algebraBaseMap k K) (Gm (Spec (CommRingCat.of k))).toGrp
      (Gm.relativeLaurent (CommRingCat.of K))
      (Gm.laurentPoint K ≫ (Gm.baseChangeIso (algebraBaseMap k K)).inv.hom.hom) =
        extendTest k K ≫ Gm.laurentPoint k := by
  apply (Gm.pointsEquiv (Spec (CommRingCat.of k)) _).injective
  change Gm.baseChangeUnitsEquiv (algebraBaseMap k K) _
    (Gm.laurentPoint K ≫ (Gm.baseChangeIso (algebraBaseMap k K)).inv.hom.hom) = _
  rw [Gm.baseChangeUnitsEquiv_baseChangeIso_inv]
  exact (extendTest_universalUnit k K).symm

variable (G : GroupScheme (Spec (CommRingCat.of k)))

/-- Base change of an underlying scheme morphism from Gm. -/
def baseChangedMorphism (f : (Gm (Spec (CommRingCat.of k))).X ⟶ G.X) :
    (Gm (Spec (CommRingCat.of K))).X ⟶
      ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X :=
  (Gm.baseChangeIso (algebraBaseMap k K)).inv.hom.hom ≫
    (Over.pullback (algebraBaseMap k K)).map f

/-- The point adjunction commutes with any underlying morphism of group schemes. -/
theorem baseChangePointsEquiv_morphism
    (H : GroupScheme (Spec (CommRingCat.of k))) (f : H.X ⟶ G.X)
    (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ ((GroupScheme.baseChange (algebraBaseMap k K)).obj H).X) :
    baseChangePointsEquiv (algebraBaseMap k K) G T
      (x ≫ (Over.pullback (algebraBaseMap k K)).map f) =
      baseChangePointsEquiv (algebraBaseMap k K) H T x ≫ f := by
  apply Over.OverMorphism.ext
  change (x ≫ (Over.pullback (algebraBaseMap k K)).map f).left ≫
      pullback.fst G.X.hom (algebraBaseMap k K) =
    (x.left ≫ pullback.fst H.X.hom (algebraBaseMap k K)) ≫ f.left
  simp [Category.assoc]

/-- The universal value of a pulled-back morphism extends its Laurent coefficients. -/
theorem baseChangedMorphism_universal
    (f : (Gm (Spec (CommRingCat.of k))).X ⟶ G.X) :
    (laurentBaseIso k K).hom ≫
      baseChangePointsEquiv (algebraBaseMap k K) G _
        (Gm.laurentPoint K ≫ baseChangedMorphism k K G f) =
      Lie.affineMap G (extendAlg k K)
        ((laurentAffineIso k).hom ≫ Gm.laurentPoint k ≫ f) := by
  unfold baseChangedMorphism
  rw [← Category.assoc (Gm.laurentPoint K), baseChangePointsEquiv_morphism,
    baseChangeIso_universalProjection]
  simp only [extendTest, Category.assoc, Iso.hom_inv_id_assoc, Lie.affineMap_apply]

/-- A field extension gives a faithful pullback on schemes over the base. -/
theorem faithful_algebraPullback :
    (Over.pullback (algebraBaseMap k K)).Faithful := by
  have h : Flat (algebraBaseMap k K) ∧ Surjective (algebraBaseMap k K) :=
    (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap k K))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  let : Flat (algebraBaseMap k K) := h.1
  let : Surjective (algebraBaseMap k K) := h.2
  infer_instance

open CategoryTheory.Functor CategoryTheory.Functor.LaxMonoidal in
/-- A faithful monoidal functor reflects preservation of the unit and product. -/
theorem isMonHom_of_faithfulMap
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] [F.Faithful]
    {X Y : C} [MonObj X] [MonObj Y] (f : X ⟶ Y) [IsMonHom (F.map f)] :
    IsMonHom f where
  one_hom := F.map_injective <| by
    simp [← obj.η_def_assoc, ← obj.η_def, ← cancel_epi (ε F)]
  mul_hom := F.map_injective <| by
    simp [← obj.μ_def_assoc, ← obj.μ_def, ← μ_natural_assoc,
      ← cancel_epi (LaxMonoidal.μ F ..)]

variable [FiniteDimensional k K] [IsGalois k K] [IsAffineHom G.X.hom]
  (ν : (Gm (Spec (CommRingCat.of K))).toGrp ⟶
    (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
  (hν : IsInvariant k K G ν)

/-- The base change of the descended scheme morphism is the original cocharacter. -/
theorem baseChangedMorphism_descendedMorphism :
    baseChangedMorphism k K G (descendedMorphism k K G ν hν) = ν.hom.hom := by
  apply (cancel_epi (Gm.relativeLaurentIso (CommRingCat.of K)).inv).mp
  apply (baseChangePointsEquiv (algebraBaseMap k K) G
    (Gm.relativeLaurent (CommRingCat.of K))).injective
  apply (cancel_epi (laurentBaseIso k K).hom).mp
  change (laurentBaseIso k K).hom ≫
      baseChangePointsEquiv (algebraBaseMap k K) G _
        (Gm.laurentPoint K ≫ baseChangedMorphism k K G (descendedMorphism k K G ν hν)) =
    universalValue k K G ν
  rw [baseChangedMorphism_universal, laurentPoint_descendedMorphism]
  simp only [Iso.hom_inv_id_assoc]
  exact extend_descendedPoint k K G ν hν

/-- Recovery expressed on the ordinary pullback before the Gm comparison. -/
theorem pullback_descendedMorphism :
    (Over.pullback (algebraBaseMap k K)).map (descendedMorphism k K G ν hν) =
      (Gm.baseChangeIso (algebraBaseMap k K)).hom.hom.hom ≫ ν.hom.hom := by
  apply (cancel_epi (Gm.baseChangeIso (algebraBaseMap k K)).inv.hom.hom).mp
  change baseChangedMorphism k K G (descendedMorphism k K G ν hν) = _
  rw [baseChangedMorphism_descendedMorphism]
  change ν.hom.hom =
    ((Gm.baseChangeIso (algebraBaseMap k K)).inv ≫
      (Gm.baseChangeIso (algebraBaseMap k K)).hom ≫ ν).hom.hom
  rw [Iso.inv_hom_id_assoc]

/-- The descended scheme morphism preserves the group laws. -/
theorem descendedMorphism_isMonHom :
    IsMonHom (descendedMorphism k K G ν hν) := by
  let := faithful_algebraPullback k K
  have : IsMonHom
      ((Over.pullback (algebraBaseMap k K)).map (descendedMorphism k K G ν hν)) := by
    rw [pullback_descendedMorphism]
    infer_instance
  exact isMonHom_of_faithfulMap (Over.pullback (algebraBaseMap k K)) _

/-- The actual group-scheme cocharacter descended to the original field. -/
def descend :
    (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G :=
  letI := descendedMorphism_isMonHom k K G ν hν
  Grp.homMk (descendedMorphism k K G ν hν)

/-- Base change of the descended cocharacter recovers the original one. -/
theorem baseChange_descend :
    (Gm.baseChangeIso (algebraBaseMap k K)).inv ≫
      (GroupScheme.baseChange (algebraBaseMap k K)).map (descend k K G ν hν) = ν := by
  apply Grp.hom_ext
  exact baseChangedMorphism_descendedMorphism k K G ν hν

end Langlands.GroupScheme.GaloisCocharacterDescent
