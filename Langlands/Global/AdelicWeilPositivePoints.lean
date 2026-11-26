import Langlands.Global.AdelicRestrictionSplitCentreComparison
import Langlands.Global.AdelicWeilPointTransport
import Langlands.Global.AdeleGaloisAction

/-! # Positive real points under the adelic Weil comparison -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal TensorProduct

namespace Langlands.Global.AdelicWeilRestriction

open Langlands.GroupScheme Langlands.GroupScheme.SplitComponent PositiveRealTorus

variable (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (G : GroupScheme (Spec (CommRingCat.of L))) [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

private abbrev inclusionHom : CommAlgCat.of K (Adeles K) ⟶
    (AffineWeil.restrictScalars K L).obj (CommAlgCat.of L (Adeles L)) :=
  letI : Algebra K (Adeles L) := Algebra.compHom _ (algebraMap K L)
  CommAlgCat.ofHom
    { toRingHom := AdelicFunctoriality.adeleInclusion
      commutes' := AdelicFunctoriality.adeleInclusion_diagonal }

private theorem tensorMap_eq_tensorInclusion_multiplication :
    (AffineWeil.tensorFunctor K L).map (inclusionHom K L) ≫
          AffineWeil.multiplication K (CommAlgCat.of L (Adeles L)) =
      CommAlgCat.ofHom (numberFieldAdeleTensorMap K L) := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul b a =>
      change (AffineWeil.multiplication K (CommAlgCat.of L (Adeles L))).hom
        (((AffineWeil.tensorFunctor K L).map (inclusionHom K L)).hom (b ⊗ₜ[K] a)) =
          numberFieldAdeleTensorMap K L (b ⊗ₜ[K] a)
      rw [AffineWeil.multiplication_tensorMap_tmul]
      exact (numberFieldAdeleTensorMap_tmul b a).symm
  | add a b ha hb =>
      erw [map_add, map_add, ha, hb]

set_option backward.isDefEq.respectTransparency false in
private theorem freeCharEquiv_adeleInclusion {I : Type u} [Finite I]
    (χ : (latticeFunctor (CommRingCat.of K) (FreeAbelianGroup I)).obj
      (CommAlgCat.of K (Adeles K)))
    (χ' : (latticeFunctor (CommRingCat.of L) (FreeAbelianGroup I)).obj
      (CommAlgCat.of L (Adeles L))) (s : I → ℝ≥0ˣ)
    (h : freeCharEquiv (CommRingCat.of K) I _ χ =
      fun j => PositiveRealIdeles.full K (s j))
    (h' : freeCharEquiv (CommRingCat.of L) I _ χ' =
      fun j => PositiveRealIdeles.full L (s j)) :
    (latticeFunctor (CommRingCat.of K) (FreeAbelianGroup I)).map
        (inclusionHom K L) χ =
      (AffineWeil.latticeRestrict K L (FreeAbelianGroup I)).app _ χ' := by
  apply (freeCharEquiv (CommRingCat.of K) I _).injective
  funext j
  apply Units.ext
  change AdelicFunctoriality.adeleInclusion
      (freeCharEquiv (CommRingCat.of K) I _ χ j : Adeles K) =
    (freeCharEquiv (CommRingCat.of L) I _ χ' j : Adeles L)
  rw [h, h']
  exact AdeleGalois.adeleInclusion_positiveReal (F := K) (L := L) (s j)

variable (T : CommGroupScheme (Spec (CommRingCat.of K)))
  (i : T.toGrp ⟶ AffineWeil.groupScheme K L G)
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I)
  {T' : CommGroupScheme (Spec (CommRingCat.of L))} {j : T'.toGrp ⟶ G}

include e

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
/-- The comparison sends the positive points of a central split torus in the restriction
into the positive image of any split component over the upper field. -/
theorem map_imageSubgroup_le (hc : IsCentral i) (hj : IsSplitComponent j) :
    (imageSubgroup K T _ i).map (adelicPointsEquiv K L G).toMonoidHom ≤
      imageSubgroup L T' G j := by
  rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  rw [← subgroup_eq_intrinsicSubgroup K I T e] at hw
  obtain ⟨s, rfl⟩ := hw
  let pK := latticeCorep (CommRingCat.of K) (FreeAbelianGroup I)
  let pL := latticeCorep (CommRingCat.of L) (FreeAbelianGroup I)
  let eK := torusIso (CommRingCat.of K) I ≪≫ e.symm
  let eL := torusIso (CommRingCat.of L) I
  let A := splitTorus.commGroupScheme (Spec (CommRingCat.of L)) I
  let α := natOfHom pK (AffineWeil.corepresentableBy K L G) (eK.hom ≫ i)
  let β := AffineWeil.counitTrans K G α
  let f := homOfNat G pL β
  have hα : IsCentralNat α := isCentralNat_of_isCentral _ _ (by
    rw [groupSchemeMap_natOfHom]
    exact hc.comp _)
  let : Algebra.FormallyUnramified K L := Algebra.FormallyUnramified.of_isSeparable K L
  have hf : IsCentral f := isCentral_homOfNat G pL
    (AffineWeil.isCentralNat_counitTrans K G hα)
  obtain ⟨d, hd⟩ := hj.exists_comp_eq_of_isCentral (finiteType_coordinateAlgebra G)
    (eL.inv ≫ f) (isSplitTorus_splitTorus I) (hf.comp _)
  let wK := full K I T e s
  let wL := full L I A (Iso.refl _) s
  have hwL : wL ∈ intrinsicSubgroup L A := by
    rw [← subgroup_eq_intrinsicSubgroup L I A (Iso.refl _)]
    exact ⟨s, rfl⟩
  refine ⟨_, map_intrinsicSubgroup_le L A T' (Additive.ofMul d : A ⟶ T')
      ⟨wL, hwL, rfl⟩, ?_⟩
  let xK := wK ≫ eK.inv.hom.hom
  let xL := wL ≫ eL.inv.hom.hom
  let χK := Corepresented.affinePointsEquiv _ pK (CommAlgCat.of K (Adeles K)) xK
  let χL := Corepresented.affinePointsEquiv _ pL (CommAlgCat.of L (Adeles L)) xL
  have hxK : xK ≫ eK.hom.hom.hom = wK := by
    rw [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  have hxL : xL ≫ eL.hom.hom.hom = wL := by
    rw [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  have hχK : freeCharEquiv (CommRingCat.of K) I _ χK =
      fun k => PositiveRealIdeles.full K (s k) := by
    rw [← coordinates_full K I T e s]
    exact (RestrictionSplitCentre.coordinates_lattice T I e (Adeles K) xK).symm.trans
      (congrArg (coordinates K I T e (Adeles K)) hxK)
  have hχL : freeCharEquiv (CommRingCat.of L) I _ χL =
      fun k => PositiveRealIdeles.full L (s k) := by
    rw [← coordinates_full L I A (Iso.refl _) s]
    exact (RestrictionSplitCentre.coordinates_lattice A I (Iso.refl _) (Adeles L) xL).symm.trans
      (congrArg (coordinates L I A (Iso.refl _) (Adeles L)) (by
        change xL ≫ eL.hom.hom.hom ≫ 𝟙 A.X = wL
        rw [Category.comp_id, hxL]))
  have hK : xK ≫ (eK.hom ≫ i).hom.hom = wK ≫ i.hom.hom := by
    rw [Grp.comp_hom_hom, ← Category.assoc, hxK]
  have hL : (wL ≫ d.hom.hom) ≫ j.hom.hom = xL ≫ f.hom.hom := by
    change _ = (wL ≫ eL.inv.hom.hom) ≫ f.hom.hom
    rw [Category.assoc, Category.assoc, ← Grp.comp_hom_hom, hd, Grp.comp_hom_hom]
  have hα_eval : α.app (CommAlgCat.of K (Adeles K)) χK =
      AffineWeil.pointsEquiv K L G (Adeles K) (wK ≫ i.hom.hom) := by
    rw [natOfHom_app, MulEquiv.symm_apply_apply, hK]
    rfl
  change (wL ≫ d.hom.hom) ≫ j.hom.hom = adelicPointsEquiv K L G (wK ≫ i.hom.hom)
  rw [hL, homOfNat_affinePoints, adelicPointsEquiv_apply, ← hα_eval,
    ← tensorMap_eq_tensorInclusion_multiplication K L]
  change (AffineWeil.counitTrans K G α).app (CommAlgCat.of L (Adeles L)) χL =
    G.affinePointMap _ (α.app (CommAlgCat.of K (Adeles K)) χK)
  have hnat := AffineWeil.affinePointMap_tensorMap_multiplication K G α
    (inclusionHom K L) χK
  rw [freeCharEquiv_adeleInclusion K L χK χL s hχK hχL] at hnat
  exact hnat.symm

end Langlands.Global.AdelicWeilRestriction
