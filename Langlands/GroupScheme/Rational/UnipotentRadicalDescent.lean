import Langlands.GroupScheme.Descent.FiniteGaloisTensor
import Langlands.GroupScheme.Descent.ClosedSubgroups
import Langlands.GroupScheme.Rational.UnipotentRadicalGalois
import Langlands.GroupScheme.BaseChangeReflection

/-! # Actual finite Galois descent of a represented unipotent radical -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace Descent

/-- On a component with first projection the identity, the canonical overlap
transport is the inverse of the canonical transport along its second projection. -/
theorem pullIso_canonicalOverlap_eq {B S : Scheme.{u}} (p : S ⟶ B)
    (C : GroupScheme B) (a : S ⟶ S) (ha : a ≫ p = p)
    (q : S ⟶ Overlap p) (hf : q ≫ fst p = 𝟙 S) (hg : q ≫ snd p = a) :
    pullIso q hf hg (canonicalOverlap p C) =
      baseChangeIdIso ((GroupScheme.baseChange p).obj C) ≪≫
        (descentBaseChangeIso p a ha C).symm := by
  apply Iso.ext
  apply (cancel_mono (descentBaseChangeIso p a ha C).hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Grp.comp_hom_hom, Over.comp_left, Category.assoc,
      descentBaseChangeIso_hom_fst, baseChangeIdIso_hom_left]
    change (pullHom q hf hg (canonicalOverlap p C).hom).hom.hom.left ≫
        pullback.fst ((GroupScheme.baseChange p).obj C).X.hom a ≫
          pullback.fst C.X.hom p =
      pullback.fst ((GroupScheme.baseChange p).obj C).X.hom (𝟙 S) ≫
        pullback.fst C.X.hom p
    exact pullHom_canonicalOverlap_fst p C q (𝟙 S) a hf hg
  · exact (Over.w ((pullIso q hf hg (canonicalOverlap p C)).hom ≫
      (descentBaseChangeIso p a ha C).hom).hom.hom).trans
        (Over.w (baseChangeIdIso ((GroupScheme.baseChange p).obj C)).hom.hom.hom).symm

/-- The inverse direct-pullback comparison is natural in the group scheme. -/
@[reassoc] theorem pullbackComparison_inv_naturality {S T V : Scheme.{u}}
    (f : T ⟶ S) (q : V ⟶ T) (r : V ⟶ S) (h : q ≫ f = r)
    {C D : GroupScheme S} (a : C ⟶ D) :
    (GroupScheme.baseChange r).map a ≫ (pullbackComparison f q r h D).inv =
      (pullbackComparison f q r h C).inv ≫
        (GroupScheme.baseChange q).map ((GroupScheme.baseChange f).map a) := by
  apply (cancel_mono (pullbackComparison f q r h D).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    pullbackComparison_naturality, Iso.inv_hom_id_assoc]

end Descent

open Descent

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {U : GroupScheme (Spec (CommRingCat.of L))}
    {i : U ⟶ (GroupScheme.baseChange (algebraBaseMap k L)).obj G}

namespace IsUnipotentRadical

variable [IsAffineHom G.X.hom] (hi : IsUnipotentRadical i)

/-- Normalized Galois source transport commutes with the identity pullback. -/
theorem galoisSourceIso_inv_fac (σ : L ≃ₐ[k] L) :
    ((baseChangeIdIso U) ≪≫ (hi.galoisSourceIso σ).symm).hom ≫
        (GroupScheme.baseChange (galoisBaseMap k L σ)).map i =
      (GroupScheme.baseChange (𝟙 _)).map i ≫
        (baseChangeIdIso ((GroupScheme.baseChange (algebraBaseMap k L)).obj G) ≪≫
          (descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
            (galoisBaseMap_over k L σ) G).symm).hom := by
  apply (cancel_mono (descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
    (galoisBaseMap_over k L σ) G).hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  change (baseChangeIdIso U).hom ≫ (hi.galoisSourceIso σ).inv ≫
      radicalGaloisHom i σ = _
  rw [← hi.galoisSourceIso_hom_comp σ, Iso.inv_hom_id_assoc]
  exact (((Functor.mapGrpNatIso Over.pullbackId) ≪≫
    Functor.mapGrpIdIso).hom.naturality i).symm

/-- The source transport on one actual component of the finite Galois overlap. -/
def galoisComponentIso [FiniteDimensional k L] [IsGalois k L]
    (j : Fin (Module.finrank k L)) :
    (GroupScheme.baseChange (finiteGaloisComponent k L j)).obj
        ((GroupScheme.baseChange (fst (fieldMap k L))).obj U) ≅
      (GroupScheme.baseChange (finiteGaloisComponent k L j)).obj
        ((GroupScheme.baseChange (snd (fieldMap k L))).obj U) :=
  pullbackComparison (fst (fieldMap k L)) (finiteGaloisComponent k L j) (𝟙 _)
      (finiteGaloisComponent_fst k L j) U ≪≫
    baseChangeIdIso U ≪≫ (hi.galoisSourceIso (galoisIndexEquiv k L j)).symm ≪≫
      (pullbackComparison (snd (fieldMap k L)) (finiteGaloisComponent k L j)
        (galoisBaseMap k L (galoisIndexEquiv k L j))
          (finiteGaloisComponent_snd k L j) U).symm

/-- Each actual component transport respects the radical inclusion. -/
theorem galoisComponentIso_fac [FiniteDimensional k L] [IsGalois k L]
    (j : Fin (Module.finrank k L)) :
    (hi.galoisComponentIso j).hom ≫
        (GroupScheme.baseChange (finiteGaloisComponent k L j)).map
          ((GroupScheme.baseChange (snd (fieldMap k L))).map i) =
      (GroupScheme.baseChange (finiteGaloisComponent k L j)).map
          ((GroupScheme.baseChange (fst (fieldMap k L))).map i) ≫
        (GroupScheme.baseChange (finiteGaloisComponent k L j)).map
          (canonicalOverlap (fieldMap k L) G).hom := by
  let q := finiteGaloisComponent k L j
  let a := galoisBaseMap k L (galoisIndexEquiv k L j)
  have hf : q ≫ fst (fieldMap k L) = 𝟙 _ := finiteGaloisComponent_fst k L j
  have hg : q ≫ snd (fieldMap k L) = a := finiteGaloisComponent_snd k L j
  apply (cancel_epi (pullbackComparison (fst (fieldMap k L)) q (𝟙 _) hf U).inv).mp
  apply (cancel_mono (pullbackComparison (snd (fieldMap k L)) q a hg
    ((GroupScheme.baseChange (algebraBaseMap k L)).obj G)).hom).mp
  simp only [Category.assoc]
  rw [pullbackComparison_naturality]
  change (pullbackComparison (fst (fieldMap k L)) q (𝟙 _) hf U).inv ≫
      ((pullbackComparison (fst (fieldMap k L)) q (𝟙 _) hf U).hom ≫
        (baseChangeIdIso U).hom ≫ (hi.galoisSourceIso (galoisIndexEquiv k L j)).inv ≫
          (pullbackComparison (snd (fieldMap k L)) q a hg U).inv) ≫
        (pullbackComparison (snd (fieldMap k L)) q a hg U).hom ≫
          (GroupScheme.baseChange a).map i = _
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change (baseChangeIdIso U ≪≫ (hi.galoisSourceIso (galoisIndexEquiv k L j)).symm).hom ≫
    (GroupScheme.baseChange a).map i = _
  rw [hi.galoisSourceIso_inv_fac]
  rw [← pullIso_canonicalOverlap_eq (fieldMap k L) G a
    (galoisBaseMap_over k L (galoisIndexEquiv k L j)) q hf hg]
  change (GroupScheme.baseChange (𝟙 _)).map i ≫
      (pullIso q hf hg (canonicalOverlap (fieldMap k L) G)).hom = _
  rw [pullIso_hom]
  simp only [pullHom]
  rw [pullbackComparison_inv_naturality_assoc]

/-- Assemble the actual source overlap from the finite Galois components. -/
def finiteGaloisOverlap [FiniteDimensional k L] [IsGalois k L] :
    OverlapIso (fieldMap k L) U :=
  FiniteComponents.groupIso (finiteGaloisComponent k L) hi.galoisComponentIso

/-- The assembled source overlap respects the original inclusion. -/
theorem finiteGaloisOverlap_fac [FiniteDimensional k L] [IsGalois k L] :
    hi.finiteGaloisOverlap.hom ≫ (GroupScheme.baseChange (snd (fieldMap k L))).map i =
      (GroupScheme.baseChange (fst (fieldMap k L))).map i ≫
        (canonicalOverlap (fieldMap k L) G).hom := by
  apply FiniteComponents.groupHom_ext (finiteGaloisComponent k L)
  intro j
  simpa only [Functor.map_comp, finiteGaloisOverlap, FiniteComponents.groupIso,
    FiniteComponents.map_groupHom] using hi.galoisComponentIso_fac j

/-- A represented radical over a finite Galois extension has actual descent
data: the cocycle follows by cancellation of its closed inclusion. -/
def finiteGaloisDatum [FiniteDimensional k L] [IsGalois k L] :
    Datum (fieldMap k L) U where
  overlap := hi.finiteGaloisOverlap
  cocycle := cocycle_of_closedSubgroup_lift (canonicalDatum (fieldMap k L) G)
    hi.isClosedSubgroup _ hi.finiteGaloisOverlap_fac

/-- The radical inclusion respects the constructed and canonical data. -/
theorem compatible_finiteGaloisDatum [FiniteDimensional k L] [IsGalois k L] :
    Compatible hi.finiteGaloisDatum (canonicalDatum (fieldMap k L) G) i :=
  hi.finiteGaloisOverlap_fac.symm

local instance fieldMap_flat : Flat (fieldMap k L) := (fieldExtension_fpqc k L).2.1
local instance fieldMap_surjective : Surjective (fieldMap k L) := (fieldExtension_fpqc k L).1

include hi in
private theorem source_isAffine : IsAffine U.X.left := by
  let : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  let : IsAffine ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.left := by
    change IsAffine (pullback G.X.hom (algebraBaseMap k L))
    infer_instance
  exact isAffine_of_isAffineHom i.hom.hom.left

/-- Effective affine descent of the actual radical source, with its compatible
pullback identification. -/
def finiteGaloisSolution [FiniteDimensional k L] [IsGalois k L] :
    Solution hi.finiteGaloisDatum := by
  letI : IsAffine U.X.left := hi.source_isAffine
  exact hi.finiteGaloisDatum.affineSolution

/-- The actual descended inclusion into the original group. -/
def finiteGaloisInclusion [FiniteDimensional k L] [IsGalois k L] :
    hi.finiteGaloisSolution.obj ⟶ G := by
  letI : IsAffine U.X.left := hi.source_isAffine
  exact hi.finiteGaloisDatum.affineHomTo G i hi.compatible_finiteGaloisDatum

/-- Pulling back the descended inclusion recovers the supplied inclusion
through the constructed source isomorphism. -/
theorem baseChange_finiteGaloisInclusion [FiniteDimensional k L] [IsGalois k L] :
    (GroupScheme.baseChange (fieldMap k L)).map hi.finiteGaloisInclusion =
      hi.finiteGaloisSolution.iso.hom ≫ i := by
  let : IsAffine U.X.left := hi.source_isAffine
  exact hi.finiteGaloisDatum.baseChange_affineHomTo G i hi.compatible_finiteGaloisDatum

/-- The descended radical source is an affine scheme. -/
instance finiteGaloisSolution_isAffine [FiniteDimensional k L] [IsGalois k L] :
    IsAffine hi.finiteGaloisSolution.obj.X.left := by
  let : IsAffine U.X.left := hi.source_isAffine
  exact inferInstanceAs (IsAffine hi.finiteGaloisDatum.affineSolution.obj.X.left)

/-- The actual descended inclusion is a closed subgroup. -/
theorem finiteGaloisInclusion_isClosedSubgroup [FiniteDimensional k L] [IsGalois k L] :
    IsClosedSubgroup hi.finiteGaloisInclusion := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  apply IsClosedSubgroup.of_baseChange_of_isAffine (fieldMap k L)
  rw [hi.baseChange_finiteGaloisInclusion]
  exact (IsClosedSubgroup.of_iso hi.finiteGaloisSolution.iso).comp hi.isClosedSubgroup

end IsUnipotentRadical

end Langlands.GroupScheme
