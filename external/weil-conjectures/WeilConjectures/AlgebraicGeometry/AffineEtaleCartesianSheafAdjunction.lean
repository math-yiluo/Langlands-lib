/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FullAffineEtaleSite
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageSmallUniverse
import WeilConjectures.AlgebraicGeometry.FullAffineEtaleTopos
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem etale_smallUniverse_sheafAdjunction {S T : Scheme.{u}} (f : T ⟶ S) :
    ∃ L : Sheaf S.smallEtaleTopology (Type u) ⥤
        Sheaf T.smallEtaleTopology (Type u),
      Nonempty (L ⊣ f.Etale.sheafPushforwardContinuous (Type u)
        S.smallEtaleTopology T.smallEtaleTopology) ∧ PreservesFiniteLimits L := by
  classical
  let US := sheafCompose S.smallEtaleTopology uliftFunctor.{u + 1, u}
  let UT := sheafCompose T.smallEtaleTopology uliftFunctor.{u + 1, u}
  let K := US ⋙ etaleSetPullback f
  have hK : ∀ G, UT.essImage (K.obj G) := by
    intro G
    let P := (K.obj G).obj
    let : FunctorToTypes.Small.{u} P := fun B ↦ etale_setPullback_small f G B.unop
    let Q := FunctorToTypes.shrink.{u} P
    let e : Q ⋙ uliftFunctor.{u + 1, u} ≅ P :=
      NatIso.ofComponents
        (fun B ↦ Equiv.toIso (Equiv.ulift.trans (equivShrink.{u} (P.obj B)).symm))
        (by
          intro B C g
          ext x
          change (equivShrink.{u} _).symm
            ((equivShrink.{u} _) (P.map g ((equivShrink.{u} _).symm x.down))) = _
          exact Equiv.symm_apply_apply _ _)
    have hQ : Presheaf.IsSheaf T.smallEtaleTopology Q := by
      have h := (Presheaf.isSheaf_of_iso_iff e).mpr (K.obj G).property
      rw [isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_comp_uliftFunctor_iff] at h
      exact (isSheaf_iff_isSheaf_of_type _ _).mpr h
    refine ⟨⟨Q, hQ⟩, ⟨?_⟩⟩
    exact ObjectProperty.isoMk _ e
  let L := Functor.essImage.liftFunctor K UT hK
  let e := Functor.essImage.liftFunctorCompIso K UT hK
  let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous f.Etale
    (Type (u + 1)) S.smallEtaleTopology T.smallEtaleTopology
  have hLex : PreservesFiniteLimits (etaleSetPullback f) := by
    unfold etaleSetPullback Functor.sheafPullbackConstruction.sheafPullback
    let : AB5OfSize.{u, u + 1} (Type (u + 1)) :=
      AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} (Type (u + 1))
    infer_instance
  let := hLex
  have hUS : PreservesFiniteLimits US := by
    have : PreservesFiniteLimits (US ⋙ sheafToPresheaf S.smallEtaleTopology
        (Type (u + 1))) :=
      inferInstanceAs (PreservesFiniteLimits
        (sheafToPresheaf S.smallEtaleTopology (Type u) ⋙
          (Functor.whiskeringRight _ _ _).obj uliftFunctor.{u + 1, u}))
    exact preservesFiniteLimits_of_reflects_of_preserves US
      (sheafToPresheaf S.smallEtaleTopology (Type (u + 1)))
  let := hUS
  have hKL : PreservesFiniteLimits (L ⋙ UT) :=
    preservesFiniteLimits_of_natIso e.symm
  let := hKL
  refine ⟨L, ⟨?_⟩, preservesFiniteLimits_of_reflects_of_preserves L UT⟩
  exact a.restrictFullyFaithful
    (fullyFaithfulSheafCompose _ fullyFaithfulULiftFunctor.{u + 1, u})
    (fullyFaithfulSheafCompose _ fullyFaithfulULiftFunctor.{u + 1, u}) e.symm (Iso.refl _)

private noncomputable def cartesianEtaleIso
    {S T : Scheme.{u}} (f : T ⟶ S)
    (F : S.FullAffineEtale ⥤ T.FullAffineEtale)
    (p : F ⋙ fullAffineEtaleInclusion T ⋙ Etale.forget T ⋙ Over.forget T ⟶
      fullAffineEtaleInclusion S ⋙ Etale.forget S ⋙ Over.forget S)
    (hp : ∀ A : S.FullAffineEtale,
      IsPullback (p.app A) (F.obj A).obj.hom A.obj.hom f) :
    F ⋙ fullAffineEtaleInclusion T ≅ fullAffineEtaleInclusion S ⋙ f.Etale :=
  NatIso.ofComponents (fun A ↦
    MorphismProperty.Over.isoMk (hp A).isoPullback
      (by exact (hp A).isoPullback_hom_snd)) (by
    intro A B g
    apply MorphismProperty.Over.Hom.ext
    change (F.map g).hom.left ≫ (hp B).isoPullback.hom =
      (hp A).isoPullback.hom ≫ (f.Etale.map g.hom).left
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [IsPullback.isoPullback_hom_fst,
        Scheme.Hom.etale_map_left_comp_fst, ← Category.assoc,
        IsPullback.isoPullback_hom_fst]
      exact p.naturality g
    · simp only [Category.assoc, IsPullback.isoPullback_hom_snd,
        Scheme.Hom.etale_map_left_comp_snd, MorphismProperty.Over.w])

/-- Source: Stacks Project, Topologies 04HR and Étale Cohomology 03Q1(2).

Proof: the natural cartesian squares identify `F`, after affine inclusion, with ordinary
small étale base change along `f`. Pullback uniqueness gives the object isomorphisms;
naturality of `p` and uniqueness give their naturality on arrows. Restriction from each
small étale site to its full affine subcategory is an equivalence on Type u sheaves
(04HR). Under these equivalences, precomposition along `F` is ordinary direct image:
on an affine object A both evaluate a sheaf on A ×_S T, and the restriction maps agree.
Conjugate the ordinary étale inverse-image/direct-image adjunction by the restriction
equivalences. The resulting left adjoint is adjoint to the displayed continuous
pushforward. Étale inverse image preserves finite limits by 03Q1(2), and equivalences
and their quasi-inverses preserve all limits, hence this left adjoint preserves finite
limits. The argument uses sheaves in the stated universe throughout and does not require
an enlargement of the coefficient universe or a choice of system coherence data.
(blueprint: lem-weil-pbc-affine-etale-cartesian-sheaf-adjunction). -/
theorem affineEtale_cartesian_sheafAdjunction
    {S T : Scheme.{u}} (f : T ⟶ S) [IsAffineHom f]
    (F : S.FullAffineEtale ⥤ T.FullAffineEtale)
    (p : F ⋙ fullAffineEtaleInclusion T ⋙ Etale.forget T ⋙ Over.forget T ⟶
      fullAffineEtaleInclusion S ⋙ Etale.forget S ⋙ Over.forget S)
    (hp : ∀ A : S.FullAffineEtale,
      IsPullback (p.app A) (F.obj A).obj.hom A.obj.hom f)
    [F.IsContinuous (fullAffineEtaleTopology S) (fullAffineEtaleTopology T)] :
    ∃ L : Sheaf (fullAffineEtaleTopology S) (Type u) ⥤
        Sheaf (fullAffineEtaleTopology T) (Type u),
      Nonempty (L ⊣ F.sheafPushforwardContinuous (Type u)
        (fullAffineEtaleTopology S) (fullAffineEtaleTopology T)) ∧
      PreservesFiniteLimits L := by
  classical
  let RS := (fullAffineEtaleInclusion S).sheafPushforwardContinuous (Type u)
    (fullAffineEtaleTopology S) S.smallEtaleTopology
  let RT := (fullAffineEtaleInclusion T).sheafPushforwardContinuous (Type u)
    (fullAffineEtaleTopology T) T.smallEtaleTopology
  let : RS.IsEquivalence := fullAffineEtale_sets_equivalence S
  let : RT.IsEquivalence := fullAffineEtale_sets_equivalence T
  let eS := RS.asEquivalence
  let eT := RT.asEquivalence
  obtain ⟨L, ⟨a⟩, hL⟩ := etale_smallUniverse_sheafAdjunction f
  let := hL
  let R := f.Etale.sheafPushforwardContinuous (Type u)
    S.smallEtaleTopology T.smallEtaleTopology
  let Q := F.sheafPushforwardContinuous (Type u)
    (fullAffineEtaleTopology S) (fullAffineEtaleTopology T)
  let : (fullAffineEtaleInclusion S ⋙ f.Etale).IsContinuous
      (fullAffineEtaleTopology S) T.smallEtaleTopology :=
    Functor.isContinuous_comp (fullAffineEtaleInclusion S) f.Etale
      (fullAffineEtaleTopology S) S.smallEtaleTopology T.smallEtaleTopology
  have h : RT ⋙ Q ≅ R ⋙ RS :=
    Functor.sheafPushforwardContinuousComp' (cartesianEtaleIso f F p hp)
      (Type u) (fullAffineEtaleTopology S) (fullAffineEtaleTopology T)
      T.smallEtaleTopology ≪≫
    (Functor.sheafPushforwardContinuousComp (fullAffineEtaleInclusion S) f.Etale
      (Type u) (fullAffineEtaleTopology S) S.smallEtaleTopology
      T.smallEtaleTopology).symm
  have hQ : eT.inverse ⋙ R ⋙ eS.functor ≅ Q :=
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft eT.inverse h.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight eT.counitIso Q ≪≫ Functor.leftUnitor Q
  refine ⟨eS.inverse ⋙ L ⋙ eT.functor, ⟨?_⟩, inferInstance⟩
  exact ((eS.symm.toAdjunction.comp a).comp eT.toAdjunction).ofNatIsoRight hQ

end AlgebraicGeometry.Scheme
