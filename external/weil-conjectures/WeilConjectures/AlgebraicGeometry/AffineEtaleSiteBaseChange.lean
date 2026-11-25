/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FullAffineEtaleTopos
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.AffineEtaleRestrictionUnit
import WeilConjectures.AlgebraicGeometry.AffineEtaleRestrictionLargeSets
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageExact

/-!
# Base change on the full affine étale sites

Source: Stacks Project, Étale Cohomology, Lemma 0EYL and Topologies, Lemma 04HR
(blueprint: lem-weil-pbc-affine-etale-site-base-change).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

namespace Scheme

/-- Source: Stacks Project, Étale Cohomology 0EYL, and Topologies 04HR
(blueprint: lem-weil-pbc-affine-etale-site-base-change).
Proof (step 1): the projection to `U` is a base change of the affine morphism `h`,
so it is affine by lem-weil-pbc-affine-morphism-permanence(1). Its target is affine,
so its source is affine by part (2) of that node. Étaleness of the structure map is
already supplied by situation-conventions(1). -/
theorem affineEtaleBaseChange_isAffine {T T' : Scheme.{u}} (h : T' ⟶ T)
    [IsAffineHom h] (U : T.FullAffineEtale) :
    IsAffine (((MorphismProperty.Over.pullback @Etale ⊤ h).obj
      ((fullAffineEtaleInclusion T).obj U)).left) := by
  let : IsAffine ((𝟭 Scheme).obj U.obj.left) := U.property
  change IsAffine (pullback U.obj.hom h)
  exact AlgebraicGeometry.instIsAffinePullbackSchemeOfIsAffineHom_1 U.obj.hom h

/-- Source: Stacks Project, Étale Cohomology 0EYL, and Topologies 04HR
(blueprint: lem-weil-pbc-affine-etale-site-base-change).
The ordinary étale base-change functor restricted to the full affine subcategories.
Its objects are `U ×_T T' → T'`; its arrows are the ordinary base-change arrows. -/
noncomputable def affineEtaleBaseChange {T T' : Scheme.{u}} (h : T' ⟶ T)
    [IsAffineHom h] : T.FullAffineEtale ⥤ T'.FullAffineEtale :=
  ObjectProperty.lift (fun U : T'.Etale ↦ IsAffine U.left)
    (Scheme.fullAffineEtaleInclusion T ⋙ MorphismProperty.Over.pullback @Etale ⊤ h)
    (affineEtaleBaseChange_isAffine h)

end Scheme

/-- Source: Stacks Project, Topologies 04HR and 0217, Sites 00WV
(blueprint: lem-weil-pbc-affine-etale-site-base-change).
Proof: base change preserves joint surjectivity by the point-lifting property of a
cartesian square. It preserves étaleness by stability under base change. The affine
full inclusions create pullbacks, and full étale base change preserves finite limits,
so the restricted functor preserves pullbacks. For continuity, test the sheaf condition
on the standard coverings of the pretopology; pullback preservation identifies matching
families with those on the image covering, where the sheaf condition holds. -/
private theorem affineEtaleBaseChange_cover_pullback_continuous {T T' : Scheme.{u}} (h : T' ⟶ T)
    [IsAffineHom h] :
    (∀ (X : T.FullAffineEtale) (R : Presieve X),
      R ∈ Scheme.fullAffineEtalePrecoverage T X →
        R.map (Scheme.affineEtaleBaseChange h) ∈ Scheme.fullAffineEtalePrecoverage T'
          ((Scheme.affineEtaleBaseChange h).obj X)) ∧
    (∀ (X Y Z : T.FullAffineEtale) (R : Presieve X),
      R ∈ Scheme.fullAffineEtalePrecoverage T X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) (Scheme.affineEtaleBaseChange h)) ∧
    (Scheme.affineEtaleBaseChange h).IsContinuous (Scheme.fullAffineEtaleTopology T)
      (Scheme.fullAffineEtaleTopology T') := by
  have hclosure (S : Scheme.{u}) :
      ObjectProperty.IsClosedUnderLimitsOfShape
        (fun U : S.Etale ↦ IsAffine U.left) WalkingCospan := ⟨by
    rintro X ⟨c⟩
    let G := Scheme.Etale.forget S ⋙ Over.forget S
    have (j : WalkingCospan) : IsAffine ((c.diag ⋙ G).obj j) := c.prop_diag_obj j
    exact Scheme.isAffine_of_isLimit (G.mapCone c.toLimitPresentation.cone)
      (isLimitOfPreserves G c.isLimit)⟩
  have := hclosure T
  have := hclosure T'
  have hi : PreservesLimitsOfShape WalkingCospan (Scheme.fullAffineEtaleInclusion T) := by
    dsimp [Scheme.fullAffineEtaleInclusion]
    infer_instance
  have hr : ReflectsLimitsOfShape WalkingCospan (Scheme.fullAffineEtaleInclusion T') := by
    dsimp [Scheme.fullAffineEtaleInclusion]
    infer_instance
  have hb : PreservesFiniteLimits (MorphismProperty.Over.pullback @Etale ⊤ h) :=
    inferInstance
  have hcomp : PreservesLimitsOfShape WalkingCospan
      (Scheme.affineEtaleBaseChange h ⋙ Scheme.fullAffineEtaleInclusion T') := by
    change PreservesLimitsOfShape WalkingCospan
      (Scheme.fullAffineEtaleInclusion T ⋙ MorphismProperty.Over.pullback @Etale ⊤ h)
    exact comp_preservesLimitsOfShape _ _
  have hp : PreservesLimitsOfShape WalkingCospan (Scheme.affineEtaleBaseChange h) := by
    exact preservesLimitsOfShape_of_reflects_of_preserves _
      (Scheme.fullAffineEtaleInclusion T')
  have hc : ∀ (X : T.FullAffineEtale) (R : Presieve X),
      R ∈ Scheme.fullAffineEtalePrecoverage T X →
      R.map (Scheme.affineEtaleBaseChange h) ∈ Scheme.fullAffineEtalePrecoverage T'
        ((Scheme.affineEtaleBaseChange h).obj X) := by
    rintro X R ⟨n, V, f, rfl, hf, hs⟩
    rw [Presieve.map_ofArrows]
    refine ⟨n, _, _, rfl, ?_, ?_⟩
    · intro i
      change Etale ((MorphismProperty.Over.pullback @Etale ⊤ h).map
        ((Scheme.fullAffineEtaleInclusion T).map (f i))).left
      exact MorphismProperty.of_isPullback (P := @Etale)
        (MorphismProperty.Over.isPullback_map_left h
          ((Scheme.fullAffineEtaleInclusion T).map (f i))) (hf i)
    · intro x
      obtain ⟨i, y, hy⟩ := hs (pullback.fst X.obj.hom h x)
      have H := MorphismProperty.Over.isPullback_map_left h
        ((Scheme.fullAffineEtaleInclusion T).map (f i))
      obtain ⟨z, hz₁, hz₂⟩ := Scheme.exists_preimage_of_isPullback H y x hy
      exact ⟨i, z, hz₂⟩
  have htop (S : Scheme.{u}) (J : Pretopology S.FullAffineEtale)
      (hJ : J.toPrecoverage = Scheme.fullAffineEtalePrecoverage S) :
      Scheme.fullAffineEtaleTopology S = J.toGrothendieck := by
    change (Scheme.fullAffineEtalePrecoverage S).toGrothendieck = J.toGrothendieck
    rw [← hJ]
    apply le_antisymm
    · apply Precoverage.toGrothendieck_le_iff_le_toPrecoverage.mpr
      intro X R hR
      exact ⟨R, hR, Sieve.le_generate R⟩
    · intro X S hS
      obtain ⟨R, hR, hRS⟩ := hS
      exact J.toPrecoverage.toGrothendieck.superset_covering
        (by rw [Sieve.generate_le_iff]; exact hRS)
        (J.toPrecoverage.generate_mem_toGrothendieck hR)
  have hu : (Scheme.affineEtaleBaseChange h).IsContinuous
      (Scheme.fullAffineEtaleTopology T) (Scheme.fullAffineEtaleTopology T') := by
    refine ⟨fun G ↦ ?_⟩
    obtain ⟨J, hJ⟩ := Scheme.fullAffineEtalePrecoverage_isPretopology T
    rw [htop T J hJ, Presieve.isSheaf_pretopology]
    intro X R hR
    rw [Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks]
    exact (isSheaf_iff_isSheaf_of_type _ _).mp G.property |>.isSheafFor_of_mem_precoverage
      (hc X R (hJ ▸ hR))
  exact ⟨hc, fun _ _ _ _ _ _ _ _ ↦ inferInstance, hu⟩

-- The existential continuity witness is used only through instance synthesis.
set_option linter.unusedVariables false in
/--
Source: Stacks Project, Étale Cohomology, Lemma 0EYL, and Topologies,
Lemma 04HR; Sites 00WV, 00WX, 00X1; Étale Cohomology 03Q1(2)
(blueprint: lem-weil-pbc-affine-etale-site-base-change).

Proof:
1. Restrict ordinary étale base change to affine objects using
   situation-conventions(1) and
   lem-weil-pbc-affine-morphism-permanence(1),(2), as in the definition above.
2. Finite jointly surjective étale covering families remain such after base change
   (lem-weil-pbc-etale-covering-base-change). Their domains are affine by step 1.
   A pullback of affine objects over an affine object is affine: its projection is
   affine by pqf-def-affine-morphism and lem-weil-pbc-affine-morphism-permanence.
   It is étale, and the canonical base-change comparison is an isomorphism, by
   situation-conventions(2),(3). This proves both covering
   continuity conditions of def-weil-pbc-sites-and-cohomology(3).
3. Precomposition preserves sheaves. The sheafified presheaf left Kan extension
   is left adjoint to it (lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction).
4. Restriction from full small étale sites to the affine sites is an equivalence
   (lem-weil-pbc-affine-etale-site-topos). Full-site direct image and affine-site
   direct image agree under restriction: both evaluate a sheaf at `V ×_T T'`, with
   the same restriction maps (situation-conventions(3)).
   Uniqueness of left adjoints therefore identifies affine inverse image with
   full-site inverse image conjugated by these restriction equivalences.
   Full-site inverse image preserves finite limits and colimits
   (lem-weil-pbc-sets-etale-inverse-image-exact), as do equivalences and their
   quasi-inverses. Thus the affine inverse image is exact, giving the morphism
   of sites of def-weil-pbc-sites-and-cohomology(3).
-/
theorem affineEtaleSiteBaseChange {T T' : Scheme.{u}} (h : T' ⟶ T)
    [IsAffineHom h] :
    (∀ (X : T.FullAffineEtale) (R : Presieve X),
      R ∈ Scheme.fullAffineEtalePrecoverage T X →
        R.map (Scheme.affineEtaleBaseChange h) ∈ Scheme.fullAffineEtalePrecoverage T'
          ((Scheme.affineEtaleBaseChange h).obj X)) ∧
    (∀ (X Y Z : T.FullAffineEtale) (R : Presieve X),
      R ∈ Scheme.fullAffineEtalePrecoverage T X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f →
        PreservesLimit (cospan f g) (Scheme.affineEtaleBaseChange h)) ∧
    ∃ (hu : (Scheme.affineEtaleBaseChange h).IsContinuous (Scheme.fullAffineEtaleTopology T)
        (Scheme.fullAffineEtaleTopology T')),
      Nonempty
        (Functor.sheafPullbackConstruction.sheafPullback (Scheme.affineEtaleBaseChange h)
          (Type (u + 1))
          (Scheme.fullAffineEtaleTopology T) (Scheme.fullAffineEtaleTopology T') ⊣
          (Scheme.affineEtaleBaseChange h).sheafPushforwardContinuous (Type (u + 1))
            (Scheme.fullAffineEtaleTopology T) (Scheme.fullAffineEtaleTopology T')) ∧
      (PreservesFiniteLimits
        (Functor.sheafPullbackConstruction.sheafPullback (Scheme.affineEtaleBaseChange h)
          (Type (u + 1))
          (Scheme.fullAffineEtaleTopology T) (Scheme.fullAffineEtaleTopology T'))) ∧
      (PreservesFiniteColimits
        (Functor.sheafPullbackConstruction.sheafPullback (Scheme.affineEtaleBaseChange h)
          (Type (u + 1))
          (Scheme.fullAffineEtaleTopology T) (Scheme.fullAffineEtaleTopology T'))) := by
  classical
  obtain ⟨hc, hp, hu⟩ := affineEtaleBaseChange_cover_pullback_continuous h
  let U := fun {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f] ↦
    Scheme.affineEtaleBaseChange f
  let t : ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f],
      U f ⋙ Scheme.fullAffineEtaleInclusion Y ≅
        Scheme.fullAffineEtaleInclusion X ⋙ MorphismProperty.Over.pullback @Etale ⊤ f :=
    fun f ↦ Iso.refl _
  have hcont : ∀ (X Y : Scheme.{u}) (f : Y ⟶ X) [IsAffineHom f],
      (U f).IsContinuous (Scheme.fullAffineEtaleTopology X)
        (Scheme.fullAffineEtaleTopology Y) :=
    fun X Y f ↦ (affineEtaleBaseChange_cover_pullback_continuous f).2.2
  let L := fun {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f] ↦
    Functor.sheafPullbackConstruction.sheafPullback (U f) (Type (u + 1))
      (Scheme.fullAffineEtaleTopology X) (Scheme.fullAffineEtaleTopology Y)
  let a := fun {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f] ↦
    Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (U f) (Type (u + 1))
      (Scheme.fullAffineEtaleTopology X) (Scheme.fullAffineEtaleTopology Y)
  obtain ⟨e, _⟩ := Scheme.affineEtale_inverseImage_restriction_unit U t L a
  let rho := fun X : Scheme.{u} ↦
    (Scheme.fullAffineEtaleInclusion X).sheafPushforwardContinuous (Type (u + 1))
      (Scheme.fullAffineEtaleTopology X) X.smallEtaleTopology
  have hrho (X : Scheme.{u}) : (rho X).IsEquivalence :=
    Scheme.fullAffineEtale_large_sets_equivalence X
  have hfull : PreservesFiniteLimits (Scheme.etaleSetPullback h) :=
    (etaleSetInverseImage_exact h).2.2.1
  have hfullcomp : PreservesFiniteLimits (Scheme.etaleSetPullback h ⋙ rho T') :=
    comp_preservesFiniteLimits _ _
  have hcomp : PreservesFiniteLimits (rho T ⋙ L h) :=
    preservesFiniteLimits_of_natIso (e h)
  have hconjugate : PreservesFiniteLimits ((rho T).inv ⋙ (rho T ⋙ L h)) :=
    comp_preservesFiniteLimits _ _
  have hL : PreservesFiniteLimits (L h) :=
    preservesFiniteLimits_of_natIso
      ((Functor.associator (rho T).inv (rho T) (L h)).symm ≪≫
        Functor.isoWhiskerRight (rho T).asEquivalence.counitIso (L h) ≪≫
        (L h).leftUnitor)
  have hleft : (L h).IsLeftAdjoint := (a h).isLeftAdjoint
  exact ⟨hc, hp, hu, ⟨a h⟩, hL, inferInstance⟩

end AlgebraicGeometry
