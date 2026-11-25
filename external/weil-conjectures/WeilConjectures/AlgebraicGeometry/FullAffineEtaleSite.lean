/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Sites.Finite
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck

/-!
# The full small affine étale site

Source: Stacks Project, Topologies, Definitions 0219 and 021B(4)
(blueprint: def-weil-pbc-full-affine-etale-site).
-/

@[expose] public section

universe uS

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks 021B(4) (blueprint: def-weil-pbc-full-affine-etale-site).
The full subcategory of the small étale site whose domains are affine. -/
abbrev FullAffineEtale (S : Scheme.{uS}) :=
  ObjectProperty.FullSubcategory (fun U : S.Etale ↦ IsAffine U.left)

/-- Source: Stacks 021B(4) (blueprint: def-weil-pbc-full-affine-etale-site).
The actual inclusion of affine étale schemes into the small étale site. -/
def fullAffineEtaleInclusion (S : Scheme.{uS}) : S.FullAffineEtale ⥤ S.Etale :=
  ObjectProperty.ι (fun U : S.Etale ↦ IsAffine U.left)

/-- Source: Stacks 0219 and 021B(4) (blueprint: def-weil-pbc-full-affine-etale-site).
Coverings are finite jointly surjective families of étale arrows between affine objects.
`Fin n` also allows the empty covering of an empty affine scheme. -/
def fullAffineEtalePrecoverage (S : Scheme.{uS}) : Precoverage S.FullAffineEtale where
  coverings U := {R | ∃ (n : ℕ) (V : Fin n → S.FullAffineEtale) (f : ∀ i, V i ⟶ U),
    R = Presieve.ofArrows V f ∧ (∀ i, Etale (f i).hom.left) ∧
    ∀ x : U.obj.left, ∃ (i : Fin n) (y : (V i).obj.left), (f i).hom.left y = x}

/-- Source: Stacks 021D (blueprint: def-weil-pbc-full-affine-etale-site).
Proof: scheme pullbacks of affines over an affine are affine, and their structure maps to S
are étale. Fullness transfers the scheme-theoretic universal property to this category. -/
theorem fullAffineEtale_hasPullbacks (S : Scheme.{uS}) :
    HasPullbacks S.FullAffineEtale := by
  let P : ObjectProperty S.Etale := fun U => IsAffine U.left
  have : P.IsClosedUnderLimitsOfShape WalkingCospan := ⟨by
    rintro X ⟨h⟩
    let F := Etale.forget S ⋙ Over.forget S
    have (j : WalkingCospan) : IsAffine ((h.diag ⋙ F).obj j) := h.prop_diag_obj j
    exact Scheme.isAffine_of_isLimit (F.mapCone h.toLimitPresentation.cone)
      (isLimitOfPreserves F h.isLimit)⟩
  infer_instance

attribute [instance] fullAffineEtale_hasPullbacks

/-- Source: Stacks 021C (blueprint: def-weil-pbc-full-affine-etale-site).
Proof: singleton isomorphisms cover; pullback preserves étaleness and joint surjectivity;
composing a finite covering with one finite covering on each of its finitely many distinct
arrows gives a finite jointly surjective étale family. These are the pretopology axioms. -/
theorem fullAffineEtalePrecoverage_isPretopology (S : Scheme.{uS}) :
    ∃ J : Pretopology S.FullAffineEtale, J.toPrecoverage = fullAffineEtalePrecoverage S :=
  by
  classical
  let P : ObjectProperty S.Etale := fun U ↦ IsAffine U.left
  have : P.IsClosedUnderLimitsOfShape WalkingCospan := ⟨by
    rintro X ⟨h⟩
    let G := Etale.forget S ⋙ Over.forget S
    have (j : WalkingCospan) : IsAffine ((h.diag ⋙ G).obj j) := h.prop_diag_obj j
    exact Scheme.isAffine_of_isLimit (G.mapCone h.toLimitPresentation.cone)
      (isLimitOfPreserves G h.isLimit)⟩
  let F := P.ι ⋙ Etale.forget S ⋙ Over.forget S
  have : PreservesLimitsOfShape WalkingCospan F := by dsimp [F]; infer_instance
  let K := (Scheme.precoverage @Etale).comap F
  refine ⟨Pretopology.finite _ ⊓ K.toPretopology, ?_⟩
  ext U R
  change (R.uncurry.Finite ∧ R ∈ K U) ↔ _
  constructor
  · rintro ⟨hfin, hR⟩
    let := hfin.fintype
    let e := Fintype.equivFin R.uncurry
    let V : Fin (Fintype.card R.uncurry) → S.FullAffineEtale :=
      fun i ↦ (e.symm i).val.1
    let f : ∀ i, V i ⟶ U := fun i ↦ (e.symm i).val.2
    have hEq : R = Presieve.ofArrows V f := by
      apply le_antisymm
      · intro W g hg
        let a : R.uncurry := ⟨⟨W, g⟩, hg⟩
        have h : Presieve.ofArrows V f (f (e a)) := .mk (e a)
        change Presieve.ofArrows V f (e.symm (e a)).val.2 at h
        rw [e.symm_apply_apply] at h
        exact h
      · rintro W g ⟨i⟩
        exact (e.symm i).property
    refine ⟨Fintype.card R.uncurry, V, f, hEq, ?_, ?_⟩
    · intro i
      infer_instance
    · rw [hEq] at hR
      change (Presieve.ofArrows V f).map F ∈ Scheme.precoverage @Etale (F.obj U) at hR
      rw [Presieve.map_ofArrows, Scheme.ofArrows_mem_precoverage_iff] at hR
      exact hR.1
  · rintro ⟨n, V, f, rfl, hf, hsurj⟩
    refine ⟨?_, ?_⟩
    · simpa only [Presieve.uncurry_ofArrows] using
        (Set.finite_range (fun i ↦ (⟨V i, f i⟩ : Σ W, W ⟶ U)))
    · change (Presieve.ofArrows V f).map F ∈ Scheme.precoverage @Etale (F.obj U)
      rw [Presieve.map_ofArrows, Scheme.ofArrows_mem_precoverage_iff]
      exact ⟨hsurj, hf⟩

/-- Source: Stacks 021B(4), Sites 00ZC (blueprint: def-weil-pbc-full-affine-etale-site).
The Grothendieck topology generated by the standard finite étale coverings. -/
def fullAffineEtaleTopology (S : Scheme.{uS}) : GrothendieckTopology S.FullAffineEtale :=
  (fullAffineEtalePrecoverage S).toGrothendieck

/-- Source: Stacks 021B(4) (blueprint: def-weil-pbc-full-affine-etale-site).
The spectrum functor lifts to the affine full subcategory, is fully faithful, and is
essentially surjective via the canonical spectrum isomorphism of an affine scheme.
Transport Mathlib's essential smallness of its affine étale category along this equivalence. -/
private theorem fullAffineEtale_essentiallySmall (S : Scheme.{uS}) :
    EssentiallySmall.{uS} S.FullAffineEtale := by
  let P : ObjectProperty S.Etale := fun U ↦ IsAffine U.left
  let F : S.AffineEtale ⥤ S.FullAffineEtale :=
    P.lift (AffineEtale.Spec S) (fun U ↦ by
      change IsAffine (Spec U.left.unop)
      infer_instance)
  have : F.Full := inferInstanceAs (P.lift (AffineEtale.Spec S) _).Full
  have : F.Faithful := inferInstanceAs (P.lift (AffineEtale.Spec S) _).Faithful
  have : F.EssSurj := ⟨fun U ↦ by
    have : IsAffine U.obj.left := U.property
    let V := AffineEtale.mk (U.obj.left.isoSpec.inv ≫ U.obj.hom)
    refine ⟨V, ⟨P.isoMk ?_⟩⟩
    exact MorphismProperty.Over.isoMk U.obj.left.isoSpec.symm (by simp [V, F])⟩
  have : F.IsEquivalence := { }
  exact (essentiallySmall_congr F.asEquivalence).mp inferInstance

/-- Source: Stacks 021B(4), Sites 00W1 (blueprint: def-weil-pbc-full-affine-etale-site).
Proof: the site is essentially small: every affine étale object is isomorphic to a spectrum
of a finitely presented étale algebra on an affine open of S. Sheafification on an essentially
small site exists for sets and abelian groups by the usual plus construction. -/
theorem fullAffineEtaleTopology_hasSheafify_sets (S : Scheme.{uS}) :
    HasSheafify (fullAffineEtaleTopology S) (Type uS) := by
  have := fullAffineEtale_essentiallySmall S
  exact hasSheafifyEssentiallySmallSite.{uS} _ _

attribute [instance] fullAffineEtaleTopology_hasSheafify_sets

/-- Source: Stacks Sites 00W1 (blueprint: def-weil-pbc-full-affine-etale-site).
Proof: sheafify the underlying abelian presheaf on the essentially small affine étale site
by the plus construction; the group operations descend uniquely. -/
theorem fullAffineEtaleTopology_hasSheafify_ab (S : Scheme.{uS}) :
    HasSheafify (fullAffineEtaleTopology S) AddCommGrpCat.{uS} := by
  have := fullAffineEtale_essentiallySmall S
  exact hasSheafifyEssentiallySmallSite.{uS} _ _

attribute [instance] fullAffineEtaleTopology_hasSheafify_ab

end AlgebraicGeometry.Scheme
