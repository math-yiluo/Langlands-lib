/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback

import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
import WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction

/-!
# Pro-etale evaluation over an algebraically closed field

Source: Bhatt--Scholze, The pro-etale topology for schemes, Examples 4.1.10 and 4.2.11
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Continuity of the relative test-object functor, by composition of the published
continuous functors. Source: Bhatt--Scholze, Example 4.1.10
(auxiliary; not a blueprint node). -/
noncomputable instance geometricFieldTest_isContinuous (X : Scheme.{u}) :
    (profiniteToProEtOf X).IsContinuous (coherentTopology Profinite.{u})
      (Scheme.ProEt.topology X) :=
  Functor.isContinuous_comp profiniteToProEt (Scheme.proEtaleBaseChange (toSpecZ X))
    (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)
    (Scheme.ProEt.topology X)

/-- Restriction along the specified relative profinite test objects, on objects and
arrows. Source: Bhatt--Scholze, Examples 4.1.10 and 4.2.11
(auxiliary; not a blueprint node). -/
noncomputable abbrev geometricFieldRestriction (X : Scheme.{u})
    (D : Type v) [Category.{u + 1} D] :=
  (profiniteToProEtOf X).sheafPushforwardContinuous D
    (coherentTopology Profinite.{u}) (Scheme.ProEt.topology X)

/-- The canonical structural map from the singleton test object to the final scheme.
Source: Bhatt--Scholze, Example 4.1.10
(auxiliary; not a blueprint node). -/
noncomputable def geometricFieldTestFinalMap (X : Scheme.{u}) :
    (profiniteToProEtOf X).obj (Profinite.of (ULift.{u, 0} PUnit.{1})) ⟶
      Scheme.ProEt.mk (𝟙 X) :=
  MorphismProperty.Over.homMk
    (((profiniteToProEtOf X).obj (Profinite.of (ULift.{u, 0} PUnit.{1}))).hom)

/-- The point adjunction, with restriction as its actual right adjoint.
Source: Bhatt--Scholze, Example 4.2.11
(auxiliary; not a blueprint node). -/
noncomputable def geometricFieldPointAdjunction (X : Scheme.{u}) :
    profinitePointSetSchemeInverseImage X ⊣ geometricFieldRestriction X (Type (u + 1)) :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous profiniteToProEt
    (Type (u + 1)) (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)).comp
      (Scheme.proEtaleSheafAdjunction (toSpecZ X) (Type (u + 1)))

/-- The same specified adjunction for abelian sheaves.
Source: Bhatt--Scholze, Example 4.2.11
(auxiliary; not a blueprint node). -/
noncomputable def geometricFieldAbelianPointAdjunction (X : Scheme.{u}) :
    upperStarFromPoint X ⊣ geometricFieldRestriction X Ab.{u + 1} :=
  pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))

/-- Canonical base change of relative profinite test objects, fixed by the fibre-product
composition comparison. Source: Bhatt--Scholze, Example 4.1.10
(auxiliary; not a blueprint node). -/
noncomputable def geometricFieldTestBaseChange {X Y : Scheme.{u}} (f : X ⟶ Y) :
    profiniteToProEtOf Y ⋙ Scheme.proEtaleBaseChange f ≅ profiniteToProEtOf X :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft profiniteToProEt
    (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
      f (toSpecZ Y) (toSpecZ X) (comp_toSpecZ f).symm).symm

/-- The canonical comparison from restriction to restriction after inverse image:
apply the adjunction unit and then the specified test-object base-change isomorphism.
Source: Bhatt--Scholze, Example 4.1.10
(auxiliary; not a blueprint node). -/
noncomputable def geometricFieldRestrictionComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [HasWeakSheafify (Scheme.ProEt.topology X) D] :
    geometricFieldRestriction Y D ⟶
      Scheme.proEtaleSheafInverseImage f D ⋙ geometricFieldRestriction X D :=
  Functor.whiskerRight (Scheme.proEtaleSheafAdjunction f D).unit
    (geometricFieldRestriction Y D) ≫
  Functor.whiskerLeft (Scheme.proEtaleSheafInverseImage f D)
    (Functor.sheafPushforwardContinuousComp'
      (eFG := geometricFieldTestBaseChange f) D
      (coherentTopology Profinite.{u}) (Scheme.ProEt.topology Y)
      (Scheme.ProEt.topology X)).hom

/-- The canonical evaluation comparison, not an unrelated isomorphism: the scheme
adjunction unit followed by restriction along the final-object base-change isomorphism.
It is defined for any coefficient category for which inverse image exists, hence its
components for rings are ring maps. Source: Bhatt--Scholze, Example 4.1.10
(auxiliary; not a blueprint node). -/
noncomputable def geometricFieldEvaluationComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [HasWeakSheafify (Scheme.ProEt.topology X) D] :
    (sheafSections (Scheme.ProEt.topology Y) D).obj (op (Scheme.ProEt.mk (𝟙 Y))) ⟶
      Scheme.proEtaleSheafInverseImage f D ⋙
        (sheafSections (Scheme.ProEt.topology X) D).obj (op (Scheme.ProEt.mk (𝟙 X))) :=
  Functor.whiskerRight (Scheme.proEtaleSheafAdjunction f D).unit
    ((sheafSections (Scheme.ProEt.topology Y) D).obj (op (Scheme.ProEt.mk (𝟙 Y)))) ≫
  Functor.whiskerLeft (Scheme.proEtaleSheafInverseImage f D)
    ((sheafSections (Scheme.ProEt.topology X) D).mapIso
      (MorphismProperty.Over.isoMk
        (asIso (pullback.snd (𝟙 Y) f)) (Category.comp_id _)).op).inv

/-- Composition of arbitrary coefficient inverse images, obtained by conjugating the
canonical fibre-product comparison of direct images.
Source: Bhatt--Scholze, Example 4.1.10
(auxiliary; not a blueprint node). -/
noncomputable def geometricFieldInverseImageComp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (D : Type v) [Category.{u + 1} D]
    [HasColimitsOfSize.{u + 1, u + 1} D]
    [HasWeakSheafify (Scheme.ProEt.topology X) D]
    [HasWeakSheafify (Scheme.ProEt.topology Y) D] :
    Scheme.proEtaleSheafInverseImage (f ≫ g) D ≅
      Scheme.proEtaleSheafInverseImage g D ⋙ Scheme.proEtaleSheafInverseImage f D :=
  ((conjugateIsoEquiv (Scheme.proEtaleSheafAdjunction (f ≫ g) D)
    ((Scheme.proEtaleSheafAdjunction g D).comp
      (Scheme.proEtaleSheafAdjunction f D))).symm
    (Functor.sheafPushforwardContinuousComp'
      (eFG := (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g).symm)
      D (Scheme.ProEt.topology Z) (Scheme.ProEt.topology Y)
      (Scheme.ProEt.topology X)).symm).symm

/-- The identity inverse-image comparison, as the adjunction conjugate of the canonical
identity direct-image comparison. Source: Bhatt--Scholze, Example 4.1.10
(auxiliary; not a blueprint node). -/
noncomputable def geometricFieldInverseImageIdentity (X : Scheme.{u})
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [HasWeakSheafify (Scheme.ProEt.topology X) D] :
    Scheme.proEtaleSheafInverseImage (𝟙 X) D ≅ 𝟭 _ :=
  (conjugateIsoEquiv Adjunction.id (Scheme.proEtaleSheafAdjunction (𝟙 X) D)).symm
    (Functor.sheafPushforwardContinuousId'
      (MorphismProperty.Over.pullbackId (P := @WeaklyEtale) (Q := ⊤) X)
      D (Scheme.ProEt.topology X)).symm

/-- Restriction of modules uses the same profinite test objects and the identity scalar
map, so it is restriction of both the sections and their ring action.
Source: Bhatt--Scholze, Example 4.2.11
(auxiliary; not a blueprint node). -/
noncomputable abbrev geometricFieldModuleRestriction (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1}) :=
  SheafOfModules.pushforward.{u + 1} (F := profiniteToProEtOf X)
    (J := coherentTopology Profinite.{u}) (K := Scheme.ProEt.topology X)
    (R := R) (𝟙 ((geometricFieldRestriction X RingCat.{u + 1}).obj R))

private theorem geometricField_finalMap_isIso (X : Scheme.{u}) :
    IsIso (geometricFieldTestFinalMap X) := by
  have : PreservesFiniteLimits (profiniteToProEtOf X) :=
    (profinite_test_object_functor X).1
  have hs : IsTerminal (Profinite.of (ULift.{u, 0} PUnit.{1})) :=
    IsTerminal.ofUniqueHom (fun _ ↦ ConcreteCategory.ofHom
      ⟨fun _ ↦ default, continuous_const⟩) (fun _ _ ↦ by ext)
  have ht : IsTerminal (Scheme.ProEt.mk (𝟙 X)) :=
    IsTerminal.ofUniqueHom (fun U ↦ MorphismProperty.Over.homMk U.hom)
      (fun U f ↦ by
        apply MorphismProperty.Over.Hom.ext
        change f.left = U.hom
        have hw := MorphismProperty.Over.w f
        change f.left ≫ 𝟙 X = U.hom at hw
        exact (Category.comp_id f.left).symm.trans hw)
  exact isIso_of_isTerminal (hs.isTerminalObj (profiniteToProEtOf X) _) ht _

/-- Over an algebraically closed field, the specified restriction is the profinite-site
identification, its left adjoint is the specified point inverse image, and evaluation
at the scheme is evaluation at the singleton. This includes ring and module structures.

Source: Bhatt--Scholze, Examples 4.1.10 and 4.2.11
(auxiliary; not a blueprint node).

Proof: The proved geometricFieldProfiniteDenseSubsite identifies the specified test
functor with a dense subsite. Mathlib's comparison theorem gives restriction
equivalences for sets, abelian groups and rings. The two specified point adjunctions
therefore have invertible units and counits. Finite-limit preservation sends the
singleton to a terminal pro-etale object, so its map to the final object is invertible.
For an arbitrary ring sheaf, the proved module transport theorem lifts its scalar
action through the set and abelian restriction equivalences and checks the module
laws on the cover-dense subsite. This proves equivalence for the specified module
restriction with its identity scalar map. -/
theorem geometric_field_proetale_evaluation (K : Type u) [Field K] [IsAlgClosed K] :
    (geometricFieldRestriction (Spec (.of K)) (Type (u + 1))).IsEquivalence ∧
    (geometricFieldRestriction (Spec (.of K)) Ab.{u + 1}).IsEquivalence ∧
    (geometricFieldRestriction (Spec (.of K)) RingCat.{u + 1}).IsEquivalence ∧
    IsIso (geometricFieldPointAdjunction (Spec (.of K))).unit ∧
    IsIso (geometricFieldPointAdjunction (Spec (.of K))).counit ∧
    IsIso (geometricFieldAbelianPointAdjunction (Spec (.of K))).unit ∧
    IsIso (geometricFieldAbelianPointAdjunction (Spec (.of K))).counit ∧
    IsIso (geometricFieldTestFinalMap (Spec (.of K))) ∧
    (∀ R : Sheaf (Scheme.ProEt.topology (Spec (.of K))) RingCat.{u + 1},
      (geometricFieldModuleRestriction (Spec (.of K)) R).IsEquivalence) := by
  have : (profiniteToProEtOf (Spec (.of K))).IsDenseSubsite
      (coherentTopology Profinite.{u}) (Scheme.ProEt.topology (Spec (.of K))) :=
    geometricFieldProfiniteDenseSubsite K
  have hset : (geometricFieldRestriction (Spec (.of K)) (Type (u + 1))).IsEquivalence :=
    inferInstance
  have hab : (geometricFieldRestriction (Spec (.of K)) Ab.{u + 1}).IsEquivalence :=
    inferInstance
  have hrings : (geometricFieldRestriction (Spec (.of K)) RingCat.{u + 1}).IsEquivalence :=
    inferInstance
  refine ⟨hset, hab, hrings, ?_, ?_, ?_, ?_, geometricField_finalMap_isIso _, ?_⟩
  · infer_instance
  · infer_instance
  · infer_instance
  · infer_instance
  · intro R
    have := Functor.IsDenseSubsite.isCoverDense (coherentTopology Profinite.{u})
      (Scheme.ProEt.topology (Spec (.of K))) (profiniteToProEtOf (Spec (.of K)))
    exact SheafOfModules.isEquivalence_pushforward_of_dense.{u + 1, u, u + 1, u, 0}
      (coherentTopology Profinite.{u}) (Scheme.ProEt.topology (Spec (.of K)))
      (profiniteToProEtOf (Spec (.of K))) R

/-- The upstream site lemmas import the incompatible generic star API.
This argument uses their lower-level weakly-etale section API directly. -/
private theorem geometricField_cover_id (K : Type u) [Field K] [IsAlgClosed K]
    {S : Sieve (Scheme.ProEt.mk (𝟙 (Spec (.of K))))}
    (hS : S ∈ Scheme.ProEt.topology (Spec (.of K)) _) : S (𝟙 _) := by
  obtain ⟨R, hR, hRS⟩ := Scheme.ProEt.mem_topology_iff.1 hS
  have hR' := (show Scheme.proetalePrecoverage ≤ Scheme.precoverage @WeaklyEtale from
    inf_le_right) _ hR
  obtain ⟨Y, g, hg, x, -⟩ := hR'.1 (IsLocalRing.closedPoint K)
  obtain ⟨hg⟩ := hg
  obtain @⟨V, f, hf⟩ := hg
  obtain ⟨σ, hσ⟩ := exists_comp_eq_id_of_weaklyEtale V.hom x
  let s : Scheme.ProEt.mk (𝟙 (Spec (.of K))) ⟶ V :=
    MorphismProperty.Over.homMk σ hσ
  have h := S.downward_closed (hRS _ _ hf) s
  convert h using 1
  apply MorphismProperty.Over.Hom.ext
  change 𝟙 _ = σ ≫ f.left
  have hf : f.left = V.hom := by
    have hw := MorphismProperty.Over.w f
    change f.left ≫ 𝟙 _ = V.hom at hw
    simpa only [Category.comp_id] using hw
  rw [hf]
  exact hσ.symm

private theorem geometricField_abelian_colimits (K : Type u) [Field K] [IsAlgClosed K]
    (J : Type) [SmallCategory J] : PreservesColimitsOfShape J
      ((sheafSections (Scheme.ProEt.topology (Spec (.of K))) Ab.{u + 1}).obj
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of K)))))) := by
  let X := Spec (.of K)
  let T := op (Scheme.ProEt.mk (𝟙 X))
  let E := (sheafSections (Scheme.ProEt.topology X) Ab.{u + 1}).obj T
  have hb (G : X.ProEtᵒᵖ ⥤ Ab.{u + 1}) :
      Function.Bijective ((toSheafify (Scheme.ProEt.topology X) G).app T) := by
    refine ⟨fun x y hxy ↦ ?_, fun s ↦ ?_⟩
    · have hh := geometricField_cover_id K
        (Presheaf.equalizerSieve_mem (Scheme.ProEt.topology X) (toSheafify _ G) x y hxy)
      change G.map (𝟙 T) x = G.map (𝟙 T) y at hh
      simpa only [CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] using hh
    · obtain ⟨t, ht⟩ := geometricField_cover_id K
        (Presheaf.imageSieve_mem (Scheme.ProEt.topology X) (toSheafify _ G) s)
      change (toSheafify (Scheme.ProEt.topology X) G).app T t =
        (sheafify (Scheme.ProEt.topology X) G).map (𝟙 T) s at ht
      rw [CategoryTheory.Functor.map_id] at ht
      exact ⟨t, ht⟩
  have (G : X.ProEtᵒᵖ ⥤ Ab.{u + 1}) : IsIso ((Functor.whiskerRight
      (sheafificationAdjunction (Scheme.ProEt.topology X) Ab.{u + 1}).unit
      ((evaluation _ Ab.{u + 1}).obj T)).app G) :=
    (isIso_iff_of_reflects_iso _ (forget Ab.{u + 1})).1
      ((isIso_iff_bijective _).2 (hb G))
  have : IsIso (Functor.whiskerRight
      (sheafificationAdjunction (Scheme.ProEt.topology X) Ab.{u + 1}).unit
      ((evaluation _ Ab.{u + 1}).obj T)) := NatIso.isIso_of_isIso_app _
  have : PreservesColimitsOfShape J (presheafToSheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙ E) :=
    preservesColimitsOfShape_of_natIso (asIso (Functor.whiskerRight
      (sheafificationAdjunction (Scheme.ProEt.topology X) Ab.{u + 1}).unit
      ((evaluation _ Ab.{u + 1}).obj T)))
  exact (sheafificationAdjunction (Scheme.ProEt.topology X) Ab.{u + 1})
    |>.preservesColimitsOfShape_of_comp E J

/-- Covers of the final object split through a member; abelian evaluation is exact,
and evaluation of arbitrary ring-sheaf modules preserves cokernels and finite free modules.
The latter are the colimits of finite families of copies of the coefficient sheaf.

Source: Bhatt--Scholze, Example 4.1.10; Stacks Project, Tag 03CN
(auxiliary; not a blueprint node).

Proof: (5) A covering member contains a point above the unique point of Spec K.
The weakly-etale section theorem splits its structure map. Hence every covering sieve
contains the identity, and a generated covering contains a split generator.
(6) Local injectivity and local surjectivity of sheafification become actual bijectivity
at the final object, by restricting along the identity in these covering sieves.
Consequently evaluation commutes with sheafification, and the reflective adjunction
reduces preservation of colimits to pointwise presheaf colimits. Limits are sectionwise.
The forgetful functor from module sheaves to abelian sheaves preserves colimits;
forgetting modules to abelian groups reflects them. This proves the module assertions,
including cokernels, rank zero and a zero coefficient ring. -/
theorem geometric_field_proetale_evaluation_exact (K : Type u) [Field K] [IsAlgClosed K] :
    (∀ (S : Presieve (Scheme.ProEt.mk (𝟙 (Spec (.of K))))),
      Sieve.generate S ∈ Scheme.ProEt.topology (Spec (.of K)) _ →
      ∃ (U : (Spec (.of K)).ProEt)
        (f : U ⟶ Scheme.ProEt.mk (𝟙 (Spec (.of K))))
        (s : Scheme.ProEt.mk (𝟙 (Spec (.of K))) ⟶ U), S f ∧ s ≫ f = 𝟙 _) ∧
    PreservesFiniteLimits
      ((sheafSections (Scheme.ProEt.topology (Spec (.of K))) Ab.{u + 1}).obj
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of K)))))) ∧
    PreservesFiniteColimits
      ((sheafSections (Scheme.ProEt.topology (Spec (.of K))) Ab.{u + 1}).obj
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of K)))))) ∧
    (∀ (R : Sheaf (Scheme.ProEt.topology (Spec (.of K))) RingCat.{u + 1}),
      PreservesColimitsOfShape WalkingParallelPair
        (SheafOfModules.evaluation.{u + 1} R
          (op (Scheme.ProEt.mk (𝟙 (Spec (.of K)))))) ∧
      ∀ n : ℕ, PreservesColimit
        (Discrete.functor (fun _ : Fin n ↦ SheafOfModules.unit R))
        (SheafOfModules.evaluation.{u + 1} R
          (op (Scheme.ProEt.mk (𝟙 (Spec (.of K))))))) := by
  have hcol (J : Type) [SmallCategory J] : PreservesColimitsOfShape J
      ((sheafSections (Scheme.ProEt.topology (Spec (.of K))) Ab.{u + 1}).obj
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of K)))))) :=
    geometricField_abelian_colimits K J
  have hlim : PreservesFiniteLimits
      ((sheafSections (Scheme.ProEt.topology (Spec (.of K))) Ab.{u + 1}).obj
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of K)))))) := by
    change PreservesFiniteLimits (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj _)
    infer_instance
  refine ⟨?_, hlim, ⟨fun J _ _ ↦ hcol J⟩, ?_⟩
  · intro S hS
    obtain ⟨U, s, f, hf, hsf⟩ :=
      geometricField_cover_id K hS
    exact ⟨U, f, s, hf, hsf⟩
  · intro R
    have hmod (J : Type) [SmallCategory J] : PreservesColimitsOfShape J
        (SheafOfModules.evaluation.{u + 1} R
          (op (Scheme.ProEt.mk (𝟙 (Spec (.of K)))))) := by
      let E := (sheafSections (Scheme.ProEt.topology (Spec (.of K))) Ab.{u + 1}).obj
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of K)))))
      have : PreservesColimitsOfShape J E := hcol J
      let M := SheafOfModules.evaluation.{u + 1} R
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of K)))))
      let U := forget₂ (ModuleCat.{u + 1}
        (R.obj.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of K))))))) Ab.{u + 1}
      have : PreservesColimitsOfShape J (M ⋙ U) :=
        inferInstanceAs (PreservesColimitsOfShape J (SheafOfModules.toSheaf R ⋙ E))
      exact preservesColimitsOfShape_of_reflects_of_preserves M U
    exact ⟨hmod WalkingParallelPair, fun n ↦ (hmod (Discrete (Fin n))).preservesColimit⟩

private theorem geometricField_comparisons_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [HasWeakSheafify (Scheme.ProEt.topology X) D]
    [(geometricFieldRestriction X D).IsEquivalence]
    [(geometricFieldRestriction Y D).IsEquivalence] :
    IsIso (geometricFieldRestrictionComparison f D) ∧
      IsIso (geometricFieldEvaluationComparison f D) := by
  have : (Scheme.proEtaleSheafDirectImage f D ⋙ geometricFieldRestriction Y D).IsEquivalence :=
    CategoryTheory.Functor.isEquivalence_of_iso
      (Functor.sheafPushforwardContinuousComp' (geometricFieldTestBaseChange f) D
        (coherentTopology Profinite.{u}) (Scheme.ProEt.topology Y)
        (Scheme.ProEt.topology X)).symm
  have : (Scheme.proEtaleSheafDirectImage f D).IsEquivalence :=
    CategoryTheory.Functor.isEquivalence_of_comp_right _ (geometricFieldRestriction Y D)
  have : IsIso (Scheme.proEtaleSheafAdjunction f D).unit := inferInstance
  constructor
  · dsimp [geometricFieldRestrictionComparison]
    infer_instance
  · dsimp [geometricFieldEvaluationComparison]
    infer_instance

/-- Algebraically closed extensions induce the identity under the specified profinite
identifications and preserve evaluation by the canonical unit-normalized comparisons.
This includes arbitrary, nonalgebraic extensions and identities. Ring components are
ring homomorphisms, and the restriction comparison for modules respects their action.

Source: Bhatt--Scholze, Example 4.1.10
(auxiliary; not a blueprint node).

Proof: (7) The canonical pullback-composition isomorphism already identifies the
relative profinite test objects after arbitrary base change. The resulting isomorphism
of direct-image restrictions, combined with the two restriction equivalences in the
preceding theorem, makes scheme direct image an equivalence. Its adjunction unit is
therefore an isomorphism. Both displayed comparisons are obtained by whiskering this
unit and composing with the specified test-object or final-object isomorphism.
Apply this argument separately to sets, abelian groups and rings. -/
theorem geometric_field_proetale_evaluation_extension
    (K K' : Type u) [Field K] [IsAlgClosed K] [Field K'] [IsAlgClosed K'] (i : K →+* K') :
    IsIso (geometricFieldRestrictionComparison (Spec.map (CommRingCat.ofHom i))
      (Type (u + 1))) ∧
    IsIso (geometricFieldRestrictionComparison (Spec.map (CommRingCat.ofHom i))
      Ab.{u + 1}) ∧
    IsIso (geometricFieldRestrictionComparison (Spec.map (CommRingCat.ofHom i))
      RingCat.{u + 1}) ∧
    IsIso (geometricFieldEvaluationComparison (Spec.map (CommRingCat.ofHom i))
      (Type (u + 1))) ∧
    IsIso (geometricFieldEvaluationComparison (Spec.map (CommRingCat.ofHom i))
      Ab.{u + 1}) ∧
    IsIso (geometricFieldEvaluationComparison (Spec.map (CommRingCat.ofHom i))
      RingCat.{u + 1}) := by
  have hK := geometric_field_proetale_evaluation K
  have hK' := geometric_field_proetale_evaluation K'
  have := hK.1
  have := hK.2.1
  have := hK.2.2.1
  have := hK'.1
  have := hK'.2.1
  have := hK'.2.2.1
  have hs := geometricField_comparisons_isIso (Spec.map (CommRingCat.ofHom i)) (Type (u + 1))
  have ha := geometricField_comparisons_isIso (Spec.map (CommRingCat.ofHom i)) Ab.{u + 1}
  have hr := geometricField_comparisons_isIso (Spec.map (CommRingCat.ofHom i)) RingCat.{u + 1}
  exact ⟨hs.1, ha.1, hr.1, hs.2, ha.2, hr.2⟩

private theorem geometricField_comparison_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (D : Type v) [Category.{u + 1} D]
    [HasColimitsOfSize.{u + 1, u + 1} D]
    [HasWeakSheafify (Scheme.ProEt.topology X) D]
    [HasWeakSheafify (Scheme.ProEt.topology Y) D]
    (F : Sheaf (Scheme.ProEt.topology Z) D)
    (U : Z.ProEt) (V : Y.ProEt) (W : X.ProEt)
    (s : V ⟶ (Scheme.proEtaleBaseChange g).obj U)
    (t : W ⟶ (Scheme.proEtaleBaseChange f).obj V) :
    ((Scheme.proEtaleSheafAdjunction (f ≫ g) D).unit.app F).hom.app (op U) ≫
        ((Scheme.proEtaleSheafInverseImage (f ≫ g) D).obj F).obj.map
          (t ≫ (Scheme.proEtaleBaseChange f).map s ≫
            (MorphismProperty.Over.pullbackComp f g).inv.app U).op =
      ((Scheme.proEtaleSheafAdjunction g D).unit.app F).hom.app (op U) ≫
        ((Scheme.proEtaleSheafInverseImage g D).obj F).obj.map s.op ≫
        ((Scheme.proEtaleSheafAdjunction f D).unit.app
          ((Scheme.proEtaleSheafInverseImage g D).obj F)).hom.app (op V) ≫
        ((Scheme.proEtaleSheafInverseImage f D).obj
          ((Scheme.proEtaleSheafInverseImage g D).obj F)).obj.map t.op ≫
        ((geometricFieldInverseImageComp f g D).inv.app F).hom.app (op W) := by
  let δ := Functor.sheafPushforwardContinuousComp'
    (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g).symm
    D (Scheme.ProEt.topology Z) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
  have h := unit_conjugateEquiv_symm (Scheme.proEtaleSheafAdjunction (f ≫ g) D)
    ((Scheme.proEtaleSheafAdjunction g D).comp (Scheme.proEtaleSheafAdjunction f D))
    δ.inv F
  have hh := congrArg (fun k ↦ k.hom.app (op U)) h
  simp only [Adjunction.comp_unit_app, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, δ, Functor.sheafPushforwardContinuousComp'_inv_app_hom_app,
    Scheme.proEtaleSheafDirectImage, lowerStar, Category.assoc] at hh
  let A := (Scheme.proEtaleSheafInverseImage g D).obj F
  let B := (Scheme.proEtaleSheafInverseImage f D).obj A
  let C := (Scheme.proEtaleSheafInverseImage (f ≫ g) D).obj F
  let α := (geometricFieldInverseImageComp f g D).inv.app F
  let η := (Scheme.proEtaleSheafAdjunction f D).unit.app A
  change ((Scheme.proEtaleSheafAdjunction (f ≫ g) D).unit.app F).hom.app (op U) ≫
      C.obj.map ((MorphismProperty.Over.pullbackComp f g).inv.app U).op =
    ((Scheme.proEtaleSheafAdjunction g D).unit.app F).hom.app (op U) ≫
      η.hom.app (op ((Scheme.proEtaleBaseChange g).obj U)) ≫
      α.hom.app (op ((Scheme.proEtaleBaseChange f).obj
        ((Scheme.proEtaleBaseChange g).obj U))) at hh
  have hαs := α.hom.naturality ((Scheme.proEtaleBaseChange f).map s).op
  change B.obj.map ((Scheme.proEtaleBaseChange f).map s).op ≫ α.hom.app _ =
    α.hom.app _ ≫ C.obj.map ((Scheme.proEtaleBaseChange f).map s).op at hαs
  have hαt := α.hom.naturality t.op
  change B.obj.map t.op ≫ α.hom.app _ = α.hom.app _ ≫ C.obj.map t.op at hαt
  have hη := η.hom.naturality s.op
  change A.obj.map s.op ≫ η.hom.app (op V) =
    η.hom.app _ ≫ B.obj.map ((Scheme.proEtaleBaseChange f).map s).op at hη
  simp only [op_comp, CategoryTheory.Functor.map_comp]
  change _ = ((Scheme.proEtaleSheafAdjunction g D).unit.app F).hom.app (op U) ≫
    A.obj.map s.op ≫ η.hom.app (op V) ≫ B.obj.map t.op ≫ α.hom.app (op W)
  calc
    _ = (((Scheme.proEtaleSheafAdjunction (f ≫ g) D).unit.app F).hom.app (op U) ≫
        C.obj.map ((MorphismProperty.Over.pullbackComp f g).inv.app U).op) ≫
          C.obj.map ((Scheme.proEtaleBaseChange f).map s).op ≫ C.obj.map t.op := by
      dsimp only [C]
      simp only [Category.assoc]
    _ = _ := by rw [hh]
    _ = _ := by
      simp only [Category.assoc]
      rw [← reassoc_of% hαs, ← reassoc_of% hη, ← hαt]

private theorem geometricField_final_pullback_hom_ext {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U : X.ProEt}
    (a b : U ⟶ (Scheme.proEtaleBaseChange f).obj (Scheme.ProEt.mk (𝟙 Y))) : a = b := by
  apply MorphismProperty.Over.Hom.ext
  apply (cancel_mono (pullback.snd (𝟙 Y) f)).1
  exact (MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm

/-- The evaluation and restriction comparisons have the same singleton component and
respect composition. This formulation is uniform in the coefficient category, so the
same equations hold for sets, abelian groups and rings, and for their operation maps.
Source: Bhatt--Scholze, Examples 4.1.10 and 4.2.11
(auxiliary; not a blueprint node).

Proof: (8) The singleton base-change isomorphism commutes with the structural maps to
terminal objects, proving the evaluation square. On finite clopen partitions the two
iterated scalar-extension maps are both multiplication on the scalar factors. The
fibre-product composition maps therefore commute. Conjugation under the given
adjunctions gives the displayed composition equations, with their specified units.
No choice of an unrelated equivalence or comparison is involved. -/
theorem geometric_field_proetale_evaluation_coherence
    (K K' K'' : Type u) [Field K] [IsAlgClosed K] [Field K'] [IsAlgClosed K']
    [Field K''] [IsAlgClosed K''] (i : K →+* K') (j : K' →+* K'')
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [HasWeakSheafify (Scheme.ProEt.topology (Spec (.of K))) D]
    [HasWeakSheafify (Scheme.ProEt.topology (Spec (.of K'))) D]
    [HasWeakSheafify (Scheme.ProEt.topology (Spec (.of K''))) D] :
    (∀ F : Sheaf (Scheme.ProEt.topology (Spec (.of K))) D,
      F.obj.map (geometricFieldTestFinalMap (Spec (.of K))).op ≫
          ((geometricFieldRestrictionComparison (Spec.map (CommRingCat.ofHom i)) D).app F).hom.app
            (op (Profinite.of (ULift.{u, 0} PUnit.{1}))) =
        (geometricFieldEvaluationComparison (Spec.map (CommRingCat.ofHom i)) D).app F ≫
          ((Scheme.proEtaleSheafInverseImage (Spec.map (CommRingCat.ofHom i)) D).obj F).obj.map
            (geometricFieldTestFinalMap (Spec (.of K'))).op) ∧
    (∀ F : Sheaf (Scheme.ProEt.topology (Spec (.of K))) D,
      (geometricFieldEvaluationComparison
        (Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom i)) D).app F =
      (geometricFieldEvaluationComparison (Spec.map (CommRingCat.ofHom i)) D).app F ≫
        (geometricFieldEvaluationComparison (Spec.map (CommRingCat.ofHom j)) D).app
          ((Scheme.proEtaleSheafInverseImage (Spec.map (CommRingCat.ofHom i)) D).obj F) ≫
        ((sheafSections (Scheme.ProEt.topology (Spec (.of K''))) D).obj
          (op (Scheme.ProEt.mk (𝟙 (Spec (.of K'')))))).map
            ((geometricFieldInverseImageComp (Spec.map (CommRingCat.ofHom j))
              (Spec.map (CommRingCat.ofHom i)) D).inv.app F)) ∧
    (∀ F : Sheaf (Scheme.ProEt.topology (Spec (.of K))) D,
      (geometricFieldRestrictionComparison
        (Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom i)) D).app F =
      (geometricFieldRestrictionComparison (Spec.map (CommRingCat.ofHom i)) D).app F ≫
        (geometricFieldRestrictionComparison (Spec.map (CommRingCat.ofHom j)) D).app
          ((Scheme.proEtaleSheafInverseImage (Spec.map (CommRingCat.ofHom i)) D).obj F) ≫
        (geometricFieldRestriction (Spec (.of K'')) D).map
          ((geometricFieldInverseImageComp (Spec.map (CommRingCat.ofHom j))
            (Spec.map (CommRingCat.ofHom i)) D).inv.app F)) := by
  let f := Spec.map (CommRingCat.ofHom j)
  let g := Spec.map (CommRingCat.ofHom i)
  let q {X Y : Scheme.{u}} (h : X ⟶ Y) :
      Scheme.ProEt.mk (𝟙 X) ⟶ (Scheme.proEtaleBaseChange h).obj (Scheme.ProEt.mk (𝟙 Y)) :=
    (MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 Y) h)) (Category.comp_id _)).inv
  refine ⟨?_, ?_, ?_⟩
  · intro F
    let G := (Scheme.proEtaleSheafInverseImage g D).obj F
    let η := (Scheme.proEtaleSheafAdjunction g D).unit.app F
    have hn := η.hom.naturality (geometricFieldTestFinalMap (Spec (.of K))).op
    change F.obj.map (geometricFieldTestFinalMap (Spec (.of K))).op ≫
        η.hom.app _ = η.hom.app _ ≫
          G.obj.map ((Scheme.proEtaleBaseChange g).map
            (geometricFieldTestFinalMap (Spec (.of K)))).op at hn
    dsimp [geometricFieldRestrictionComparison, geometricFieldEvaluationComparison]
    simp only [Functor.sheafPushforwardContinuousComp'_hom_app_hom_app,
      Functor.sheafPushforwardContinuous_map_hom_app, Iso.op_inv]
    rw [← Category.assoc, hn, Category.assoc]
    change η.hom.app _ ≫ G.obj.map _ ≫ G.obj.map _ =
      (η.hom.app _ ≫ G.obj.map _) ≫ G.obj.map _
    simp only [← CategoryTheory.Functor.map_comp, ← op_comp, Category.assoc]
    congr 2
    exact congrArg Quiver.Hom.op (geometricField_final_pullback_hom_ext g _ _)
  · intro F
    have h := geometricField_comparison_comp f g D F
      (Scheme.ProEt.mk (𝟙 (Spec (.of K))))
      (Scheme.ProEt.mk (𝟙 (Spec (.of K'))))
      (Scheme.ProEt.mk (𝟙 (Spec (.of K'')))) (q g) (q f)
    have ht : q f ≫ (Scheme.proEtaleBaseChange f).map (q g) ≫
        (MorphismProperty.Over.pullbackComp f g).inv.app _ = q (f ≫ g) :=
      geometricField_final_pullback_hom_ext _ _ _
    rw [ht] at h
    dsimp [geometricFieldEvaluationComparison]
    simpa only [q, f, g, Iso.op_inv, Category.assoc] using h
  · intro F
    ext S
    have h := geometricField_comparison_comp f g D F
      ((profiniteToProEtOf (Spec (.of K))).obj S.unop)
      ((profiniteToProEtOf (Spec (.of K'))).obj S.unop)
      ((profiniteToProEtOf (Spec (.of K''))).obj S.unop)
      ((geometricFieldTestBaseChange g).inv.app S.unop)
      ((geometricFieldTestBaseChange f).inv.app S.unop)
    have ht : (geometricFieldTestBaseChange f).inv.app S.unop ≫
        (Scheme.proEtaleBaseChange f).map
          ((geometricFieldTestBaseChange g).inv.app S.unop) ≫
        (MorphismProperty.Over.pullbackComp f g).inv.app _ =
          (geometricFieldTestBaseChange (f ≫ g)).inv.app S.unop := by
      apply MorphismProperty.Over.Hom.ext
      change ((geometricFieldTestBaseChange f).inv.app S.unop).left ≫
          ((Scheme.proEtaleBaseChange f).map
            ((geometricFieldTestBaseChange g).inv.app S.unop)).left ≫
          ((MorphismProperty.Over.pullbackComp f g).inv.app _).left =
            ((geometricFieldTestBaseChange (f ≫ g)).inv.app S.unop).left
      apply pullback.hom_ext
      · apply pullback.hom_ext <;>
          simp [geometricFieldTestBaseChange,
            Scheme.proEtaleBaseChange, MorphismProperty.Over.pullbackComp_hom_app_left,
            MorphismProperty.Over.pullbackComp_inv_app_left,
            MorphismProperty.Over.pullback, MorphismProperty.Over.mk, profiniteToProEtOf,
            Category.assoc]
      · simp [geometricFieldTestBaseChange,
          Scheme.proEtaleBaseChange, MorphismProperty.Over.pullbackComp_hom_app_left,
          MorphismProperty.Over.pullbackComp_inv_app_left,
          MorphismProperty.Over.pullback, MorphismProperty.Over.mk, profiniteToProEtOf,
          Category.assoc]
    rw [ht] at h
    dsimp [geometricFieldRestrictionComparison]
    simpa only [Functor.sheafPushforwardContinuousComp'_hom_app_hom_app,
      Functor.sheafPushforwardContinuous_map_hom_app, f, g, Category.assoc] using h

set_option backward.isDefEq.respectTransparency false in
/-- Identity compatibility, including the actual inverse-image identity comparison.
Source: Bhatt--Scholze, Example 4.1.10
(auxiliary; not a blueprint node).

Proof: (8) Base change along the identity has its canonical projection to the original
test object. The unit triangle identity makes its conjugate the identity inverse-image
comparison. Evaluate at the singleton for the first equation; retain every test object
for the second. -/
theorem geometric_field_proetale_evaluation_identity
    (K : Type u) [Field K] [IsAlgClosed K]
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [HasWeakSheafify (Scheme.ProEt.topology (Spec (.of K))) D]
    (F : Sheaf (Scheme.ProEt.topology (Spec (.of K))) D) :
    (geometricFieldEvaluationComparison (𝟙 (Spec (.of K))) D).app F ≫
      ((sheafSections (Scheme.ProEt.topology (Spec (.of K))) D).obj
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of K)))))).map
          ((geometricFieldInverseImageIdentity (Spec (.of K)) D).hom.app F) = 𝟙 _ ∧
    (geometricFieldRestrictionComparison (𝟙 (Spec (.of K))) D).app F ≫
      (geometricFieldRestriction (Spec (.of K)) D).map
        ((geometricFieldInverseImageIdentity (Spec (.of K)) D).hom.app F) = 𝟙 _ := by
  let adj := Scheme.proEtaleSheafAdjunction (𝟙 (Spec (.of K))) D
  let e := Functor.sheafPushforwardContinuousId'
    (MorphismProperty.Over.pullbackId (P := @WeaklyEtale) (Q := ⊤) (Spec (.of K)))
    D (Scheme.ProEt.topology (Spec (.of K)))
  have h := unit_conjugateEquiv_symm Adjunction.id adj e.inv F
  simp only [Adjunction.id_unit, NatTrans.id_app, Category.id_comp, Functor.id_obj] at h
  change e.inv.app F = adj.unit.app F ≫
    (Scheme.proEtaleSheafDirectImage (𝟙 (Spec (.of K))) D).map
      ((geometricFieldInverseImageIdentity (Spec (.of K)) D).hom.app F) at h
  let α := (geometricFieldInverseImageIdentity (Spec (.of K)) D).hom.app F
  let G := (Scheme.proEtaleSheafInverseImage (𝟙 (Spec (.of K))) D).obj F
  let r := MorphismProperty.Over.pullbackId (P := @WeaklyEtale) (Q := ⊤) (Spec (.of K))
  have hU (U : (Spec (.of K)).ProEt) :
      (adj.unit.app F).hom.app (op U) ≫ G.obj.map (r.inv.app U).op ≫
        α.hom.app (op U) = 𝟙 _ := by
    have hh := congrArg (fun k ↦ k.hom.app (op U)) h
    simp only [e, Functor.sheafPushforwardContinuousId'_inv_app_hom_app,
      Scheme.proEtaleSheafDirectImage, lowerStar] at hh
    change F.obj.map (r.hom.app U).op = (adj.unit.app F).hom.app (op U) ≫
      α.hom.app (op ((Scheme.proEtaleBaseChange (𝟙 (Spec (.of K)))).obj U)) at hh
    have hn := α.hom.naturality (r.inv.app U).op
    change G.obj.map (r.inv.app U).op ≫ α.hom.app (op U) =
      α.hom.app _ ≫ F.obj.map (r.inv.app U).op at hn
    rw [hn, ← Category.assoc, ← hh]
    rw [← CategoryTheory.Functor.map_comp, ← op_comp, r.inv_hom_id_app,
      op_id, CategoryTheory.Functor.map_id]
    rfl
  constructor
  · dsimp [geometricFieldEvaluationComparison]
    rw [Category.assoc]
    have ht : (MorphismProperty.Over.isoMk
        (asIso (pullback.snd (𝟙 (Spec (.of K))) (𝟙 (Spec (.of K)))))
        (Category.comp_id _)).inv = r.inv.app (Scheme.ProEt.mk (𝟙 (Spec (.of K)))) := by
      apply (cancel_mono (r.hom.app _)).1
      rw [r.inv_hom_id_app]
      apply MorphismProperty.Over.Hom.ext
      change inv (pullback.snd (𝟙 (Spec (.of K))) (𝟙 (Spec (.of K)))) ≫
        pullback.fst (𝟙 (Spec (.of K))) (𝟙 (Spec (.of K))) = 𝟙 _
      rw [show pullback.fst (𝟙 (Spec (.of K))) (𝟙 (Spec (.of K))) =
          pullback.snd (𝟙 (Spec (.of K))) (𝟙 (Spec (.of K))) by
        simpa only [Category.comp_id] using
          pullback.condition (f := 𝟙 (Spec (.of K))) (g := 𝟙 (Spec (.of K)))]
      exact IsIso.inv_hom_id _
    change (adj.unit.app F).hom.app _ ≫ G.obj.map _ ≫ α.hom.app _ = 𝟙 _
    simpa only [Iso.op_inv, ← ht] using hU (Scheme.ProEt.mk (𝟙 (Spec (.of K))))
  · ext T
    dsimp [geometricFieldRestrictionComparison]
    rw [Category.assoc]
    have ht : (geometricFieldTestBaseChange (𝟙 (Spec (.of K)))).inv.app T.unop =
        r.inv.app ((profiniteToProEtOf (Spec (.of K))).obj T.unop) := by
      simp only [geometricFieldTestBaseChange, MorphismProperty.Over.pullbackComp_id_left,
        MorphismProperty.Over.pullbackCongr_refl]
      rfl
    simp only [Functor.sheafPushforwardContinuousComp'_hom_app_hom_app]
    change (adj.unit.app F).hom.app _ ≫ G.obj.map _ ≫ α.hom.app _ = 𝟙 _
    rw [ht]
    exact hU ((profiniteToProEtOf (Spec (.of K))).obj T.unop)

/-- Compatibility with every finite-arity operation on sheaves of sets. In particular,
apply this to addition, multiplication, units and an arbitrary ring-sheaf module action.
The inverse-image operation is its image under the specified scheme inverse image;
the product comparisons specify the product identification rather than choosing one.
Source: Bhatt--Scholze, Examples 4.1.10 and 4.2.11
(auxiliary; not a blueprint node).

Proof: (8) The restriction comparison is natural at all operation morphisms, since it
is built from an adjunction unit and a test-object isomorphism. Inverse image preserves
finite products. The naturality equations for product projections identify the comparison
on a finite product with the product of its components; naturality at the operation
then gives the equation. The empty family is the nullary case and includes zero and one.
The same equations apply to the action R times M to M, without requiring commutativity
or a nonzero ring. Thus the evaluation comparison is linear over its coefficient-ring
comparison for every ring-sheaf module, not only constant coefficient modules. -/
theorem geometric_field_proetale_evaluation_operations
    (K K' : Type u) [Field K] [IsAlgClosed K] [Field K'] [IsAlgClosed K']
    (i : K →+* K') (I : Type u) [Finite I]
    (F : I → Sheaf (Scheme.ProEt.topology (Spec (.of K))) (Type (u + 1)))
    (H : Sheaf (Scheme.ProEt.topology (Spec (.of K))) (Type (u + 1)))
    (a : (∏ᶜ F) ⟶ H) :
    PreservesFiniteProducts
      (Scheme.proEtaleSheafInverseImage (Spec.map (CommRingCat.ofHom i)) (Type (u + 1))) ∧
    ((sheafSections (Scheme.ProEt.topology (Spec (.of K))) (Type (u + 1))).obj
      (op (Scheme.ProEt.mk (𝟙 (Spec (.of K)))))).map a ≫
        (geometricFieldEvaluationComparison (Spec.map (CommRingCat.ofHom i))
          (Type (u + 1))).app H =
      (geometricFieldEvaluationComparison (Spec.map (CommRingCat.ofHom i))
        (Type (u + 1))).app (∏ᶜ F) ≫
        ((sheafSections (Scheme.ProEt.topology (Spec (.of K'))) (Type (u + 1))).obj
          (op (Scheme.ProEt.mk (𝟙 (Spec (.of K')))))).map
            ((Scheme.proEtaleSheafInverseImage (Spec.map (CommRingCat.ofHom i))
              (Type (u + 1))).map a) ∧
    (∀ k : I,
      ((sheafSections (Scheme.ProEt.topology (Spec (.of K))) (Type (u + 1))).obj
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of K)))))).map (Pi.π F k) ≫
          (geometricFieldEvaluationComparison (Spec.map (CommRingCat.ofHom i))
            (Type (u + 1))).app (F k) =
        (geometricFieldEvaluationComparison (Spec.map (CommRingCat.ofHom i))
          (Type (u + 1))).app (∏ᶜ F) ≫
          ((sheafSections (Scheme.ProEt.topology (Spec (.of K'))) (Type (u + 1))).obj
            (op (Scheme.ProEt.mk (𝟙 (Spec (.of K')))))).map
              ((Scheme.proEtaleSheafInverseImage (Spec.map (CommRingCat.ofHom i))
                (Type (u + 1))).map (Pi.π F k))) := by
  have : RepresentablyFlat (Scheme.proEtaleBaseChange
      (Spec.map (CommRingCat.ofHom i))) := flat_of_preservesFiniteLimits _
  have : AB5OfSize.{u, u + 1} (Type (u + 1)) :=
    AB5OfSize_shrink.{u, u + 1, u + 1, u + 1} _
  have : PreservesFiniteLimits (Scheme.proEtaleSheafInverseImage
      (Spec.map (CommRingCat.ofHom i)) (Type (u + 1))) := by
    dsimp [Scheme.proEtaleSheafInverseImage]
    infer_instance
  refine ⟨inferInstance, ?_, ?_⟩
  · exact (geometricFieldEvaluationComparison _ _).naturality a
  · intro k
    exact (geometricFieldEvaluationComparison _ _).naturality (Pi.π F k)


end AlgebraicGeometry.ProEtale
