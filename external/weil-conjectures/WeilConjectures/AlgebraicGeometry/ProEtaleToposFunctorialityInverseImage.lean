/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying

/-!
# Functoriality of the inverse image on small pro-étale topoi

Source: Weil conjectures blueprint, `det-pe-topos-functoriality-inverse-image`, clauses 1–5
(blueprint: det-pe-topos-functoriality-inverse-image).

## Main definitions

* `setPullback`: the sheafified left Kan extension on set-valued sheaves.
* `setPullbackAdjunction`: its constructed adjunction to the existing `lowerStar` on sets.
* `setPullbackComp`: the canonical composition comparison, conjugate to `lowerStarComp`.

## Main statements

* `toposFunctorialityInverseImage`: covering families, finite limits, the adjunction,
  colimits, abelian underlying sets and exactness, and compatibility of composition.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- The inverse image on set-valued sheaves, as sheafified left Kan extension.

Source: Weil conjectures blueprint, clause 2
(blueprint: proposition-topos-functoriality--2). The direct image is the existing
`lowerStar (Type (u + 1)) f`, whose definition is restriction along base change. -/
noncomputable def setPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf (Scheme.ProEt.topology Y) (Type (u + 1)) ⥤
      Sheaf (Scheme.ProEt.topology X) (Type (u + 1)) :=
  Functor.sheafPullbackConstruction.sheafPullback
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) (Type (u + 1))
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)

/-- The constructed Kan-extension/sheafification adjunction on set-valued sheaves.

Source: Weil conjectures blueprint, clause 2
(blueprint: proposition-topos-functoriality--2). -/
noncomputable def setPullbackAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    setPullback f ⊣ lowerStar (Type (u + 1)) f :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) (Type (u + 1))
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)

/-- The canonical composition comparison for set-valued inverse images.

Source: Weil conjectures blueprint, clause 5
(blueprint: proposition-topos-functoriality--3). It is the conjugate of the existing
pushforward comparison, hence is compatible with the constructed adjunctions. The direct
image comparison in the direction of clause 5 is `(lowerStarComp (Type (u + 1)) f g).symm`.
The underlying site comparison is the canonical pullback associativity isomorphism. -/
noncomputable def setPullbackComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    setPullback (f ≫ g) ≅ setPullback g ⋙ setPullback f :=
  (conjugateIsoEquiv ((setPullbackAdjunction g).comp (setPullbackAdjunction f))
    (setPullbackAdjunction (f ≫ g))).symm (lowerStarComp (Type (u + 1)) f g)

/-- The geometric morphism attached to an arbitrary morphism of schemes.

Source: Weil conjectures blueprint, clauses 1–5
(blueprint: proposition-topos-functoriality).

Proof:
1. Base change preserves weakly étale objects and coverings by stability under base change
   (proposition-topos-functoriality--2, proposition-topos-functoriality).
   The small sites have terminal objects and fibre products
   (proposition-topos-functoriality, proposition-topos-functoriality). Their universal properties
   show that base change preserves both, hence finite limits.
2. Restriction along base change preserves the sheaf equalizer, since it preserves covers
   and fibre products. Compose the left Kan extension adjunction with sheafification
   (proposition-topos-functoriality). This is precisely
   `setPullbackAdjunction`; the same construction in abelian groups is the recorded
   `upperStarLowerStarAdjunction` (proposition-topos-functoriality--2).
3. The adjunction gives all colimits (situation-conventions).
   The opposite comma category at a site object is filtered, using finite limits of the
   source site and their preservation in step 1. Thus the Kan extension preserves finite
   limits of sets (situation-conventions). Inclusion of sheaves
   preserves limits (proposition-topos-functoriality), and sheafification
   preserves finite limits (situation-conventions). Their composite is
   left exact, giving the geometric morphism.
4. Apply proposition-topos-functoriality, transporting the site presentation
   to its larger universe when necessary. Lifting the set adjunction to abelian group
   objects identifies the underlying sets of `upperStar AddCommGrpCat f` with set inverse
   image, including the group operations. This is the pullback of
   proposition-topos-functoriality--2. Finite limits give kernels and the abelian adjunction gives
   cokernels, so it is exact (proposition-topos-functoriality--2).
5. The canonical associativity isomorphism for fibre products gives `lowerStarComp` on
   sections, naturally in the site object and sheaf (proposition-topos-functoriality--3).
   Compose adjunctions (proposition-topos-functoriality). Taking the conjugate of the
   direct image comparison gives `setPullbackComp`, exactly as for abelian pullback
   (proposition-topos-functoriality--3). The conjugation unit equation
   (situation-conventions) gives the last displayed equality, proving
   compatibility with the adjunctions and thus composition of geometric morphisms. -/
theorem toposFunctorialityInverseImage {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (PreservesFiniteLimits (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) ∧
      ∀ (V : Y.ProEt) (R : Presieve V), R ∈ Scheme.ProEt.precoverage Y V →
        Presieve.map (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) R ∈
          Scheme.ProEt.precoverage X
            ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj V)) ∧
    Nonempty (setPullback f ⊣ lowerStar (Type (u + 1)) f) ∧
    PreservesColimits (setPullback f) ∧
    PreservesFiniteLimits (setPullback f) ∧
    (Nonempty (upperStar AddCommGrpCat.{u + 1} f ⋙
        sheafCompose (Scheme.ProEt.topology X) (forget AddCommGrpCat.{u + 1}) ≅
      sheafCompose (Scheme.ProEt.topology Y) (forget AddCommGrpCat.{u + 1}) ⋙
        setPullback f) ∧
      PreservesFiniteLimits (upperStar AddCommGrpCat.{u + 1} f) ∧
      PreservesFiniteColimits (upperStar AddCommGrpCat.{u + 1} f)) ∧
    ∀ F : Sheaf (Scheme.ProEt.topology Z) (Type (u + 1)),
      (setPullbackAdjunction (f ≫ g)).unit.app F ≫
          (lowerStar (Type (u + 1)) (f ≫ g)).map ((setPullbackComp f g).hom.app F) =
        ((setPullbackAdjunction g).comp (setPullbackAdjunction f)).unit.app F ≫
          (lowerStarComp (Type (u + 1)) f g).hom.app
            ((setPullback g ⋙ setPullback f).obj F) := by
  have hlimits : PreservesFiniteLimits (setPullback f) := by
    have : PreservesFiniteLimits
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.lan :
          (Y.ProEtᵒᵖ ⥤ Type (u + 1)) ⥤ X.ProEtᵒᵖ ⥤ Type (u + 1)) := by
      let : AB5OfSize.{u, u + 1} (Type (u + 1)) :=
        AB5OfSize_shrink.{u, u + 1, u + 1, u + 1} (Type (u + 1))
      apply preservesFiniteLimits_op_lan_of_flat
    unfold setPullback Functor.sheafPullbackConstruction.sheafPullback
    infer_instance
  refine ⟨⟨inferInstance, ?_⟩, ⟨setPullbackAdjunction f⟩,
    (setPullbackAdjunction f).leftAdjoint_preservesColimits, hlimits, ⟨?_,
    inferInstance, inferInstance⟩, ?_⟩
  · intro V R hR
    obtain ⟨ι, V, a, rfl⟩ := R.exists_eq_ofArrows
    rw [Presieve.map_ofArrows]
    rw [Scheme.ProEt.mem_precoverage_iff] at hR ⊢
    rw [Presieve.map_ofArrows] at hR ⊢
    exact Precoverage.mem_coverings_of_isPullback (fun i ↦ (a i).left) hR
      (pullback.fst _ f) _ (fun i ↦ pullback.fst (V i).hom f)
      fun i ↦ (MorphismProperty.Over.isPullback_map_left f (a i)).flip
  · let := Scheme.ProEt.isContinuous_overPullback f
    let : PreservesFiniteLimits
        (Functor.sheafPullbackConstruction.sheafPullback
          (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) (Type (u + 1))
          (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)) := hlimits
    exact sitePullback_abelian_underlying_of_hasSheafify.{u + 1, u, 0}
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f)
  · intro F
    exact (unit_conjugateEquiv_symm
      ((setPullbackAdjunction g).comp (setPullbackAdjunction f))
      (setPullbackAdjunction (f ≫ g))
      (lowerStarComp (Type (u + 1)) f g).hom F).symm

end AlgebraicGeometry.ProEtale
