import Langlands.AbelianScheme.RelativeEndomorphismAffineHomSchemePieces
import Langlands.AbelianScheme.RelativeEndomorphismAffineExtension
import Langlands.AbelianScheme.RelativeIntegralActionUniversal

/-! # Integral-action schemes for projective abelian schemes over noetherian affine bases -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module Opposite

universe u uI uO

namespace Langlands.AbelianScheme.ProjectiveIntegralAction

open Langlands.GroupScheme.Cartier

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
    (B : Langlands.AbelianScheme (Spec (CommRingCat.of R)))
    (hB : Langlands.AlgebraicGeometry.IsHProjective B.X.hom)

include hB in
private theorem exists_endomorphismScheme :
    ∃ E : Over (Spec (CommRingCat.of R)),
      IsSeparated E.hom ∧ LocallyOfFiniteType E.hom ∧ FormallyUnramified E.hom ∧
        Nonempty
          ((relativeHomFunctor B.toCommGroupScheme B.toCommGroupScheme ⋙
              forget AddCommGrpCat.{u}) ≅ yoneda.obj E) := by
  obtain ⟨E, hsep, hlft, hunram, ⟨e⟩, _⟩ :=
    AffineHomSchemePieces.affineHomSchemePieces R B hB
  exact ⟨E, hsep, hlft, hunram, nonempty_iso_yoneda_of_affine e⟩

/-- A chosen actual endomorphism scheme, retaining the geometry of the published construction. -/
def endomorphismScheme : Over (Spec (CommRingCat.of R)) :=
  (exists_endomorphismScheme R B hB).choose

instance endomorphismScheme_isSeparated :
    IsSeparated (endomorphismScheme R B hB).hom :=
  (exists_endomorphismScheme R B hB).choose_spec.1

instance endomorphismScheme_locallyOfFiniteType :
    LocallyOfFiniteType (endomorphismScheme R B hB).hom :=
  (exists_endomorphismScheme R B hB).choose_spec.2.1

instance endomorphismScheme_formallyUnramified :
    FormallyUnramified (endomorphismScheme R B hB).hom :=
  (exists_endomorphismScheme R B hB).choose_spec.2.2.1

instance endomorphismScheme_isLocallyNoetherian :
    IsLocallyNoetherian (endomorphismScheme R B hB).left :=
  LocallyOfFiniteType.isLocallyNoetherian (endomorphismScheme R B hB).hom

/-- The chosen scheme represents the actual relative endomorphism presheaf on all tests. -/
def endomorphismSchemeIso :
    (relativeHomFunctor B.toCommGroupScheme B.toCommGroupScheme ⋙
        forget AddCommGrpCat.{u}) ≅ yoneda.obj (endomorphismScheme R B hB) :=
  (exists_endomorphismScheme R B hB).choose_spec.2.2.2.some

/-- Restrict the same representation to the full locally noetherian test category. -/
def endomorphismSchemeLocallyNoetherianIso :
    (locallyNoetherianTestInclusion (Spec (CommRingCat.of R))).op ⋙
        relativeHomFunctor B.toCommGroupScheme B.toCommGroupScheme ⋙
          forget AddCommGrpCat.{u} ≅
      (locallyNoetherianTestInclusion (Spec (CommRingCat.of R))).op ⋙
        yoneda.obj (endomorphismScheme R B hB) :=
  Functor.isoWhiskerLeft
    (locallyNoetherianTestInclusion (Spec (CommRingCat.of R))).op
    (endomorphismSchemeIso R B hB)

variable {I : Type uI} [Fintype I] {O : Type uO} [Ring O] (b : Basis I ℤ O)

/-- The actual finite equation scheme classifying integral actions on pullbacks of `B`. -/
def scheme : Over (Spec (CommRingCat.of R)) :=
  (relativeIntegralActionLocusTest (endomorphismScheme R B hB) B b
    (endomorphismSchemeLocallyNoetherianIso R B hB)).obj

/-- The integral-action scheme sits inside the finite actual endomorphism-tuple scheme. -/
def inclusion : scheme R B hB b ⟶ ∏ᶜ fun _ : I => endomorphismScheme R B hB :=
  relativeIntegralActionLocusInclusion B b (endomorphismScheme R B hB)
    (endomorphismSchemeLocallyNoetherianIso R B hB)
    (relativeEndomorphismPower_isLocallyNoetherian (I := I) (endomorphismScheme R B hB))

instance inclusion_isClosedImmersion :
    IsClosedImmersion (inclusion R B hB b).left :=
  inferInstanceAs (IsClosedImmersion
    (relativeIntegralActionLocusInclusion B b (endomorphismScheme R B hB)
      (endomorphismSchemeLocallyNoetherianIso R B hB)
      (relativeEndomorphismPower_isLocallyNoetherian
        (I := I) (endomorphismScheme R B hB))).left)

instance scheme_locallyOfFiniteType : LocallyOfFiniteType (scheme R B hB b).hom := by
  change LocallyOfFiniteType
    (relativeIntegralActionLocus B b (endomorphismScheme R B hB)
      (endomorphismSchemeLocallyNoetherianIso R B hB)
      (relativeEndomorphismPower_isLocallyNoetherian
        (I := I) (endomorphismScheme R B hB))).hom
  infer_instance

instance scheme_isSeparated : IsSeparated (scheme R B hB b).hom := by
  change IsSeparated
    (relativeIntegralActionLocus B b (endomorphismScheme R B hB)
      (endomorphismSchemeLocallyNoetherianIso R B hB)
      (relativeEndomorphismPower_isLocallyNoetherian
        (I := I) (endomorphismScheme R B hB))).hom
  infer_instance

instance scheme_isLocallyNoetherian : IsLocallyNoetherian (scheme R B hB b).left :=
  LocallyOfFiniteType.isLocallyNoetherian (scheme R B hB b).hom

/-- Natural representability of actual integral actions, with no supplied End representative. -/
def schemeIso :
    (locallyNoetherianTestInclusion (Spec (CommRingCat.of R))).op ⋙
        relativeIntegralActionFunctor B b ≅
      (locallyNoetherianTestInclusion (Spec (CommRingCat.of R))).op ⋙
        uliftYoneda.{max uI uO}.obj (scheme R B hB b) :=
  relativeIntegralActionLocusTestIso (endomorphismScheme R B hB) B b
    (endomorphismSchemeLocallyNoetherianIso R B hB)

/-- The universal actual action is on the actual pullback of `B` to this scheme. -/
def universalAction :
    O →+* CategoryTheory.End ((baseChange (scheme R B hB b).hom).obj B) :=
  relativeIntegralActionUniversal B b (endomorphismScheme R B hB)
    (endomorphismSchemeLocallyNoetherianIso R B hB)

/-- Every actual action on a locally noetherian test has a unique actual classifying map. -/
theorem universalAction_existsUnique
    (T : ObjectProperty.FullSubcategory
      (fun T : Over (Spec (CommRingCat.of R)) => IsLocallyNoetherian T.left))
    (a : O →+* CategoryTheory.End ((baseChange T.obj.hom).obj B)) :
    ∃! f : T.obj ⟶ scheme R B hB b,
      (relativeEndRestrict B f).comp (universalAction R B hB b) = a :=
  relativeIntegralActionUniversal_existsUnique B b (endomorphismScheme R B hB)
    (endomorphismSchemeLocallyNoetherianIso R B hB) T a

end Langlands.AbelianScheme.ProjectiveIntegralAction
