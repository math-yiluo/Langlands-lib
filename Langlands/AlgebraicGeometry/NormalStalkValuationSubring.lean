import Langlands.AlgebraicGeometry.AffineStalkModelNeighbourhood
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Normal one-dimensional stalks as distinct valuation subrings -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry

/-- The image of the local ring in the function field of an integral scheme. -/
def stalkImageSubring (X : Scheme.{u}) [IsIntegral X] (x : X) :
    Subring X.functionField :=
  (algebraMap (X.presheaf.stalk x) X.functionField).range

/-- The local ring is canonically isomorphic to its image in the function field. -/
def stalkEquivImage (X : Scheme.{u}) [IsIntegral X] (x : X) :
    X.presheaf.stalk x ≃+* stalkImageSubring X x :=
  RingEquiv.ofBijective
    (algebraMap (X.presheaf.stalk x) X.functionField).rangeRestrict
    ⟨fun _ _ h ↦ IsFractionRing.injective (X.presheaf.stalk x) X.functionField
      (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩

@[simp]
theorem coe_stalkEquivImage (X : Scheme.{u}) [IsIntegral X] (x : X)
    (a : X.presheaf.stalk x) :
    (stalkEquivImage X x a : X.functionField) =
      algebraMap (X.presheaf.stalk x) X.functionField a := rfl

@[simp]
theorem algebraMap_stalkEquivImage_symm (X : Scheme.{u}) [IsIntegral X] (x : X)
    (a : stalkImageSubring X x) :
    algebraMap (X.presheaf.stalk x) X.functionField
      ((stalkEquivImage X x).symm a) = (a : X.functionField) :=
  congrArg Subtype.val ((stalkEquivImage X x).apply_symm_apply a)

set_option backward.isDefEq.respectTransparency false in
/-- Separatedness makes different points give different local subrings of
the function field. -/
theorem stalkImageSubring_injective (X : Scheme.{u}) [IsIntegral X] [X.IsSeparated] :
    Function.Injective (stalkImageSubring X) := by
  intro x y h
  let e : X.presheaf.stalk y ≃+* X.presheaf.stalk x :=
    (stalkEquivImage X y).trans
      ((RingEquiv.subringCongr h.symm).trans (stalkEquivImage X x).symm)
  let er : X.presheaf.stalk y →+* X.presheaf.stalk x := e.toRingHom
  have : IsLocalHom er := IsLocalHom.of_surjective er e.surjective
  have he : (algebraMap (X.presheaf.stalk x) X.functionField).comp er =
      algebraMap (X.presheaf.stalk y) X.functionField := by
    ext a
    simp [er, e]
  let j := Spec.map (CommRingCat.ofHom
    (algebraMap (X.presheaf.stalk x) X.functionField))
  have : IsDominant j := isDominant_specMap_of_injective _
    (IsFractionRing.injective (X.presheaf.stalk x) X.functionField)
  have hh : X.fromSpecStalk x =
      Spec.map (CommRingCat.ofHom er) ≫ X.fromSpecStalk y := by
    apply ext_of_isDominant j
    dsimp only [j]
    have he' : CommRingCat.ofHom er ≫
        CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) =
        CommRingCat.ofHom (algebraMap (X.presheaf.stalk y) X.functionField) := by
      ext a
      exact congrArg (fun k : X.presheaf.stalk y →+* X.functionField ↦ k a) he
    rw [← Spec.map_comp_assoc, he']
    exact (Scheme.SpecMap_stalkSpecializes_fromSpecStalk
      (genericPoint_specializes x)).trans
        (Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes y)).symm
  have hpoint := congrArg
    (fun k : Spec (X.presheaf.stalk x) ⟶ X ↦
      k (IsLocalRing.closedPoint (X.presheaf.stalk x))) hh
  have hp : Spec.map (CommRingCat.ofHom er)
      (IsLocalRing.closedPoint (X.presheaf.stalk x)) =
      IsLocalRing.closedPoint (X.presheaf.stalk y) := by
    change PrimeSpectrum.comap er _ = _
    exact IsLocalRing.comap_closedPoint er
  rw [Scheme.Hom.comp_apply, Scheme.fromSpecStalk_closedPoint] at hpoint
  exact hpoint.trans ((congrArg (X.fromSpecStalk y) hp).trans
    Scheme.fromSpecStalk_closedPoint)

/-- A stalk fills the function field exactly when it is a field. -/
theorem stalkImageSubring_eq_top_iff_isField
    (X : Scheme.{u}) [IsIntegral X] (x : X) :
    stalkImageSubring X x = ⊤ ↔ IsField (X.presheaf.stalk x) :=
  RingHom.range_eq_top.trans IsFractionRing.surjective_iff_isField

@[simp]
theorem stalkImageSubring_genericPoint (X : Scheme.{u}) [IsIntegral X] :
    stalkImageSubring X (genericPoint X) = ⊤ :=
  (stalkImageSubring_eq_top_iff_isField X _).mpr
    (inferInstance : Field X.functionField).toIsField

/-- On a separated integral scheme, precisely the generic stalk is a field. -/
theorem isField_stalk_iff_eq_genericPoint
    (X : Scheme.{u}) [IsIntegral X] [X.IsSeparated] (x : X) :
    IsField (X.presheaf.stalk x) ↔ x = genericPoint X := by
  constructor
  · intro hx
    apply stalkImageSubring_injective X
    exact ((stalkImageSubring_eq_top_iff_isField X x).mpr hx).trans
      (stalkImageSubring_genericPoint X).symm
  · rintro rfl
    exact (inferInstance : Field X.functionField).toIsField

/-- A normal noetherian local domain of Krull dimension at most one is a
valuation ring, including the field case. -/
theorem valuationRing_of_normal_dim_le_one
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [IsIntegrallyClosed A] (hA : ringKrullDim A ≤ 1) : ValuationRing A := by
  have : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.mpr hA
  apply ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain A).out 2 4).mpr
  refine ⟨inferInstance, fun P hP hprime ↦ ?_⟩
  exact IsLocalRing.eq_maximalIdeal (hprime.isMaximal_of_ne_bot hP)

/-- The nonfield case is a discrete valuation ring. -/
theorem discreteValuationRing_of_normal_dim_le_one
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [IsIntegrallyClosed A] (hA : ringKrullDim A ≤ 1) (hnf : ¬ IsField A) :
    IsDiscreteValuationRing A := by
  have : ValuationRing A := valuationRing_of_normal_dim_le_one hA
  exact ((IsDiscreteValuationRing.TFAE A hnf).out 1 2).mpr this

/-- A valuation stalk is realized as its actual image subring in the
scheme's function field. -/
def stalkValuationSubring (X : Scheme.{u}) [IsIntegral X] (x : X)
    [ValuationRing (X.presheaf.stalk x)] : ValuationSubring X.functionField :=
  ValuationSubring.ofSubring (stalkImageSubring X x) fun a ↦
    ValuationRing.isInteger_or_isInteger (X.presheaf.stalk x) a

@[simp]
theorem stalkValuationSubring_toSubring (X : Scheme.{u}) [IsIntegral X] (x : X)
    [ValuationRing (X.presheaf.stalk x)] :
    (stalkValuationSubring X x).toSubring = stalkImageSubring X x := rfl

/-- The valuation subring attached to a normal stalk of dimension at most one. -/
def normalStalkValuationSubring
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] (x : X)
    (hn : IsIntegrallyClosed (X.presheaf.stalk x))
    (hd : ringKrullDim (X.presheaf.stalk x) ≤ 1) : ValuationSubring X.functionField := by
  letI := hn
  letI := valuationRing_of_normal_dim_le_one hd
  exact stalkValuationSubring X x

@[simp]
theorem normalStalkValuationSubring_toSubring
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] (x : X)
    (hn : IsIntegrallyClosed (X.presheaf.stalk x))
    (hd : ringKrullDim (X.presheaf.stalk x) ≤ 1) :
    (normalStalkValuationSubring X x hn hd).toSubring = stalkImageSubring X x := rfl

/-- The valuation subring is the local ring itself, with its specified
embedding in the function field. -/
def normalStalkEquivValuationSubring
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] (x : X)
    (hn : IsIntegrallyClosed (X.presheaf.stalk x))
    (hd : ringKrullDim (X.presheaf.stalk x) ≤ 1) :
    X.presheaf.stalk x ≃+* normalStalkValuationSubring X x hn hd :=
  stalkEquivImage X x

/-- Away from the generic point the valuation subring is a DVR. -/
theorem normalStalkValuationSubring_isDiscreteValuationRing
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] [X.IsSeparated] (x : X)
    (hn : IsIntegrallyClosed (X.presheaf.stalk x))
    (hd : ringKrullDim (X.presheaf.stalk x) ≤ 1) (hx : x ≠ genericPoint X) :
    IsDiscreteValuationRing (normalStalkValuationSubring X x hn hd) := by
  have := hn
  have : IsDiscreteValuationRing (X.presheaf.stalk x) :=
    discreteValuationRing_of_normal_dim_le_one hd
      (fun h ↦ hx ((isField_stalk_iff_eq_genericPoint X x).mp h))
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (normalStalkEquivValuationSubring X x hn hd)

end Langlands.AlgebraicGeometry
