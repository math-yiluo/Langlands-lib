import Langlands.GroupScheme.IntegralModel.GreenbergPointModelCases
import Langlands.GroupScheme.IntegralModel.EqualCharacteristicGreenberg.CoefficientField
import Langlands.GroupScheme.IntegralModel.EqualCharacteristicGreenberg.WeilPoints
import Langlands.GroupScheme.IntegralModel.EqualCharacteristicGreenberg.Connected
import Langlands.GroupScheme.AffineWeilSmooth
import Langlands.AlgebraicGeometry.PointedConnectedComponentGeometry

/-! # Greenberg point models over equal-characteristic discrete valuation rings

A coefficient field `σ : k → R/𝔪ⁿ` makes the congruence quotient a finite `k`-algebra, and
the model of a smooth affine group is the affine Weil restriction of its base change along
`k → R/𝔪ⁿ` (Kaletha–Prasad, paragraph before Theorem A.4.19). -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.IntegralModel.EqualCharacteristicGreenberg

open Langlands.Algebra Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology

section SpecialFibre

variable {B : Type u} [CommRing B] (k : Type u) [Field k] [Algebra B k]
  (Y : Over (Spec (CommRingCat.of B))) [IsAffine Y.left]

/-- The fibre of an affine scheme over `Spec B` along `Spec k → Spec B` is the spectrum
of `k ⊗[B] O`, `O` its global-section ring. -/
theorem isPullback_specialFibre :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom :
          AffineCoordinateRing B Y →+* k ⊗[B] AffineCoordinateRing B Y)) ≫
        (affineSchemeOverIso B Y).inv.left)
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
          k →+* k ⊗[B] AffineCoordinateRing B Y)))
      Y.hom (Spec.map (CommRingCat.ofHom (algebraMap B k))) := by
  have h1 := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct B k (AffineCoordinateRing B Y))).flip
  have : IsIso (affineSchemeOverIso B Y).inv.left :=
    (Over.forget _).map_isIso (affineSchemeOverIso B Y).inv
  have h2 : IsPullback (affineSchemeOverIso B Y).inv.left
      (Spec.map (CommRingCat.ofHom (algebraMap B (AffineCoordinateRing B Y)))) Y.hom
      (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [Category.comp_id]
      exact Over.w (affineSchemeOverIso B Y).inv⟩
  simpa only [Category.comp_id] using h1.paste_horiz h2

end SpecialFibre

section BaseChange

variable {R B : Type u} [CommRing R] [CommRing B]
  (q : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
  (Z : GroupScheme (Spec (CommRingCat.of R)))

theorem isAffine_baseChange [IsAffineHom Z.X.hom] :
    IsAffine ((GroupScheme.baseChange q).obj Z).X.left := by
  change IsAffine (pullback Z.X.hom q)
  exact isAffine_of_isAffineHom (pullback.snd Z.X.hom q)

theorem smooth_baseChange [Smooth Z.X.hom] :
    Smooth ((GroupScheme.baseChange q).obj Z).X.hom := by
  change Smooth (pullback.snd Z.X.hom q)
  infer_instance

end BaseChange

attribute [local instance] isAffine_baseChange smooth_baseChange

section Model

variable {R k B : Type u} [CommRing R] [Field k] [IsAlgClosed k] [CommRing B]
  [Algebra k B] [Module.Finite k B] [Algebra B k] [IsScalarTower k B k]
  (q : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))

/-- **Geometric connectedness.** The Weil restriction of the base change of a smooth
affine geometrically connected group is geometrically connected. Its special fibre over
`B` is connected (the original group is geometrically connected), so the Weil
restriction is connected (`connectedSpace_weilRestriction`), hence geometrically
connected over the algebraically closed field `k`. -/
theorem geometricallyConnected_weilRestriction
    (hnil : IsNilpotent (RingHom.ker (algebraMap B k)))
    (Z : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom Z.X.hom] [Smooth Z.X.hom]
    [hconn : GeometricallyConnected Z.X.hom] :
    GeometricallyConnected
      (AffineWeil.groupScheme k B ((GroupScheme.baseChange q).obj Z)).X.hom := by
  let ZB := (GroupScheme.baseChange q).obj Z
  have t : IsPullback (pullback.fst Z.X.hom q) ZB.X.hom Z.X.hom q :=
    IsPullback.of_hasPullback Z.X.hom q
  have hsq := (isPullback_specialFibre k ZB.X).paste_horiz t
  have hA : ConnectedSpace (PrimeSpectrum (k ⊗[B] AffineCoordinateRing B ZB.X)) :=
    hconn.geometrically_connectedSpace _ _ _ hsq
  let e : AffineCoordinateRing B ZB.X →ₐ[B] B :=
    (affineSchemePointEquiv B ZB.X B
      ((ringTestSelfIso B).hom ≫ (1 : rationalPoints ZB))).toAlgHom
  have hW : ConnectedSpace
      (PrimeSpectrum (WeilRestrictionFiniteType k B (AffineCoordinateRing B ZB.X))) :=
    connectedSpace_weilRestriction k B _ hnil e
  have hG : ConnectedSpace (AffineWeil.groupScheme k B ZB).X.left := hW
  exact @geometricallyConnected_of_connected_isAlgClosed k _ _ _
    (AffineWeil.groupScheme k B ZB).X.hom hG

/-- **The point model over a coefficient field.** For a finite `k`-algebra `B` whose
residue map has nilpotent kernel and is a retraction of `k → B`, the affine Weil
restriction along `k → B` of the base change of a smooth affine group is a point model
with all the conclusions of `HasGreenbergPointModel`. -/
theorem exists_pointModel (hnil : IsNilpotent (RingHom.ker (algebraMap B k)))
    (X : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom X.X.hom]
    (hX : Smooth X.X.hom) :
    ∃ (G : GroupScheme (Spec (CommRingCat.of k)))
      (eX : rationalPoints ((GroupScheme.baseChange q).obj X) ≃* rationalPoints G),
      IsAffineHom G.X.hom ∧ Smooth G.X.hom ∧
      ∀ (Z : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom Z.X.hom],
        Smooth Z.X.hom → ∀ h : Z ⟶ X,
        ∃ (GZ : GroupScheme (Spec (CommRingCat.of k)))
          (eZ : rationalPoints ((GroupScheme.baseChange q).obj Z) ≃* rationalPoints GZ)
          (g : GZ ⟶ G),
          IsAffineHom GZ.X.hom ∧ Smooth GZ.X.hom ∧
          (∀ z, eX (rationalPoints.map ((GroupScheme.baseChange q).map h) z) =
            rationalPoints.map g (eZ z)) ∧
          (GeometricallyConnected Z.X.hom → GeometricallyConnected GZ.X.hom) := by
  have : Smooth X.X.hom := hX
  refine ⟨AffineWeil.groupScheme k B ((GroupScheme.baseChange q).obj X),
    (weilRationalPointsEquiv k B _).symm, isAffineHom_of_isAffine _,
    AffineWeil.smooth_groupScheme k B _, ?_⟩
  intro Z _ hZ h
  have : Smooth Z.X.hom := hZ
  refine ⟨AffineWeil.groupScheme k B ((GroupScheme.baseChange q).obj Z),
    (weilRationalPointsEquiv k B _).symm,
    AffineWeil.map k B ((GroupScheme.baseChange q).map h), isAffineHom_of_isAffine _,
    AffineWeil.smooth_groupScheme k B _, fun z => ?_, fun hconn => ?_⟩
  · apply (weilRationalPointsEquiv k B _).injective
    rw [weilRationalPointsEquiv_map, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  · have : GeometricallyConnected Z.X.hom := hconn
    exact geometricallyConnected_weilRestriction q hnil Z

end Model

end Langlands.GroupScheme.IntegralModel.EqualCharacteristicGreenberg

namespace Langlands.GroupScheme.IntegralModel

open EqualCharacteristicGreenberg

/-- **Kaletha–Prasad, Theorem A.4.19, equal characteristic.** Over a discrete valuation
ring with algebraically closed residue field of the same characteristic, every smooth
affine group scheme has a Greenberg point model at every positive level. -/
theorem equalCharacteristicGreenbergPointModel :
    EqualCharacteristicGreenbergPointModelStatement.{u} := by
  intro R _ _ _ _ hchar n X _ hX
  obtain ⟨σ, hσ⟩ := exists_coefficientField R hchar n
  let : Algebra (IsLocalRing.ResidueField R) (congruenceRing R n) := σ.toAlgebra
  let : Algebra (congruenceRing R n) (IsLocalRing.ResidueField R) :=
    (congruenceResidue R n).toAlgebra
  have : Module.Finite (IsLocalRing.ResidueField R) (congruenceRing R n) :=
    congruenceRing_finite R n σ hσ
  have : IsScalarTower (IsLocalRing.ResidueField R) (congruenceRing R n)
      (IsLocalRing.ResidueField R) :=
    IsScalarTower.of_algebraMap_eq' hσ.symm
  exact exists_pointModel (congruenceBaseMap R n) (isNilpotent_ker_congruenceResidue R n) X hX

end Langlands.GroupScheme.IntegralModel
