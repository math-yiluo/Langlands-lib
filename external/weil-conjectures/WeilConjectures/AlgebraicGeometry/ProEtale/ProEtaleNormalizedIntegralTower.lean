/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCompletedCoefficientData
public import Mathlib.Topology.Algebra.Ring.Ideal
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement

/-!
# The normalized integral quotient cone
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar

private noncomputable def normalizedContinuousMap
    {R S : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    (f : R →+* S) (hf : Continuous f) :
    Mon.mk (Profinite.continuousMapRingObj.{u} R) ⟶
      Mon.mk (Profinite.continuousMapRingObj S) :=
  Mon.ofHom ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (Profinite.continuousMapRingSheafMap f hf))

private theorem normalizedConstants_naturality
    {R S : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    (f : R →+* S) (hf : Continuous f) :
    sfbConstantToContinuous R ≫ (normalizedContinuousMap.{u} f hf).hom =
      (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map
        (AddCommGrpCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
          (f.comp ULift.ringEquiv.toRingHom)).toAddMonoidHom) ≫
        sfbConstantToContinuous S := by
  let J := coherentTopology Profinite.{u}
  let adj := sheafificationAdjunction J Ab.{u + 1}
  let a := AddCommGrpCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
    (f.comp ULift.ringEquiv.toRingHom)).toAddMonoidHom
  change sfbConstantToContinuous R ≫ (normalizedContinuousMap f hf).hom =
    (presheafToSheaf J Ab.{u + 1}).map
      ((Functor.const Profinite.{u}ᵒᵖ).map a) ≫ sfbConstantToContinuous S
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_right, adj.homEquiv_naturality_left]
  change (adj.homEquiv _ _) ((adj.homEquiv _ _).symm _) ≫ _ =
    _ ≫ (adj.homEquiv _ _) ((adj.homEquiv _ _).symm _)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rfl

private noncomputable def normalizedFiniteIso (R : Type) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [DiscreteTopology R] [Finite R] :
    sfbPointConstantRing.{u}.obj (RingCat.of (ULift.{u + 1} R)) ≅
      Mon.mk (Profinite.continuousMapRingObj R) := by
  let e := completedFinitePointIso.{u} R
  have he : @IsMonHom _ _ _ _ _
      ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).monObjObj
        (AddCommGrpCat.of (ULift.{u + 1} R))) _ e.hom := by
    rw [constantSheafRingMonObj]
    exact completedFinitePointIso_isMonHom R
  exact Mon.mkIso e he.one_hom he.mul_hom

private theorem normalizedFiniteIso_naturality
    {R S : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [DiscreteTopology R] [Finite R]
    [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    [DiscreteTopology S] [Finite S] (f : R →+* S) :
    sfbPointConstantRing.map (RingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
        (f.comp ULift.ringEquiv.toRingHom))) ≫ (normalizedFiniteIso.{u} S).hom =
      (normalizedFiniteIso R).hom ≫
        normalizedContinuousMap f continuous_of_discreteTopology := by
  apply Mon.Hom.ext
  exact (normalizedConstants_naturality f continuous_of_discreteTopology).symm

private noncomputable def normalizedSequenceCompIso
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {T : ℕ → C} (t : ∀ n, T (n + 1) ⟶ T n) :
    Functor.ofOpSequence t ⋙ F ≅
      Functor.ofOpSequence (X := fun n ↦ F.obj (T n)) (fun n ↦ F.map (t n)) := by
  let a : Functor.ofOpSequence t ⋙ F ⟶
      Functor.ofOpSequence (X := fun n ↦ F.obj (T n)) (fun n ↦ F.map (t n)) :=
    NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (fun n ↦ by
      simp only [Functor.comp_map, Functor.ofOpSequence_map_homOfLE_succ,
        Category.comp_id, Category.id_comp])
  have (n : ℕᵒᵖ) : IsIso (a.app n) := inferInstanceAs (IsIso (𝟙 _))
  have : IsIso a := NatIso.isIso_of_isIso_app a
  exact asIso a

private noncomputable def normalizedContinuousTower
    (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (I : Ideal R) :
    ℕᵒᵖ ⥤ Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  Functor.ofOpSequence (X := fun n ↦ Mon.mk (Profinite.continuousMapRingObj (R ⧸ I ^ n)))
    (fun n ↦ normalizedContinuousMap
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ n)))
      (continuous_quot_lift _ continuous_quot_mk))

private noncomputable def normalizedContinuousCone
    (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (I : Ideal R) :
    Cone (normalizedContinuousTower.{u} R I) where
  pt := Mon.mk (Profinite.continuousMapRingObj R)
  π := NatTrans.ofOpSequence
    (fun n ↦ normalizedContinuousMap (Ideal.Quotient.mk (I ^ n)) continuous_quot_mk)
    (fun n ↦ by
      simp only [Functor.const_obj_map, normalizedContinuousTower,
        Functor.ofOpSequence_map_homOfLE_succ]
      apply Mon.Hom.ext
      apply Sheaf.hom_ext
      ext S x
      rfl)

private noncomputable def normalizedTowerIso
    (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (I : Ideal R)
    [∀ n : ℕ, Finite (R ⧸ I ^ n)] [∀ n : ℕ, DiscreteTopology (R ⧸ I ^ n)] :
    sfbCoefficientQuotientTower R I ⋙ sfbPointConstantRing ≅
      normalizedContinuousTower.{u} R I := by
  let a : sfbCoefficientQuotientTower R I ⋙ sfbPointConstantRing ⟶
      normalizedContinuousTower.{u} R I :=
    NatTrans.ofOpSequence (fun n ↦ (normalizedFiniteIso (R ⧸ I ^ n)).hom)
      (fun n ↦ by
        simp only [Functor.comp_map, sfbCoefficientQuotientTower,
          normalizedContinuousTower, Functor.ofOpSequence_map_homOfLE_succ]
        exact normalizedFiniteIso_naturality _)
  have (n : ℕᵒᵖ) : IsIso (a.app n) :=
    inferInstanceAs (IsIso (normalizedFiniteIso (R ⧸ I ^ n.unop)).hom)
  have : IsIso a := NatIso.isIso_of_isIso_app a
  exact asIso a

private noncomputable def normalizedQuotientCone
    (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (I : Ideal R)
    [∀ n : ℕ, Finite (R ⧸ I ^ n)] [∀ n : ℕ, DiscreteTopology (R ⧸ I ^ n)] :
    Cone (sfbCoefficientQuotientTower R I ⋙ sfbPointConstantRing.{u}) :=
  (Cone.postcompose (normalizedTowerIso R I).inv).obj (normalizedContinuousCone R I)

private theorem normalizedQuotientCone_constants
    (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (I : Ideal R)
    [∀ n : ℕ, Finite (R ⧸ I ^ n)] [∀ n : ℕ, DiscreteTopology (R ⧸ I ^ n)] (n : ℕ) :
    sfbConstantToContinuous R ≫ ((normalizedQuotientCone.{u} R I).π.app (op n)).hom =
      (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map
        (AddCommGrpCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
          ((Ideal.Quotient.mk (I ^ n)).comp ULift.ringEquiv.toRingHom)).toAddMonoidHom) := by
  let e := normalizedTowerIso.{u} R I
  have hleg : ((normalizedQuotientCone R I).π.app (op n)).hom ≫
      (e.hom.app (op n)).hom =
        (normalizedContinuousMap (Ideal.Quotient.mk (I ^ n)) continuous_quot_mk).hom := by
    rw [← Mon.comp_hom']
    change (((normalizedContinuousCone R I).π.app (op n) ≫ e.inv.app (op n)) ≫
      e.hom.app (op n)).hom = _
    rw [Category.assoc, e.inv_hom_id_app, Category.comp_id]
    rfl
  apply (cancel_mono (e.hom.app (op n)).hom).mp
  rw [Category.assoc, hleg]
  exact normalizedConstants_naturality _ _

private noncomputable def normalizedContinuousCone_isLimit
    (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CompactSpace R] [T2Space R] (I : Ideal R)
    [∀ n : ℕ, Finite (R ⧸ I ^ n)] [∀ n : ℕ, DiscreteTopology (R ⧸ I ^ n)]
    (hsep : ∀ x y : R,
      (∀ n : ℕ, Ideal.Quotient.mk (I ^ n) x = Ideal.Quotient.mk (I ^ n) y) → x = y)
    (X : Scheme.{u}) :
    IsLimit ((upperStarFromPoint X).mapMon.mapCone (normalizedContinuousCone R I)) := by
  let Q (n : ℕ) := R ⧸ I ^ n
  let q (n : ℕ) : R →+* Q n := Ideal.Quotient.mk _
  let t (n : ℕ) : Q (n + 1) →+* Q n :=
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ n))
  have : ∀ n, T2Space (Q n) := fun n ↦ @DiscreteTopology.toT2Space
    (Q n) _ (inferInstanceAs (DiscreteTopology (Q n)))
  have : ∀ n, TotallyDisconnectedSpace (Q n) := fun n ↦
    @TotallySeparatedSpace.totallyDisconnectedSpace (Q n) _
      (@TotallySeparatedSpace.of_discrete (Q n) _ inferInstance)
  have : TotallyDisconnectedSpace R := completedTowerTotallyDisconnected Q
    (fun n ↦ ⟨q n, continuous_quot_mk⟩) hsep
  let c := completedRingTowerCone X R Q q (fun _ ↦ continuous_quot_mk) t
    (fun _ ↦ continuous_of_discreteTopology) (fun _ _ ↦ rfl)
  let hc := completedRingTowerLimit X R Q q (fun _ ↦ continuous_quot_mk) t
    (fun _ ↦ continuous_of_discreteTopology) (fun _ _ ↦ rfl) hsep
    (fun _ ↦ Ideal.Quotient.mk_surjective)
  let F := (upperStarFromPoint X).mapMon
  let e := normalizedSequenceCompIso F
    (T := fun n ↦ Mon.mk (Profinite.continuousMapRingObj.{u} (Q n)))
    (fun n ↦ normalizedContinuousMap (t n) continuous_of_discreteTopology)
  apply (IsLimit.equivOfNatIsoOfIso e (F.mapCone (normalizedContinuousCone R I)) c
    (Cone.ext (Iso.refl _) ?_)).symm hc
  intro n
  change F.map (normalizedContinuousMap (q n.unop) continuous_quot_mk) ≫ 𝟙 _ =
    𝟙 _ ≫ F.map (normalizedContinuousMap (q n.unop) continuous_quot_mk)
  simp only [Category.comp_id, Category.id_comp]

private noncomputable def normalizedQuotientCone_isLimit
    (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CompactSpace R] [T2Space R] (I : Ideal R)
    [∀ n : ℕ, Finite (R ⧸ I ^ n)] [∀ n : ℕ, DiscreteTopology (R ⧸ I ^ n)]
    (hsep : ∀ x y : R,
      (∀ n : ℕ, Ideal.Quotient.mk (I ^ n) x = Ideal.Quotient.mk (I ^ n) y) → x = y)
    (X : Scheme.{u}) :
    IsLimit ((upperStarFromPoint X).mapMon.mapCone (normalizedQuotientCone R I)) := by
  let F := (upperStarFromPoint X).mapMon
  let e := normalizedTowerIso.{u} R I
  let c := normalizedContinuousCone.{u} R I
  let h := (IsLimit.postcomposeInvEquiv (Functor.isoWhiskerRight e F)
    (F.mapCone c)).symm (normalizedContinuousCone_isLimit R I hsep X)
  exact h.ofIsoLimit (Functor.mapConePostcompose F).symm

private noncomputable def normalizedConstantPullback (X : Scheme.{u}) :
    sfbPointConstantRing ⋙ (upperStarFromPoint X).mapMon ≅ sfbConstantRing X :=
  (Functor.associator RingCat.toMonAb
    (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapMon
    (upperStarFromPoint X).mapMon).symm ≪≫
  Functor.isoWhiskerLeft RingCat.toMonAb
    ((Functor.mapMonCompIso (F := constantSheaf (coherentTopology Profinite.{u})
      Ab.{u + 1}) (G := upperStarFromPoint X)).symm ≪≫
      (Functor.mapMonNatIso (constantSchemeIso X)).symm)

/-- A compact ring separated by finite discrete ideal-power quotients gives the canonical
integral limit cone, including its normalization and its preservation under scheme pullback.
-/
theorem sfb_normalized_integral_quotient_cone (R : Type) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R] [T2Space R]
    (I : Ideal R) [∀ n : ℕ, Finite (R ⧸ I ^ n)]
    [∀ n : ℕ, DiscreteTopology (R ⧸ I ^ n)]
    (hsep : ∀ x y : R,
      (∀ n : ℕ, Ideal.Quotient.mk (I ^ n) x = Ideal.Quotient.mk (I ^ n) y) → x = y) :
    ∃ ρ : (Functor.const ℕᵒᵖ).obj (Mon.mk (Profinite.continuousMapRingObj.{u} R)) ⟶
        sfbCoefficientQuotientTower R I ⋙ sfbPointConstantRing,
      (∀ n : ℕ, sfbConstantToContinuous R ≫ (ρ.app (op n)).hom =
        (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map
          (AddCommGrpCat.ofHom
            (ULift.ringEquiv.symm.toRingHom.comp
              ((Ideal.Quotient.mk (I ^ n)).comp ULift.ringEquiv.toRingHom)).toAddMonoidHom)) ∧
      (∀ X : Scheme.{u},
        Nonempty (IsLimit ((upperStarFromPoint X).mapMon.mapCone
          (Cone.mk (Mon.mk (Profinite.continuousMapRingObj R)) ρ))) ∧
        Nonempty ((sfbCoefficientQuotientTower R I ⋙ sfbPointConstantRing ⋙
          (upperStarFromPoint X).mapMon) ≅
            (sfbCoefficientQuotientTower R I ⋙ sfbConstantRing X))) ∧
      (∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
        Nonempty (IsLimit ((upperStar Ab.{u + 1} f).mapMon.mapCone
          ((upperStarFromPoint Y).mapMon.mapCone
            (Cone.mk (Mon.mk (Profinite.continuousMapRingObj R)) ρ))))) := by
  refine ⟨(normalizedQuotientCone R I).π, normalizedQuotientCone_constants R I, ?_, ?_⟩
  · intro X
    exact ⟨⟨normalizedQuotientCone_isLimit R I hsep X⟩,
      ⟨Functor.isoWhiskerLeft (sfbCoefficientQuotientTower R I)
        (normalizedConstantPullback X)⟩⟩
  · intro X Y f
    let e : (upperStarFromPoint Y).mapMon ⋙ (upperStar Ab.{u + 1} f).mapMon ≅
        (upperStarFromPoint X).mapMon :=
      (Functor.mapMonCompIso (F := upperStarFromPoint Y)
        (G := upperStar Ab.{u + 1} f)).symm ≪≫
        Functor.mapMonNatIso (upperStarFromPointComp f)
    exact ⟨(IsLimit.mapConeEquiv e.symm
      (normalizedQuotientCone_isLimit R I hsep X)).ofIsoLimit
        (Functor.mapConeMapCone (normalizedQuotientCone R I)).symm⟩

end AlgebraicGeometry.ProEtale
