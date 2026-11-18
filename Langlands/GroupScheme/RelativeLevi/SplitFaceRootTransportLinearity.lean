import Langlands.GroupScheme.RelativeLevi.SplitFaceRootRangeTransport
import Langlands.GroupScheme.Reductive.LocalSplitCommonTorus
import Langlands.GroupScheme.RelativeLevi.SplitFaceCocharacterRealization
import Langlands.GroupScheme.RelativeUnipotent.RootWeightTorusAction
import Langlands.GroupScheme.RelativeUnipotent.LinearQuotientComparison

/-! # Linear vector-quotient comparison under actual torus-compatible root transport -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeUnipotent.RootWeightData

open LocalSplitCell

variable {R : Type u} [CommRing R] {I J : Type u} [Fintype I]
  {U G : GroupScheme (Spec (CommRingCat.of R))}
  {t : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {ch : J → I → ℤ} {fam : J → (Ga R ⟶ G)}
  {C : RootHeightChart U} (W : RootWeightData C)
  (j : U ⟶ G) [Mono j.hom.hom]
  {index : Fin C.dimension → J}
  (hroot : ∀ k, C.roots (ULift.up k) ≫ j = fam (index k))
  (hu : TorusEquivariant t ch fam)

include hroot hu in
/-- Restriction along an arbitrary actual torus cocharacter gives scalar
quotient equivariance when its exact-layer characters have one common power. -/
theorem quotientMap_isEquivariant_of_characterRestriction
    (ν : cocharacterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I))
    (d : ℕ) (N : ℕ)
    (hw : ∀ k, W.weight k = d + 1 →
      ν ≫ splitTorus.exponentCharacter _ I (ch (index k)) = Gm.powerHom _ (N : ℤ)) :
    ((W.torusAction j hroot hu d).restrict (CommGroupScheme.groupHom ν)).IsEquivariant
      (VectorGroup.powerWeightAction (Nat.card (W.exactSupport d)) N) (W.quotientMap d) := by
  intro T s x
  apply VectorGroup.points_ext
  intro k
  rw [W.comp_quotientMap, W.quotientPoints_coord,
    VectorGroup.coordinates_weightAction_act, Pi.smul_apply, smul_eq_mul,
    W.comp_quotientMap, W.quotientPoints_coord, AutomorphicAction.restrict_act,
    W.coordinates_torusAction_inclusion j hroot hu]
  dsimp only
  congr 1
  rw [torusChar, VectorGroup.charValue, VectorGroup.charValue,
    ← comp_groupHom_comp, hw _ (W.exactEnumeration d k).property]

include hroot hu in
/-- The restricted action has precisely its original ambient conjugation equation. -/
theorem restrictedTorusAction_ambient
    (ν : cocharacterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I))
    (d : ℕ) (T : Over (Spec (CommRingCat.of R)))
    (s : T ⟶ (Gm (Spec (CommRingCat.of R))).X) (x : T ⟶ (W.groupScheme d).X) :
    ((W.torusAction j hroot hu d).restrict (CommGroupScheme.groupHom ν)).act s x ≫
        (W.inclusion d ≫ j).hom.hom =
      (s ≫ (CommGroupScheme.groupHom ν ≫ t).hom.hom) *
        (x ≫ (W.inclusion d ≫ j).hom.hom) *
          (s ≫ (CommGroupScheme.groupHom ν ≫ t).hom.hom)⁻¹ := by
  rw [AutomorphicAction.restrict_act, Grp.comp_hom_hom, ← Category.assoc,
    W.torusAction_inclusion j hroot hu, C.torusAction_comp j hroot hu]
  simp only [Grp.comp_hom_hom, Category.assoc]

end Langlands.GroupScheme.RelativeUnipotent.RootWeightData

namespace Langlands.GroupScheme.SplitParabolicFaceChart

open LocalSplitCell RelativeUnipotent
open Langlands.LinearAlgebra.RootDatumFaceHeight

variable {R : Type u} [CommRing R]
  {I I' J J' : Type u} [Fintype I] [Fintype I'] [Fintype J] [Fintype J']
  [DecidableEq I] [DecidableEq I']
  {G H : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {j : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H}
  {P : RootDatum J (I → ℤ) (I → ℤ)} {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
  {fam : J → (Ga R ⟶ G)} {fam' : J' → (Ga R ⟶ H)}
  {wt : I → ℤ} {wt' : I' → ℤ}
  (C : SplitParabolicFaceChart i P fam wt) (D : SplitParabolicFaceChart j Q fam' wt')
  (e : RootPairing.Equiv P Q) (f : G ≅ H)
  (hroot : ∀ a : J, SubgroupFunctor.range (fam a ≫ f.hom) =
    SubgroupFunctor.range (fam' (e.indexEquiv a)))
  (hheight : ∀ a : J,
    faceHeight C.base C.faceCoweight (P.rootSpanMem ℤ a) =
      faceHeight D.base D.faceCoweight (Q.rootSpanMem ℤ (e.indexEquiv a)))

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom

include hroot hheight in
/-- Actual transported term isomorphisms respect the original successive maps. -/
theorem step_comp_rootTransportTermIso (d : ℕ) :
    C.weights.step d ≫ (C.rootTransportTermIso D e f hroot hheight d).hom =
      (C.rootTransportTermIso D e f hroot hheight (d + 1)).hom ≫ D.weights.step d := by
  let b := D.weights.inclusion d ≫
    Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter j D.cocharacter)
  have hm : Mono b.hom.hom := by
    change Mono ((D.weights.inclusion d).hom.hom ≫ _)
    exact mono_comp' (D.weights.isRepresentedBy_inclusion d).1
      (Dynamic.Affine.isRepresentedBy_unipotentHom
        (AffineRegularBorel.cocharacter j D.cocharacter)).1
  have hb : (SubgroupFunctor.range b).IsRepresentedBy b := ⟨hm, rfl⟩
  apply hb.hom_ext
  change (C.weights.step d ≫ _) ≫ (D.weights.inclusion d ≫ _) =
    (_ ≫ D.weights.step d) ≫ (D.weights.inclusion d ≫ _)
  rw [Category.assoc, C.rootTransportTermIso_hom_comp D e f hroot hheight d]
  simp only [Category.assoc] 
  rw [← Category.assoc (C.weights.step d), C.weights.step_comp_inclusion,
    ← Category.assoc (D.weights.step d), D.weights.step_comp_inclusion,
    C.rootTransportTermIso_hom_comp D e f hroot hheight (d + 1)]
  simp only [Category.assoc]

/-- The actual full fppf quotient comparison for transported root terms. -/
def rootTransportQuotientIso (d : ℕ) :
    VectorGroup.groupScheme (CommRingCat.of R) (Nat.card (C.weights.exactSupport d)) ≅
      VectorGroup.groupScheme (CommRingCat.of R) (Nat.card (D.weights.exactSupport d)) :=
  FppfQuotientComparison.isoOfCompatibleTerms (C.weights.step d) (D.weights.step d)
    (C.weights.isFppfQuotient_quotientMap d) (D.weights.isFppfQuotient_quotientMap d)
    (C.rootTransportTermIso D e f hroot hheight d)
    (C.rootTransportTermIso D e f hroot hheight (d + 1))
    (C.step_comp_rootTransportTermIso D e f hroot hheight d)

/-- The actual quotient comparison retains the original quotient maps. -/
theorem quotientMap_comp_rootTransportQuotientIso (d : ℕ) :
    C.weights.quotientMap d ≫ (C.rootTransportQuotientIso D e f hroot hheight d).hom =
      (C.rootTransportTermIso D e f hroot hheight d).hom ≫ D.weights.quotientMap d :=
  FppfQuotientComparison.isoOfCompatibleTerms_fac _ _ _ _ _ _ _

/-- The actual realizing cocharacter in the source coordinate torus. -/
def realizingTorusCocharacter :
    cocharacterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) :=
  splitTorus.exponentCocharacter _ I C.faceCocharacter

/-- Transport the actual cocharacter through the fixed integral torus isomorphism.
No choice of coordinate vector over a disconnected base is needed. -/
def transportedRealizingCocharacter :
    cocharacterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I') :=
  C.realizingTorusCocharacter ≫ (splitTorus.exponentEquivIso _ e.weightEquiv).hom

/-- Realizing characters on the source exact layer have its common positive power. -/
theorem realizing_character_eq (d : ℕ) (k : Fin C.chart.dimension)
    (hk : C.weights.weight k = d + 1) :
    C.realizingTorusCocharacter ≫ splitTorus.exponentCharacter _ I (P.root (C.index k)) =
      Gm.powerHom _ ((C.faceMultiplier * (d + 1) : ℕ) : ℤ) := by
  rw [realizingTorusCocharacter, splitTorus.exponentCocharacter_comp_exponentCharacter]
  change Gm.powerHom _ (coPairing (P.root (C.index k)) C.faceCocharacter) = _
  rw [C.facePairing, ← C.weight_eq k, hk, Nat.cast_mul, Nat.cast_add, Nat.cast_one]

include hheight in
/-- Exact transported face heights give the same common power on the target layer,
although its torus, root datum and root coordinates may differ. -/
theorem transported_realizing_character_eq (d : ℕ) (k : Fin D.chart.dimension)
    (hk : D.weights.weight k = d + 1) :
    C.transportedRealizingCocharacter e ≫
        splitTorus.exponentCharacter _ I' (Q.root (D.index k)) =
      Gm.powerHom _ ((C.faceMultiplier * (d + 1) : ℕ) : ℤ) := by
  let a := e.indexEquiv.symm (D.index k)
  have hr : e.weightEquiv (P.root a) = Q.root (D.index k) := by
    rw [RootPairing.Equiv.weightEquiv_apply, e.root_weightMap_apply P Q]
    simp [a]
  have hc : (splitTorus.exponentEquivIso (Spec (CommRingCat.of R)) e.weightEquiv).inv ≫
      splitTorus.exponentCharacter _ I (P.root a) =
        splitTorus.exponentCharacter _ I' (Q.root (D.index k)) := by
    rw [← hr]
    exact splitTorus.congr_exponentEquivIso _ e.weightEquiv (P.root a)
  have hh : faceHeight C.base C.faceCoweight (P.rootSpanMem ℤ a) =
      (D.weights.weight k : ℤ) := by
    have h := hheight a
    simpa only [a, Equiv.apply_symm_apply, ← D.weight_eq k] using h
  rw [transportedRealizingCocharacter, ← hc, Category.assoc, Iso.hom_inv_id_assoc,
    realizingTorusCocharacter, splitTorus.exponentCocharacter_comp_exponentCharacter]
  change Gm.powerHom _ (coPairing (P.root a) C.faceCocharacter) = _
  rw [C.facePairing, hh, hk, Nat.cast_mul, Nat.cast_add, Nat.cast_one]

variable (hfam : ∀ a, IsRootParametrization i (P.root a) (fam a))
  (hfam' : ∀ a, IsRootParametrization j (Q.root a) (fam' a))

/-- The actual action restricted along any actual coordinate-torus cocharacter. -/
def restrictedAction
    (ν : cocharacterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I))
    (d : ℕ) : AutomorphicAction (Gm (Spec (CommRingCat.of R))).toGrp (C.weights.groupScheme d) := by
  let c := Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter)
  letI : Mono c.hom.hom := (Dynamic.Affine.isRepresentedBy_unipotentHom _).1
  exact (C.weights.torusAction c C.root_comp
    (fun a T s x => (hfam a).equivariant T s x) d).restrict (CommGroupScheme.groupHom ν)

/-- The restricted actual action retains its ambient conjugation formula. -/
theorem restrictedAction_ambient
    (ν : cocharacterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I))
    (d : ℕ) (T : Over (Spec (CommRingCat.of R)))
    (s : T ⟶ (Gm (Spec (CommRingCat.of R))).X) (x : T ⟶ (C.weights.groupScheme d).X) :
    (C.restrictedAction hfam ν d).act s x ≫
        (C.weights.inclusion d ≫ Dynamic.Affine.unipotentHom
          (AffineRegularBorel.cocharacter i C.cocharacter)).hom.hom =
      (s ≫ (CommGroupScheme.groupHom ν ≫ i).hom.hom) *
        (x ≫ (C.weights.inclusion d ≫ Dynamic.Affine.unipotentHom
          (AffineRegularBorel.cocharacter i C.cocharacter)).hom.hom) *
            (s ≫ (CommGroupScheme.groupHom ν ≫ i).hom.hom)⁻¹ := by
  letI : Mono (Dynamic.Affine.unipotentHom
      (AffineRegularBorel.cocharacter i C.cocharacter)).hom.hom :=
    (Dynamic.Affine.isRepresentedBy_unipotentHom _).1
  unfold restrictedAction
  exact C.weights.restrictedTorusAction_ambient _ C.root_comp _ ν d T s x

/-- The source quotient carries its actual common scalar power action. -/
theorem realizingAction_quotient_equivariant (d : ℕ) :
    (C.restrictedAction hfam C.realizingTorusCocharacter d).IsEquivariant
      (VectorGroup.powerWeightAction (Nat.card (C.weights.exactSupport d))
        (C.faceMultiplier * (d + 1))) (C.weights.quotientMap d) := by
  letI : Mono (Dynamic.Affine.unipotentHom
      (AffineRegularBorel.cocharacter i C.cocharacter)).hom.hom :=
    (Dynamic.Affine.isRepresentedBy_unipotentHom _).1
  unfold restrictedAction
  intro T s x
  exact C.weights.quotientMap_isEquivariant_of_characterRestriction _ C.root_comp
    (fun a T s x => (hfam a).equivariant T s x) C.realizingTorusCocharacter d _ (C.realizing_character_eq d) s x

include hheight in
/-- The transported actual target action has precisely the same scalar power. -/
theorem transportedAction_quotient_equivariant (d : ℕ) :
    (D.restrictedAction hfam' (C.transportedRealizingCocharacter e) d).IsEquivariant
      (VectorGroup.powerWeightAction (Nat.card (D.weights.exactSupport d))
        (C.faceMultiplier * (d + 1))) (D.weights.quotientMap d) := by
  letI : Mono (Dynamic.Affine.unipotentHom
      (AffineRegularBorel.cocharacter j D.cocharacter)).hom.hom :=
    (Dynamic.Affine.isRepresentedBy_unipotentHom _).1
  unfold restrictedAction
  intro T s x
  exact D.weights.quotientMap_isEquivariant_of_characterRestriction _ D.root_comp
    (fun a T s x => (hfam' a).equivariant T s x) (C.transportedRealizingCocharacter e) d _
    (C.transported_realizing_character_eq D e hheight d) s x

variable (hsquare : i ≫ f.hom = precompTorus e.weightEquiv j)

include hroot hheight hfam hfam' hsquare in
/-- The actual ambient-compatible term comparison intertwines the actual
source and transported target cocharacter actions. -/
theorem rootTransportTermIso_isEquivariant (d : ℕ) :
    (C.restrictedAction hfam C.realizingTorusCocharacter d).IsEquivariant
      (D.restrictedAction hfam' (C.transportedRealizingCocharacter e) d)
      (C.rootTransportTermIso D e f hroot hheight d).hom := by
  have hχ : (CommGroupScheme.groupHom C.realizingTorusCocharacter ≫ i) ≫ f.hom =
      CommGroupScheme.groupHom (C.transportedRealizingCocharacter e) ≫ j := by
    rw [Category.assoc, hsquare]
    rfl
  let c := C.weights.inclusion d ≫
    Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i C.cocharacter)
  let b := D.weights.inclusion d ≫
    Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter j D.cocharacter)
  have hm : Mono b.hom.hom := by
    change Mono ((D.weights.inclusion d).hom.hom ≫ _)
    exact mono_comp' (D.weights.isRepresentedBy_inclusion d).1
      (Dynamic.Affine.isRepresentedBy_unipotentHom
        (AffineRegularBorel.cocharacter j D.cocharacter)).1
  have he (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ (C.weights.groupScheme d).X) :
      (x ≫ (C.rootTransportTermIso D e f hroot hheight d).hom.hom.hom) ≫ b.hom.hom =
        (x ≫ c.hom.hom) ≫ f.hom.hom.hom := by
    have h := congrArg (fun g => x ≫ g.hom.hom)
      (C.rootTransportTermIso_hom_comp D e f hroot hheight d)
    simpa only [Grp.comp_hom_hom, Category.assoc, c, b] using h
  intro T s x
  apply hm.right_cancellation
  rw [he, C.restrictedAction_ambient hfam, D.restrictedAction_ambient hfam', he]
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]
  have hp := congrArg (fun g => s ≫ g.hom.hom) hχ
  simp only [Grp.comp_hom_hom, ← Category.assoc] at hp ⊢
  rw [hp]
  rfl

local instance quotient_quasiCompact (d : ℕ) :
    QuasiCompact (C.weights.quotientMap d).hom.hom.left := by
  have hAffine (n : ℕ) : IsAffine (VectorGroup.groupScheme (CommRingCat.of R) n).X.left := by
    change IsAffine (Spec (CommRingCat.of (MvPolynomial (Fin n) R)))
    infer_instance
  have := hAffine (Nat.card (C.weights.support d))
  have := hAffine (Nat.card (C.weights.exactSupport d))
  rw [C.weights.quotientMap_hom]
  infer_instance

include hroot hheight hfam hfam' hsquare in
/-- The actual transported quotient isomorphism has a common positive scalar
weight, derived from the actual source and quotient equivariance equations. -/
theorem rootTransportQuotientIso_hasScalarWeight (d : ℕ) :
    VectorGroup.HasScalarWeight
      (VectorGroup.pointTransformation (C.rootTransportQuotientIso D e f hroot hheight d).hom)
      (C.faceMultiplier * (d + 1)) :=
  FppfQuotientComparison.isoOfCompatibleTerms_hasScalarWeight
    (C.weights.step d) (D.weights.step d)
    (C.weights.isFppfQuotient_quotientMap d) (D.weights.isFppfQuotient_quotientMap d)
    (C.rootTransportTermIso D e f hroot hheight d)
    (C.rootTransportTermIso D e f hroot hheight (d + 1))
    (C.step_comp_rootTransportTermIso D e f hroot hheight d)
    (C.restrictedAction hfam C.realizingTorusCocharacter d)
    (D.restrictedAction hfam' (C.transportedRealizingCocharacter e) d)
    (C.faceMultiplier * (d + 1))
    (C.realizingAction_quotient_equivariant hfam d)
    (C.transportedAction_quotient_equivariant D e hheight hfam' d)
    (C.rootTransportTermIso_isEquivariant D e f hroot hheight hfam hfam' hsquare d)

/-- The actual transported vector quotient comparison is linear over every
coefficient algebra. The height-preserving root-index equivalence identifies
the two exact-height supports, so their cardinalities agree and may be zero. -/
def rootTransportLayerLinearEquiv (d : ℕ) (A : CommAlgCat.{u} (CommRingCat.of R)) :
    (Fin (Nat.card (C.weights.exactSupport d)) → A) ≃ₗ[A]
      (Fin (Nat.card (D.weights.exactSupport d)) → A) :=
  VectorGroup.linearEquivOfWeight (C.rootTransportQuotientIso D e f hroot hheight d)
    (Nat.mul_pos C.faceMultiplier_pos (Nat.succ_pos d))
    (C.rootTransportQuotientIso_hasScalarWeight D e f hroot hheight hfam hfam' hsquare d) A

include hroot hheight hfam hfam' hsquare in
/-- One base-ring matrix represents the original actual quotient comparison. -/
theorem rootTransportQuotientIso_eq_matrixHom (d : ℕ) :
    (C.rootTransportQuotientIso D e f hroot hheight d).hom =
      VectorGroup.matrixHom (VectorGroup.weightMatrix (VectorGroup.pointTransformation
        (C.rootTransportQuotientIso D e f hroot hheight d).hom)) :=
  VectorGroup.eq_matrixHom_of_hasScalarWeight _
    (Nat.mul_pos C.faceMultiplier_pos (Nat.succ_pos d))
    (C.rootTransportQuotientIso_hasScalarWeight D e f hroot hheight hfam hfam' hsquare d)

include hroot hheight hfam hfam' hsquare in
/-- The same matrix formula holds on arbitrary scheme tests over the base. -/
theorem coordinates_rootTransportQuotientIso (d : ℕ)
    (T : Over (Spec (CommRingCat.of R)))
    (x : T ⟶ (VectorGroup.groupScheme (CommRingCat.of R)
      (Nat.card (C.weights.exactSupport d))).X) :
    (VectorGroup.coordinates (CommRingCat.of R) (Nat.card (D.weights.exactSupport d)) T
      (x ≫ (C.rootTransportQuotientIso D e f hroot hheight d).hom.hom.hom)).toAdd =
      (VectorGroup.weightMatrix (VectorGroup.pointTransformation
        (C.rootTransportQuotientIso D e f hroot hheight d).hom)).map
          (scalarMap T) *ᵥ
      (VectorGroup.coordinates (CommRingCat.of R) (Nat.card (C.weights.exactSupport d)) T x).toAdd :=
  VectorGroup.coordinates_of_hasScalarWeight _
    (Nat.mul_pos C.faceMultiplier_pos (Nat.succ_pos d))
    (C.rootTransportQuotientIso_hasScalarWeight D e f hroot hheight hfam hfam' hsquare d) T x

end Langlands.GroupScheme.SplitParabolicFaceChart
