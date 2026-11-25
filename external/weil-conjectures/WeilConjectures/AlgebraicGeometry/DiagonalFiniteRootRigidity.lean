/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import WeilConjectures.AlgebraicGeometry.ModuleAbelianInverseImageComparison
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback

/-! # Restriction to the diagonal detects ordinary finite root maps -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

private theorem unit_pullback (Λ : Type (u + 1)) [CommRing Λ]
    {X S : Scheme.{u}} (p : X ⟶ S)
    [Flat p] [QuasiCompact p] [GeometricallyConnected p]
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app G) := by
  let adj := Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p
  have hi (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
      IsIso (adj.unit.app G) := by
    have : IsIso ((sheafToPresheaf _ _).map (adj.unit.app G)) := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro V
      let q := pullback.fst V.unop.hom p
      let φ := 𝟙 ((MorphismProperty.Over.pullback @Etale ⊤ p).obj V.unop)
      have hq : φ.left ≫ q = q := Category.id_comp _
      let : Flat (φ.left ≫ q) := by rw [hq]; dsimp [q]; infer_instance
      let : QuasiCompact (φ.left ≫ q) := by rw [hq]; dsimp [q]; infer_instance
      let : GeometricallyConnected (φ.left ≫ q) := by rw [hq]; dsimp [q]; infer_instance
      have h := Etale.isIso_upperStarSectionsMap Λ p G φ
      change IsIso ((adj.unit.app G).hom.app V)
      change IsIso ((adj.unit.app G).hom.app V ≫
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) p).obj G).obj.map (𝟙 _)) at h
      rw [CategoryTheory.Functor.map_id] at h
      exact (isIso_comp_right_iff ((adj.unit.app G).hom.app V) (𝟙 _)).mp h
    exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)
  exact hi G

private theorem section_injective
    {C D E : Type*} [Category C] [Category D] [Category E]
    (L : C ⥤ D) (R : D ⥤ E) (T : C ⥤ E) [L.Full] [T.Faithful]
    (e : L ⋙ R ≅ T) (M N : C) :
    Function.Injective (fun f : L.obj M ⟶ L.obj N ↦ R.map f) := by
  intro f g h
  change R.map f = R.map g at h
  have hp : L.preimage f = L.preimage g := by
    apply T.map_injective
    apply (cancel_epi (e.hom.app M)).1
    rw [← e.hom.naturality, ← e.hom.naturality]
    change R.map (L.map (L.preimage f)) ≫ e.hom.app N =
      R.map (L.map (L.preimage g)) ≫ e.hom.app N
    rw [L.map_preimage, L.map_preimage, h]
  rw [← L.map_preimage f, ← L.map_preimage g, hp]

private theorem projectiveLine_connected (S : Scheme.{u}) :
    GeometricallyConnected (ProjectiveLine S ↘ S) := by
  refine ⟨fun K _ y Z fst snd h ↦ ?_⟩
  have e : Z ≅ ProjectiveLine (Spec (.of K)) :=
    h.isoIsPullback _ _ (ProjectiveSpace.isPullback_map _ y)
  exact (Scheme.homeoOfIso e.symm).connectedSpace_iff.1 inferInstance

private theorem ab_unit_pullback
    {X S : Scheme.{u}} (p : X ⟶ S)
    [Flat p] [QuasiCompact p] [GeometricallyConnected p]
    (G : Sheaf S.smallEtaleTopology Ab.{u + 1}) :
    IsIso ((Etale.upperStarLowerStarAdjunction Ab.{u + 1} p).unit.app G) := by
  let R := ULift.{u + 1} ℤ
  let eqv : Ab.{u + 1} ≌ ModuleCat.{u + 1} R :=
    (Functor.asEquivalence (forget₂ (ModuleCat.{u + 1} ℤ) Ab.{u + 1})).symm.trans
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
        (ULift.ringEquiv : R ≃+* ℤ))
  let U := sheafCompose S.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} R) Ab.{u + 1})
  let U' := sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} R) Ab.{u + 1})
  let a := Etale.upperStarLowerStarAdjunction Ab.{u + 1} p
  let b := Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) p
  have hi (J : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} R)) :
      IsIso (a.unit.app (U.obj J)) := by
    let z := (a.homEquiv (U.obj J)
      (U'.obj ((Etale.upperStar (ModuleCat.{u + 1} R) p).obj J))).symm
        (U.map (b.unit.app J))
    have hz : IsIso z := Etale.isIso_moduleAbelianInverseImageComparison p R J
    have hunit : a.unit.app (U.obj J) ≫ (Etale.lowerStar Ab.{u + 1} p).map z =
        U.map (b.unit.app J) := by
      exact (a.homEquiv _ _).apply_symm_apply _
    have : IsIso (b.unit.app J) := unit_pullback R p J
    have : IsIso (a.unit.app (U.obj J) ≫ (Etale.lowerStar Ab.{u + 1} p).map z) := by
      rw [hunit]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((Etale.lowerStar Ab.{u + 1} p).map z)
  let J := (sheafCompose S.smallEtaleTopology eqv.functor).obj G
  let v : G ≅ U.obj J := ObjectProperty.isoMk _
    ((Functor.rightUnitor G.obj).symm ≪≫
      Functor.isoWhiskerLeft G.obj eqv.unitIso ≪≫ (Functor.associator _ _ _).symm)
  let : IsIso (a.unit.app (U.obj J)) := hi J
  let T := Etale.upperStar Ab.{u + 1} p ⋙ Etale.lowerStar Ab.{u + 1} p
  have hn := a.unit.naturality v.hom
  have : IsIso (a.unit.app G ≫ T.map v.hom) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (T.map v.hom)

private theorem ab_full_pullback
    {X S : Scheme.{u}} (p : X ⟶ S)
    [Flat p] [QuasiCompact p] [GeometricallyConnected p] :
    (Etale.upperStar Ab.{u + 1} p).Full := by
  let adj := Etale.upperStarLowerStarAdjunction Ab.{u + 1} p
  let : ∀ G, IsIso (adj.unit.app G) := ab_unit_pullback p
  exact adj.full_L_of_isSplitEpi_unit_app

/-- The diagonal section detects maps between abelian etale-origin objects
pulled back by the first projection of the product of projective lines.
Source: diagonal coefficient proof (3), connected-fibre root-map rigidity.
(blueprint: lem-diagonal-finite-root-rigidity).

Proof: transfer section invariance from integer-module sheaves to abelian
sheaves using their coefficient equivalence and the normalized inverse-image
comparison. Thus the etale first-projection pullback is full. Comparison inverse
image is fully faithful. The diagonal is a section, so the restriction of this
full composite is faithful. Lift the two maps and cancel this faithful functor. -/
private theorem diagonalAbRoot_restriction_injective
    (Y : Scheme.{u})
    (M N : Sheaf (ProjectiveLine Y).smallEtaleTopology Ab.{u + 1}) :
    let p := pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)
    let d := pullback.diagonal (ProjectiveLine Y ↘ Y)
    let L := Etale.upperStar Ab.{u + 1} p ⋙ comparisonUpperStar Ab.{u + 1} (pullback _ _)
    Function.Injective (fun f : L.obj M ⟶ L.obj N ↦ (upperStar Ab.{u + 1} d).map f) := by
  dsimp only
  let P := ProjectiveLine Y
  let q := P ↘ Y
  let W := pullback q q
  let p : W ⟶ P := pullback.fst q q
  let d : P ⟶ W := pullback.diagonal q
  let A := Ab.{u + 1}
  let L := Etale.upperStar A p ⋙ comparisonUpperStar A W
  let R := upperStar A d
  let T := comparisonUpperStar A P
  have hp : d ≫ p = 𝟙 P := by simp [d, p]
  let : GeometricallyConnected q := projectiveLine_connected Y
  let : Smooth q := SmoothOfRelativeDimension.smooth 1 q
  let : Flat q := inferInstance
  let : (Etale.upperStar A p).Full := ab_full_pullback p
  let : L.Full := inferInstance
  let e : L ⋙ R ≅ T :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (comparisonUpperStarCompUpperStarIso A d) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        ((Etale.upperStarComp A d p (𝟙 P) hp.symm).symm ≪≫ Etale.upperStarId A P) _ ≪≫
      Functor.leftUnitor _
  exact section_injective L R T e M N

/-- Restriction to the diagonal detects endomorphisms of the ordinary roots
sheaf on the product of projective lines.
Source: diagonal coefficient changes (3), connected-fibre scalar rigidity.
(blueprint: lem-diagonal-finite-root-rigidity).

Proof: the roots sheaf is comparison inverse image of the etale roots sheaf,
which is itself pulled back by the first projection. Conjugate by these
canonical root isomorphisms. The abelian etale-origin restriction theorem
then detects equality; conjugating back gives equality of root maps. -/
theorem diagonalFiniteRoot_restriction_injective (Y : Scheme.{u})
    (N : ℕ) (hN : 0 < N) (hY : IsUnit (N : Γ(Y, ⊤))) :
    let q := ProjectiveLine Y ↘ Y
    let W := pullback q q
    let d := pullback.diagonal q
    Function.Injective (fun f : Scheme.proEtaleRootsOfUnitySheaf W N ⟶
        Scheme.proEtaleRootsOfUnitySheaf W N ↦ (upperStar Ab.{u + 1} d).map f) := by
  dsimp only
  let P := ProjectiveLine Y
  let q := P ↘ Y
  let W := pullback q q
  let p : W ⟶ P := pullback.fst q q
  let d : P ⟶ W := pullback.diagonal q
  let R := upperStar Ab.{u + 1} d
  have hP : IsUnit (N : Γ(P, ⊤)) := by
    simpa only [map_natCast] using hY.map q.appTop.hom
  have hW : IsUnit (N : Γ(W, ⊤)) := by
    simpa only [map_natCast] using hP.map p.appTop.hom
  let : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let M := P.rootsOfUnitySheaf N
  have : IsIso (Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf N p) :=
    Scheme.isIso_upperStarRootsOfUnitySheafToRootsOfUnitySheaf_of_isUnit N p hP
  let e := (comparisonUpperStar Ab.{u + 1} W).mapIso
      (asIso (Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf N p)) ≪≫
    cartierRootsIso W N hN hW
  intro f g heq
  change R.map f = R.map g at heq
  have h := diagonalAbRoot_restriction_injective Y M M
  have hfg : e.hom ≫ f ≫ e.inv = e.hom ≫ g ≫ e.inv := by
    apply h
    simp only [Functor.map_comp]
    rw [heq]
  exact (cancel_epi e.hom).1 ((cancel_mono e.inv).1 hfg)

end AlgebraicGeometry.ProEtale
