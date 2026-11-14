import Langlands.GroupScheme.Reductive.EtaleLocalSplitStatement
import Langlands.GroupScheme.Reductive.SplitRootDatumNeighbourhood
import Langlands.GroupScheme.Reductive.SplitDataBaseChange
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.Torus.RootWeightTrivialization
import Langlands.GroupScheme.Torus.EtaleLocalMaximalExistenceProof

/-! # Reductive group schemes split étale-locally on the base -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

local instance splitProof_affinePullback {S S' : Scheme.{u}}
    (G : GroupScheme S) [IsAffineHom G.X.hom] (a : S' ⟶ S) :
    IsAffineHom ((GroupScheme.baseChange a).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom a inferInstance

/-- A full coordinate root datum on every supplied field landing in an open
restricts to a fibrewise datum on a principal localization inside the open. -/
theorem fibrewiseRootDatumOf_principalRestriction
    {R : Type u} [CommRing R] (I : Type u) [Fintype I]
    (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom]
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    {J : Type v} [Finite J] (P : RootDatum J (I → ℤ) (I → ℤ)) (hred : P.IsReduced)
    (U : Set (PrimeSpectrum R))
    (hP : ∀ (k : Type u) [Field k] [Algebra R k],
      (algebraBaseMap R k) (IsLocalRing.closedPoint k) ∈ U →
        IsRootDatumOf (splitTorus.baseChangeHom (K := k) G I i)
          (CoordinateRootDatum.fieldRealization k P))
    (r : R) (hsub : (PrimeSpectrum.basicOpen r : Set _) ⊆ U) :
    IsFibrewiseRootDatumOf I
      ((GroupScheme.baseChange (algebraBaseMap R (Localization.Away r))).obj G)
      (splitTorus.baseChangeHom (K := Localization.Away r) G I i) P := by
  refine ⟨inferInstance, hred, fun k _ _ => ?_⟩
  let A := Localization.Away r
  let : Algebra R k := ((algebraMap A k).comp (algebraMap R A)).toAlgebra
  let : IsScalarTower R A k := IsScalarTower.of_algebraMap_eq' rfl
  apply IsRootDatumOf.baseChangeHom_scalarTower G I i k
  apply hP k
  have hrange : Set.range (algebraBaseMap R A) ⊆ U := by
    change Set.range (PrimeSpectrum.comap (algebraMap R A)) ⊆ U
    rw [PrimeSpectrum.localization_away_comap_range A r]
    exact hsub
  apply hrange
  refine ⟨(algebraBaseMap A k) (IsLocalRing.closedPoint k), ?_⟩
  exact congrArg (fun f => f (IsLocalRing.closedPoint k))
    (splitTorus.algebraBaseMap_scalarTower (R := R) (A := A) (B := k))

/-- Every reductive group scheme splits on an affine étale neighbourhood
of every point of its base. -/
theorem etaleLocalSplitReductive : EtaleLocalSplitReductiveStatement.{u} := by
  classical
  intro S G hG s
  let := hG.isAffineHom
  obtain ⟨R, hR, f, hf, ⟨p, hp⟩, I, hI, i, hi, hmax⟩ := exists_etale_affine_split_maximalTorus S G hG s
  let : CommRing R := hR
  let : Fintype I := hI
  let G' := (GroupScheme.baseChange f).obj G
  have hG' : IsReductive G' := hG.baseChange f
  let := hG'.isAffineHom
  let := hG'.smooth
  obtain ⟨J, hJ, P, U, hred, hU, hpU, hrank, hP⟩ :=
    exists_open_coordinateRootDatum I G' hG' i hmax p
  let : Finite J := hJ
  obtain ⟨r, hr, hsub, hrootLines⟩ := splitTorus.exists_principal_exponentWeightLines I G' i P.root p U hU hpU hrank
  let A := Localization.Away r
  let a := algebraBaseMap R A
  let H := (GroupScheme.baseChange a).obj G'
  let iA : splitTorus (Spec (CommRingCat.of A)) I ⟶ H :=
    splitTorus.baseChangeHom (K := A) G' I i
  have hiA : IsClosedSubgroup iA :=
    (hi.baseChange a).iso_comp (splitTorus.baseChangeIso a I).symm
  have hmaxA : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) iA :=
    hmax.baseChange_coordinates a
  have hPA : IsFibrewiseRootDatumOf I H iA P :=
    fibrewiseRootDatumOf_principalRestriction I G' i P hred U hP r hsub
  let e : H ≅ (GroupScheme.baseChange (a ≫ f)).obj G := (baseChangeCompIso f a G).symm
  let t : splitTorus (Spec (CommRingCat.of A)) I ⟶
      (GroupScheme.baseChange (a ≫ f)).obj G := iA ≫ e.hom
  let : Etale f := hf
  have ha : IsOpenImmersion a := by
    dsimp [a, algebraBaseMap]
    infer_instance
  let : IsOpenImmersion a := ha
  refine ⟨A, inferInstance, a ≫ f, inferInstance, ?_, I, inferInstance, t,
    hiA.comp_iso e, IsFibrewiseMaximalTorus.comp_ambientIso iA e hmaxA,
    J, P, IsFibrewiseRootDatumOf.comp_ambientIso iA e hPA, ?_⟩
  · have hpRange : p ∈ Set.range a := by
      change p ∈ Set.range (PrimeSpectrum.comap (algebraMap R A))
      rw [PrimeSpectrum.localization_away_comap_range A r]
      exact hr
    obtain ⟨x, hx⟩ := hpRange
    exact ⟨x, (congrArg f hx).trans hp⟩
  · intro α
    obtain ⟨l⟩ := hrootLines α
    exact ⟨(splitTorus.exponentWeightAmbientEquiv iA e (P.root α)).symm.trans l⟩

end Langlands.GroupScheme
