import Langlands.HarmonicAnalysis.HarishChandraSchwartz.FullLeviOrbitMeasure
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.FullLeviProductCoefficients

/-! # Comparing the actual group-Levi packet with ambient coefficients -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Plancherel Langlands.Aubert.General

namespace Langlands.HarishChandraSchwartz

section CoefficientTransport

variable {Γ L : Type u} [Group Γ] [TopologicalSpace Γ]
  [Group L] [TopologicalSpace L]
  (e : L ≃ₜ* Γ) (j : Γ ≃ₜ* L)
  {P : SmoothRep.{0, u, uV} ℂ Γ} {R : SmoothRep.{0, u, uV} ℂ L}
  (f : R.representation.Equiv (SmoothRep.pullback e P).representation)

private def ambientEquivOfPullback (hj : ∀ g, e (j g) = g) :
    (SmoothRep.pullback j R).representation.Equiv P.representation :=
  Representation.Equiv.mk f.toLinearEquiv fun g => by
    ext v
    change f.toLinearEquiv (R.representation (j g) v) = P.representation g (f.toLinearEquiv v)
    have hf := Representation.IntertwiningMap.isIntertwining _ _ f.toIntertwiningMap (j g) v
    change f.toLinearEquiv (R.representation (j g) v) =
      P.representation (e (j g)) (f.toLinearEquiv v) at hf
    rw [hj g] at hf
    exact hf

private theorem exists_coefficientTensor_of_fullLeviClass
    [LocallyCompactSpace Γ] [NonarchimedeanGroup Γ] (M : Subgroup Γ) (hM : M = ⊤)
    (e : M ≃ₜ* Γ) (he : ∀ g, e (fullLeviGroupEquiv M hM g) = g)
    (C : SmoothDualClass.{0, u, uV} (k := ℂ) (G := Γ))
    (Q : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := M))
    (hQ : Quotient.mk _ Q = SmoothDualClass.pullback e C)
    (c : LocallyConstant Γ ℂ)
    (hc : ∃ t : CoefficientTensor (fullLeviAmbientSmoothRep M hM Q.obj),
      coefficientTensorMap (fullLeviAmbientSmoothRep M hM Q.obj) t = c) :
    ∃ t : CoefficientTensor C.out.obj, coefficientTensorMap C.out.obj t = c := by
  have hC : Quotient.mk _ (IrreducibleAdmissibleRep.pullback e C.out) =
      SmoothDualClass.pullback e C :=
    (SmoothDualClass.pullback_mk e C.out).symm.trans
      (congrArg (SmoothDualClass.pullback e) (Quotient.out_eq C))
  obtain ⟨f⟩ := Quotient.exact (hQ.trans hC.symm)
  let fe : Q.obj.representation.Equiv (SmoothRep.pullback e C.out.obj).representation :=
    SmoothRep.equivOfIso ((irreducibleAdmissibleProperty (k := ℂ) (G := M)).ι.mapIso f)
  let E := ambientEquivOfPullback e (fullLeviGroupEquiv M hM) fe he
  obtain ⟨t, ht⟩ := hc
  exact ⟨coefficientTensorCongr E t, (coefficientTensorMap_congr E t).trans ht⟩

end CoefficientTransport

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine T.X.left]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  [Fintype (RationalPointFamily.SimpleRoot i ν)]
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (s : T.toGrp ⟶ G) (hs : IsSplitComponent s)

set_option hygiene false in
local notation "𝐌" => standardLeviPoints i ν (RationalPointFamily.rootSet i ν Finset.univ)
set_option hygiene false in
local notation "νG" => (fun ψ => (rationalNormCharacters G ψ).toMul)
set_option hygiene false in
local notation "νM" => RationalPointFamily.leviRationalNormCharacters i ν Finset.univ
set_option hygiene false in
local notation "sL" => rationalFullLeviSplitComponent hG hi hν s
set_option hygiene false in
local notation "hsL" => isSplitComponent_rationalFullLeviSplitComponent hG hi hν s hs
set_option hygiene false in
local notation "A" => (rationalPoints.map s).range
set_option hygiene false in
local notation "hA" => hs.isCentralSplitTorus.isCentral.range_le_center
set_option hygiene false in
local notation "B" => rationalLeviSplitCenter Finset.univ sL
set_option hygiene false in
local notation "hB" => rationalLeviSplitCenter_le_center Finset.univ sL hsL
set_option hygiene false in
local notation "eG" => rationalFullLeviLiteralPointEquiv hG hi hν
set_option hygiene false in
local notation "eX" => rationalFullLeviCharacterEquiv hG hi hν
set_option hygiene false in
local notation "hM" => RationalPointFamily.levi_univ_eq_top i ν standardCocharacter hG hi hν
set_option hygiene false in
local notation "eIn" => fullLeviGroupEquiv 𝐌 hM

variable [(A).Normal] [(B).Normal] [(rationalPoints.map sL).range.Normal]
  [MeasurableSpace (rationalPoints G ⧸ A)] [BorelSpace (rationalPoints G ⧸ A)]
  [MeasurableSpace (𝐌 ⧸ B)] [BorelSpace (𝐌 ⧸ B)]
  (mu : Measure (rationalPoints G ⧸ A)) [mu.IsHaarMeasure]

set_option hygiene false in
local notation "muM" => rationalFullLeviQuotientHaar hG hi hν s mu

omit [IsAffine T.X.left] [(rationalPoints.map sL).range.Normal] in
/-- Each point of the orbit homeomorphism has the pulled-back
discrete-series class. -/
theorem rationalFullLeviOrbitHomeomorph_val
    (ω : DiscreteSeriesClass.{u, uV} A hA mu)
    (x : discreteSeriesOrbit A hA mu νG ω) :
    (rationalFullLeviOrbitHomeomorph hG hi hν s hs mu ω x).val =
      rationalFullLeviDiscreteSeriesClass hG hi hν s hs mu x.val := by
  obtain ⟨chi, rfl⟩ :=
    (isOpenQuotientMap_discreteSeriesOrbitMap A hA mu νG ω).surjective x
  have hX : ∀ (psi : unitaryUnramifiedCharacters νG) (m : 𝐌),
      (eX psi).val m = psi.val (eG m) := by
    intro psi m
    rw [rationalFullLeviCharacterEquiv_apply, rationalFullLeviLiteralPointEquiv_apply]
  have hAB := map_rationalFullLeviSplitCenter hG hi hν s
  have hmu := map_rationalFullLeviQuotientHaar hG hi hν s mu
  calc
    _ = eX chi • rationalFullLeviDiscreteSeriesClass hG hi hν s hs mu ω :=
      congrArg Subtype.val
        (discreteSeriesOrbitCharacterEquiv_orbitMap eG νG νM eX hX
          A hA B hB hAB mu muM hmu ω chi)
    _ = _ :=
      (discreteSeriesPullback_smul_characterEquiv eG νG νM eX hX
        A hA B hB hAB mu muM hmu chi ω).symm

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
private theorem rationalFullLeviLiteralPointEquiv_fullLeviGroupEquiv
    (g : rationalPoints G) : eG (eIn g) = g :=
  (rationalFullLeviLiteralPointEquiv_apply hG hi hν (eIn g)).trans
    (coe_fullLeviGroupEquiv 𝐌 hM g)

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := rationalPoints G))
  (hsq : IsSquareIntegrableModCentralSubgroup A hA π.obj.representation mu)

set_option hygiene false in
local notation "πM" => IrreducibleAdmissibleRep.pullback eG π
set_option hygiene false in
local notation "ω" => discreteSeriesClass A hA mu π hsq

include hsq in
omit [IsAffine T.X.left] [(rationalPoints.map sL).range.Normal] in
/-- The pulled-back inducing representative is square integrable for the
transport of the given ambient quotient Haar measure. -/
theorem rationalFullLeviPullback_isSquareIntegrable :
    IsSquareIntegrableModCentralSubgroup B hB (πM).obj.representation muM :=
  (isSquareIntegrableModCentralSubgroup_comp_iff eG A hA B hB
    (map_rationalFullLeviSplitCenter hG hi hν s) mu muM
    (map_rationalFullLeviQuotientHaar hG hi hν s mu) π.obj.representation).mpr hsq

set_option hygiene false in
local notation "hsqM" => rationalFullLeviPullback_isSquareIntegrable hG hi hν s hs mu π hsq
set_option hygiene false in
local notation "ωM" => discreteSeriesClass B hB muM πM hsqM
set_option hygiene false in
local notation "eO" => rationalFullLeviOrbitHomeomorph hG hi hν s hs mu ω

variable {K : OpenSubgroup (rationalPoints G)}
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)

set_option hygiene false in
local notation "sections" =>
  rationalInducedSmoothOrbitSections hG hi hν Finset.univ hKc hPK πM
set_option hygiene false in
local notation "coeff" =>
  rationalInducedOrbitCoefficientMap hG hi hν Finset.univ hKc hPK πM B hB muM hsqM

set_option maxHeartbeats 300000 in
omit [IsAffine T.X.left] [(rationalPoints.map sL).range.Normal] in
private theorem exists_ambientCoeff_of_representative
    (x : discreteSeriesOrbit A hA mu νG ω)
    (R : UnitaryOrbitRepresentative νM πM)
    (hR : unitaryOrbitRepresentativeDiscreteSeriesOrbit νM πM B hB muM hsqM R = eO x)
    (c : LocallyConstant (rationalPoints G) ℂ)
    (hc : ∃ t : CoefficientTensor (fullLeviAmbientSmoothRep 𝐌 hM R.val.obj),
      coefficientTensorMap (fullLeviAmbientSmoothRep 𝐌 hM R.val.obj) t = c) :
    ∃ t : CoefficientTensor (Quotient.out x.val.val).obj,
      coefficientTensorMap (Quotient.out x.val.val).obj t = c := by
  have hclass : (Quotient.mk _ R.val : SmoothDualClass.{0, u, uV} (k := ℂ) (G := 𝐌)) =
      SmoothDualClass.pullback eG x.val.val := by
    have he := congrArg (fun w : discreteSeriesOrbit B hB muM νM ωM => w.val.val) hR
    change Quotient.mk _ R.val = (eO x).val.val at he
    exact he.trans (congrArg Subtype.val
      (rationalFullLeviOrbitHomeomorph_val hG hi hν s hs mu ω x))
  exact exists_coefficientTensor_of_fullLeviClass 𝐌 hM eG
    (rationalFullLeviLiteralPointEquiv_fullLeviGroupEquiv hG hi hν) x.val.val R.val hclass c hc

set_option maxHeartbeats 300000 in
omit [IsAffine T.X.left] [(rationalPoints.map sL).range.Normal] in
private theorem exists_fullLeviProductCoefficientTensor
    (Q : SmoothRep.{0, u, uV} ℂ 𝐌) (hQ : Q.IsAdmissible)
    (Φ : productInducedCoefficientObject
      (isSemidirectDecomposition_standard hG hi hν
        (RationalPointFamily.rootSet_subset i ν Finset.univ))
      (isClosed_standardUnipotentPoints i ν
        (RationalPointFamily.rootSet i ν Finset.univ)) Q) :
    ∃ t : CoefficientTensor (fullLeviAmbientSmoothRep 𝐌 hM Q),
      coefficientTensorMap (fullLeviAmbientSmoothRep 𝐌 hM Q) t =
        rationalInducedCoefficientMap hG hi hν Finset.univ hKc hPK Q hQ Φ := by
  have h := coefficientTensorMap_rationalFullLeviProductCoefficientTensorEquiv
    hG hi hν hKc hPK Q hQ Φ
  refine ⟨rationalFullLeviProductCoefficientTensorEquiv hG hi hν hKc hPK Q hQ Φ, ?_⟩
  refine (DFunLike.congr ?_ ?_).trans (h.trans (DFunLike.congr ?_ ?_))
  · rfl
  · refine DFunLike.congr ?_ ?_ <;> rfl
  · rfl
  · rfl

omit [IsAffine T.X.left] [(rationalPoints.map sL).range.Normal] in
/-- The full-root orbit coefficient read at the orbit point corresponding to
the given ambient discrete series. -/
def rationalFullLeviAmbientOrbitCoefficient
    (q : sections) (x : discreteSeriesOrbit A hA mu νG ω) :
    LocallyConstant (rationalPoints G) ℂ :=
  coeff q (eO x)

set_option maxHeartbeats 300000 in
set_option backward.isDefEq.respectTransparency.types false in
omit [IsAffine T.X.left] [(rationalPoints.map sL).range.Normal] in
/-- At each ambient orbit point, the coefficient of the transported full-root
section has a tensor in the canonical ambient representative. -/
theorem exists_rationalFullLeviOrbitCoefficientTensor
    (q : sections) (x : discreteSeriesOrbit A hA mu νG ω) :
    ∃ t : CoefficientTensor (Quotient.out x.val.val).obj,
      coefficientTensorMap (Quotient.out x.val.val).obj t =
        rationalFullLeviAmbientOrbitCoefficient hG hi hν s hs mu π hsq hKc hPK q x := by
  unfold rationalFullLeviAmbientOrbitCoefficient
  obtain ⟨R, hR⟩ :=
    unitaryOrbitRepresentativeDiscreteSeriesOrbit_surjective νM πM B hB muM hsqM (eO x)
  let c := rationalInducedCoefficientMap hG hi hν Finset.univ hKc hPK
    R.val.obj R.val.property.2 (q.val R)
  have hc : ∃ t : CoefficientTensor (fullLeviAmbientSmoothRep 𝐌 hM R.val.obj),
      coefficientTensorMap (fullLeviAmbientSmoothRep 𝐌 hM R.val.obj) t = c :=
    exists_fullLeviProductCoefficientTensor hG hi hν hKc hPK
    R.val.obj R.val.property.2 (q.val R)
  obtain ⟨t, ht⟩ :=
    exists_ambientCoeff_of_representative hG hi hν s hs mu π hsq x R hR c hc
  have hq : coeff q (unitaryOrbitRepresentativeDiscreteSeriesOrbit νM πM B hB muM hsqM R) = c := by
    dsimp only [c]
    have h := rationalInducedOrbitCoefficientMap_representative
      hG hi hν Finset.univ hKc hPK πM B hB muM hsqM q R
    with_reducible_and_instances exact h
  have hx := congrArg (fun (y : discreteSeriesOrbit B hB muM νM ωM) => coeff q y) hR
  with_reducible_and_instances exact ⟨t, ht.trans (hq.symm.trans hx)⟩

omit [IsAffine T.X.left] [(rationalPoints.map sL).range.Normal] in
/-- An ambient tensor giving the full-root section coefficient at the
corresponding orbit point. -/
def rationalFullLeviOrbitCoefficientTensor
    (q : sections) (x : discreteSeriesOrbit A hA mu νG ω) :
    CoefficientTensor (Quotient.out x.val.val).obj :=
  (exists_rationalFullLeviOrbitCoefficientTensor hG hi hν s hs mu π hsq hKc hPK q x).choose

omit [IsAffine T.X.left] [(rationalPoints.map sL).range.Normal] in
/-- The chosen tensor gives the transported orbit coefficient as a locally
constant function on the ambient rational points. -/
theorem coefficientTensorMap_rationalFullLeviOrbitCoefficientTensor
    (q : sections) (x : discreteSeriesOrbit A hA mu νG ω) :
    coefficientTensorMap (Quotient.out x.val.val).obj
      (rationalFullLeviOrbitCoefficientTensor hG hi hν s hs mu π hsq hKc hPK q x) =
        rationalFullLeviAmbientOrbitCoefficient hG hi hν s hs mu π hsq hKc hPK q x :=
  (exists_rationalFullLeviOrbitCoefficientTensor hG hi hν s hs mu π hsq hKc hPK q x).choose_spec

end Langlands.HarishChandraSchwartz
