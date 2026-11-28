import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitWeakCasselman
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionTargets

/-! # The coefficient tensor on the fixed compact picture -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.BruhatTits.SpecialCompact
open RationalPointFamily

namespace Langlands.HarishChandraSchwartz.WeakExpansion

universe u uV

set_option maxRecDepth 8000

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I : Finset (SimpleRoot i ν))
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)

set_option hygiene false in
local notation "𝐌" => standardLeviPoints i ν (rootSet i ν I)
set_option hygiene false in
local notation "decomp" => isSemidirectDecomposition_standard hG hi hν (rootSet_subset i ν I)
set_option hygiene false in
local notation "closedU" => isClosed_standardUnipotentPoints i ν (rootSet i ν I)
set_option hygiene false in
local notation "νM" => leviRationalNormCharacters i ν I

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))

set_option hygiene false in
local notation "twistRep" χ => unitaryOrbitTwistRepresentative νM π χ
set_option hygiene false in
local notation "induced" χ =>
  (normalizedInductionFunctor decomp closedU).obj (twistRep χ).val.obj
set_option hygiene false in
local notation "Picture" => ProductInducedCompactPicture decomp K π.obj
set_option hygiene false in
local notation "Sections" => rationalInducedSmoothOrbitSections hG hi hν I hKc hPK π

private def upperCompactEquiv (χ : unitaryUnramifiedCharacters νM) :
    productInducedCoefficientObject decomp closedU (twistRep χ).val.obj ≃ₗ[ℂ] Picture :=
  (productInducedCompactEquiv νM decomp K
    (isClosed_standardParabolicPoints_rootSet hG hi hν I) hKc
    (continuous_leviRationalNormCharacters i ν I)
    (continuous_projection_standard hG hi hν (rootSet_subset i ν I) decomp)
    closedU (factorization_subtype (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK))
    (unitaryUnramifiedInclusion νM χ) π.obj).toLinearEquiv

/-- Recover the coefficient tensor from the fixed compact picture at a unitary parameter. -/
def rationalCompactCoefficientTensorEquiv (χ : unitaryUnramifiedCharacters νM) :
    Picture ≃ₗ[ℂ] CoefficientTensor (induced χ) :=
  (upperCompactEquiv hG hi hν I hKc hPK π χ).symm.trans
    (rationalInducedCoefficientTensorEquiv hG hi hν I hKc hPK
      (twistRep χ).val.obj (twistRep χ).val.property.2).toLinearEquiv

set_option maxHeartbeats 1600000 in
/-- On the compact restriction of a section, this is the tensor of the section's value. -/
theorem rationalCompactCoefficientTensorEquiv_section (q : Sections)
    (χ : unitaryUnramifiedCharacters νM) :
    rationalCompactCoefficientTensorEquiv hG hi hν I hKc hPK π χ
        (sectionCompactPicture hG hi hν I hKc hPK π q χ) =
      rationalOrbitCoefficientTensor hG hi hν I hKc hPK π q χ := by
  let e := (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv
  have h :
      sectionCompactPicture hG hi hν I hKc hPK π q χ =
        upperCompactEquiv hG hi hν I hKc hPK π χ (q.val (twistRep χ)) := by
    change upperCompactEquiv hG hi hν I hKc hPK π (e.symm (e χ))
        (q.val (twistRep (e.symm (e χ)))) = _
    rw [e.symm_apply_apply]
  rw [h]
  simp only [rationalCompactCoefficientTensorEquiv, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]
  rfl

end Langlands.HarishChandraSchwartz.WeakExpansion
