import Langlands.GroupScheme.Dynamic.FlagQuotientCell
import Langlands.GroupScheme.Dynamic.FlagQuotientDensity
import Langlands.GroupScheme.Dynamic.FlagQuotientFiber
import Langlands.GroupScheme.Dynamic.FlagQuotientStatement
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.Absolute.DynamicParabolicRecognition
import Langlands.GroupScheme.Reductive.RationalPointDensityProof
import Langlands.GroupScheme.Absolute.OppositeCellProof
import Langlands.GroupScheme.FiniteFieldTorsorPointProof
import Langlands.GroupScheme.HomogeneousQuotientProof
import Langlands.GroupScheme.ParabolicQuotientProperProof

/-! # Proper dynamic flag quotients with rational-point local sections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.GroupScheme.Dynamic

/-- Every dynamic parabolic of a connected reductive group has a proper
quotient with exact all-test coset fibers and algebraic sections near every
rational point. -/
theorem dynamicFlagQuotientExistence :
    DynamicFlagQuotientExistenceStatement.{u} := by
  have hcell : OppositeCellStatement.{u} := oppositeCellStatement.{u}
  intro k _ G hG χ
  let := hG.smooth
  let := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let P := Affine.parabolicScheme χ
  let iP : P ⟶ G := Affine.parabolicHom χ
  have hrepr : (parabolic χ).IsRepresentedBy iP :=
    Affine.isRepresentedBy_parabolicHom χ
  have hclosed : IsClosedSubgroup iP := Affine.isClosedSubgroup_parabolicHom χ
  have hP : IsParabolicSubgroup iP :=
    isParabolicSubgroup_of_range_eq_dynamicParabolic hG iP hclosed χ hrepr.2
  obtain ⟨Q, q, hsep, hft, hqc, hsm, hsurj, hqcc, hf⟩ :=
    smoothSubgroupQuotientExistence k G P iP hclosed hP.smooth
  have hQproper : IsProper Q.hom :=
    parabolicSubgroupQuotientProper k G hG.connectedSpace P iP hP Q q
      hsep hft hqc hsm hsurj hqcc hf
  have hfdyn : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (parabolic χ).carrier T := by
    simpa only [hrepr.2] using hf
  let χneg := CommGroupScheme.groupHom
    (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ
  let U := Affine.unipotentScheme χneg
  let iU : U ⟶ G := Affine.unipotentHom χneg
  have hU : (unipotent χneg).IsRepresentedBy iU :=
    Affine.isRepresentedBy_unipotentHom χneg
  let : Mono iP.hom.hom := hrepr.1
  let : Smooth q.left := hsm
  let : Surjective q.left := hsurj
  let : QuasiCompact q.left := hqcc
  let : IsOpenImmersion (QuotientCell.multiplication iP iU.hom.hom).left :=
    hcell k G χ U P iU iP hU hrepr
  have hlift : ∀ p : RingPoint k Q k, ∃ g : RingPoint k G.X k, g ≫ q = p := by
    rcases finite_or_infinite k with hfin | hinf
    · let : Finite k := hfin
      let : Smooth P.X.hom := hP.smooth
      let : IsClosedImmersion iP.hom.hom.left := hclosed
      let : IsAffineHom P.X.hom := by
        rw [← Over.w iP.hom.hom]
        infer_instance
      let : ConnectedSpace G.X.left := hG.connectedSpace
      have hPconn := DynamicConnected.connectedSpace_of_isRepresentedBy_parabolic
        G χ hrepr
      exact rational_lifts_of_finite_torsor k G P q iP hf
        finiteFieldTorsorPointStatement.{u} hPconn
    · let : Infinite k := hinf
      let seed := flagQuotientCell k iP iU q hf
      have hseed := range_identity_subset_flagQuotientCell k iP iU q hf
      rw [rationalPointEquiv_left] at hseed
      exact rational_lifts_of_reductive_density k G (SubgroupFunctor.range iP) q hf
        reductiveRationalPointDensity.{u} hG seed.1 seed.2 hseed (flagQuotientCell_comp k iP iU q hf)
  exact ⟨Q, q, hQproper, hfdyn,
    localSections_of_open_multiplication k iP iU q hf hlift⟩

end Langlands.GroupScheme
