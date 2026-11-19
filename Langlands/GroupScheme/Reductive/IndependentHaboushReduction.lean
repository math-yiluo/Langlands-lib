import Langlands.GroupScheme.Reductive.GeometricReductivityReduction
import Langlands.GroupScheme.Reductive.CentralDerivedProductProof
import Langlands.GroupScheme.Reductive.CharZeroSemisimplicityProof
import Langlands.GroupScheme.Reductive.SteinbergBigCellReduction
import Langlands.GroupScheme.SimplyConnected.SplitCoverExistenceStatement
import Langlands.GroupScheme.SimplyConnected.SplitCoverOfRootDatum
import Langlands.GroupScheme.Torus.StrictHenselianMaximalReduction
import Langlands.GroupScheme.Derived.SemisimpleReduction
import Langlands.GroupScheme.Derived.MaximalTorusIntersectionReduction
import Langlands.GroupScheme.Derived.CentralIntersectionProof

/-! # Geometric reductivity from independent split-cover and Steinberg inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix

namespace Langlands.GroupScheme.IndependentHaboush

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A split-cover input suffices over the algebraically closed ground field. -/
theorem exists_cover
    (hcover : SplitSimplyConnectedCoverExistenceStatement.{u})
    {D : GroupScheme (Spec (CommRingCat.of k))} (hD : IsSemisimple D) :
    ∃ (C : GroupScheme (Spec (CommRingCat.of k))) (π : C ⟶ D),
      IsSimplyConnected C ∧ IsCentralIsogeny π := by
  let : Smooth D.X.hom := hD.isConnectedReductive.smooth
  let : IsAffineHom D.X.hom := hD.isConnectedReductive.isAffineHom
  obtain ⟨T, t, ht, hT⟩ := exists_isMaximalTorus_isSplitTorus_of_isSepClosed D
  exact hcover k D T hD hT t ht

/-- The two remaining positive-characteristic inputs give separators in standard
finite coordinates. Neither input is discharged here. -/
theorem separator_fin
    (hcover : SplitSimplyConnectedCoverExistenceStatement.{u})
    (hcell : SteinbergBigCellStatement.{u})
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsPseudoReductive G)
    {N : ℕ} (ρ : MatrixRepresentation G (Fin N)) (v : Fin N → k)
    (hv0 : v ≠ 0) (hv : ρ.IsFixedVector v) :
    ∃ (r : ℕ) (F : MvPolynomial (Fin N) k), 0 < r ∧ F.IsHomogeneous r ∧
      ρ.IsInvariantPolynomial F ∧ MvPolynomial.eval v F ≠ 0 := by
  have hred := hG.isConnectedReductive_of_isAlgClosed
  obtain ⟨Z, D, i, d, _, _, hZ, _, hc, hd, hepi⟩ := reductiveCentralDerivedProduct k G hred
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Epi (subgroupProductMap i d) := hepi
  obtain ⟨E, c, hcc, hcr, hfin⟩ := derivedCentralIntersectionFiniteness k G D d hred hd
  have hD : IsSemisimple D :=
    ⟨hd.isConnectedReductive hred,
      hd.hasFiniteCenter_of_centralProduct i d hc hd E c hcc hcr hfin⟩
  obtain ⟨C, π, hC, hπ⟩ := exists_cover hcover hD
  let : IsClosedImmersion d.hom.hom.left := hd.1
  let : IsAffineHom D.X.hom := by
    rw [← Over.w d.hom.hom]
    infer_instance
  let : IsAffine D.X.left := isAffine_of_isAffineHom D.X.hom
  obtain ⟨I, hI, ⟨eZ⟩⟩ :=
    hZ.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  let : Finite I := hI
  let : Fintype I := Fintype.ofFinite I
  let : DecidableEq I := Classical.decEq I
  let j : splitTorus (Spec (CommRingCat.of k)) I ⟶ G := eZ.inv ≫ i
  have hcj : IsCentral j := by
    intro T t
    exact hc T (t ≫ eZ.inv.hom.hom)
  let : Epi (subgroupProductMap j d) := HaboushReduction.epi_subgroupProductMap_iso i d eZ.symm
  exact HaboushReduction.separator_of_central_split_product p
    (simplyConnectedPositiveCharConjugationMap_of_bigCell hcell) I j d hcj π hC hπ ρ v hv0 hv

/-- Finite regular coordinates transport the standard-coordinate separator to
any finite coordinate representation without restricting its scheme tests. -/
theorem separator
    (hcover : SplitSimplyConnectedCoverExistenceStatement.{u})
    (hcell : SteinbergBigCellStatement.{u})
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsPseudoReductive G)
    (n : Type) [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n) (v : n → k) (hv0 : v ≠ 0)
    (hv : ρ.IsFixedVector v) :
    ∃ (r : ℕ) (F : MvPolynomial n k), 0 < r ∧ F.IsHomogeneous r ∧
      ρ.IsInvariantPolynomial F ∧ MvPolynomial.eval v F ≠ 0 := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨V, d, b, hV, C, hC, h1⟩ :=
    Chevalley.exists_affine_finite_regular_map_to_one ρ v hv0 hv
  have hw0 : C *ᵥ v ≠ 0 := by
    intro hw
    have h01 : (0 : AffineCoordinates.algebra G) = 1 := by
      simpa only [hw, Pi.zero_apply, zero_smul, Finset.sum_const_zero] using h1
    have hk := congrArg
      (AffineLinearEmbedding.counit (AffineCoordinates.corepresentation G)) h01
    exact zero_ne_one (by simpa only [map_zero, map_one] using hk)
  obtain ⟨r, F, hr, hhom, hinv, hval⟩ := separator_fin hcover hcell
    p G hG (Chevalley.affineRegularRepresentation G V b hV) (C *ᵥ v) hw0
      (hC.isFixedVector hv)
  exact ⟨r, _, hr, hC.pullback_separator v hhom hinv hval⟩

/-- Conditional assembly at every universe. Independent proofs of the two
explicit inputs are still needed before this gives the task's exact target. -/
theorem reductiveGeometricReductivity_of_splitCover_and_bigCell
    (hcover : SplitSimplyConnectedCoverExistenceStatement.{u})
    (hcell : SteinbergBigCellStatement.{u}) :
    ReductiveGeometricReductivityStatement.{u} := by
  intro k _ _ G hG n _ _ ρ v hv0 hv
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | hp
  · let : Fact (ringChar k).Prime := ⟨hp⟩
    exact separator hcover hcell (ringChar k) G hG n ρ v hv0 hv
  · have : CharP k 0 := hp ▸ inferInstanceAs (CharP k (ringChar k))
    have : CharZero k := CharP.charP_to_charZero k
    exact invariant_polynomial_of_reductive_charZero_semisimplicity
      reductiveCharZeroSemisimplicityStatement G hG n ρ v hv0 hv

/-- Root-datum existence supplies the split cover in the conditional assembly.
Both hypotheses still require independent proofs. -/
theorem reductiveGeometricReductivity_of_rootDatum_and_bigCell
    (hRD : RootDatumExistenceStatement.{u})
    (hcell : SteinbergBigCellStatement.{u}) :
    ReductiveGeometricReductivityStatement.{u} :=
  reductiveGeometricReductivity_of_splitCover_and_bigCell
    (splitSimplyConnectedCoverExistence_of_rootDatumExistence hRD) hcell

end Langlands.GroupScheme.IndependentHaboush
