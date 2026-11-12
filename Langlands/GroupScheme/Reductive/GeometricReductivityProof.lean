import Langlands.GroupScheme.Reductive.GeometricReductivityReduction
import Langlands.GroupScheme.Reductive.CentralDerivedProductProof
import Langlands.GroupScheme.Reductive.CharZeroSemisimplicityProof
import Langlands.GroupScheme.Reductive.SteinbergBigCellReduction
import Langlands.GroupScheme.Reductive.SteinbergBigCellRootCorootAssembly
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Reductive.SplitExistence
import Langlands.GroupScheme.Reductive.SplitCentralIsogenyExistenceProof
import Langlands.GroupScheme.Reductive.SplitSemisimplicity
import Langlands.GroupScheme.SimplyConnected.SplitNecessityAssembly
import Langlands.GroupScheme.SimplyConnected.SplitCoverExistenceProof
import Langlands.GroupScheme.Torus.StrictHenselianMaximalReduction
import Langlands.GroupScheme.Derived.SemisimpleReduction
import Langlands.GroupScheme.Derived.MaximalTorusIntersectionReduction
import Langlands.GroupScheme.Derived.CentralIntersectionProof

/-! # Haboush's theorem: reductive groups are geometrically reductive -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix

namespace Langlands.GroupScheme

namespace HaboushReduction

/-- The simply connected positive-characteristic conjugation-map input, obtained from the
Steinberg big-cell assembly, root-datum existence and integral coroot generation, the latter
from the split existence, isogeny and semisimplicity theorems. -/
theorem simplyConnectedConjugationMap :
    SimplyConnectedPositiveCharConjugationMapStatement.{u} :=
  simplyConnectedPositiveCharConjugationMap_of_bigCell
    (steinbergBigCell_of_rootAndCoroot rootDatumExistence
      (splitSimplyConnectedCorootSpan_of_inputs
        ⟨splitReductiveExistence, splitCentralIsogenyExistence, splitSemisimpleRootDatum⟩))

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Over an algebraically closed field, a semisimple group has a split maximal torus, hence a
simply connected central cover. -/
theorem exists_simplyConnected_cover_of_isSemisimple
    {D : GroupScheme (Spec (CommRingCat.of k))} (hD : IsSemisimple D) :
    ∃ (C : GroupScheme (Spec (CommRingCat.of k))) (π : C ⟶ D),
      IsSimplyConnected C ∧ IsCentralIsogeny π := by
  let : Smooth D.X.hom := hD.isConnectedReductive.smooth
  let : IsAffineHom D.X.hom := hD.isConnectedReductive.isAffineHom
  obtain ⟨T, t, ht, hT⟩ := exists_isMaximalTorus_isSplitTorus_of_isSepClosed D
  exact splitSimplyConnectedCoverExistence k D T hD hT t ht

/-- In prime characteristic, a separator for a representation in standard finite coordinates:
the central torus and derived subgroup product, semisimplicity of the derived subgroup, its
simply connected cover and the conjugation-map input. -/
theorem separator_fin_of_isAlgClosed
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
  obtain ⟨C, π, hC, hπ⟩ := exists_simplyConnected_cover_of_isSemisimple hD
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
  let : Epi (subgroupProductMap j d) := epi_subgroupProductMap_iso i d eZ.symm
  exact separator_of_central_split_product p simplyConnectedConjugationMap I j d hcj π hC hπ
    ρ v hv0 hv

/-- In prime characteristic, the normalized finite regular-map construction transports the
standard-coordinate separator to every finite coordinate type. -/
theorem separator_of_isAlgClosed
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
  obtain ⟨r, F, hr, hhom, hinv, hval⟩ := separator_fin_of_isAlgClosed
    p G hG (Chevalley.affineRegularRepresentation G V b hV) (C *ᵥ v) hw0
      (hC.isFixedVector hv)
  exact ⟨r, _, hr, hC.pullback_separator v hhom hinv hval⟩

end HaboushReduction

/-- **Haboush's theorem.** A connected reductive group over an algebraically closed field is
geometrically reductive: every nonzero fixed vector of a finite-dimensional representation is
separated from zero by an invariant homogeneous polynomial of positive degree. -/
theorem reductiveGeometricReductivity : ReductiveGeometricReductivityStatement.{u} := by
  intro k _ _ G hG n _ _ ρ v hv0 hv
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | hp
  · let : Fact (ringChar k).Prime := ⟨hp⟩
    exact HaboushReduction.separator_of_isAlgClosed (ringChar k) G hG n ρ v hv0 hv
  · have : CharP k 0 := hp ▸ inferInstanceAs (CharP k (ringChar k))
    have : CharZero k := CharP.charP_to_charZero k
    exact invariant_polynomial_of_reductive_charZero_semisimplicity
      reductiveCharZeroSemisimplicityStatement G hG n ρ v hv0 hv

end Langlands.GroupScheme
