import Langlands.GroupScheme.Reductive.GeometricReductivityStatement
import Langlands.GroupScheme.Reductive.RegularConjugationReduction
import Langlands.GroupScheme.Reductive.InvariantPolynomialUniversal
import Langlands.GroupScheme.Reductive.PositiveCharConjugationMapStatement
import Langlands.GroupScheme.Reductive.CharZeroSemisimplicityStatement
import Langlands.GroupScheme.Reductive.CentralDerivedProductStatement
import Langlands.GroupScheme.Reductive.AlgebraicallyClosedPseudoReductive
import Langlands.GroupScheme.SimplyConnected.DerivedCoverStatement
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.SplitReflection

/-! # Conditional assembly of geometric reductivity -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace HaboushReduction

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The conjugation-map input on a supplied simply connected cover gives
an invariant separator downstairs, without descending the auxiliary representation. -/
theorem separator_of_simplyConnected_cover
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (hmap : SimplyConnectedPositiveCharConjugationMapStatement.{u})
    {C D : GroupScheme (Spec (CommRingCat.of k))}
    (π : C ⟶ D) (hC : IsSimplyConnected C) (hπ : IsCentralIsogeny π)
    {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation D n) (v : n → k) (hv0 : v ≠ 0)
    (hv : ρ.IsFixedVector v) :
    ∃ (r : ℕ) (F : MvPolynomial n k), 0 < r ∧ F.IsHomogeneous r ∧
      ρ.IsInvariantPolynomial F ∧ MvPolynomial.eval v F ≠ 0 := by
  have hv' : (ρ.restrict π).IsFixedVector v := by
    intro T g
    rw [MatrixRepresentation.pointMatrix_restrict]
    exact hv T (g ≫ π.hom.hom)
  obtain ⟨m, hm, σ, φ, a, ha, hφ⟩ := hmap k p C hC n (ρ.restrict π) v hv0 hv'
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  obtain ⟨r, F, hr, hhom, hinv, hval⟩ :=
    φ.exists_invariant_polynomial_of_scalar v ha hφ
  let : Flat π.hom.hom.left := hπ.flat
  let : Surjective π.hom.hom.left := hπ.surjective
  exact ⟨r, F, hr, hhom, (ρ.isInvariantPolynomial_restrict_iff π F).mp hinv, hval⟩

/-- A central split-torus product combines a separator on the covered factor
with the zero-weight projection. -/
theorem separator_of_central_split_product
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (hmap : SimplyConnectedPositiveCharConjugationMapStatement.{u})
    {G D C : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffine G.X.left] [IsAffine D.X.left]
    (I : Type u) [Fintype I] [DecidableEq I]
    (j : splitTorus (Spec (CommRingCat.of k)) I ⟶ G) (d : D ⟶ G)
    (hc : IsCentral j) [Epi (subgroupProductMap j d)]
    (π : C ⟶ D) (hC : IsSimplyConnected C) (hπ : IsCentralIsogeny π)
    {N : ℕ} (ρ : MatrixRepresentation G (Fin N)) (v : Fin N → k)
    (hv0 : v ≠ 0) (hv : ρ.IsFixedVector v) :
    ∃ (r : ℕ) (F : MvPolynomial (Fin N) k), 0 < r ∧ F.IsHomogeneous r ∧
      ρ.IsInvariantPolynomial F ∧ MvPolynomial.eval v F ≠ 0 := by
  have hvd : (ρ.restrict d).IsFixedVector v := by
    intro T g
    rw [MatrixRepresentation.pointMatrix_restrict]
    exact hv T (g ≫ d.hom.hom)
  have hvj : (ρ.restrict j).IsFixedVector v := by
    intro T g
    rw [MatrixRepresentation.pointMatrix_restrict]
    exact hv T (g ≫ j.hom.hom)
  obtain ⟨r, F, hr, hhom, hinv, hval⟩ :=
    separator_of_simplyConnected_cover p hmap π hC hπ (ρ.restrict d) v hv0 hvd
  exact ⟨r, _, hr,
    MatrixRepresentation.CentralZeroWeight.linearPullback_separator_of_epi_product
      ρ I j d hc v hvj hhom hinv hval⟩

/-- Changing the parametrization of one factor by an isomorphism preserves
the epimorphic subgroup product. -/
theorem epi_subgroupProductMap_iso
    {S : Scheme.{u}} {G Z Z' D : GroupScheme S}
    (i : Z ⟶ G) (d : D ⟶ G) (e : Z' ≅ Z)
    [Epi (subgroupProductMap i d)] :
    Epi (subgroupProductMap (e.hom ≫ i) d) := by
  let a : Z'.X ⊗ D.X ⟶ Z.X ⊗ D.X := e.hom.hom.hom ⊗ₘ 𝟙 D.X
  have : IsIso e.hom.hom.hom := (Grp.forget (Over S)).map_isIso e.hom
  have : IsIso a := by dsimp [a]; infer_instance
  have heq : a ≫ subgroupProductMap i d = subgroupProductMap (e.hom ≫ i) d := by
    simp only [a, subgroupProductMap, MonObj.comp_mul,
      tensorHom_fst_assoc, tensorHom_snd_assoc, Category.id_comp, Grp.comp_hom_hom]
  rw [← heq]
  infer_instance

/-- The two structural existence inputs and the positive-characteristic map
input give separators for representations in standard finite coordinates. -/
theorem separator_fin_of_structural_inputs
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (hproduct : ReductiveCentralDerivedProductStatement.{u})
    (hcover : SimplyConnectedDerivedCoverExistenceStatement.{u})
    (hmap : SimplyConnectedPositiveCharConjugationMapStatement.{u})
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsPseudoReductive G)
    {N : ℕ} (ρ : MatrixRepresentation G (Fin N)) (v : Fin N → k)
    (hv0 : v ≠ 0) (hv : ρ.IsFixedVector v) :
    ∃ (r : ℕ) (F : MvPolynomial (Fin N) k), 0 < r ∧ F.IsHomogeneous r ∧
      ρ.IsInvariantPolynomial F ∧ MvPolynomial.eval v F ≠ 0 := by
  have hred := hG.isConnectedReductive_of_isAlgClosed
  obtain ⟨Z, D, i, d, _, _, hZ, _, hc, hd, hepi⟩ := hproduct k G hred
  obtain ⟨D', C, d', π, hcov⟩ := hcover k G hred
  let e : D' ≅ D :=
    SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy
      hcov.isDerivedSubgroup.isRepresentedBy hd.isRepresentedBy
  have hπ : IsCentralIsogeny (π ≫ e.hom) :=
    hcov.isSimplyConnectedCover.isCentralIsogeny.comp_iso e
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
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
  let : Epi (subgroupProductMap i d) := hepi
  let : Epi (subgroupProductMap j d) := epi_subgroupProductMap_iso i d eZ.symm
  exact separator_of_central_split_product p hmap I j d hcj (π ≫ e.hom)
    hcov.isSimplyConnectedCover.isSimplyConnected hπ ρ v hv0 hv

/-- The normalized finite regular-map construction transports the standard-coordinate
separator back to every finite coordinate type. -/
theorem separator_of_structural_inputs
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (hproduct : ReductiveCentralDerivedProductStatement.{u})
    (hcover : SimplyConnectedDerivedCoverExistenceStatement.{u})
    (hmap : SimplyConnectedPositiveCharConjugationMapStatement.{u})
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
  obtain ⟨r, F, hr, hhom, hinv, hval⟩ := separator_fin_of_structural_inputs
    p hproduct hcover hmap G hG (Chevalley.affineRegularRepresentation G V b hV)
      (C *ᵥ v) hw0 (hC.isFixedVector hv)
  exact ⟨r, _, hr, hC.pullback_separator v hhom hinv hval⟩

end HaboushReduction

/-- Conditional final assembly. All four structural and representation-theoretic
propositions remain explicit hypotheses; this theorem does not discharge them. -/
theorem reductiveGeometricReductivity_of_structural_inputs
    (hproduct : ReductiveCentralDerivedProductStatement.{u})
    (hcover : SimplyConnectedDerivedCoverExistenceStatement.{u})
    (hmap : SimplyConnectedPositiveCharConjugationMapStatement.{u})
    (hzero : ReductiveCharZeroSemisimplicityStatement.{u}) :
    ReductiveGeometricReductivityStatement.{u} := by
  intro k _ _ G hG n _ _ ρ v hv0 hv
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | hp
  · let : Fact (ringChar k).Prime := ⟨hp⟩
    exact HaboushReduction.separator_of_structural_inputs (ringChar k) hproduct hcover hmap
      G hG n ρ v hv0 hv
  · have : CharP k 0 := hp ▸ inferInstanceAs (CharP k (ringChar k))
    have : CharZero k := CharP.charP_to_charZero k
    exact invariant_polynomial_of_reductive_charZero_semisimplicity
      hzero G hG n ρ v hv0 hv

namespace MatrixRepresentation

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- A polynomial separator selected from the conditional assembly.
All four still-unproved inputs are arguments of this construction. -/
def separatorOfStructuralInputs (ρ : MatrixRepresentation G n)
    (hproduct : ReductiveCentralDerivedProductStatement.{u})
    (hcover : SimplyConnectedDerivedCoverExistenceStatement.{u})
    (hmap : SimplyConnectedPositiveCharConjugationMapStatement.{u})
    (hzero : ReductiveCharZeroSemisimplicityStatement.{u})
    (hG : IsPseudoReductive G) (v : n → k) (hv0 : v ≠ 0)
    (hv : ρ.IsFixedVector v) : MvPolynomial n k :=
  Classical.choose (Classical.choose_spec
    (reductiveGeometricReductivity_of_structural_inputs hproduct hcover hmap hzero
      k G hG n ρ v hv0 hv))

/-- The selected polynomial has positive homogeneous degree, is invariant on every
relative test scheme, and does not vanish at the supplied fixed vector. -/
theorem separatorOfStructuralInputs_spec (ρ : MatrixRepresentation G n)
    (hproduct : ReductiveCentralDerivedProductStatement.{u})
    (hcover : SimplyConnectedDerivedCoverExistenceStatement.{u})
    (hmap : SimplyConnectedPositiveCharConjugationMapStatement.{u})
    (hzero : ReductiveCharZeroSemisimplicityStatement.{u})
    (hG : IsPseudoReductive G) (v : n → k) (hv0 : v ≠ 0)
    (hv : ρ.IsFixedVector v) :
    ∃ r : ℕ, 0 < r ∧
      (ρ.separatorOfStructuralInputs hproduct hcover hmap hzero hG v hv0 hv).IsHomogeneous r ∧
      ρ.IsInvariantPolynomial
        (ρ.separatorOfStructuralInputs hproduct hcover hmap hzero hG v hv0 hv) ∧
      MvPolynomial.eval v
        (ρ.separatorOfStructuralInputs hproduct hcover hmap hzero hG v hv0 hv) ≠ 0 := by
  let h := reductiveGeometricReductivity_of_structural_inputs hproduct hcover hmap hzero
    k G hG n ρ v hv0 hv
  exact ⟨Classical.choose h, Classical.choose_spec (Classical.choose_spec h)⟩

end MatrixRepresentation

end Langlands.GroupScheme
