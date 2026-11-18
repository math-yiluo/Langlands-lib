import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCentralLatticeBounds
import Langlands.GroupScheme.Rational.StandardCocharacterProof

/-! # Dominant coefficient bounds from finitely many Jacquet faces -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

set_option maxHeartbeats 1500000

/-- The lattice form of uniform Casselman asymptotics from a simultaneous basis. -/
theorem exists_lattice_casselman_pairings
    (hG : IsConnectedReductive G)
    {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
    {ν : cocharacterLattice S} (hν : IsGenericCocharacter i ν)
    {K0 : Subgroup (rationalPoints G)} (hBasis : SimultaneousStandardBasisAt i ν K0)
    (π : Representation ℂ (rationalPoints G) V) (hπ : IsAdmissible π) :
    ∃ b : ∀ J : Set (characterLattice S),
        Jacquet.Coinvariants (smoothContragredient π) (standardOppositeUnipotentPoints i ν J) →ₗ[ℂ]
          Jacquet.Coinvariants π (standardUnipotentPoints i ν J) →ₗ[ℂ] ℂ,
      ∀ (v : V) (ell : SmoothDual π), ∃ T : ℝ, ∀ lam : cocharacterLattice S,
        (∀ α ∈ simpleRelativeRoots i ν, 0 ≤ latticePairing S α lam) →
        ∀ J, J ⊆ simpleRelativeRoots i ν →
        (∀ α ∈ simpleRelativeRoots i ν, α ∉ J → T < latticePairing S α lam) →
          smoothDualPairing π ell (π (Aubert.General.uniformizerPowers i (.ofAdd lam)) v) =
            b J (Jacquet.mk (smoothContragredient π) (standardOppositeUnipotentPoints i ν J) ell)
              (Jacquet.mk π (standardUnipotentPoints i ν J)
                (π (Aubert.General.uniformizerPowers i (.ofAdd lam)) v)) := by
  classical
  obtain ⟨B, hB, hBJ⟩ := hBasis
  have hdata : ∀ J : Set (characterLattice S),
      ∃ (A' : CommGroupScheme (Spec (CommRingCat.of F))) (q' : A'.toGrp ⟶ S.toGrp),
        J ⊆ simpleRelativeRoots i ν →
          IsCompatibleStandardSplitComponent i ν J A' q' ∧
            ∀ K ∈ B, StandardParabolicBasisMember i ν J q' K := by
    intro J
    by_cases hJ : J ⊆ simpleRelativeRoots i ν
    · obtain ⟨-, A', q', h1, h2⟩ := hBJ J hJ
      exact ⟨A', q', fun _ => ⟨h1, h2⟩⟩
    · exact ⟨S, 𝟙 _, fun h => absurd h hJ⟩
  choose A q hAq using hdata
  have hζex : ∀ J : Set (characterLattice S), ∃ ζ : cocharacterLattice S,
      J ⊆ simpleRelativeRoots i ν → IsStandardCocharacter i ν J ζ := by
    intro J
    by_cases hJ : J ⊆ simpleRelativeRoots i ν
    · obtain ⟨ζ, hζ⟩ := (standardCocharacter F G hG S i hi ν hν J hJ).1
      exact ⟨ζ, fun _ => hζ⟩
    · exact ⟨0, fun h => absurd h hJ⟩
  choose ζ hζ using hζex
  obtain ⟨b, -, hb⟩ := exists_uniform_standardCasselmanPairing hG hi hν hB A q
    (fun J hJ => (hAq J hJ).1) (fun J hJ => (hAq J hJ).2) ζ hζ π hπ
  exact ⟨b, hb⟩

/-- Uniform unipotence on each face gives a degree independent of the vector
and smooth functional in the dominant coefficient estimate. -/
theorem exists_dominant_lattice_coefficient_bound
    (hG : IsConnectedReductive G)
    {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
    {ν : cocharacterLattice S} (hν : IsGenericCocharacter i ν)
    {K0 : Subgroup (rationalPoints G)} (hBasis : SimultaneousStandardBasisAt i ν K0)
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (ρ : MatrixRepresentation G n) (hρ : IsClosedSubgroup ρ)
    (π : Representation ℂ (rationalPoints G) V) (hπ : IsAdmissible π)
    (hUnip : ∀ J : Set (characterLattice S), J ⊆ simpleRelativeRoots i ν →
      ∃ r : ℕ, ∀ x : Multiplicative (faceCocharacterLattice J),
        (Jacquet.normalizedActionOfModulus π
          (standardUnipotentPoints i ν J) (standardLeviPoints i ν J)
          (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J)
          (standardUnipotentModulus i ν J) (faceUniformizerPowers i ν J x) - 1) ^ r = 0) :
    ∃ d : ℕ, ∀ (v : V) (ell : SmoothDual π), ∃ C : ℝ, 0 ≤ C ∧
      ∀ lam : cocharacterLattice S,
        (∀ α ∈ simpleRelativeRoots i ν, 0 ≤ latticePairing S α lam) →
          ‖smoothDualPairing π ell (π (Aubert.General.uniformizerPowers i (.ofAdd lam)) v)‖ ≤
            C * (NNReal.sqrt (rationalMinimalModulus i ν
                (uniformizerPowersParabolic i ν (.ofAdd lam)) : ℝ≥0) : ℝ) *
              (1 + rationalHeight (F := F) ρ
                (Aubert.General.uniformizerPowers i (.ofAdd lam))) ^ d := by
  classical
  have hfinite := hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν
  let Face := {J : Set (characterLattice S) // J ⊆ simpleRelativeRoots i ν}
  let : Fintype Face := hfinite.finite_subsets.fintype
  choose r hr using fun j : Face => hUnip j.1 j.2
  choose ds hds using fun j : Face => exists_face_jacquet_coefficient_height hG hi hν j.2
    (standardCocharacter F G hG S i hi ν hν j.1 j.2).1 ρ hρ π (r j) (hr j)
  obtain ⟨b, hb⟩ := exists_lattice_casselman_pairings hG hi hν hBasis π hπ
  refine ⟨Finset.univ.sup ds, fun v ell => ?_⟩
  obtain ⟨T, hT⟩ := hb v ell
  have hreps : ∀ j : Face, ∃ M : Set (cocharacterLattice S), M.Finite ∧
      ∀ lam : cocharacterLattice S,
        (∀ α ∈ j.1, 0 ≤ latticePairing S α lam ∧ latticePairing S α lam ≤ ⌈T⌉) →
          ∃ m ∈ M, lam - m ∈ faceCocharacterLattice j.1 := by
    intro j
    let : Fintype j.1 := (hfinite.subset j.2).fintype
    let f := (LinearMap.pi fun α : j.1 => latticePairing S α.1).toAddMonoidHom
    obtain ⟨M, hM, hm⟩ := LatticeFaceTools.exists_finite_representatives f ⌈T⌉
    refine ⟨M, hM, fun lam hlam => ?_⟩
    obtain ⟨m, hmem, hzero⟩ := hm lam (fun α => hlam α.1 α.2)
    exact ⟨m, hmem, hzero⟩
  choose Ms hMs hrep using hreps
  let : ∀ j : Face, Fintype (Ms j) := fun j => (hMs j).fintype
  let ellJ (j : Face) := b j.1
    (Jacquet.mk (smoothContragredient π) (standardOppositeUnipotentPoints i ν j.1) ell)
  choose Cs hCs hCsbound using fun (j : Face) (m : cocharacterLattice S) =>
    hds j v (ellJ j) m
  let total : ℝ := ∑ j : Face, ∑ m : Ms j, Cs j m
  have htotal : 0 ≤ total := Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun m _ => hCs j m
  have hCle (j : Face) (m : Ms j) : Cs j m ≤ total := by
    calc
      _ ≤ ∑ a : Ms j, Cs j a :=
        Finset.single_le_sum (f := fun a : Ms j => Cs j a)
          (fun a _ => hCs j a) (Finset.mem_univ m)
      _ ≤ ∑ a : Face, ∑ b : Ms a, Cs a b :=
        Finset.single_le_sum (f := fun a : Face => ∑ b : Ms a, Cs a b) (fun a _ =>
          Finset.sum_nonneg fun b _ => hCs a b) (Finset.mem_univ j)
  refine ⟨total, htotal, fun lam hlam => ?_⟩
  let j : Face :=
    ⟨{α | α ∈ simpleRelativeRoots i ν ∧ latticePairing S α lam ≤ ⌈T⌉},
      fun _ h => h.1⟩
  have hdeep : ∀ α ∈ simpleRelativeRoots i ν, α ∉ j.1 → T < latticePairing S α lam := by
    intro α hα hαj
    have hlt : ⌈T⌉ < latticePairing S α lam := lt_of_not_ge fun h => hαj ⟨hα, h⟩
    have hlt' : (⌈T⌉ : ℝ) < (latticePairing S α lam : ℝ) := by exact_mod_cast hlt
    exact lt_of_le_of_lt (Int.le_ceil T) hlt'
  obtain ⟨m, hm, hx⟩ := hrep j lam (fun α hα => ⟨hlam α hα.1, hα.2⟩)
  let x : faceCocharacterLattice j.1 := ⟨lam - m, hx⟩
  have hbound := hCsbound j m x
  simp only [x, sub_add_cancel] at hbound
  rw [hT lam hlam j.1 j.2 hdeep]
  change ‖ellJ j (Jacquet.mk π (standardUnipotentPoints i ν j.1)
    (π (Aubert.General.uniformizerPowers i (.ofAdd lam)) v))‖ ≤ _
  have hbase : 1 ≤ 1 + rationalHeight (F := F) ρ
      (Aubert.General.uniformizerPowers i (.ofAdd lam)) :=
    le_add_of_nonneg_right (rationalHeight_nonneg ρ _)
  have hδ : 0 ≤ (NNReal.sqrt (rationalMinimalModulus i ν
      (uniformizerPowersParabolic i ν (.ofAdd lam)) : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
  calc
    _ ≤ Cs j m * _ * _ ^ ds j := hbound
    _ ≤ Cs j m * _ * _ ^ Finset.univ.sup ds :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hbase (Finset.le_sup (Finset.mem_univ j))) (mul_nonneg (hCs j m) hδ)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hCle j ⟨m, hm⟩) hδ)
        (pow_nonneg (zero_le_one.trans hbase) _)

end Langlands.HarishChandraSchwartz
