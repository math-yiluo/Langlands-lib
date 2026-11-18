import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLatticeHeightTools
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalFaceLattice
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalFaceJacquetCoefficientBoundStatement
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalModulusFactorization

/-! # Coefficient bounds on central cocharacter lattices -/

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

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

variable [LocallyOfFiniteType G.X.hom]

set_option maxHeartbeats 1500000

/-- On the face lattice, the normalizing modulus equals the minimal modulus. -/
theorem faceUniformizerPowers_modulus (hG : IsConnectedReductive G)
    {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
    {ν : cocharacterLattice S} (hν : IsGenericCocharacter i ν)
    {J : Set (characterLattice S)} (hJ : J ⊆ simpleRelativeRoots i ν)
    (hexists : ∃ ζ, IsStandardCocharacter i ν J ζ)
    (x : Multiplicative (faceCocharacterLattice J)) :
    standardUnipotentModulus i ν J (faceUniformizerPowers i ν J x) =
      rationalMinimalModulus i ν
        (uniformizerPowersParabolic i ν (.ofAdd x.toAdd.val)) := by
  let p : (standardParabolicPoints i ν ∅ ⊓ standardLeviPoints i ν J :
      Subgroup (rationalPoints G)) :=
    ⟨_, (uniformizerPowersParabolic i ν (.ofAdd x.toAdd.val)).property,
      (faceUniformizerPowers i ν J x).property⟩
  have hp (m : rationalPoints G) (hm : m ∈ standardLeviPoints i ν J) :
      (p : rationalPoints G) * m = m * p :=
    congrArg Subtype.val
      (faceUniformizerPowers_central i ν (hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν)
        J hexists x ⟨m, hm⟩)
  exact (rationalMinimalModulus_eq_standardUnipotentModulus_of_commute
    hG hi hν hJ p hp).symm

/-- Facewise polynomial growth for the unnormalized Jacquet coefficient, with
the square root of the minimal modulus and the actual matrix height. -/
theorem exists_face_jacquet_coefficient_height (hG : IsConnectedReductive G)
    {i : S.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
    {ν : cocharacterLattice S} (hν : IsGenericCocharacter i ν)
    {J : Set (characterLattice S)} (hJ : J ⊆ simpleRelativeRoots i ν)
    (hexists : ∃ ζ, IsStandardCocharacter i ν J ζ)
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (ρ : MatrixRepresentation G n) (hρ : IsClosedSubgroup ρ)
    (π : Representation ℂ (rationalPoints G) V) (r : ℕ)
    (hr : ∀ x : Multiplicative (faceCocharacterLattice J),
      (Jacquet.normalizedActionOfModulus π
        (standardUnipotentPoints i ν J) (standardLeviPoints i ν J)
        (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J)
        (standardUnipotentModulus i ν J) (faceUniformizerPowers i ν J x) - 1) ^ r = 0) :
    ∃ d : ℕ, ∀ (v : V)
      (ell : Module.Dual ℂ (Jacquet.Coinvariants π (standardUnipotentPoints i ν J)))
      (m : cocharacterLattice S),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x : faceCocharacterLattice J,
        ‖ell (Jacquet.mk π (standardUnipotentPoints i ν J)
          (π (Aubert.General.uniformizerPowers i (.ofAdd ((x : cocharacterLattice S) + m))) v))‖ ≤
          C * (NNReal.sqrt (rationalMinimalModulus i ν
              (uniformizerPowersParabolic i ν (.ofAdd ((x : cocharacterLattice S) + m))) :
                ℝ≥0) : ℝ) *
            (1 + rationalHeight (F := F) ρ
              (Aubert.General.uniformizerPowers i (.ofAdd ((x : cocharacterLattice S) + m)))) ^ d := by
  classical
  let πN := Jacquet.normalizedActionOfModulus π
    (standardUnipotentPoints i ν J) (standardLeviPoints i ν J)
    (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J)
    (standardUnipotentModulus i ν J)
  let πF := πN.comp (faceUniformizerPowers i ν J)
  obtain ⟨d, hd⟩ := exists_unipotent_submodule_coefficient_height i hi.isSplitSubtorus.1
    hi.isSplitSubtorus.2 ρ hρ (faceCocharacterLattice J) πF r hr
  let halfδ := (Jacquet.positiveHalfCharacter (rationalMinimalModulus i ν)).comp
    (uniformizerPowersParabolic i ν)
  refine ⟨d, fun v ell m => ?_⟩
  let w := Jacquet.mk π (standardUnipotentPoints i ν J)
    (π (Aubert.General.uniformizerPowers i (.ofAdd m)) v)
  obtain ⟨C, hC, hCbound⟩ := hd w ell m
  have hhalfδm : 0 < ((halfδ (.ofAdd m) : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero _))
  refine ⟨C / ((halfδ (.ofAdd m) : ℝ≥0) : ℝ), div_nonneg hC hhalfδm.le, fun x => ?_⟩
  have hmul :
      π (Aubert.General.uniformizerPowers i (.ofAdd ((x : cocharacterLattice S) + m))) v =
        π (faceUniformizerPowers i ν J (.ofAdd x))
          (π (Aubert.General.uniformizerPowers i (.ofAdd m)) v) := by
    change π (Aubert.General.uniformizerPowers i
      ((.ofAdd (x : cocharacterLattice S)) * (.ofAdd m))) v = _
    rw [map_mul, map_mul, Module.End.mul_apply]
    rfl
  have hquot :
      Jacquet.mk π (standardUnipotentPoints i ν J)
        (π (Aubert.General.uniformizerPowers i (.ofAdd ((x : cocharacterLattice S) + m))) v) =
      ((((halfδ (.ofAdd (x : cocharacterLattice S)) : ℝ≥0) : ℝ) : ℂ)) • πF (.ofAdd x) w := by
    rw [hmul, jacquet_mk_action_eq_sqrt_smul]
    change _ = _ • πN (faceUniformizerPowers i ν J (.ofAdd x)) w
    rw [faceUniformizerPowers_modulus hG hi hν hJ hexists]
    rfl
  have hhalfδmul :
      ((halfδ (.ofAdd ((x : cocharacterLattice S) + m)) : ℝ≥0) : ℝ) =
        ((halfδ (.ofAdd (x : cocharacterLattice S)) : ℝ≥0) : ℝ) *
          ((halfδ (.ofAdd m) : ℝ≥0) : ℝ) := by
    change ((halfδ ((.ofAdd (x : cocharacterLattice S)) * (.ofAdd m)) : ℝ≥0) : ℝ) = _
    rw [map_mul, Units.val_mul, NNReal.coe_mul]
  rw [hquot, map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (NNReal.coe_nonneg _)]
  calc
    _ ≤ ((halfδ (.ofAdd (x : cocharacterLattice S)) : ℝ≥0) : ℝ) *
        (C * (1 + rationalHeight (F := F) ρ
          (Aubert.General.uniformizerPowers i (.ofAdd ((x : cocharacterLattice S) + m)))) ^ d) :=
      mul_le_mul_of_nonneg_left (hCbound x) (NNReal.coe_nonneg _)
    _ = _ := by
      change _ = (C / ((halfδ (.ofAdd m) : ℝ≥0) : ℝ)) *
        ((halfδ (.ofAdd ((x : cocharacterLattice S) + m)) : ℝ≥0) : ℝ) * _
      rw [hhalfδmul]
      field_simp

/-- The complete facewise growth prerequisite at arbitrary universes. -/
theorem rationalFaceJacquetCoefficientBound :
    RationalFaceJacquetCoefficientBoundStatement.{u, uV} := by
  intro F _ _ _ _ G _ _ S V _ _ hG i hi ν hν J hJ hexists
    n _ _ _ ρ hρ π r hr
  exact exists_face_jacquet_coefficient_height hG hi hν hJ hexists ρ hρ π r hr

end Langlands.HarishChandraSchwartz
