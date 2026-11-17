import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalMinimalInducedJacquetStatement
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalModulusFactorization

/-! # Central face lattices and their uniformizer maps -/

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

/-- The integral lattice annihilated by the roots in a face. -/
def faceCocharacterLattice (J : Set (characterLattice S)) :
    Submodule ℤ (cocharacterLattice S) :=
  (LinearMap.pi fun α : J => latticePairing S α.1).ker

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem faceCocharacterLattice_pairing {J : Set (characterLattice S)}
    (x : faceCocharacterLattice J) {α : characterLattice S} (hα : α ∈ J) :
    latticePairing S α x = 0 :=
  congrFun x.property ⟨α, hα⟩

/-- Uniformizer powers lie in every standard Levi, for arbitrary root subsets. -/
theorem uniformizerPowers_mem_standardLevi (i : S.toGrp ⟶ G)
    (ν : cocharacterLattice S) (J : Set (characterLattice S))
    (x : Multiplicative (cocharacterLattice S)) :
    Aubert.General.uniformizerPowers i x ∈ standardLeviPoints i ν J :=
  range_le_standardLevi i ν J _ ⟨_, rfl⟩

/-- The uniformizer homomorphism with codomain the minimal parabolic. -/
def uniformizerPowersParabolic (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) :
    Multiplicative (cocharacterLattice S) →* standardParabolicPoints i ν ∅ :=
  { toFun := fun x => ⟨Aubert.General.uniformizerPowers i x,
      standardLevi_le_standardParabolic i ν ∅ _
        (uniformizerPowers_mem_standardLevi i ν ∅ x)⟩
    map_one' := Subtype.ext (map_one _)
    map_mul' := fun x y => Subtype.ext (map_mul _ x y) }

/-- The face lattice acts through the actual standard Levi. -/
def faceUniformizerPowers (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    (J : Set (characterLattice S)) :
    Multiplicative (faceCocharacterLattice J) →* standardLeviPoints i ν J :=
  { toFun := fun x => ⟨Aubert.General.uniformizerPowers i (.ofAdd x.toAdd.val),
      uniformizerPowers_mem_standardLevi i ν J _⟩
    map_one' := by
      apply Subtype.ext
      change Aubert.General.uniformizerPowers i 1 = 1
      exact map_one _
    map_mul' := by
      intro x y
      apply Subtype.ext
      change Aubert.General.uniformizerPowers i
        ((.ofAdd x.toAdd.val) * (.ofAdd y.toAdd.val)) = _
      exact map_mul _ _ _ }

/-- A face lattice point is central in the corresponding standard Levi. -/
theorem faceUniformizerPowers_central (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    (hfinite : (simpleRelativeRoots i ν).Finite) (J : Set (characterLattice S))
    (hexists : ∃ ζ, IsStandardCocharacter i ν J ζ)
    (x : Multiplicative (faceCocharacterLattice J))
    (m : standardLeviPoints i ν J) :
    faceUniformizerPowers i ν J x * m = m * faceUniformizerPowers i ν J x := by
  apply Subtype.ext
  have hm : (m : rationalPoints G) ∈
      (cocharacterAnnihilatorCentralizer i J).carrier (Over.mk (𝟙 _)) := by
    rw [← standardLevi_eq_cocharacterAnnihilatorCentralizer i ν hfinite J hexists]
    exact m.property
  rw [mem_cocharacterAnnihilatorCentralizer] at hm
  have hc := hm x.toAdd.val (fun α hα => faceCocharacterLattice_pairing x.toAdd hα)
  rw [← torusCentralizer_gm_eq_dynamicCentralizer, mem_torusCentralizer] at hc
  have h := hc (Over.mk (𝟙 _)) (𝟙 _)
    ((Gm.affinePointsEquiv (𝟙 _)).symm (SplitTorusValuation.uniformizerUnit F))
  rw [Category.id_comp, Grp.comp_hom_hom, ← Category.assoc] at h
  exact h.symm

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] in
/-- Undo the inverse square root in the normalized Jacquet action. -/
theorem jacquet_mk_action_eq_sqrt_smul
    (π : Representation ℂ (rationalPoints G) V)
    (N M : Subgroup (rationalPoints G)) (hMN : M ≤ Subgroup.normalizer N)
    (δ : M →* ℝ≥0ˣ) (m : M) (v : V) :
    Jacquet.mk π N (π m v) =
      (((NNReal.sqrt (δ m : ℝ≥0) : ℝ) : ℂ)) •
        Jacquet.normalizedActionOfModulus π N M hMN δ m (Jacquet.mk π N v) := by
  have hc : (((NNReal.sqrt (δ m : ℝ≥0) : ℝ) : ℂ)) ≠ 0 :=
    Units.ne_zero (Jacquet.complexCharacter (Jacquet.positiveHalfCharacter δ) m)
  rw [Jacquet.normalizedActionOfModulus_mk, smul_smul, mul_inv_cancel₀ hc, one_smul]

end Langlands.HarishChandraSchwartz
