import Langlands.GroupScheme.Rational.CentralCocharacterDescent
import Langlands.GroupScheme.Torus.SplitPartCharacterTrace
import Langlands.GroupScheme.Rational.RootAnnihilatorCentralityProof
import Langlands.GroupScheme.Rational.RootAnnihilatorRange
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.Geometry.Building.RealTorusDuality
import Langlands.LinearAlgebra.RationalRealSpan

/-! # Character traces from a split component into the actual root span -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme

section IntegralDetection

open RealTorusSpace

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Integral common annihilators detect the rational span of any finite set
of actual characters of a split torus. -/
theorem IsSplitTorus.toRat_mem_ratSpan_iff_annihilator
    (hT : IsSplitTorus T.toGrp) (R : Set (characterLattice T)) [Finite R]
    (χ : characterLattice T) :
    toRat χ ∈ ratSpan R ↔
      ∀ ν : cocharacterLattice T,
        (∀ α ∈ R, latticePairing T α ν = 0) → latticePairing T χ ν = 0 := by
  have hreal :
      (1 : ℝ) ⊗ₜ[ℤ] χ ∈
          Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' R) ↔
        ∀ ν : cocharacterLattice T,
          (∀ α ∈ R, latticePairing T α ν = 0) → latticePairing T χ ν = 0 := by
    rw [← characterAnnihilator_cocharacterAnnihilator hT
        (Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' R)),
      ← rootAnnihilator_eq_cocharacterAnnihilator, mem_characterAnnihilator]
    constructor
    · intro h ν hν
      have hv : (1 : ℝ) ⊗ₜ[ℤ] ν ∈ rootAnnihilator T R := by
        rw [mem_rootAnnihilator]
        intro α hα
        simp only [eval_tmul, hν α hα, Int.cast_zero, mul_zero]
      have hz := h _ hv
      simp only [pair_tmul_tmul, one_mul] at hz
      exact_mod_cast hz
    · intro h
      have hle : rootAnnihilator T R ≤ (eval T χ).ker := by
        rw [rootAnnihilator_le_iff_integral]
        intro ν hν
        change eval T χ ((1 : ℝ) ⊗ₜ[ℤ] ν) = 0
        simp only [eval_tmul, h ν hν, Int.cast_zero, mul_zero]
      intro v hv
      rw [← eval_eq_pair]
      exact hle hv
  rw [← toReal_mem_span_iff (characterLattice T) R (toRat χ), toReal_toRat]
  exact hreal

end IntegralDetection

section Trace

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
  {T A : CommGroupScheme (Spec (CommRingCat.of k))}
  {M : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom T.X.hom] [IsAffineHom M.X.hom]
  {t : T.toGrp ⟶ M} [Mono t.hom.hom.left]
  {a : A.toGrp ⟶ M} (ha : IsSplitComponent a)
  (f : A ⟶ T) (hf : CommGroupScheme.groupHom f ≫ t = a)

local notation "T_K" => Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T
local notation "M_K" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) M
local notation "t_K" =>
  CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k K)) t
local notation "f_K" =>
  CategoryTheory.Functor.map (CommGroupScheme.baseChange (algebraBaseMap k K)) f

include ha hf in
/-- The actual character trace annihilates every cocharacter central in the
extended ambient group. -/
theorem IsSplitComponent.latticePairing_characterTrace_eq_zero
    (χ : characterLattice T_K) (hχ : f_K ≫ χ = 0)
    (ν : cocharacterLattice T_K) (hν : ν ∈ centralCocharacters t_K) :
    latticePairing T_K (CharacterAveraging.galoisOrbitSum k K T χ) ν = 0 := by
  rw [CharacterAveraging.latticePairing_galoisOrbitSum]
  exact ha.latticePairing_centralOrbitSum_eq_zero f hf χ hχ ν hν

variable [Smooth M.X.hom] [ConnectedSpace M.X.left]

local instance instSplitComponentCharacterTrace1 : IsAffineHom (M_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd M.X.hom (algebraBaseMap k K))
  infer_instance

local instance instSplitComponentCharacterTrace2 : Smooth (M_K).X.hom := by
  change Smooth (CategoryTheory.Limits.pullback.snd M.X.hom (algebraBaseMap k K))
  infer_instance

local instance instSplitComponentCharacterTrace3 : ConnectedSpace (M_K).X.left :=
  M.connectedSpace_baseChange_of_smooth_affine (algebraBaseMap k K)

include ha hf in
/-- Tracing a character trivial on the extended rational split component
places it in the actual rational root span over the splitting field. -/
theorem IsSplitComponent.characterTrace_mem_relativeRootSpan
    (hT : IsSplitTorus (T_K).toGrp)
    (χ : characterLattice T_K) (hχ : f_K ≫ χ = 0) :
    toRat (CharacterAveraging.galoisOrbitSum k K T χ) ∈
      relativeRootSpan (T := T_K) t_K := by
  let := (hT.finite_relativeRoots t_K).fintype
  apply (hT.toRat_mem_ratSpan_iff_annihilator (relativeRoots t_K) _).mpr
  intro ν hν
  exact ha.latticePairing_characterTrace_eq_zero f hf χ hχ ν
    (rootAnnihilatorCentrality K M_K T_K hT t_K ν hν)

/-- The Galois character trace as an actual vector of the extended root span. -/
def IsSplitComponent.rootSpanCharacterTrace
    (hT : IsSplitTorus (T_K).toGrp)
    (χ : characterLattice T_K) (hχ : f_K ≫ χ = 0) :
    relativeRootSpan (T := T_K) t_K :=
  ⟨toRat (CharacterAveraging.galoisOrbitSum k K T χ),
    ha.characterTrace_mem_relativeRootSpan f hf hT χ hχ⟩

@[simp] theorem IsSplitComponent.rootSpanCharacterTrace_coe
    (hT : IsSplitTorus (T_K).toGrp)
    (χ : characterLattice T_K) (hχ : f_K ≫ χ = 0) :
    (ha.rootSpanCharacterTrace f hf hT χ hχ : ℚ ⊗[ℤ] characterLattice T_K) =
      toRat (CharacterAveraging.galoisOrbitSum k K T χ) := rfl

end Trace

end Langlands.GroupScheme
