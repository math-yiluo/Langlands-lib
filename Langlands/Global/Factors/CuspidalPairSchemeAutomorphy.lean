import Langlands.Global.Factors.CuspidalPairEisensteinSeries
import Langlands.Global.AdelicBlockAutomorphicSections
import Langlands.Automorphic.CuspidalJointAdmissibility

/-! # Cuspidal-pair sections as automorphic functions on the block-parabolic quotient

A section `φ` with `IsSection T T' φ` is a smooth compact-finite realized section of the upper
two-block shape for the realizations `T` and `(T')^∨`. Transported to the points of the group
scheme `GL_N`, it is therefore an automorphic function on `U_P(𝔸) M(F) \ GL_N(𝔸)`. See the paired
Markdown. -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

namespace Langlands.Global.CuspidalPairEisenstein

open Langlands.Automorphic Langlands.GeneralLinear
open Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
open AdelicBlockScalarSections AdelicBlockEisensteinGeometry AdelicGroupPoints
  GeneralLinearGroupPoints
open Langlands.Automorphic.GroupSchemeFunctions AdelicBlockParabolic
  AdelicBlockDeterminantCharacter PrimitiveAdelicHeight

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r t : ℕ}

/-- The two block realizations `(T, (T')^∨)`, indexed by the blocks of `blockShape r t`. -/
def blockRealizations (T : CuspidalOperatorRealization F r)
    (T' : CuspidalOperatorRealization F t) :
    ∀ i : Fin (blockShape r t).length, OperatorRealization F ((blockShape r t).size i) :=
  Fin.cons (α := fun i : Fin 2 => OperatorRealization F ((blockShape r t).size i))
    T.realization
    (Fin.cons (α := fun i : Fin 1 => OperatorRealization F ((blockShape r t).size i.succ))
      (dualRealization T').realization finZeroElim)

theorem blockRealizations_isJointlyAdmissible (T : CuspidalOperatorRealization F r)
    (T' : CuspidalOperatorRealization F t) (i : Fin (blockShape r t).length) :
    (blockRealizations T T' i).IsJointlyAdmissible := by
  have h : ∀ j : Fin 2, (blockRealizations T T' j).IsJointlyAdmissible := by
    intro j
    fin_cases j
    · exact T.isJointlyAdmissible
    · exact (dualRealization T').isJointlyAdmissible
  exact h i

/-- The product coefficients of `IsSection` are realized block coefficients. -/
theorem pairCoefficients_le_coefficientValues (T : CuspidalOperatorRealization F r)
    (T' : CuspidalOperatorRealization F t) :
    Submodule.span ℂ (Set.range fun v : T.Space × (dualRealization T').Space =>
        fun m : FullLevi F (blockShape r t) =>
          ContinuousRationalFunctions.evaluate F (r + 1) (T.realization.toContinuous v.1)
            (m (0 : Fin 2)) *
          ContinuousRationalFunctions.evaluate F (t + 1)
            ((dualRealization T').realization.toContinuous v.2) (m (1 : Fin 2))) ≤
      coefficientValues F (blockShape r t) (blockRealizations T T') := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨v, rfl⟩
  refine Submodule.subset_span ⟨Fin.cons (α := fun i : Fin 2 =>
      (blockRealizations T T' i).Space) v.1
    (Fin.cons (α := fun i : Fin 1 => (blockRealizations T T' i.succ).Space) v.2 finZeroElim), ?_⟩
  funext m
  exact (Fin.prod_univ_two _).trans rfl

/-- A section of the cuspidal pair lies in the realized scalar sections. -/
theorem isSection_mem_realizedSections {T : CuspidalOperatorRealization F r}
    {T' : CuspidalOperatorRealization F t} {φ : AdelicGL F (r + t + 2) → ℂ}
    (hφ : IsSection T T' φ) :
    φ ∈ RealizedSections F (blockShape r t) (blockRealizations T T') := by
  obtain ⟨-, -, -, hU, hslice⟩ := hφ
  refine ⟨fun u g => ?_, fun k => ?_⟩
  · exact hU ⟨u.val.val, Subgroup.mem_map.mpr ⟨u.val, u.property, rfl⟩⟩ g
  · exact pairCoefficients_le_coefficientValues T T' (hslice k)

variable {T : CuspidalOperatorRealization F r} {T' : CuspidalOperatorRealization F t}
  {φ : AdelicGL F (r + t + 2) → ℂ}

/-- The realized scalar section of a cuspidal-pair section. -/
def realizedSection (hφ : IsSection T T' φ) :
    RealizedSections F (blockShape r t) (blockRealizations T T') :=
  ⟨φ, isSection_mem_realizedSections hφ⟩

theorem realizedSection_mem_finiteSmooth (hφ : IsSection T T' φ) :
    realizedSection hφ ∈
      FiniteSmoothRealizedSections F (blockShape r t) (blockRealizations T T') := by
  obtain ⟨-, ⟨J, hJ⟩, -⟩ := hφ
  refine ⟨J, fun j => ?_⟩
  apply Subtype.ext
  funext g
  exact hJ ⟨j.val, j.property⟩ g

/-- The realized section in the finite-smooth carrier. -/
def finiteSmoothSection (hφ : IsSection T T' φ) :
    FiniteSmoothRealizedSections F (blockShape r t) (blockRealizations T T') :=
  ⟨realizedSection hφ, realizedSection_mem_finiteSmooth hφ⟩

local instance cuspidalPairRealizedAddGroup :
    AddCommGroup (FiniteSmoothRealizedSections F (blockShape r t) (blockRealizations T T')) :=
  Submodule.addCommGroup _

theorem finiteSmoothSection_isFiniteVector (hφ : IsSection T T' φ) :
    FiniteVectors.IsFiniteVector
      (finiteSmoothCompactAction F (blockShape r t) (blockRealizations T T'))
      (finiteSmoothSection hφ) := by
  have hfin := hφ.2.2.1
  let incl : FiniteSmoothRealizedSections F (blockShape r t) (blockRealizations T T') →ₗ[ℂ]
      (AdelicGL F (r + t + 2) → ℂ) :=
    (RealizedSections F (blockShape r t) (blockRealizations T T')).subtype.comp
      (FiniteSmoothRealizedSections F (blockShape r t) (blockRealizations T T')).subtype
  have hincl : Function.Injective incl := Subtype.val_injective.comp Subtype.val_injective
  have hle : (FiniteVectors.orbitSpan
      (finiteSmoothCompactAction F (blockShape r t) (blockRealizations T T'))
      (finiteSmoothSection hφ)).map incl ≤
      Submodule.span ℂ (Set.range
        (fun k : standardCompact F (r + t + 2) => fun g => φ (g * k.val))) := by
    rw [FiniteVectors.orbitSpan, Submodule.map_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨⟨AdelicGL.ofInfinite F (r + t + 2) k.val,
      (mem_standardCompact_iff F (r + t + 2) _).mpr ⟨?_, ?_⟩⟩, rfl⟩
    · rw [AdelicGL.infinite_ofInfinite]
      exact k.property
    · rw [AdelicGL.finite_ofInfinite]
      exact one_mem _
  have : FiniteDimensional ℂ ((FiniteVectors.orbitSpan
      (finiteSmoothCompactAction F (blockShape r t) (blockRealizations T T'))
      (finiteSmoothSection hφ)).map incl) := Submodule.finiteDimensional_of_le hle
  exact Module.Finite.equiv (Submodule.equivMapOfInjective incl hincl _).symm

/-- The cuspidal-pair section as a smooth compact-finite block section. -/
def smoothSection (hφ : IsSection T T' φ) :
    smoothCompactFiniteSections F (blockShape r t) (blockRealizations T T') :=
  ⟨finiteSmoothSection hφ,
    (mem_smoothCompactFiniteSections F (blockShape r t) (blockRealizations T T') _).mpr
      ⟨finiteSmoothSection_isFiniteVector hφ, fun d => hφ.1 d⟩⟩

theorem smoothSectionOnScheme_smoothSection (hφ : IsSection T T' φ) :
    smoothSectionOnScheme F (blockShape r t) (blockRealizations T T') (smoothSection hφ) =
      φ ∘ adelicHomeomorph F (r + t + 2) :=
  rfl

local instance cuspidalPairGeneralLinearIsAffine (n : ℕ) :
    IsAffine (groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  isAffine_groupScheme (Fin n) (CommRingCat.of F)

/-- **Automorphy of the section.** On the points of the group scheme `GL_N`, a section of the
cuspidal pair is an automorphic function on `U_P(𝔸) M(F) \ GL_N(𝔸)` for the upper two-block
parabolic, the archimedean part of the standard maximal compact subgroup and the standard
matrix embedding. -/
theorem isAutomorphicFunctionOn_of_isSection (hφ : IsSection T T' φ) {d : ℕ}
    (hsmooth : SmoothOfRelativeDimension d
      (groupScheme (Fin (r + t + 2)) (CommRingCat.of F)).X.hom)
    (hcalc : AdelicDifferentialCommutator F
      (groupScheme (Fin (r + t + 2)) (CommRingCat.of F)) hsmooth) :
    IsAutomorphicFunctionOn F (groupScheme (Fin (r + t + 2)) (CommRingCat.of F)) hsmooth hcalc
      (parabolicQuotientSubgroup F
        (blockParabolicHom (Fin (r + t + 2)) (CommRingCat.of F)
          (blockShapeWeight (blockShape r t)))
        (blockUnipotentInclusion F (blockShape r t)) (blockLeviInclusion F (blockShape r t)))
      ((standardCompactPoints F (r + t + 2)).comap
        (ofInfinite F (groupScheme (Fin (r + t + 2)) (CommRingCat.of F))).toMonoidHom)
      (MatrixRepresentation.standard (Fin (r + t + 2)) (CommRingCat.of F))
      (φ ∘ adelicHomeomorph F (r + t + 2)) := by
  rw [standardCompactPoints_comap_ofInfinite, ← smoothSectionOnScheme_smoothSection hφ]
  exact AdelicBlockScalarSections.SchemeSection.isAutomorphicFunctionOn F (blockShape r t)
    (blockRealizations T T') (by omega) (blockRealizations_isJointlyAdmissible T T') hsmooth
    hcalc (smoothSection hφ)

end Langlands.Global.CuspidalPairEisenstein
