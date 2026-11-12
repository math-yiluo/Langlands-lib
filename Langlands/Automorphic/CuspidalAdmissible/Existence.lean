import Langlands.Automorphic.CuspidalAdmissible.CentralEigen
import Langlands.Automorphic.CuspidalAdmissible.Reproduction
import Langlands.Automorphic.CuspidalAdmissible.Irreducible
import Langlands.Automorphic.CuspidalContragredientSlice
import Langlands.Automorphic.CuspidalAllLocalIrreduciblePresentation

/-! # Every cuspidal realization contains an irreducible admissible finite slice -/

noncomputable section
universe u
set_option autoImplicit false

open MeasureTheory

namespace Langlands.Automorphic

open Langlands.Global

local instance cuspidalAdmExistAddCommGroupRationalInvariant {F : Type u} [Field F]
    [NumberField F] {n : ℕ} : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance cuspidalAdmExistAddCommGroupContinuousRational {F : Type u} [Field F]
    [NumberField F] {n : ℕ} : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance cuspidalAdmExistAddCommGroupFiniteSmoothRational {F : Type u} [Field F]
    [NumberField F] {n : ℕ} : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance cuspidalAdmExistAddCommGroupAutomorphicForms {F : Type u} [Field F]
    [NumberField F] {n : ℕ} : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance cuspidalAdmExistAddCommGroupStableAutomorphic {F : Type u} [Field F]
    [NumberField F] {n : ℕ} : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance cuspidalAdmExistAddCommGroupSpace {F : Type u} [Field F] [NumberField F] {n : ℕ}
    (S : OperatorRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

namespace OperatorRealization

open ContinuousRationalFunctions
variable {F : Type u} [Field F] [NumberField F] {n : ℕ} (S : OperatorRealization F n)

/-- **Finite fixed vectors.** In a cuspidal realization, a subrepresentation of the finite
action that is reproduced by one continuous compactly supported kernel and lies in one
eigenspace of the central derivative has finite-dimensional fixed vectors for every open
subgroup. -/
theorem finite_inf_fixedVectors [CompactSpace (AdeleQuotient F)] (hS : S.IsCuspidal)
    (hn : 0 < n) [MeasurableSpace (InfiniteAdelicGL F n)] [BorelSpace (InfiniteAdelicGL F n)]
    (μ : Measure (InfiniteAdelicGL F n)) [IsFiniteMeasureOnCompacts μ]
    {κ : InfiniteAdelicGL F n → ℂ} (hκ : Continuous κ) (hκc : HasCompactSupport κ) (lam : ℂ)
    (V₀ : Subrepresentation S.finiteRepresentation) (hR : V₀ ≤ reproducing S μ hκ hκc)
    (hE : V₀ ≤ centralEigenspace S lam) (K : OpenSubgroup (FiniteAdelicGL F n)) :
    Module.Finite ℂ ↥(V₀.toSubmodule ⊓ fixedVectors S.finiteRepresentation K.toSubgroup) := by
  refine S.finiteDimensional_of_reproduced μ hS hn hκ hκc K.toSubgroup K.isOpen lam _
    ?_ ?_ ?_
  · intro f hf g l hl
    have hfix : S.finiteRepresentation l f = f := (Submodule.mem_inf.mp hf).2 ⟨l, hl⟩
    calc evaluate F n (S.toContinuous f) (g * AdelicGL.ofFinite F n l)
        = evaluate F n (S.toContinuous (S.finiteRepresentation l f)) g :=
          (S.evaluate_finiteRepresentation l f g).symm
      _ = evaluate F n (S.toContinuous f) g := by rw [hfix]
  · intro f hf g h
    exact (mem_reproducing S μ hκ hκc f).mp (hR (Submodule.mem_inf.mp hf).1) g h
  · intro f hf g t
    exact S.evaluate_mul_centralTorus lam f
      ((mem_centralEigenspace S lam f).mp (hE (Submodule.mem_inf.mp hf).1)) g t

/-- Every realized vector is fixed by some compact open subgroup of the finite adelic group. -/
theorem exists_compact_fixedVectors (f : S.Space) :
    ∃ U : OpenSubgroup (FiniteAdelicGL F n), IsCompact (U : Set (FiniteAdelicGL F n)) ∧
      f ∈ fixedVectors S.finiteRepresentation U.toSubgroup := by
  obtain ⟨K, hK⟩ := S.finiteRepresentation_isSmooth f
  obtain ⟨U, hUK, hU⟩ := finiteAdelicGL_exists_compact_le n K
  exact ⟨U, hU, fun k => hK ⟨k.val, hUK k.property⟩⟩

end OperatorRealization

/-- **Every cuspidal realization contains an irreducible admissible finite slice.** Choose a
nonzero eigenvector `f₀` of the central derivative and one smooth compactly supported kernel
reproducing `f₀` at every adelic point. The finite adelic translates of `f₀` span a
subrepresentation `V₀` that is still reproduced and still central-eigen, so its fixed vectors
are finite-dimensional for every open subgroup by the cusp-form finiteness argument. A compact
open subgroup `U` fixing `f₀` meets every nonzero subrepresentation by irreducibility of the
whole realization, so the minimal-fixed-dimension argument gives a nonzero irreducible
admissible subrepresentation, which is packaged as a finite slice. -/
theorem cuspidalIrreducibleAdmissibleFiniteSliceExistence :
    CuspidalIrreducibleAdmissibleFiniteSliceExistenceStatement.{u} := by
  intro F _ _ _ r S
  obtain ⟨lam, f₀, hf₀, hlam⟩ := S.realization.exists_centralEigenvector
  let : MeasurableSpace (InfiniteAdelicGL F (r + 1)) := ArchimedeanGL.borelMeasurableSpace F (r + 1)
  have : BorelSpace (InfiniteAdelicGL F (r + 1)) :=
    ArchimedeanGL.borelMeasurableSpace_borelSpace F (r + 1)
  let μ : Measure (InfiniteAdelicGL F (r + 1)) := ArchimedeanGL.leftHaarMeasure F (r + 1)
  obtain ⟨κ, hκ⟩ := S.realization.exists_reproducingKernel μ f₀
  have hκc : Continuous κ.val.val := (ArchimedeanGL.kernelToContinuousMap F (r + 1) κ).continuous
  have hκs : HasCompactSupport κ.val.val := κ.property
  let V₀ := CuspidalAdmissible.generated S.realization.finiteRepresentation (Submodule.span ℂ {f₀})
  have hR : V₀ ≤ OperatorRealization.reproducing S.realization μ hκc hκs :=
    CuspidalAdmissible.generated_le _ ((Submodule.span_singleton_le_iff_mem _ _).mpr hκ)
  have hE : V₀ ≤ OperatorRealization.centralEigenspace S.realization lam :=
    CuspidalAdmissible.generated_le _ ((Submodule.span_singleton_le_iff_mem _ _).mpr
      ((OperatorRealization.mem_centralEigenspace S.realization lam f₀).mpr hlam))
  have hfin :=
    S.realization.finite_inf_fixedVectors S.cuspidal (Nat.succ_pos r) μ hκc hκs lam V₀ hR hE
  obtain ⟨U, hU, hf₀U⟩ := S.realization.exists_compact_fixedVectors f₀
  have hf₀V : f₀ ∈ V₀.toSubmodule :=
    CuspidalAdmissible.le_generated _ _ (Submodule.mem_span_singleton_self f₀)
  have hne : ∀ {M : Submodule ℂ S.realization.Space}, f₀ ∈ M →
      M ⊓ fixedVectors S.realization.finiteRepresentation U.toSubgroup ≠ ⊥ := fun hM h =>
    hf₀ ((Submodule.mem_bot ℂ).mp (h ▸ Submodule.mem_inf.mpr ⟨hM, hf₀U⟩))
  have hfix : fixedVectors S.realization.finiteRepresentation U.toSubgroup ≠ ⊥ := by
    simpa only [top_inf_eq] using hne (M := ⊤) Submodule.mem_top
  obtain ⟨A, -, hA, hirr, hadm⟩ := CuspidalAdmissible.exists_irreducible_admissible_le
    S.realization.finiteRepresentation S.realization.finiteRepresentation_isSmooth V₀ hfin U
    (hne hf₀V)
    fun Z _ hZ => S.realization.inf_fixedVectors_ne_bot U hU S.irreducible hfix Z hZ
  exact S.exists_finiteSlice_of_subrepresentation A hA hirr hadm

end Langlands.Automorphic
