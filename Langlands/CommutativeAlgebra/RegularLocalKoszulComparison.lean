import Langlands.CommutativeAlgebra.FiniteKoszulEnds
import Langlands.CommutativeAlgebra.RegularLocalFiniteLengthAcyclicityStatement
import Langlands.Cohomology.PerfectModuleComplexHomotopy
import Langlands.Cohomology.HyperextSecondPage
import Mathlib.Data.Fintype.EquivFin

/-! # Comparison with the regular-local Koszul resolution -/

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing
open Langlands.Cohomology.ModuleComplex

noncomputable section

namespace Langlands.CommutativeAlgebra

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R]

/-- Choose a dimension-sized generating family for the maximal ideal. -/
lemma exists_regularLocalParameters (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (g : ℕ) (hdim : ringKrullDim R = g) :
    ∃ a : Fin g → R, Ideal.span (Set.range a) = maximalIdeal R := by
  classical
  have hsg : (maximalIdeal R).spanFinrank = g := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
    rw [hdim] at h
    exact_mod_cast h
  obtain ⟨s, hcard, hspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank
      (p := (maximalIdeal R : Submodule R R)) (IsNoetherian.noetherian _)
  let e := s.equivFinOfCardEq (hcard.trans hsg)
  let a : Fin g → R := fun i ↦ (e.symm i).val
  refine ⟨a, ?_⟩
  have hrange : Set.range a = (s : Set R) := by
    ext r
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).property
    · intro hr
      refine ⟨e ⟨r, hr⟩, ?_⟩
      simp [a]
  rw [hrange]
  exact hspan

/-- A chosen generating family of length equal to the dimension. -/
def regularLocalParameters (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (g : ℕ) (hdim : ringKrullDim R = g) : Fin g → R :=
  (exists_regularLocalParameters R g hdim).choose

lemma regularLocalParameters_span (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (g : ℕ) (hdim : ringKrullDim R = g) :
    Ideal.span (Set.range (regularLocalParameters R g hdim)) = maximalIdeal R :=
  (exists_regularLocalParameters R g hdim).choose_spec

/-- Acyclicity makes the parameter Koszul complex a resolution in degree `g`. -/
lemma finiteKoszulCochain_isZero_homology_of_ne
    (hacyclicity : RegularLocalFiniteLengthAcyclicityStatement.{u})
    [IsRegularLocalRing R] (g : ℕ) (hdim : ringKrullDim R = g)
    (a : Fin g → R) (ha : Ideal.span (Set.range a) = maximalIdeal R)
    (i : ℤ) (hi : i ≠ (g : ℤ)) :
    IsZero ((finiteKoszulCochain a).homology i) := by
  by_cases hlt : i < (g : ℤ)
  · apply hacyclicity R g hdim (finiteKoszulCochain a)
      (finiteKoszulCochain_isFiniteFree a) (finiteKoszulCochain_isStrictlyGE a) ?_ i hlt
    intro j
    refine ⟨1, ?_⟩
    simpa only [pow_one, ← ha] using finiteKoszulCochain_span_le_annihilator a j
  · have := finiteKoszulCochain_isStrictlyLE a
    exact (finiteKoszulCochain a).isZero_of_isLE (g : ℤ) i (by omega)

/-- A complex concentrated in one homology degree is derived-isomorphic to that module. -/
def derivedIsoOfHomologyConcentrated
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (hK : ∀ i : ℤ, i ≠ n → IsZero (K.homology i)) :
    DerivedCategory.Q.obj K ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) n).obj (K.homology n) := by
  have : (DerivedCategory.Q.obj K).IsGE n := by
    rw [DerivedCategory.isGE_iff]
    intro i hi
    exact (hK i (by omega)).of_iso
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app K)
  have : (DerivedCategory.Q.obj K).IsLE n := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    exact (hK i (by omega)).of_iso
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app K)
  exact Langlands.Cohomology.HyperextSpectralSequence.isoSingleHomology
    (DerivedCategory.Q.obj K) n ≪≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) n).mapIso
        ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n).app K)

/-- Strictly perfect complexes with the same single homology module are homotopy equivalent. -/
def homotopyEquivOfSingleHomology
    {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyPerfect K) (hL : IsStrictlyPerfect L) (n : ℤ)
    (hvanK : ∀ i : ℤ, i ≠ n → IsZero (K.homology i))
    (hvanL : ∀ i : ℤ, i ≠ n → IsZero (L.homology i))
    (e : K.homology n ≅ L.homology n) : HomotopyEquiv K L :=
  homotopyEquivOfDerivedIso hK hL
    (derivedIsoOfHomologyConcentrated K n hvanK ≪≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) n).mapIso e ≪≫
        (derivedIsoOfHomologyConcentrated L n hvanL).symm)

/-- Compare a finite free residue-field resolution to the parameter Koszul complex. -/
def regularLocalKoszulResolutionComparison
    (hacyclicity : RegularLocalFiniteLengthAcyclicityStatement.{u})
    [IsRegularLocalRing R] (g : ℕ) (hdim : ringKrullDim R = g)
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (hC : IsFiniteFree C)
    (hvan : ∀ i : ℤ, i ≠ (g : ℤ) → IsZero (C.homology i))
    (e : C.homology (g : ℤ) ≅ ModuleCat.of R (ResidueField R)) :
    HomotopyEquiv C (finiteKoszulCochain (regularLocalParameters R g hdim)) :=
  homotopyEquivOfSingleHomology (isStrictlyPerfect_of_isFiniteFree hC)
    (isStrictlyPerfect_of_isFiniteFree (finiteKoszulCochain_isFiniteFree _)) (g : ℤ)
    hvan (finiteKoszulCochain_isZero_homology_of_ne hacyclicity g hdim _
      (regularLocalParameters_span R g hdim))
    (e ≪≫ (finiteKoszulCochainTopHomologyIsoResidueField _
      (regularLocalParameters_span R g hdim)).symm)

end Langlands.CommutativeAlgebra
