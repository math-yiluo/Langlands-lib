import Langlands.Representation.Exponents.SplitComponentWeights
import Langlands.Representation.Exponents.CentralDecompositionProof
import Langlands.Representation.Exponents.ArbitraryParabolicInduction
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Decomposition for a continuous central group action -/

noncomputable section

namespace Langlands

universe uR uA uM uV

variable {R : Type uR} [Field R] {A : Type uA} [Group A]
  {M : Type uM} [Group M] [TopologicalSpace M] [NonarchimedeanGroup M]
  [WeaklyLocallyCompactSpace M] {V : Type uV} [AddCommGroup V] [Module R V]
  (π : Representation R M V) (ι : A →* M)
  (hι : ∀ t : A, ι t ∈ Subgroup.center M)

/-- Distinct uniform generalized characters of a central action give independent
subspaces. Admissibility is unnecessary. -/
theorem generalizedWeightSpace_independent (hπ : IsSmooth π) :
    iSupIndep (fun χ : A →* Rˣ => (generalizedWeightSpace π ι χ hι).toSubmodule) := by
  let f : A → Module.End R V := fun t => π (ι t)
  have hi := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f
    (fun i j μ => Module.End.mapsTo_maxGenEigenspace_of_comm (by
      change Commute (π (ι j)) (π (ι i))
      exact (show Commute (ι j) (ι i) from
        Subgroup.mem_center_iff.mp (hι i) (ι j)).map π) μ)
  let c : (A →* Rˣ) → (A → R) := fun χ t => (χ t : R)
  have hc : Function.Injective c := by
    intro χ ψ h
    apply MonoidHom.ext
    intro t
    apply Units.ext
    exact congrFun h t
  apply (hi.comp hc).mono
  intro χ v hv
  obtain ⟨n, hn⟩ := (mem_generalizedWeightSpace_of_isSmooth ι χ hι hπ v).mp hv
  change v ∈ ⨅ t : A, Module.End.maxGenEigenspace (π (ι t)) (χ t : R)
  rw [Submodule.mem_iInf]
  intro t
  exact Module.End.mem_genEigenspace_top.mpr ⟨n, hn t⟩

/-- Restricting full-center characters spans the characteristic spaces of any
central map. Equal restrictions are allowed. -/
theorem generalizedWeightSpace_iSup_eq_top [IsAlgClosed R]
    (hπ : IsSmooth π) (hc : IsCenterFinite π) :
    (⨆ χ : A →* Rˣ, (generalizedWeightSpace π ι χ hι).toSubmodule) = ⊤ := by
  apply top_unique
  rw [← CentralDecomposition.algebraic_spanning π hc]
  refine iSup_le fun χZ v hv => ?_
  let j : A →* Subgroup.center M := ι.codRestrict _ hι
  exact Submodule.mem_iSup_of_mem (χZ.comp j)
    (generalizedCentralCharacterSpace_le_generalizedWeightSpace ι (χZ.comp j) hι
      hπ χZ (fun _ => rfl) hv)

variable [TopologicalSpace A]

/-- The nonzero smooth generalized weights form an internal direct sum
spanning the representation. -/
def GeneralizedWeightDecompositionStatement : Prop :=
  iSupIndep (fun χ : {χ : A →* Rˣ | IsGeneralizedWeight π ι χ hι} =>
    (generalizedWeightSpace π ι χ hι).toSubmodule) ∧
    (⨆ χ : {χ : A →* Rˣ | IsGeneralizedWeight π ι χ hι},
      (generalizedWeightSpace π ι χ hι).toSubmodule) = ⊤

/-- For an admissible representation, its nonzero smooth central-map weight
spaces form an internal direct sum equal to the entire representation. -/
theorem generalizedWeightSpace_decomposition [IsAlgClosed R]
    (hιc : Continuous ι) (hπ : IsAdmissible π) :
    GeneralizedWeightDecompositionStatement π ι hι := by
  refine ⟨(generalizedWeightSpace_independent π ι hι hπ.1).comp
    Subtype.val_injective, ?_⟩
  apply top_unique
  rw [← generalizedWeightSpace_iSup_eq_top π ι hι hπ.1
    (CentralDecomposition.admissible_centerFinite π hπ)]
  refine iSup_le fun χ v hv => ?_
  by_cases hz : v = 0
  · subst v
    exact Submodule.zero_mem _
  · have hw : generalizedWeightSpace π ι χ hι ≠ ⊥ := by
      intro h
      rw [h] at hv
      exact hz ((Submodule.mem_bot R).mp hv)
    have hopen := isOpen_ker_of_isGeneralizedEigencharacter_comp π hπ.1 ι hιc χ
      ((generalizedWeightSpace_ne_bot_iff ι χ hι hπ.1).mp hw)
    exact Submodule.mem_iSup_of_mem ⟨χ, hopen, hw⟩ hv

/-- Finite generation over the acting group algebra makes the exponent set
finite. This lemma does not assume finite-dimensionality of the carrier. -/
theorem finite_generalizedWeights [IsAlgClosed R]
    (hπ : IsAdmissible π)
    [Module.Finite (MonoidAlgebra R M) π.asModule] :
    {χ : A →* Rˣ | IsGeneralizedWeight π ι χ hι}.Finite := by
  classical
  have hi := generalizedWeightSpace_independent π ι hι hπ.1
  have hspan := generalizedWeightSpace_iSup_eq_top π ι hι hπ.1
    (CentralDecomposition.admissible_centerFinite π hπ)
  have haspan := CentralDecomposition.asSubmodule_iSup_eq_top π
    (fun χ => generalizedWeightSpace π ι χ hι) hspan
  have hfg : (⊤ : Submodule (MonoidAlgebra R M) π.asModule).FG := Module.Finite.fg_top
  obtain ⟨s, hs⟩ := (Submodule.fg_iff_compact _).mp hfg |>.exists_finset_of_le_iSup
    (fun χ : A →* Rˣ => (generalizedWeightSpace π ι χ hι).asSubmodule) haspan.ge
  have hs' : (⨆ χ ∈ s, (generalizedWeightSpace π ι χ hι).asSubmodule) = ⊤ :=
    top_unique hs
  have hsR := congrArg (Submodule.restrictScalars R) hs'
  simp only [Submodule.restrictScalars_iSup, Submodule.restrictScalars_top] at hsR
  apply s.finite_toSet.subset
  intro χ hχ
  apply hi.mem_of_biSup_eq_top hsR
  intro h
  exact hχ.2 (Subrepresentation.toSubmodule_injective h)

end Langlands

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

universe u v

variable {k : Type u} [Field k] [TopologicalSpace k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]

local instance decompositionAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]

/-- The whole-group clause of VII.1.1, on the published compact-open weight spaces. -/
theorem groupWeightSpace_decomposition
    {AG : CommGroupScheme (Spec (CommRingCat.of k))} {aG : AG.toGrp ⟶ G}
    (haG : IsSplitComponent aG) (V : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (hV : V.IsAdmissible) :
    iSupIndep (fun χ : groupExponents haG V =>
      (groupWeightSpace haG V χ).toSubmodule) ∧
      (⨆ χ : groupExponents haG V, (groupWeightSpace haG V χ).toSubmodule) = ⊤ := by
  have := haG.isAffine
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let := RationalPointFamily.splitComponentPointTopology haG
  exact generalizedWeightSpace_decomposition V.representation (rationalPoints.map aG)
    haG.isCentralSplitTorus.isCentral.map_mem_center
    (continuous_rationalPointMap k aG.hom.hom) hV

/-- Admissible representations of a closed literal Levi image decompose into
the published split-component weight spaces. -/
theorem leviWeightSpace_decomposition (j : M ⟶ G)
    (hj : IsClosed (pointImage j : Set (rationalPoints G)))
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
    (ha : IsSplitComponent a) (W : SmoothRep.{0, u, v} ℂ (pointImage j))
    (hW : W.IsAdmissible) :
    iSupIndep (fun ψ : leviExponents j ha W => (leviWeightSpace j ha W ψ).toSubmodule) ∧
      (⨆ ψ : leviExponents j ha W, (leviWeightSpace j ha W ψ).toSubmodule) = ⊤ := by
  have := hj.locallyCompactSpace
  let := RationalPointFamily.splitComponentPointTopology ha
  exact generalizedWeightSpace_decomposition W.representation (splitComponentPointsMap j a)
    (splitComponentPointsMap_mem_center j ha)
    (continuous_splitComponentPointsMap j ha) hW

/-- An admissible finite-length Levi representation has finitely many exponents. -/
theorem finite_leviExponents_of_finiteLength (j : M ⟶ G)
    (hj : IsClosed (pointImage j : Set (rationalPoints G)))
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
    (ha : IsSplitComponent a) (W : SmoothRep.{0, u, v} ℂ (pointImage j))
    (hW : W.IsAdmissible) (hfinite : W.HasFiniteLength) :
    (leviExponents j ha W).Finite := by
  have := hj.locallyCompactSpace
  let := RationalPointFamily.splitComponentPointTopology ha
  have : IsNoetherian (MonoidAlgebra ℂ (pointImage j)) W.representation.asModule :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfinite).1
  exact finite_generalizedWeights W.representation (splitComponentPointsMap j a)
    (splitComponentPointsMap_mem_center j ha) hW

variable [T2Space k]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}

/-- The normalized Jacquet characteristic spaces are independent without
an admissibility hypothesis. -/
theorem normalizedJacquetWeightSpace_independent (ha : IsSplitComponent a)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) :
    iSupIndep (fun χ : normalizedJacquetExponents p l r hp hl hr hmul ha π =>
      (normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ).toSubmodule) := by
  have := (isClosed_leviPoints p l hp hl).locallyCompactSpace
  exact (generalizedWeightSpace_independent
    ((jacquetFunctor p l r hp hr hl hmul).obj π).representation
    (splitComponentPointsMap (l ≫ p) a) (splitComponentPointsMap_mem_center (l ≫ p) ha)
    ((jacquetFunctor p l r hp hr hl hmul).obj π).isSmooth).comp Subtype.val_injective

/-- Jacquet spanning follows from admissibility of the actual normalized
Jacquet representation; this lemma retains that premise explicitly. -/
theorem normalizedJacquetWeightSpace_decomposition_of_admissible
    (ha : IsSplitComponent a) (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (hJ : ((jacquetFunctor p l r hp hr hl hmul).obj π).IsAdmissible) :
    iSupIndep (fun χ : normalizedJacquetExponents p l r hp hl hr hmul ha π =>
      (normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ).toSubmodule) ∧
      (⨆ χ : normalizedJacquetExponents p l r hp hl hr hmul ha π,
        (normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ).toSubmodule) = ⊤ :=
  leviWeightSpace_decomposition (l ≫ p) (isClosed_leviPoints p l hp hl) ha _ hJ

/-- Finiteness follows when the actual Jacquet representation is admissible
and has finite length. Neither preservation assertion is assumed silently. -/
theorem finite_normalizedJacquetExponents_of_admissible_of_finiteLength
    (ha : IsSplitComponent a) (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (hJ : ((jacquetFunctor p l r hp hr hl hmul).obj π).IsAdmissible)
    (hfinite : ((jacquetFunctor p l r hp hr hl hmul).obj π).HasFiniteLength) :
    (normalizedJacquetExponents p l r hp hl hr hmul ha π).Finite :=
  finite_leviExponents_of_finiteLength (l ≫ p) (isClosed_leviPoints p l hp hl)
    ha _ hJ hfinite

end Langlands.Aubert.General.RepresentedParabolic
