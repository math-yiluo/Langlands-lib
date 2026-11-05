import Langlands.Representation.Exponents.SplitComponentDecomposition
import Langlands.Representation.Aubert.General.JacquetFiniteGeneration

/-! # Finite exponent support from spanning and finite generation -/

noncomputable section

namespace Langlands

universe uR uA uM uV

variable {R : Type uR} [Field R] {A : Type uA} [Group A] [TopologicalSpace A]
  {M : Type uM} [Group M] [TopologicalSpace M] [NonarchimedeanGroup M]
  [WeaklyLocallyCompactSpace M] {V : Type uV} [AddCommGroup V] [Module R V]
  (π : Representation R M V) (centralMap : A →* M)
  (hcentralMap : ∀ t : A, centralMap t ∈ Subgroup.center M)

/-- Spanning and finite generation suffice for finite exponent support.
No admissibility or algebraic closure is required. -/
def GeneralizedWeightFiniteSupportStatement : Prop :=
  IsSmooth π →
    (⨆ χ : A →* Rˣ, (generalizedWeightSpace π centralMap χ hcentralMap).toSubmodule) = ⊤ →
      Module.Finite (MonoidAlgebra R M) π.asModule →
        {χ : A →* Rˣ | IsGeneralizedWeight π centralMap χ hcentralMap}.Finite

/-- A finite set of spanning weight submodules must contain every nonzero
weight, by independence. -/
theorem finite_generalizedWeights_of_spanning (hπ : IsSmooth π)
    (hspan : (⨆ χ : A →* Rˣ,
      (generalizedWeightSpace π centralMap χ hcentralMap).toSubmodule) = ⊤)
    [Module.Finite (MonoidAlgebra R M) π.asModule] :
    {χ : A →* Rˣ | IsGeneralizedWeight π centralMap χ hcentralMap}.Finite := by
  classical
  have hi := generalizedWeightSpace_independent π centralMap hcentralMap hπ
  have haspan := CentralDecomposition.asSubmodule_iSup_eq_top π
    (fun χ => generalizedWeightSpace π centralMap χ hcentralMap) hspan
  have hfg : (⊤ : Submodule (MonoidAlgebra R M) π.asModule).FG := Module.Finite.fg_top
  obtain ⟨s, hs⟩ := (Submodule.fg_iff_compact _).mp hfg |>.exists_finset_of_le_iSup
    (fun χ : A →* Rˣ => (generalizedWeightSpace π centralMap χ hcentralMap).asSubmodule)
    haspan.ge
  have hs' : (⨆ χ ∈ s,
      (generalizedWeightSpace π centralMap χ hcentralMap).asSubmodule) = ⊤ := top_unique hs
  have hsR := congrArg (Submodule.restrictScalars R) hs'
  simp only [Submodule.restrictScalars_iSup, Submodule.restrictScalars_top] at hsR
  apply s.finite_toSet.subset
  intro χ hχ
  apply hi.mem_of_biSup_eq_top hsR
  intro h
  exact hχ.2 (Subrepresentation.toSubmodule_injective h)

theorem generalizedWeight_finiteSupport :
    GeneralizedWeightFiniteSupportStatement π centralMap hcentralMap := by
  intro hπ hspan hfg
  let := hfg
  exact finite_generalizedWeights_of_spanning π centralMap hcentralMap hπ hspan

end Langlands

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

universe u v

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]

local instance finiteSupportAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}

/-- If the actual normalized Jacquet weight spaces span, a compact parabolic
quotient and finite ambient generation imply finite Jacquet exponent support. -/
theorem finite_normalizedJacquetExponents_of_compactQuotient_of_spanning
    [CompactSpace (Induction.LeftQuotient (pointImage p))]
    (ha : IsSplitComponent a) (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (hfg : Module.Finite (MonoidAlgebra ℂ (rationalPoints G)) π.representation.asModule)
    (hspan : (⨆ χ : normalizedJacquetExponents p l r hp hl hr hmul ha π,
      (normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ).toSubmodule) = ⊤) :
    (normalizedJacquetExponents p l r hp hl hr hmul ha π).Finite := by
  have := (isClosed_leviPoints p l hp hl).locallyCompactSpace
  let := RationalPointFamily.splitComponentPointTopology ha
  have : Module.Finite (MonoidAlgebra ℂ (pointImage (l ≫ p)))
      ((jacquetFunctor p l r hp hr hl hmul).obj π).representation.asModule :=
    JacquetFiniteGeneration.finite_of_compactQuotient
      (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
      (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup) π hfg
  have hspan' : (⨆ χ : rationalPoints A.toGrp →* ℂˣ,
      (normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ).toSubmodule) = ⊤ := by
    apply top_unique
    rw [← hspan]
    exact iSup_le fun χ => le_iSup
      (fun ψ => (normalizedJacquetWeightSpace p l r hp hl hr hmul ha π ψ).toSubmodule) χ.1
  exact finite_generalizedWeights_of_spanning
    ((jacquetFunctor p l r hp hr hl hmul).obj π).representation
    (splitComponentPointsMap (l ≫ p) a) (splitComponentPointsMap_mem_center (l ≫ p) ha)
    ((jacquetFunctor p l r hp hr hl hmul).obj π).isSmooth hspan'

/-- The finite-length case needs only spanning and compactness; no preservation
of admissibility or finite length is required by this reduction. -/
theorem finite_normalizedJacquetExponents_of_hasFiniteLength_of_compactQuotient_of_spanning
    [CompactSpace (Induction.LeftQuotient (pointImage p))]
    (ha : IsSplitComponent a) (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (hfinite : π.HasFiniteLength)
    (hspan : (⨆ χ : normalizedJacquetExponents p l r hp hl hr hmul ha π,
      (normalizedJacquetWeightSpace p l r hp hl hr hmul ha π χ).toSubmodule) = ⊤) :
    (normalizedJacquetExponents p l r hp hl hr hmul ha π).Finite := by
  have : IsNoetherian (MonoidAlgebra ℂ (rationalPoints G)) π.representation.asModule :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfinite).1
  exact finite_normalizedJacquetExponents_of_compactQuotient_of_spanning
    p l r hp hl hr hmul ha π inferInstance hspan

end Langlands.Aubert.General.RepresentedParabolic
