import Langlands.Representation.Exponents.TemperedJacquetStructure
import Langlands.Representation.Exponents.SplitComponentComparison
import Langlands.Representation.Compact.SurjectivityProof
import Langlands.Representation.Smooth.Admissibility.CofinalProof
import Langlands.Representation.Category.Subquotients

/-! # Normalized-exponent temperedness passes to quotients -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance quotientTemperedAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]
  {P M U : GroupScheme (Spec (CommRingCat.of k))}
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  {π : SmoothRep.{0, u, v} ℂ (rationalPoints G)}
  {τ : SmoothRep.{0, u, w} ℂ (rationalPoints G)}

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- An onto intertwiner induces an onto map on the actual normalized Jacquet
modules, including when its two carriers have different universes. -/
theorem jacquetIntertwining_surjective
    (r : U ⟶ P) (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    (f : π.representation.IntertwiningMap τ.representation)
    (hf : Function.Surjective f) :
    Function.Surjective (jacquetIntertwining r hp hl hr hmul f) :=
  Jacquet.Localization.map_surjective (pointImage (r ≫ p)) 1 (pointImage (l ≫ p))
    (pointImage_le_normalizer p l r hr)
    (Jacquet.Localization.isInvariant_one _ _ _) f hf

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- Every normalized exponent of a smooth quotient is an exponent of its
source when the source's actual normalized Jacquet module is admissible.
No admissibility of the target Jacquet module is assumed. -/
theorem isNormalizedJacquetExponent_of_surjective_intertwining
    (r : U ⟶ P) (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r)) (ha : IsSplitComponent a)
    (hJ : ((jacquetFunctor p l r hp hr hl hmul).obj π).IsAdmissible)
    (f : π.representation.IntertwiningMap τ.representation)
    (hf : Function.Surjective f)
    {χ : rationalPoints A.toGrp →* ℂˣ}
    (hχ : IsNormalizedJacquetExponent p l r hp hl hr hmul ha τ χ) :
    IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ := by
  have := (isClosed_leviPoints p l hp hl).locallyCompactSpace
  let Jπ := (jacquetFunctor p l r hp hr hl hmul).obj π
  let Jτ := (jacquetFunctor p l r hp hr hl hmul).obj τ
  let F := jacquetIntertwining r hp hl hr hmul f
  let centralMap := splitComponentPointsMap (l ≫ p) a
  have hcentral : ∀ t, centralMap t ∈ Subgroup.center (pointImage (l ≫ p)) :=
    splitComponentPointsMap_mem_center (l ≫ p) ha
  have hspan := generalizedWeightSpace_iSup_eq_top Jπ.representation centralMap hcentral
    Jπ.isSmooth (CentralDecomposition.admissible_centerFinite Jπ.representation hJ)
  refine ⟨hχ.1, ?_⟩
  exact generalizedWeightSpace_ne_bot_of_surjective
    Jπ.representation centralMap hcentral Jτ.representation centralMap hcentral
    Jπ.isSmooth Jτ.isSmooth hspan F.toLinearMap
    (fun t => (F.isIntertwining' (centralMap t)).symm)
    (jacquetIntertwining_surjective r hp hl hr hmul f hf) χ hχ.2

/-- Vanishing of the actual unitary Jacquet part passes to every smooth
quotient when the source Jacquet module is admissible. -/
theorem unitaryJacquetPart_eq_bot_of_surjective_intertwining
    (r : U ⟶ P) (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r)) (ha : IsSplitComponent a)
    (hJ : ((jacquetFunctor p l r hp hr hl hmul).obj π).IsAdmissible)
    (f : π.representation.IntertwiningMap τ.representation)
    (hf : Function.Surjective f)
    (hunit : unitaryJacquetPart p l r hp hl hr hmul ha π = ⊥) :
    unitaryJacquetPart p l r hp hl hr hmul ha τ = ⊥ := by
  apply le_antisymm ?_ bot_le
  refine iSup_le fun χ => iSup_le fun hχ => iSup_le fun h0 => ?_
  have hsource := isNormalizedJacquetExponent_of_surjective_intertwining
    r hp hl hr hmul ha hJ f hf hχ
  have hle := normalizedJacquetWeightSpace_le_unitaryJacquetPart
    p l r hp hl hr hmul ha π hsource h0
  rw [hunit] at hle
  exact (hsource.2 (le_antisymm hle bot_le)).elim

/-- Normalized-exponent temperedness passes through every surjective
intertwiner. Source temperedness supplies actual Jacquet admissibility and
presentation coverage; target admissibility follows by compact averaging. -/
theorem IsNormalizedExponentTempered.of_surjective_intertwining
    {hG : IsConnectedReductive G}
    (hπ : IsNormalizedExponentTempered hG π)
    (f : π.representation.IntertwiningMap τ.representation)
    (hf : Function.Surjective f) :
    IsNormalizedExponentTempered hG τ := by
  have := hG.smooth
  refine ⟨⟨τ.isSmooth, ?_⟩, ?_⟩
  · intro H
    obtain ⟨K, hK, hKH⟩ := compactOpenSubgroupBasis (rationalPoints G)
      (H : Set (rationalPoints G)) (H.isOpen.mem_nhds H.one_mem)
    have : Module.Finite ℂ (fixedVectors π.representation K.toSubgroup) :=
      hπ.isAdmissible.2 K
    have : Module.Finite ℂ (fixedVectors τ.representation K.toSubgroup) :=
      Module.Finite.of_surjective
        (Compact.fixedVectorMap π.representation τ.representation f K.toSubgroup)
        (Compact.fixedVectorSurjectivity _ _ _ _ _ π.isSmooth τ.isSmooth K hK f hf)
    exact finite_fixedVectors_of_le (ρ := τ.representation)
      (show K.toSubgroup ≤ H.toSubgroup from hKH)
  · intro P M A p l a hp hl ha
    have hcone := hπ.parabolic p l a hp hl ha
    refine ⟨hcone.1, ?_⟩
    intro pres U r hr hmul χ hχ
    exact hcone.2 pres U r hr hmul χ
      (isNormalizedJacquetExponent_of_surjective_intertwining r hp hl hr hmul ha
        (hπ.isAdmissible_jacquetFunctor_obj p l r hp hl hr hmul ha) f hf hχ)

/-- The quotient closure property for a morphism in one fixed-universe
smooth representation category. -/
theorem IsNormalizedExponentTempered.of_surjective
    {hG : IsConnectedReductive G}
    {σ : SmoothRep.{0, u, v} ℂ (rationalPoints G)}
    (hπ : IsNormalizedExponentTempered hG π)
    (f : π ⟶ σ) (hf : Function.Surjective (SmoothRep.hom f)) :
    IsNormalizedExponentTempered hG σ :=
  hπ.of_surjective_intertwining (SmoothRep.hom f) hf

/-- The actual smooth module quotient, bundled as a normalized-exponent
tempered representation. The invariant submodule is supplied; no abstract
quotient object is chosen. -/
def normalizedTemperedQuotient
    {hG : IsConnectedReductive G}
    (hπ : IsNormalizedExponentTempered hG π)
    (S : Subrepresentation π.representation) :
    {τ : SmoothRep.{0, u, v} ℂ (rationalPoints G) //
      IsNormalizedExponentTempered hG τ} :=
  ⟨SmoothRep.quotient π S,
    hπ.of_surjective (SmoothRep.mkQ π S) (SmoothRep.mkQ_surjective π S)⟩

/-- The canonical surjection onto the constructed tempered quotient. -/
def normalizedTemperedQuotientMap
    {hG : IsConnectedReductive G}
    (hπ : IsNormalizedExponentTempered hG π)
    (S : Subrepresentation π.representation) :
    π ⟶ (normalizedTemperedQuotient hπ S).val :=
  SmoothRep.mkQ π S

theorem normalizedTemperedQuotientMap_surjective
    {hG : IsConnectedReductive G}
    (hπ : IsNormalizedExponentTempered hG π)
    (S : Subrepresentation π.representation) :
    Function.Surjective (SmoothRep.hom (normalizedTemperedQuotientMap hπ S)) :=
  SmoothRep.mkQ_surjective π S

end Langlands.Aubert.General.RepresentedParabolic
