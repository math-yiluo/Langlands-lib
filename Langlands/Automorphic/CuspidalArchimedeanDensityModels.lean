import Langlands.Automorphic.ArchimedeanPlaceOperatorFamily

/-! # Actual source density models for the archimedean multiplicity space -/

noncomputable section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open scoped TensorProduct Matrix

namespace Langlands.Automorphic

open Langlands.Global ArchimedeanGL InfinitePlaceFamily

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem restrictedInclusion_ne_zero
    {K L V : Type*} [Group K] [LieRing L] [LieAlgebra ℂ L]
    [AddCommGroup V] [Module ℂ V]
    (κ : Representation ℂ K V) (π : L →ₗ⁅ℂ⁆ Module.End ℂ V)
    (W : Submodule ℂ V) (hW : PlaceComponent.IsStable κ π W) (hne : W ≠ ⊥) :
    (⟨W.subtype, (fun _ _ => rfl), (fun _ _ => rfl)⟩ :
      Archimedean.gkHoms (PlaceComponent.restrictCompact hW) (PlaceComponent.restrictLie hW)
        κ π) ≠ 0 := by
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  intro h
  exact hw0 (congrArg
    (fun f : Archimedean.gkHoms (PlaceComponent.restrictCompact hW)
      (PlaceComponent.restrictLie hW) κ π => f.val ⟨w, hw⟩) h)

private theorem exists_secondFactorHom
    {K L Q A B W : Type*} [Group K] [LieRing L] [LieAlgebra ℂ L]
    [AddCommGroup Q] [Module ℂ Q] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ K Q) (p : L →ₗ⁅ℂ⁆ Module.End ℂ Q)
    (ρB : Representation ℂ K B) (πB : L →ₗ⁅ℂ⁆ Module.End ℂ B)
    (ρW : Representation ℂ K W) (πW : L →ₗ⁅ℂ⁆ Module.End ℂ W)
    (e : A ⊗[ℂ] B ≃ₗ[ℂ] W)
    (hek : ∀ k t, e (TensorProduct.map LinearMap.id (ρB k) t) = ρW k (e t))
    (hel : ∀ X t, e (TensorProduct.map LinearMap.id (πB X) t) = πW X (e t))
    (f : Archimedean.gkHoms σ p ρW πW) (hf : f ≠ 0) :
    ∃ g : Archimedean.gkHoms σ p ρB πB, g ≠ 0 := by
  obtain ⟨φ, hφ⟩ := Archimedean.TensorContraction.exists_nonzero_contractedGKHom
    σ p ρB πB ρW πW e hek hel f hf
  exact ⟨_, hφ⟩

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance densityModelsRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance densityModelsContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance densityModelsSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance densityModelsFormsGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance densityModelsStableGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance densityModelsSpaceGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorRealization

variable (S : OperatorRealization F n)

/-- Actual irreducible admissible source subspaces for all infinite places. -/
structure PlaceDensityModels where
  subspace : Index F → Submodule ℂ S.Space
  irreducible : ∀ i, PlaceComponent.IsIrreducible
    (S.placeCompactFamily i) (S.placeLieFamily i) (subspace i)
  admissible : ∀ i, PlaceComponent.IsAdmissible (S.placeCompactFamily i) (subspace i)

namespace PlaceDensityModels

variable {S} (D : S.PlaceDensityModels)

local instance densityModelsFactorGroup (i : Index F) :
    AddCommGroup (D.subspace i) := Submodule.addCommGroup _

/-- The genuine local compact representation on the chosen source subspace. -/
def sourceCompact (i : Index F) : Representation ℂ (Compact n i) (D.subspace i) :=
  PlaceComponent.restrictCompact (D.irreducible i).2.1

/-- The genuine local complexified Lie action on the chosen source subspace. -/
def sourceLie (i : Index F) : Lie n i →ₗ⁅ℂ⁆ Module.End ℂ (D.subspace i) :=
  PlaceComponent.restrictLie (D.irreducible i).2.1

theorem source_isRealGKModule
    (v : {v : NumberField.InfinitePlace F // v.IsReal}) :
    Archimedean.IsRealGKModule n (D.sourceCompact (.inl v)) (D.sourceLie (.inl v)) :=
  PlaceComponent.isRealGKModule_restrict (D.irreducible (.inl v)).2.1
    (S.isRealGKModule_realPlace v)

theorem source_isComplexGKModule
    (v : {v : NumberField.InfinitePlace F // v.IsComplex}) :
    Archimedean.IsComplexGKModule n (D.sourceCompact (.inr v)) (D.sourceLie (.inr v)) :=
  PlaceComponent.isComplexGKModule_restrict (D.irreducible (.inr v)).2.1
    (S.isComplexGKModule_complexPlace v)

/-- Every chosen actual source has the hypotheses of simultaneous GK density. -/
theorem densityHyp (i : Index F) :
    Archimedean.GKModuleDensity.Hyp (D.sourceCompact i) (D.sourceLie i) := by
  have hfin : ∀ w, FiniteVectors.IsFiniteVector (D.sourceCompact i) w := by
    cases i with
    | inl v => exact (D.source_isRealGKModule v).1
    | inr v => exact (D.source_isComplexGKModule v).1
  have hcont : ∀ (w : D.subspace i) (ℓ : D.subspace i →ₗ[ℂ] ℂ),
      Continuous fun k => ℓ (D.sourceCompact i k w) := by
    cases i with
    | inl v => exact (D.source_isRealGKModule v).2.1
    | inr v => exact (D.source_isComplexGKModule v).2.1
  exact
    { irreducible := PlaceComponent.isIrreducibleGKModule_restrict (D.irreducible i)
      admissible := PlaceComponent.isAdmissibleGKModule_restrict
        (D.irreducible i).2.1 (D.admissible i)
      finite := fun w =>
        ⟨FiniteVectors.orbitSpan (D.sourceCompact i) w,
          FiniteVectors.self_mem_orbitSpan (D.sourceCompact i) w, hfin w,
          fun k _ hx =>
            (FiniteVectors.orbitSubrepresentation (D.sourceCompact i) w).apply_mem_toSubmodule k hx⟩
      continuous := hcont }

/-- Inclusion of the source subspace intertwines both actual place actions. -/
def sourceInclusion (i : Index F) :
    Archimedean.gkHoms (D.sourceCompact i) (D.sourceLie i)
      (S.placeCompactFamily i) (S.placeLieFamily i) :=
  ⟨(D.subspace i).subtype, (fun _ _ => rfl), (fun _ _ => rfl)⟩

theorem sourceInclusion_ne_zero (i : Index F) : D.sourceInclusion i ≠ 0 :=
  restrictedInclusion_ne_zero (S.placeCompactFamily i) (S.placeLieFamily i)
    (D.subspace i) (D.irreducible i).2.1 (D.irreducible i).1

variable (A : Subrepresentation S.finiteRepresentation)

local instance densityModelsFiniteFactorGroup : AddCommGroup A.toSubmodule :=
  Submodule.addCommGroup _

private theorem finiteTensorEquiv_compact
    (hS : S.IsIrreducible) (hne : A ≠ ⊥) (hA : A.toRepresentation.IsIrreducible)
    (ha : IsAdmissible A.toRepresentation) (i : Index F) (k : Compact n i)
    (t : A.toSubmodule ⊗[ℂ] S.FiniteMultiplicity A) :
    S.finiteMultiplicityEquiv A hS hne hA ha
        (TensorProduct.map LinearMap.id (S.finiteMultiplicityPlaceCompact A i k) t) =
      S.placeCompactFamily i k (S.finiteMultiplicityEquiv A hS hne hA ha t) :=
  S.finiteMultiplicityEvaluation_compact A (compactInclusion n i k) t

private theorem finiteTensorEquiv_lie
    (hS : S.IsIrreducible) (hne : A ≠ ⊥) (hA : A.toRepresentation.IsIrreducible)
    (ha : IsAdmissible A.toRepresentation) (i : Index F) (X : Lie n i)
    (t : A.toSubmodule ⊗[ℂ] S.FiniteMultiplicity A) :
    S.finiteMultiplicityEquiv A hS hne hA ha
        (TensorProduct.map LinearMap.id (S.finiteMultiplicityPlaceLie A i X) t) =
      S.placeLieFamily i X (S.finiteMultiplicityEquiv A hS hne hA ha t) := by
  induction t with
  | tmul a f => rfl
  | add t t' ht ht' =>
    simp only [LinearMap.map_add, LinearEquiv.map_add, ht, ht']

/-- A nonzero source component remains nonzero in the archimedean multiplicity
space after separating the actual finite factor. -/
theorem exists_nonzero_multiplicityHom
    (hS : S.IsIrreducible) (hne : A ≠ ⊥) (hA : A.toRepresentation.IsIrreducible)
    (ha : IsAdmissible A.toRepresentation) (i : Index F) :
    ∃ f : Archimedean.gkHoms (D.sourceCompact i) (D.sourceLie i)
      (S.finiteMultiplicityPlaceCompact A i) (S.finiteMultiplicityPlaceLie A i), f ≠ 0 :=
  exists_secondFactorHom
    (D.sourceCompact i) (D.sourceLie i) (S.finiteMultiplicityPlaceCompact A i)
    (S.finiteMultiplicityPlaceLie A i) (S.placeCompactFamily i) (S.placeLieFamily i)
    (S.finiteMultiplicityEquiv A hS hne hA ha)
    (finiteTensorEquiv_compact A hS hne hA ha i)
    (finiteTensorEquiv_lie A hS hne hA ha i)
    (D.sourceInclusion i) (D.sourceInclusion_ne_zero i)

/-- Supplied nonzero pairings on the actual local models give a nonzero simultaneous
local pairing on the actual archimedean multiplicity space. -/
def multiplicityPairing
    (hS : S.IsIrreducible) (hne : A ≠ ⊥) (hA : A.toRepresentation.IsIrreducible)
    (ha : IsAdmissible A.toRepresentation)
    (θK : ∀ i : Index F, Compact n i → Compact n i)
    (θL : ∀ i : Index F, Lie n i → Lie n i)
    (hB : ∀ i, ∃ B : D.subspace i →ₗ[ℂ] D.subspace i →ₗ[ℂ] ℂ,
      Archimedean.FiniteFamilyPairing.IsTwistedPairing
        (θK i) (θL i) (D.sourceCompact i) (D.sourceLie i) B ∧ B ≠ 0) :
    {B : S.FiniteMultiplicity A →ₗ[ℂ] S.FiniteMultiplicity A →ₗ[ℂ] ℂ //
      (∀ i, Archimedean.FiniteFamilyPairing.IsTwistedPairing
        (θK i) (θL i) (S.finiteMultiplicityPlaceCompact A i)
        (S.finiteMultiplicityPlaceLie A i) B) ∧ B ≠ 0} :=
  Archimedean.FiniteFamilyPairing.assemblePairing.{u, 0, 0, u, u}
    (Index F) (Compact n) (Lie n)
    (fun i => (D.subspace i : Type u)) D.sourceCompact D.sourceLie θK θL D.densityHyp hB
    (S.FiniteMultiplicity A) (S.finiteMultiplicityPlaceCompact A)
    (S.finiteMultiplicityPlaceLie A)
    (S.finiteMultiplicityPlaceFamily_commutes A hne hA)
    (S.finiteMultiplicityPlaceFamily_irreducible A hS hne hA ha)
    (D.exists_nonzero_multiplicityHom A hS hne hA ha)

end PlaceDensityModels
end OperatorRealization

namespace CuspidalOperatorRealization

variable [CompactSpace (AdeleQuotient F)] {r : ℕ}
  (T : CuspidalOperatorRealization F r)

theorem nonempty_placeDensityModels : Nonempty T.realization.PlaceDensityModels := by
  classical
  have hex : ∀ i : Index F, ∃ W : Submodule ℂ T.realization.Space,
      PlaceComponent.IsIrreducible (T.realization.placeCompactFamily i)
        (T.realization.placeLieFamily i) W ∧
      PlaceComponent.IsAdmissible (T.realization.placeCompactFamily i) W := by
    intro i
    cases i with
    | inl v => exact T.exists_realPlaceComponent v
    | inr v => exact T.exists_complexPlaceComponent v
  choose W hI hA using hex
  exact ⟨⟨W, hI, hA⟩⟩

/-- Choose actual local irreducible admissible source subspaces of a cuspidal realization. -/
def placeDensityModels : T.realization.PlaceDensityModels :=
  Classical.choice T.nonempty_placeDensityModels

end CuspidalOperatorRealization
end Langlands.Automorphic
