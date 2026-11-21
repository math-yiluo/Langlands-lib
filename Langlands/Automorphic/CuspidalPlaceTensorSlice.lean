import Langlands.Automorphic.CuspidalPlaceTensorDecomposition
import Langlands.Automorphic.PlaceComponentMinimal

/-! # Fixed-factor slices of the actual cuspidal tensor decomposition -/

noncomputable section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

open scoped Classical TensorProduct

namespace Langlands.Automorphic

open Langlands.Global InfinitePlaceFamily

attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance sliceRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance sliceContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance sliceSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance sliceFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance sliceStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance sliceSpaceGroup (S : OperatorRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

namespace OperatorRealization.PlaceDensityModels

variable {S : OperatorRealization F n} (D : S.PlaceDensityModels)
  (A : Subrepresentation S.finiteRepresentation)

local instance sliceFactorGroup (i : Index F) : AddCommGroup (D.subspace i) :=
  Submodule.addCommGroup _
local instance sliceFiniteGroup : AddCommGroup A.toSubmodule :=
  Submodule.addCommGroup _

variable (hS : S.IsIrreducible) (hne : A ≠ ⊥) (hA : A.toRepresentation.IsIrreducible)
  (hadm : IsAdmissible A.toRepresentation)
  (i : Index F) (a : A.toSubmodule) (b : ∀ j, D.subspace j)

/-- Hold the finite vector and every infinite vector but the one at `i` fixed. -/
def tensorSlice : D.subspace i →ₗ[ℂ] S.Space :=
  (D.fullTensorEquiv A hS hne hA hadm).toLinearMap.comp
    ((TensorProduct.mk ℂ _ _ a).comp ((PiTensorProduct.tprod ℂ).toLinearMap b i))

theorem tensorSlice_apply (x : D.subspace i) :
    D.tensorSlice A hS hne hA hadm i a b x =
      D.fullTensorEquiv A hS hne hA hadm
        (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update b i x)) := rfl

theorem tensorSlice_compact (k : Compact n i) (x : D.subspace i) :
    D.tensorSlice A hS hne hA hadm i a b (D.sourceCompact i k x) =
      S.placeCompactFamily i k (D.tensorSlice A hS hne hA hadm i a b x) := by
  simpa only [tensorSlice_apply] using D.fullTensorEquiv_compact A hS hne hA hadm i k a
    (Function.update b i x) (Function.update b i (D.sourceCompact i k x))
    (fun j hj => by simp only [Function.update_of_ne hj])
    (by simp only [Function.update_self])

theorem tensorSlice_lie (X : Lie n i) (x : D.subspace i) :
    D.tensorSlice A hS hne hA hadm i a b (D.sourceLie i X x) =
      S.placeLieFamily i X (D.tensorSlice A hS hne hA hadm i a b x) := by
  simpa only [tensorSlice_apply] using D.fullTensorEquiv_lie A hS hne hA hadm i X a
    (Function.update b i x) (Function.update b i (D.sourceLie i X x))
    (fun j hj => by simp only [Function.update_of_ne hj])
    (by simp only [Function.update_self])

theorem tensorSlice_injective (ha : a ≠ 0) (hb : ∀ j, j ≠ i → b j ≠ 0) :
    Function.Injective (D.tensorSlice A hS hne hA hadm i a b) := by
  apply LinearMap.ker_eq_bot.mp
  refine eq_bot_iff.mpr fun x hx => (Submodule.mem_bot ℂ).mpr ?_
  by_contra hx0
  apply D.fullTensorEquiv_pure_ne_zero A hS hne hA hadm a (Function.update b i x) ha _
    ((D.tensorSlice_apply A hS hne hA hadm i a b x).symm.trans (LinearMap.mem_ker.mp hx))
  intro j
  by_cases hj : j = i
  · subst j
    simpa only [Function.update_self] using hx0
  · simpa only [Function.update_of_ne hj] using hb j hj

/-- A compact open subgroup fixing `a` fixes every vector in the slice. -/
theorem exists_compactOpen_fixes_tensorSlice :
    ∃ U : OpenSubgroup (FiniteAdelicGL F n), IsCompact (U : Set (FiniteAdelicGL F n)) ∧
      ∀ g ∈ U, ∀ x, S.finiteRepresentation g (D.tensorSlice A hS hne hA hadm i a b x) =
        D.tensorSlice A hS hne hA hadm i a b x := by
  have hsmooth : Langlands.IsSmooth A.toRepresentation := hadm.1
  have hsv : Langlands.IsSmoothVector A.toRepresentation a := hsmooth a
  obtain ⟨V, hV⟩ := hsv
  obtain ⟨U, hUV, hU⟩ := exists_compact_openSubgroup_le V
  refine ⟨U, hU, fun g hg x => ?_⟩
  have hga : A.toRepresentation g a = a := hV ⟨g, hUV hg⟩
  have h := D.fullTensorEquiv_finite A hS hne hA hadm g a
    (PiTensorProduct.tprod ℂ (Function.update b i x))
  simpa only [hga, tensorSlice_apply] using h.symm

/-- A slice with nonzero fixed factors is an irreducible admissible place component. -/
theorem tensorSlice_range (ha : a ≠ 0) (hb : ∀ j, j ≠ i → b j ≠ 0) :
    let W := LinearMap.range (D.tensorSlice A hS hne hA hadm i a b)
    PlaceComponent.IsIrreducible (S.placeCompactFamily i) (S.placeLieFamily i) W ∧
      PlaceComponent.IsAdmissible (S.placeCompactFamily i) W := by
  let L := D.tensorSlice A hS hne hA hadm i a b
  have hinj : Function.Injective L := D.tensorSlice_injective A hS hne hA hadm i a b ha hb
  have hsrc := (D.densityHyp i).irreducible
  have : Nontrivial (D.subspace i) := hsrc.1
  have htop : PlaceComponent.IsIrreducible (D.sourceCompact i) (D.sourceLie i) ⊤ :=
    ⟨top_ne_bot, ⟨fun _ _ _ => Submodule.mem_top, fun _ _ _ => Submodule.mem_top⟩,
      fun W _ hW => hsrc.2 W hW.1 hW.2⟩
  have hneImage : (⊤ : Submodule ℂ (D.subspace i)).map L ≠ ⊥ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : D.subspace i)
    have hxL : L x ∈ (⊤ : Submodule ℂ (D.subspace i)).map L :=
      ⟨x, Submodule.mem_top, rfl⟩
    rw [h] at hxL
    have hzero : L x = 0 := (Submodule.mem_bot ℂ).mp hxL
    exact hx (hinj (hzero.trans (map_zero L).symm))
  have hadmTop : PlaceComponent.IsAdmissible (D.sourceCompact i) ⊤ := by
    intro d τ hτ
    have := (D.densityHyp i).admissible d τ hτ
    exact Submodule.finiteDimensional_of_le (S₂ := Archimedean.gkIntertwiners (D.sourceCompact i) d τ)
      (fun _ h => h.2)
  have hκ := D.tensorSlice_compact A hS hne hA hadm i a b
  have hπ := D.tensorSlice_lie A hS hne hA hadm i a b
  change PlaceComponent.IsIrreducible _ _ (LinearMap.range L) ∧
    PlaceComponent.IsAdmissible _ (LinearMap.range L)
  rw [← Submodule.map_top]
  exact ⟨PlaceComponent.isIrreducible_map L hκ hπ htop hneImage,
    PlaceComponent.isAdmissible_map L hκ htop.2.1.1
      (fun x _ hx => hinj (hx.trans (map_zero L).symm)) hadmTop⟩

end OperatorRealization.PlaceDensityModels

namespace CuspidalOperatorRealization

variable [CompactSpace (AdeleQuotient F)] {r : ℕ} (T : CuspidalOperatorRealization F r)

/-- The slice of the chosen cuspidal tensor decomposition at `i`. -/
def placeTensorSlice (i : Index F) (a : T.finiteInfiniteDecomposition.finite.toSubmodule)
    (b : ∀ j, T.placeDensityModels.subspace j) :
    T.placeDensityModels.subspace i →ₗ[ℂ] T.Space :=
  T.placeDensityModels.tensorSlice T.finiteInfiniteDecomposition.finite T.irreducible
    T.finiteInfiniteDecomposition.nonzero T.finiteInfiniteDecomposition.irreducible
    T.finiteInfiniteDecomposition.admissible i a b

theorem placeTensorSlice_apply (i : Index F) (a : T.finiteInfiniteDecomposition.finite.toSubmodule)
    (b : ∀ j, T.placeDensityModels.subspace j) (x : T.placeDensityModels.subspace i) :
    T.placeTensorSlice i a b x =
      T.allPlaceTensorEquiv (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update b i x)) := rfl

/-- Nonzero fixed factors give an injective slice with irreducible admissible range and a
common finite stabilizer. -/
def PlaceTensorSliceStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]
    (s : ℕ) (S : CuspidalOperatorRealization K s) (j : Index K)
    (a : S.finiteInfiniteDecomposition.finite.toSubmodule)
    (b : ∀ k, S.placeDensityModels.subspace k),
    a ≠ 0 → (∀ k, k ≠ j → b k ≠ 0) →
    let L := S.placeTensorSlice j a b
    Function.Injective L ∧
    PlaceComponent.IsIrreducible (S.realization.placeCompactFamily j)
      (S.realization.placeLieFamily j) (LinearMap.range L) ∧
    PlaceComponent.IsAdmissible (S.realization.placeCompactFamily j) (LinearMap.range L) ∧
    ∃ U : OpenSubgroup (FiniteAdelicGL K (s + 1)),
      IsCompact (U : Set (FiniteAdelicGL K (s + 1))) ∧
      ∀ g ∈ U, ∀ x, S.realization.finiteRepresentation g (L x) = L x

theorem placeTensorSliceStatement : PlaceTensorSliceStatement.{u} := by
  intro K _ _ _ s S j a b ha hb
  let A := S.finiteInfiniteDecomposition
  let D := S.placeDensityModels
  have hI := D.tensorSlice_injective A.finite S.irreducible A.nonzero A.irreducible
    A.admissible j a b ha hb
  have hR := D.tensorSlice_range A.finite S.irreducible A.nonzero A.irreducible
    A.admissible j a b ha hb
  have hF := D.exists_compactOpen_fixes_tensorSlice A.finite S.irreducible A.nonzero
    A.irreducible A.admissible j a b
  exact ⟨hI, hR.1, hR.2, hF⟩

end CuspidalOperatorRealization
end Langlands.Automorphic
