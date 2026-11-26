import Langlands.Automorphic.AssociatedGammaEulerFamily
import Langlands.Global.AdelicFunctoriality.Inclusion
import Langlands.Global.Factors.FiniteEquationGrouping

/-! # Grouping number-field Euler families along the restriction of places -/

noncomputable section

set_option autoImplicit false

universe uF uE uI

namespace Langlands.Global.FunctionalEquationComparison

open Langlands.Global.AdelicFunctoriality
open scoped NumberField

variable {F : Type uF} {E : Type uE} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E]

/-- Restriction of either kind of place along a number-field inclusion. -/
def restrictPlace : AllPlaces E → AllPlaces F :=
  Sum.map (fun w => w.comap (algebraMap F E)) (fun w => w.under (𝓞 F))

private def finiteFibreEmbedding (v : FinitePlace F) : FinitePlacesAbove E v ↪ FinitePlace E :=
  ⟨Subtype.val, Subtype.val_injective⟩

/-- The finite places over a finite set of base places. -/
def finitePlacesOver (B : Finset (FinitePlace F)) : Finset (FinitePlace E) := by
  classical
  exact B.biUnion fun v => Finset.univ.map (finiteFibreEmbedding (E := E) v)

@[simp] theorem mem_finitePlacesOver (B : Finset (FinitePlace F)) (w : FinitePlace E) :
    w ∈ finitePlacesOver B ↔ w.under (𝓞 F) ∈ B := by
  classical
  simp only [finitePlacesOver, Finset.mem_biUnion, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨v, hv, w', rfl⟩
    exact (finitePlacesAbove_under v w').symm ▸ hv
  · exact fun hw => ⟨w.under (𝓞 F), hw, ⟨w, liesOver_under w⟩, rfl⟩

/-- A fibre of the map on all places, with finite and infinite places kept distinct. -/
def placesAbove : AllPlaces F → Finset (AllPlaces E) := by
  classical
  exact Sum.elim
    (fun v => (Finset.univ.filter (fun w : NumberField.InfinitePlace E =>
      w.comap (algebraMap F E) = v)).map ⟨Sum.inl, Sum.inl_injective⟩)
    (fun v => Finset.univ.map ((finiteFibreEmbedding (E := E) v).trans
      ⟨Sum.inr, Sum.inr_injective⟩))

@[simp] theorem mem_placesAbove (w : AllPlaces E) (v : AllPlaces F) :
    w ∈ placesAbove v ↔ restrictPlace w = v := by
  classical
  cases w with
  | inl w => cases v <;> simp [placesAbove, restrictPlace]
  | inr w =>
    cases v with
    | inl v => simp [placesAbove, restrictPlace]
    | inr v =>
      simp only [placesAbove, Sum.elim_inr, Finset.mem_map, Finset.mem_univ, true_and,
        Function.Embedding.trans_apply, Function.Embedding.coeFn_mk, restrictPlace,
        Sum.map_inr, Sum.inr.injEq]
      change (∃ w' : FinitePlacesAbove E v, w'.1 = w) ↔ w.under (𝓞 F) = v
      constructor
      · rintro ⟨w', rfl⟩
        exact finitePlacesAbove_under v w'
      · rintro rfl
        exact ⟨⟨w, liesOver_under w⟩, rfl⟩

variable {I : Type uI} [Fintype I]

/-- Group the finite product of upper local factors by their restriction to the base field. -/
def numberFieldProductFactors (L : I → AllPlaces E → LocalFactors)
    (v : AllPlaces F) : LocalFactors := by
  classical
  exact localFactorsProduct (placesAbove v) fun w => localFactorsProduct Finset.univ fun i => L i w

/-- Projection from one coordinate of the grouped local factors at a finite place. -/
theorem numberFieldProductFactors_finite (L : I → AllPlaces E → LocalFactors) (v : FinitePlace F)
    (s : ℂ) :
    (numberFieldProductFactors L (.inr v)).lFactor s =
      ∏ w : FinitePlacesAbove E v, ∏ i, (L i (.inr w.1)).lFactor s ∧
    (numberFieldProductFactors L (.inr v)).dualLFactor s =
      ∏ w : FinitePlacesAbove E v, ∏ i, (L i (.inr w.1)).dualLFactor s ∧
    (numberFieldProductFactors L (.inr v)).gamma s =
      ∏ w : FinitePlacesAbove E v, ∏ i, (L i (.inr w.1)).gamma s := by
  classical
  have hmap (f : AllPlaces E → ℂ) : (∏ w ∈ placesAbove (.inr v), f w) =
      ∏ w : FinitePlacesAbove E v, f (.inr w.1) := Finset.prod_map _ _ _
  refine ⟨hmap _, hmap _, ?_⟩
  simp only [numberFieldProductFactors, localFactorsProduct_gamma, hmap]

/-- The product of upper functional equations gives equation inputs over the
base with every upper place over a removed base place omitted from its tails. -/
def NumberFieldEquationGroupingStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (I : Type uI) [Fintype I] (L : I → AllPlaces E → LocalFactors)
    (B : Finset (FinitePlace F)),
    (∀ i, HeckeEulerFamily.HasEngineInputs (L i) (finitePlacesOver B)) →
    HeckeEulerFamily.HasEngineInputs (numberFieldProductFactors L) B

set_option maxHeartbeats 700000 in
/-- Form a product on the upper field first, then group it fibre by fibre. -/
theorem numberFieldEquationGrouping : NumberFieldEquationGroupingStatement.{uF,uE,uI} := by
  classical
  intro F E _ _ _ _ _ I _ L B h
  choose σ a b h using h
  let D (i : I) : FiniteEulerData (AllPlaces E) := ⟨L i, a i, b i⟩
  let M : ℝ := ∑ i, |σ i|
  let T := exceptionalPlaces E (finitePlacesOver B)
  let S := exceptionalPlaces F B
  have hM (i : I) : σ i ≤ M :=
    (le_abs_self _).trans (Finset.single_le_sum (fun j _ => abs_nonneg (σ j)) (Finset.mem_univ i))
  have hD := finiteEulerData_product_holds Finset.univ D T M fun i _ =>
    ⟨(h i).1, HeckeEulerFamily.hasEulerProductsOutside_mono (hM i) (h i).2.1, (h i).2.2⟩
  have hTS (w : AllPlaces E) : w ∈ T ↔ restrictPlace w ∈ S := by
    cases w <;> simp [T, S, exceptionalPlaces, restrictPlace]
  obtain ⟨hA, hP, hEq⟩ := finiteEquationGrouping (AllPlaces E) (AllPlaces F)
    restrictPlace placesAbove mem_placesAbove T S hTS (FiniteEulerData.product Finset.univ D) M
    hD.1 hD.2.1 hD.2.2
  exact ⟨M, fun s => ∏ i, a i s, fun s => ∏ i, b i s, hA, hP, hEq⟩

end Langlands.Global.FunctionalEquationComparison
