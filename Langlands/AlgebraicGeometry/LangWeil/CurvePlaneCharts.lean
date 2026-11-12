import Langlands.AlgebraicGeometry.AffineChartPoints
import Langlands.AlgebraicGeometry.GeometricIrreducibilityAffine
import Langlands.AlgebraicGeometry.SchemeEtalePureFibreDimension
import Langlands.AlgebraicGeometry.SchemeFiberBaseChange
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# Affine charts of geometrically irreducible curve families

For a scheme `Y` over `S` and an affine open `S₀` of `S`, the ring of an affine chart of `Y`
over `S₀` inherits from the morphism `Y ⟶ S` geometric irreducibility of its field fibres,
pure fibre dimension and finite type. Points of `Y` over `S` with values in a field are
counted by one chart up to the points of finitely many principal closed subsets of further
charts.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.LangWeil.CurvePlane

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.SchemeFiberGeometry

section Ring

/-- A ring with prime nilradical and pure dimension `d` has Krull dimension `d`. -/
theorem ringKrullDim_eq_of_hasPureRingDimension {T : Type*} [CommRing T]
    [(nilradical T).IsPrime] {d : ℕ} (h : HasPureRingDimension T d) :
    ringKrullDim T = d := by
  have hmin : nilradical T ∈ minimalPrimes T :=
    ⟨⟨inferInstance, bot_le⟩, fun q hq _ => by
      have : q.IsPrime := hq.1
      exact nilradical_le_prime q⟩
  rw [← h _ hmin, ringKrullDim_quotient,
    (PrimeSpectrum.zeroLocus_eq_univ_iff _).mpr subset_rfl]
  exact (Order.krullDim_eq_of_orderIso (OrderIso.Set.univ (α := PrimeSpectrum T))).symm

/-- Algebra maps from an algebra of finite type to a finite ring form a finite set. -/
theorem algHom_finite_of_finiteType {A D κ : Type*} [CommRing A] [CommRing D] [Algebra A D]
    [Algebra.FiniteType A D] [CommRing κ] [Algebra A κ] [Finite κ] : Finite (D →ₐ[A] κ) := by
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType A D).out
  let ev : (D →ₐ[A] κ) → (s → κ) := fun φ x => φ x
  exact Finite.of_injective ev fun φ ψ h =>
    AlgHom.ext_of_adjoin_eq_top hs fun a ha => congrFun h ⟨a, ha⟩

end Ring

variable {S : Scheme.{u}} {S₀ : S.Opens} (hS₀ : IsAffineOpen S₀) {Y : Over S}

include hS₀ in
/-- Chart rings are of finite type over the base sections. -/
theorem chart_finiteType [LocallyOfFiniteType Y.hom] (c : Chart S₀ Y) :
    Algebra.FiniteType Γ(S, S₀) c.Ring :=
  HasRingHomProperty.appLE @LocallyOfFiniteType Y.hom inferInstance ⟨S₀, hS₀⟩
    ⟨c.U, c.isAffine⟩ c.le

include hS₀ in
/-- A nonempty field fibre of a chart of a geometrically irreducible morphism is irreducible:
it is an open subscheme of the irreducible field fibre of the morphism. -/
theorem chart_nilradical_isPrime [GeometricallyIrreducible Y.hom] (c : Chart S₀ Y)
    (L : Type u) [Field L] [Algebra Γ(S, S₀) L] [Nontrivial (L ⊗[Γ(S, S₀)] c.Ring)] :
    (nilradical (L ⊗[Γ(S, S₀)] c.Ring)).IsPrime := by
  rw [← irreducibleSpace_pullbackSpec_iff_nilradical_isPrime]
  have hirr : IrreducibleSpace ↥(pullback Y.hom (testMap hS₀ L)) :=
    pullback_of_geometrically (GeometricallyIrreducible.geometrically_irreducibleSpace
      (f := Y.hom)) L (testMap hS₀ L)
  let ι := pullback.map (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, S₀) c.Ring)))
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, S₀) L))) Y.hom (testMap hS₀ L) c.fromSpec
    (𝟙 _) hS₀.fromSpec (c.fromSpec_hom hS₀).symm (Category.id_comp _).symm
  have : Nonempty ↥(pullback (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, S₀) c.Ring)))
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, S₀) L)))) := by
    let e := pullbackSymmetry _ _ ≪≫ pullbackSpecIso Γ(S, S₀) L c.Ring
    exact ⟨e.inv (Nonempty.some
      (inferInstanceAs (Nonempty (PrimeSpectrum (L ⊗[Γ(S, S₀)] c.Ring)))))⟩
  have : IsOpenImmersion ι := Scheme.pullback_map_isOpenImmersion _ _ _ _ _ _ _ _ _
  exact (Scheme.Hom.isOpenEmbedding ι).irreducibleSpace

include hS₀ in
/-- The residue-field fibres of a chart ring have pure dimension `d` when the fibres of the
morphism do: open immersions are étale. -/
theorem chart_hasPureRingDimension_fiber [LocallyOfFiniteType Y.hom] {d : ℕ}
    (hdim : ∀ s, HasPureDimension (Y.hom.fiber s) d) (c : Chart S₀ Y)
    (p : PrimeSpectrum Γ(S, S₀)) : HasPureRingDimension (p.asIdeal.Fiber c.Ring) d := by
  have h₀ : PureFibreDimensionMorphismProperty d Y.hom := ⟨inferInstance, hdim⟩
  have h₁ := pureFibreDimension_precomp_etale d c.fromSpec Y.hom inferInstance h₀
  rw [c.fromSpec_hom hS₀] at h₁
  have h₂ := pureFibreDimension_of_postcomp_etale d _ hS₀.fromSpec inferInstance h₁
  exact (hasPureDimension_specFiber_iff Γ(S, S₀) c.Ring p d).mp (h₂.2 p)

/-- Points of `Y` over `S` with values in a finite field are counted by one chart `c₀`, up to
the points of principal closed subsets of finitely many charts covering `Y` over `S₀`, provided
each principal open complement lies in `c₀`. -/
theorem card_points_bounds [LocallyOfFiniteType Y.hom] (κ : Type u) [Field κ] [Finite κ]
    [Algebra Γ(S, S₀) κ] {ι : Type*} [Fintype ι] (c : ι → Chart S₀ Y)
    (hcov : Y.hom ⁻¹ᵁ S₀ ≤ ⨆ i, (c i).U) (c₀ : Chart S₀ Y) (h : ∀ i, (c i).Ring)
    (hh : ∀ i, Y.left.basicOpen (U := (c i).U) (h i) ≤ c₀.U) :
    Nat.card (c₀.Ring →ₐ[Γ(S, S₀)] κ) ≤ Nat.card (testObj hS₀ κ ⟶ Y) ∧
      Nat.card (testObj hS₀ κ ⟶ Y) ≤ Nat.card (c₀.Ring →ₐ[Γ(S, S₀)] κ) +
        ∑ i, Nat.card ((c i).Ring ⧸ Ideal.span {h i} →ₐ[Γ(S, S₀)] κ) := by
  classical
  have := chart_finiteType hS₀ c₀
  have : ∀ i, Algebra.FiniteType Γ(S, S₀) ((c i).Ring ⧸ Ideal.span {h i}) := fun i =>
    have := chart_finiteType hS₀ (c i)
    inferInstance
  have : Finite (c₀.Ring →ₐ[Γ(S, S₀)] κ) := algHom_finite_of_finiteType
  have : ∀ i, Finite ((c i).Ring ⧸ Ideal.span {h i} →ₐ[Γ(S, S₀)] κ) := fun _ =>
    algHom_finite_of_finiteType
  let F : (c₀.Ring →ₐ[Γ(S, S₀)] κ) ⊕
      (Σ i, ((c i).Ring ⧸ Ideal.span {h i} →ₐ[Γ(S, S₀)] κ)) → (testObj hS₀ κ ⟶ Y) :=
    Sum.elim (c₀.pt hS₀) fun z => (c z.1).pt hS₀ (z.2.comp (Ideal.Quotient.mkₐ _ _))
  have hF : Function.Surjective F := by
    intro x
    let z₀ : Spec (CommRingCat.of κ) := IsLocalRing.closedPoint κ
    have hrange : ∀ U : Y.left.Opens, x.left z₀ ∈ U → Set.range x.left ⊆ U := by
      rintro U hU _ ⟨z, rfl⟩
      rwa [Subsingleton.elim (α := PrimeSpectrum κ) z z₀]
    have hS : x.left z₀ ∈ Y.hom ⁻¹ᵁ S₀ := by
      change Y.hom (x.left z₀) ∈ S₀
      have hx : Y.hom (x.left z₀) = (testMap hS₀ κ) z₀ := by
        rw [← Scheme.Hom.comp_apply, Over.w x]
        rfl
      rw [hx, testMap, Scheme.Hom.comp_apply]
      change _ ∈ (S₀ : Set S)
      rw [← hS₀.range_fromSpec]
      exact ⟨_, rfl⟩
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov hS)
    obtain ⟨ψ, rfl⟩ := (c i).exists_pt hS₀ x (hrange _ hi)
    by_cases hψ : ψ (h i) = 0
    · refine ⟨Sum.inr ⟨i, Ideal.Quotient.liftₐ _ ψ ?_⟩, ?_⟩
      · intro a ha
        obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
        rw [map_mul, hψ, mul_zero]
      · change (c i).pt hS₀ _ = _
        congr 1
    · have hmem : ((c i).pt hS₀ ψ).left z₀ ∈ Y.left.basicOpen (U := (c i).U) (h i) := by
        let w : Spec Γ(Y.left, (c i).U) := PrimeSpectrum.comap (ψ : (c i).Ring →+* κ) z₀
        have hw : w ∈ (PrimeSpectrum.basicOpen (h i) : (Spec Γ(Y.left, (c i).U)).Opens) := by
          change ψ (h i) ∉ IsLocalRing.maximalIdeal κ
          rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not, isUnit_iff_ne_zero]
          exact hψ
        exact (SetLike.ext_iff.mp ((c i).isAffine.fromSpec_preimage_basicOpen (h i)) w).mpr hw
      obtain ⟨ψ₀, hψ₀⟩ := c₀.exists_pt hS₀ _ (hrange _ (hh i hmem))
      exact ⟨Sum.inl ψ₀, hψ₀⟩
  have : Finite (testObj hS₀ κ ⟶ Y) := Finite.of_surjective F hF
  refine ⟨Nat.card_le_card_of_injective _ (c₀.pt_injective hS₀), ?_⟩
  calc
    Nat.card (testObj hS₀ κ ⟶ Y) ≤ Nat.card ((c₀.Ring →ₐ[Γ(S, S₀)] κ) ⊕
        (Σ i, ((c i).Ring ⧸ Ideal.span {h i} →ₐ[Γ(S, S₀)] κ))) :=
      Nat.card_le_card_of_surjective F hF
    _ = _ := by rw [Nat.card_sum, Nat.card_sigma]

end Langlands.AlgebraicGeometry.LangWeil.CurvePlane
