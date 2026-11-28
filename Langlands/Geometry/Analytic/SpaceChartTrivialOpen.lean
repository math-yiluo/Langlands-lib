import Langlands.Geometry.Analytic.SpaceChartRelation
import Langlands.Geometry.Analytic.AffineAnalytificationSeminormProof
import Langlands.Geometry.Analytic.AffineAnalytificationJointSurjectivity
import Langlands.Geometry.Analytic.AffineAnalytificationLocalizedEtaleReduction
import Langlands.Geometry.Analytic.AffineAnalytificationEtaleProof
import Langlands.Geometry.Analytic.StrongEtaleSmallIndexComparisonProof
import Langlands.Geometry.Analytic.EtaleSectionsOpen
import Langlands.Geometry.Analytic.LocalizedOpenRelation

/-! # Open sets on which the analytified relation of an elementary chart is trivial

Let `y : Spec B → X` be an étale test point of a presheaf, with a model `Spec C` of
`Spec B ×_X Spec B` closed in `Spec B ×_K Spec B`. If `y` is elementary at a prime `q` of `B`,
every analytic point `v` of `Spec(B)ᵃⁿ` with center `q` has an open neighbourhood on which
the analytified relation is the diagonal. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Set Topology
open _root_.AlgebraicGeometry

namespace Langlands.Analytic.SpaceAnalytification.ChartQuotient

open SaturatedAtlasPresentation AffineAnalytification ExistenceReduction
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology
open scoped TensorProduct

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Analytifications of étale algebra maps are étale. -/
theorem etale_localizedHom {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (f : A →ₐ[K] B) (hf : f.toRingHom.Etale) : etale (localizedHom K P Q f) :=
  affineAnalytificationLocalizedEtaleReduction affineAnalytificationEtale
    strongEtaleSmallIndexComparison K A B P Q f hf

section Compact

variable {F : AlgebraicSpace.Presheaf (Spec (CommRingCat.of K))}
  {B : Type u} [CommRing B] [Algebra K B] (Q : FinitePolynomialPresentation K B)
  {y : (schemeYoneda (Spec (CommRingCat.of K))).obj (ringTest K B) ⟶ F}

/-- If the model of the self-intersection of a test point is closed in the product, the set of
its analytic points whose two projections lie in a compact set is compact. -/
theorem isCompact_relationPreimage (M : TestModel y y)
    (hprod : Function.Surjective
      (Algebra.TensorProduct.lift M.f M.g (fun a b => mul_comm (M.f a) (M.g b)) :
        B ⊗[K] B →ₐ[K] M.C))
    {N : Set (Space K Q)} (hN : IsCompact N) :
    IsCompact {r : Space K M.R | baseMap K Q M.R M.f r ∈ N ∧ baseMap K Q M.R M.g r ∈ N} := by
  let S := {r : Space K M.R | baseMap K Q M.R M.f r ∈ N ∧ baseMap K Q M.R M.g r ∈ N}
  have hb : ∀ b : B, ∃ c : ℝ, 0 ≤ c ∧ ∀ v ∈ N, pointSeminorm K Q v b ≤ c := by
    intro b
    obtain ⟨c, hc⟩ := hN.bddAbove_image (continuous_pointSeminorm_apply K Q b).continuousOn
    exact ⟨max c 0, le_max_right _ _, fun v hv => (hc ⟨v, hv, rfl⟩).trans (le_max_left _ _)⟩
  have key : ∀ t : B ⊗[K] B, ∃ c : ℝ, ∀ r ∈ S, pointSeminorm K M.R r
      (Algebra.TensorProduct.lift M.f M.g (fun a b => mul_comm (M.f a) (M.g b)) t) ≤ c := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul b b' =>
      obtain ⟨c, hc0, hc⟩ := hb b
      obtain ⟨c', hc'0, hc'⟩ := hb b'
      refine ⟨c * c', fun r hr => ?_⟩
      have e : (Algebra.TensorProduct.lift M.f M.g (fun a b => mul_comm (M.f a) (M.g b)) :
          B ⊗[K] B →ₐ[K] M.C) (b ⊗ₜ b') = M.f b * M.g b' := Algebra.TensorProduct.lift_tmul _ _ _ _ _
      rw [e, map_mul, ← pointSeminorm_baseMap, ← pointSeminorm_baseMap]
      exact mul_le_mul (hc _ hr.1) (hc' _ hr.2) (apply_nonneg _ _) hc0
    | add s t hs ht =>
      obtain ⟨c, hc⟩ := hs
      obtain ⟨c', hc'⟩ := ht
      refine ⟨c + c', fun r hr => ?_⟩
      rw [map_add]
      exact (map_add_le_add _ _ _).trans (add_le_add (hc r hr) (hc' r hr))
  have hgen : ∀ j : Fin M.R.arity, ∃ c : ℝ, ∀ r ∈ S,
      pointSeminorm K M.R r (M.R.map (MvPolynomial.X j)) ≤ c := by
    intro j
    obtain ⟨t, ht⟩ := hprod (M.R.map (MvPolynomial.X j))
    obtain ⟨c, hc⟩ := key t
    exact ⟨c, fun r hr => ht ▸ hc r hr⟩
  choose c hc using hgen
  obtain ⟨m, hm⟩ := exists_radius_gt K (∑ j, |c j|)
  have hsub : S ⊆ range (chart K M.R m) := by
    intro r hr
    rw [mem_range_chart_iff]
    intro j
    rw [SeminormComparison.coordinateNorm_eq]
    refine ((hc j r hr).trans (le_abs_self _)).trans (le_trans ?_ hm.le)
    exact Finset.single_le_sum (f := fun j => |c j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ j)
  have hclosed : IsClosed S :=
    (hN.isClosed.preimage (baseMap K Q M.R M.f).continuous).inter
      (hN.isClosed.preimage (baseMap K Q M.R M.g).continuous)
  exact (isCompact_range (continuous_chart K M.R m)).of_isClosed_subset hclosed hsub

end Compact

section TrivialOpen

variable {F : AlgebraicSpace.Presheaf (Spec (CommRingCat.of K))}
  {B : Type u} [CommRing B] [Algebra K B] (Q : FinitePolynomialPresentation K B)
  {y : (schemeYoneda (Spec (CommRingCat.of K))).obj (ringTest K B) ⟶ F}

/-- **Relation-trivial neighbourhoods.** Let `y` be an étale test point with a closed model `M`
of its self-intersection, elementary at a prime `q`. Every analytic point `v` with center `q`
has an open neighbourhood `O` such that any two analytic maps into `O` related through `M` are
equal. -/
theorem exists_trivial_open (hy : AlgebraicSpace.IsEtale y) (M : TestModel y y)
    (hprod : Function.Surjective
      (Algebra.TensorProduct.lift M.f M.g (fun a b => mul_comm (M.f a) (M.g b)) :
        B ⊗[K] B →ₐ[K] M.C))
    (q : PrimeSpectrum B)
    (helem : ∀ μ : (M.C : Type u) →ₐ[K] B, μ.comp M.f = AlgHom.id K B →
      μ.comp M.g = AlgHom.id K B → ∀ P : PrimeSpectrum M.C,
        PrimeSpectrum.comap (M.f : B →+* M.C) P = q →
        PrimeSpectrum.comap (M.g : B →+* M.C) P = q → P = PrimeSpectrum.comap (μ : M.C →+* B) q)
    (v : Space K Q) (hv : center K Q v = q) :
    ∃ O : Set (Space K Q), IsOpen O ∧ v ∈ O ∧
      ∀ (T : LocalizedCategory.{u, u, u} (K := K)) (α β : T ⟶ localized K Q),
        (∀ t, localizedSpaceFunctor.map α t ∈ O) → (∀ t, localizedSpaceFunctor.map β t ∈ O) →
        M.ARel Q Q α β → α = β := by
  classical
  obtain ⟨μ, hμf, hμg⟩ := M.exists_lift (AlgHom.id K B) (AlgHom.id K B) rfl
  let δ : localized K Q ⟶ localized K M.R := localizedHom K M.R Q μ
  have hδf : δ ≫ localizedHom K Q M.R M.f = 𝟙 _ := by
    rw [← lhom_comp, hμf, lhom_id]
  have hδg : δ ≫ localizedHom K Q M.R M.g = 𝟙 _ := by
    rw [← lhom_comp, hμg, lhom_id]
  have hδ : openImmersion δ :=
    localizedEtaleSectionsOpen (etale_localizedHom Q M.R M.f (M.etale_f hy)) hδf
  let Δ : Set (Space K M.R) := range (localizedSpaceFunctor.map δ)
  have hΔ : IsOpen Δ := (openImmersion.isOpenEmbedding hδ).isOpen_range
  have hδpt : ∀ v', localizedSpaceFunctor.map δ v' = baseMap K M.R Q μ v' := by
    intro v'
    rw [localizedSpaceFunctor_map_localizedHom]
    rfl
  -- analytic points of the relation over `(v, v)` lie on the diagonal
  have hdiag : ∀ r : Space K M.R, baseMap K Q M.R M.f r = v → baseMap K Q M.R M.g r = v →
      r ∈ Δ := by
    intro r hrf hrg
    have hcf : PrimeSpectrum.comap (M.f : B →+* M.C) (center K M.R r) = q := by
      rw [← center_baseMap, hrf, hv]
    have hcg : PrimeSpectrum.comap (M.g : B →+* M.C) (center K M.R r) = q := by
      rw [← center_baseMap, hrg, hv]
    have hc := helem μ hμf hμg _ hcf hcg
    obtain ⟨v', hv'⟩ := exists_baseMap_eq K M.R Q μ r ⟨q, hc.symm⟩
    exact ⟨v', (hδpt v').trans hv'⟩
  -- a compact neighbourhood of `v`
  obtain ⟨m, s, hs⟩ := exists_chart K Q v
  let N := range (chart K Q (m + 1))
  have hNv : N ∈ 𝓝 v := range_chart_mem_nhds K Q ⟨s, hs⟩
  have hNc : IsCompact N := isCompact_range (continuous_chart K Q (m + 1))
  let S := {r : Space K M.R | baseMap K Q M.R M.f r ∈ N ∧ baseMap K Q M.R M.g r ∈ N}
  have hSc : IsCompact S := isCompact_relationPreimage Q M hprod hNc
  let Fc := S ∩ Δᶜ
  have hFc : IsCompact Fc := hSc.inter_right hΔ.isClosed_compl
  let ρ : Space K M.R → Space K Q × Space K Q :=
    fun r => (baseMap K Q M.R M.f r, baseMap K Q M.R M.g r)
  have hρ : Continuous ρ :=
    (baseMap K Q M.R M.f).continuous.prodMk (baseMap K Q M.R M.g).continuous
  have hρF : IsClosed (ρ '' Fc) := (hFc.image hρ).isClosed
  have hvv : (v, v) ∉ ρ '' Fc := by
    rintro ⟨r, ⟨-, hrΔ⟩, hr⟩
    exact hrΔ (hdiag r (congrArg Prod.fst hr) (congrArg Prod.snd hr))
  obtain ⟨U₁, U₂, hU₁, hU₂, hvU₁, hvU₂, hU⟩ :=
    isOpen_prod_iff.mp hρF.isOpen_compl v v hvv
  refine ⟨U₁ ∩ U₂ ∩ interior N, (hU₁.inter hU₂).inter isOpen_interior,
    ⟨⟨hvU₁, hvU₂⟩, mem_interior_iff_mem_nhds.mpr hNv⟩, ?_⟩
  intro T α β hα hβ ⟨t, htf, htg⟩
  have hpt : ∀ x, localizedSpaceFunctor.map t x ∈ Δ := by
    intro x
    by_contra hx
    have hf : baseMap K Q M.R M.f (localizedSpaceFunctor.map t x) =
        localizedSpaceFunctor.map α x := by
      rw [← htf, Functor.map_comp, TopCat.comp_app, localizedSpaceFunctor_map_localizedHom]
      rfl
    have hg : baseMap K Q M.R M.g (localizedSpaceFunctor.map t x) =
        localizedSpaceFunctor.map β x := by
      rw [← htg, Functor.map_comp, TopCat.comp_app, localizedSpaceFunctor_map_localizedHom]
      rfl
    have hmem : ρ (localizedSpaceFunctor.map t x) ∈ ρ '' Fc :=
      ⟨_, ⟨⟨hf ▸ interior_subset (hα x).2, hg ▸ interior_subset (hβ x).2⟩, hx⟩, rfl⟩
    have hU' : ρ (localizedSpaceFunctor.map t x) ∈ U₁ ×ˢ U₂ := by
      change (baseMap K Q M.R M.f _, baseMap K Q M.R M.g _) ∈ U₁ ×ˢ U₂
      rw [hf, hg]
      exact ⟨(hα x).1.1, (hβ x).1.2⟩
    exact hU hU' hmem
  obtain ⟨σ, hσ⟩ := openImmersion.exists_lift hδ t hpt
  rw [← htf, ← htg, ← hσ, Category.assoc, Category.assoc, hδf, hδg]


end TrivialOpen

end Langlands.Analytic.SpaceAnalytification.ChartQuotient
