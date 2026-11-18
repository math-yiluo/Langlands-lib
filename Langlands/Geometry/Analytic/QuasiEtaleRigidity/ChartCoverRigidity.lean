import Langlands.Geometry.Analytic.QuasiEtaleRigidity.RigidityTransport
import Langlands.Geometry.Analytic.QuasiEtaleRigidity.RefinementGluing
import Langlands.Geometry.Analytic.InvariantAnalyticDomains

/-! # Rigidity from rigidity on the charts of a finite chart cover -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Helpers

variable {T A B : SaturatedAtlasPresentation.{u, v, w} K}

theorem pullback_congr {f g : T ⟶ A} (h : f = g) (i : T.presentation.atlas.Index)
    (j : A.presentation.atlas.Index)
    (hf : f.baseMap '' Set.range (T.presentation.atlas.chart i) ⊆
      Set.range (A.presentation.atlas.chart j))
    (hg : g.baseMap '' Set.range (T.presentation.atlas.chart i) ⊆
      Set.range (A.presentation.atlas.chart j)) :
    f.pullback i j hf = g.pullback i j hg := by
  subst h
  rfl

theorem localizedSpaceFunctor_map_apply (f : T ⟶ A) (y : T.presentation.space) :
    localizedSpaceFunctor.map (localizationFunctor.map f) y = f.baseMap y := by
  rw [localizedSpaceFunctor_map]
  rfl

theorem mem_of_baseMap_mem (f : T ⟶ A) (Z : Set A.presentation.space)
    (y : T.presentation.space) (h : f.baseMap y ∈ Z) :
    localizedSpaceFunctor.map (localizationFunctor.map f) y ∈ Z :=
  (Iff.of_eq (congrArg (fun z => z ∈ Z) (localizedSpaceFunctor_map_apply f y))).mpr h

/-- **Test relations of domain lifts.** Strong maps into an analytic domain `D` which are near
for the ambient triple of a test triple of `D` have near lifts through `D`. -/
theorem isNear_lift_of_strongNear (D : A.AnalyticDomain) (τ : TestTriple (A.domain D))
    (a b : T ⟶ A) (ξa ξb : localizationFunctor.obj T ⟶ localizationFunctor.obj (A.domain D))
    (ha : ξa ≫ A.localizedDomainInclusion D = localizationFunctor.map a)
    (hb : ξb ≫ A.localizedDomainInclusion D = localizationFunctor.map b)
    (h : StrongNear τ.ambient a b) :
    IsNear (X := localizationFunctor.obj (A.domain D)) (Y := localizationFunctor.obj T) τ
      ξa ξb := by
  obtain ⟨T', t, ht, a', b', hta, htb⟩ := exists_commonStrongNumerators ξa ξb
  have hca : a' ≫ A.domainInclusion D = t ≫ a := by
    apply localizationFunctor_map_injective
    change localizationFunctor.map (a' ≫ A.domainInclusion D) = localizationFunctor.map (t ≫ a)
    rw [Functor.map_comp, Functor.map_comp, ← hta, Category.assoc]
    change localizationFunctor.map t ≫ (ξa ≫ A.localizedDomainInclusion D) = _
    rw [ha]
  have hcb : b' ≫ A.domainInclusion D = t ≫ b := by
    apply localizationFunctor_map_injective
    change localizationFunctor.map (b' ≫ A.domainInclusion D) = localizationFunctor.map (t ≫ b)
    rw [Functor.map_comp, Functor.map_comp, ← htb, Category.assoc]
    change localizationFunctor.map t ≫ (ξb ≫ A.localizedDomainInclusion D) = _
    rw [hb]
  have hn : StrongNear τ a' b' := by
    rw [← strongNear_comp_domainInclusion_iff, hca, hcb]
    exact h.precomp t
  exact (isNear_iff_numerators (X := localizationFunctor.obj (A.domain D))
    (Y := localizationFunctor.obj T) τ ξa ξb).2 ⟨T', t, ht, a', b', hta, htb, hn⟩

end Helpers

variable {A B : SaturatedAtlasPresentation.{u, v, w} K}

/-- The test triple with the domain of a chart, the function `0` and bound `1`; it controls
preimages of the chart. -/
def chartTestTriple (A : SaturatedAtlasPresentation.{u, v, w} K)
    (i : A.presentation.atlas.Index) : TestTriple A :=
  ⟨i, 0, 1, one_pos⟩

/-- On a chart of the source mapped by `x₀` into a chart `i`, the rigidity of the restriction to
`i` makes the pullbacks of `x₁` and `x₂` equal. -/
theorem pullback_eq_of_isRigidOn_chart {S : SaturatedAtlasPresentation.{u, v, w} K}
    (g : A ⟶ B) (i : A.presentation.atlas.Index)
    (E : Finset (TestTriple (A.domain (A.chartDomain i))))
    (hR : ∀ (V : LocalizedCategory.{u, v, w} (K := K))
      (ψ ψ₁ ψ₂ : V ⟶ localizationFunctor.obj (A.domain (A.chartDomain i))),
      ψ₁ ≫ (A.localizedDomainInclusion (A.chartDomain i) ≫ localizationFunctor.map g) =
          ψ₂ ≫ (A.localizedDomainInclusion (A.chartDomain i) ≫ localizationFunctor.map g) →
        (∀ τ ∈ E, IsNear τ ψ ψ₁ ∧ IsNear τ ψ ψ₂) → ψ₁ = ψ₂)
    (x₀ x₁ x₂ : S ⟶ A) (hg : x₁ ≫ g = x₂ ≫ g)
    (hn : ∀ τ ∈ E, StrongNear τ.ambient x₀ x₁ ∧ StrongNear τ.ambient x₀ x₂)
    (P : S.presentation.atlas.Index)
    (h₀ : x₀.baseMap '' Set.range (S.presentation.atlas.chart P) ⊆
      Set.range (A.presentation.atlas.chart i))
    (h₁ : x₁.baseMap '' Set.range (S.presentation.atlas.chart P) ⊆
      Set.range (A.presentation.atlas.chart i))
    (h₂ : x₂.baseMap '' Set.range (S.presentation.atlas.chart P) ⊆
      Set.range (A.presentation.atlas.chart i)) :
    x₁.pullback P i h₁ = x₂.pullback P i h₂ := by
  let ι := S.domainInclusion (S.chartDomain P)
  have himg : ∀ (x : S ⟶ A), x.baseMap '' Set.range (S.presentation.atlas.chart P) ⊆
      Set.range (A.presentation.atlas.chart i) →
      ∀ y, localizedSpaceFunctor.map (localizationFunctor.map (ι ≫ x)) y ∈
        (A.chartDomain i).carrier := fun x hx y =>
    mem_of_baseMap_mem (ι ≫ x) _ y (hx ⟨y.val, y.property, rfl⟩)
  obtain ⟨ξ₀, hξ₀⟩ := exists_localizedDomainLift (S := A) (A.chartDomain i) _ (himg x₀ h₀)
  obtain ⟨ξ₁, hξ₁⟩ := exists_localizedDomainLift (S := A) (A.chartDomain i) _ (himg x₁ h₁)
  obtain ⟨ξ₂, hξ₂⟩ := exists_localizedDomainLift (S := A) (A.chartDomain i) _ (himg x₂ h₂)
  have hξeq : ξ₁ = ξ₂ := by
    refine hR _ ξ₀ ξ₁ ξ₂ ?_ fun τ hτ => ⟨?_, ?_⟩
    · rw [← Category.assoc, hξ₁, ← Category.assoc, hξ₂, ← Functor.map_comp, ← Functor.map_comp,
        Category.assoc, hg, Category.assoc]
    · exact isNear_lift_of_strongNear (A.chartDomain i) τ _ _ ξ₀ ξ₁ hξ₀ hξ₁
        ((hn τ hτ).1.precomp ι)
    · exact isNear_lift_of_strongNear (A.chartDomain i) τ _ _ ξ₀ ξ₂ hξ₀ hξ₂
        ((hn τ hτ).2.precomp ι)
  have hιx : ι ≫ x₁ = ι ≫ x₂ := by
    apply localizationFunctor_map_injective
    change localizationFunctor.map (ι ≫ x₁) = localizationFunctor.map (ι ≫ x₂)
    rw [← hξ₁, ← hξ₂, hξeq]
  let P' : (S.domain (S.chartDomain P)).presentation.atlas.Index :=
    ⟨P, fun _ h => h⟩
  have h₁' : (ι ≫ x₁).baseMap ''
      Set.range ((S.domain (S.chartDomain P)).presentation.atlas.chart P') ⊆
        Set.range (A.presentation.atlas.chart i) := by
    rintro _ ⟨y, ⟨q, rfl⟩, rfl⟩
    exact h₁ ⟨_, ⟨q, rfl⟩, rfl⟩
  have h₂' : (ι ≫ x₂).baseMap ''
      Set.range ((S.domain (S.chartDomain P)).presentation.atlas.chart P') ⊆
        Set.range (A.presentation.atlas.chart i) := by
    rintro _ ⟨y, ⟨q, rfl⟩, rfl⟩
    exact h₂ ⟨_, ⟨q, rfl⟩, rfl⟩
  rw [← domainInclusion_comp_pullback x₁ (S.chartDomain P) P' i h₁ h₁',
    ← domainInclusion_comp_pullback x₂ (S.chartDomain P) P' i h₂ h₂']
  exact pullback_congr hιx P' i h₁' h₂'

section Cover

variable {C S : SaturatedAtlasPresentation.{u, v, w} K}

theorem comp_eq_of_numerators (g : A ⟶ B)
    (ψ₁ ψ₂ : localizationFunctor.obj C ⟶ localizationFunctor.obj A) (σ : S ⟶ C) (x₁ x₂ : S ⟶ A)
    (h1 : localizationFunctor.map σ ≫ ψ₁ = localizationFunctor.map x₁)
    (h2 : localizationFunctor.map σ ≫ ψ₂ = localizationFunctor.map x₂)
    (heq : ψ₁ ≫ localizationFunctor.map g = ψ₂ ≫ localizationFunctor.map g) :
    x₁ ≫ g = x₂ ≫ g := by
  apply localizationFunctor_map_injective
  change localizationFunctor.map (x₁ ≫ g) = localizationFunctor.map (x₂ ≫ g)
  rw [Functor.map_comp, Functor.map_comp, ← h1, ← h2, Category.assoc, Category.assoc, heq]

theorem eq_of_numerators (ψ₁ ψ₂ : localizationFunctor.obj C ⟶ localizationFunctor.obj A)
    (σ : S ⟶ C) (hσ : σ.IsQuasiIso) (x₁ x₂ : S ⟶ A)
    (h1 : localizationFunctor.map σ ≫ ψ₁ = localizationFunctor.map x₁)
    (h2 : localizationFunctor.map σ ≫ ψ₂ = localizationFunctor.map x₂)
    (hx : localizationFunctor.map x₁ = localizationFunctor.map x₂) : ψ₁ = ψ₂ := by
  have : IsIso (localizationFunctor.map σ) :=
    Localization.inverts localizationFunctor (quasiIsomorphisms (K := K)) σ hσ
  exact (cancel_epi (localizationFunctor.map σ)).1 (h1.trans (hx.trans h2.symm))

/-- **Rigidity from a finite chart cover.** If the space of `A` is Hausdorff and finitely many
charts cover it, rigidity of the restrictions of `g` to these charts gives rigidity of `g`. -/
theorem isRigidOn_of_chart_cover [T2Space A.presentation.space] (g : A ⟶ B)
    (s : Finset A.presentation.atlas.Index)
    (hs : ∀ y : A.presentation.space, ∃ i ∈ s, y ∈ Set.range (A.presentation.atlas.chart i))
    (hR : ∀ i ∈ s, IsRigidOn
      (A.localizedDomainInclusion (A.chartDomain i) ≫ localizationFunctor.map g) Set.univ) :
    IsRigidOn (U := localizationFunctor.obj A) (X := localizationFunctor.obj B)
      (localizationFunctor.map g) Set.univ := by
  classical
  choose E hEL hE using hR
  let Etot : Finset (TestTriple A) :=
    s.attach.biUnion (fun i => (E i.1 i.2).image fun τ =>
      TestTriple.ambient (B := A) (D := A.chartDomain i.1) τ) ∪ s.image (chartTestTriple A)
  refine ⟨Etot, fun _ _ => Set.subset_univ _, fun V ψ ψ₁ ψ₂ _ _ _ heq hnear => ?_⟩
  obtain ⟨S, σ, hσ, x₀, x₁, x₂, h0, h1, h2, hn⟩ :=
    exists_strongNear_numerators (X := localizationFunctor.obj A) Etot ψ ψ₁ ψ₂
      (fun τ hτ => (hnear τ hτ).1) (fun τ hτ => (hnear τ hτ).2)
  have : T2Space (presentationOf (localizationFunctor.obj A)).presentation.space :=
    ‹T2Space A.presentation.space›
  have hg : x₁ ≫ g = x₂ ≫ g :=
    comp_eq_of_numerators (C := presentationOf V) g ψ₁ ψ₂ σ x₁ x₂ h1 h2 heq
  have hchart : ∀ c ∈ s, chartTestTriple A c ∈ Etot := fun c hc =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ hc)
  have hamb : ∀ c (hc : c ∈ s), ∀ τ ∈ E c hc, TestTriple.ambient (B := A)
      (D := A.chartDomain c) τ ∈ Etot := fun c hc τ hτ =>
    Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨⟨c, hc⟩, Finset.mem_attach _ _,
      Finset.mem_image_of_mem _ hτ⟩)
  have hx : localizationFunctor.map x₁ = localizationFunctor.map x₂ := by
    refine localizationFunctor_map_eq_of_local_eq x₀ x₁ x₂ Set.univ s
      (fun _ _ => Set.subset_univ _) (fun y _ => ?_) (fun _ => Set.mem_univ _)
      (fun c hc => (hn (chartTestTriple A c) (hchart c hc)).1.1)
      (fun c hc => (hn (chartTestTriple A c) (hchart c hc)).2.1) ?_
    · obtain ⟨i, hi, hyi⟩ := hs y
      exact Set.mem_iUnion₂.mpr ⟨i, hi, hyi⟩
    · intro P c hc h₁ h₂ hPc
      have h₀ : x₀.baseMap '' Set.range (S.presentation.atlas.chart P) ⊆
          Set.range (A.presentation.atlas.chart c) := by
        rintro _ ⟨z, hz, rfl⟩
        exact hPc hz
      exact pullback_eq_of_isRigidOn_chart g c (E c hc)
        (fun V ψ ψ₁ ψ₂ heq hn => hE c hc V ψ ψ₁ ψ₂ (Set.subset_univ _) (Set.subset_univ _)
          (Set.subset_univ _) heq hn)
        x₀ x₁ x₂ hg (fun τ hτ => hn _ (hamb c hc τ hτ)) P h₀ h₁ h₂
  exact eq_of_numerators (C := presentationOf V) ψ₁ ψ₂ σ hσ x₁ x₂ h1 h2 hx

end Cover

end Langlands.Analytic.SaturatedAtlasPresentation
