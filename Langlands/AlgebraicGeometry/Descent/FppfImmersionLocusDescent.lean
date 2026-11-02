import Langlands.AlgebraicGeometry.Descent.FppfClosedLocusDescentProof
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # fppf descent of loci cut out by immersions

The set of points under the local immersions is locally closed, because flat morphisms locally
of finite presentation are open. On the open subscheme where it is closed, the local immersions
are closed immersions, and `fppfClosedLocusDescent` applies.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

namespace Langlands.AlgebraicGeometry.FppfClosedLocusDescent

/-- Let `ι₁` and `ι₂` cut out the pullbacks of the same sieve `E` along `f₁` and `f₂`. If
`f₁ y₁ = f₂ y₂` and `y₁` lies in the image of `ι₁`, then `y₂` lies in the image of `ι₂`. -/
lemma mem_range_of_mem_range {Y Y₁ Y₂ Z₁ Z₂ : Scheme.{u}} (E : Sieve Y) (f₁ : Y₁ ⟶ Y)
    (f₂ : Y₂ ⟶ Y) (ι₁ : Z₁ ⟶ Y₁) (ι₂ : Z₂ ⟶ Y₂)
    (h₁ : ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ Y₁), (∃ k : T ⟶ Z₁, k ≫ ι₁ = g) ↔ E (g ≫ f₁))
    (h₂ : ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ Y₂), (∃ k : T ⟶ Z₂, k ≫ ι₂ = g) ↔ E (g ≫ f₂))
    {y₁ : Y₁} {y₂ : Y₂} (hy : f₁ y₁ = f₂ y₂) (hy₁ : y₁ ∈ Set.range ι₁) :
    y₂ ∈ Set.range ι₂ := by
  obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback y₁ y₂ hy
  have hw : w ∈ Set.range (pullback.snd ι₁ (pullback.fst f₁ f₂)) := by
    rw [Scheme.Pullback.range_snd, Set.mem_preimage, hw₁]
    exact hy₁
  obtain ⟨v, rfl⟩ := hw
  have hE : E ((pullback.snd ι₁ (pullback.fst f₁ f₂) ≫ pullback.snd f₁ f₂) ≫ f₂) := by
    have h1 := pullback.condition (f := ι₁) (g := pullback.fst f₁ f₂)
    have h2 := pullback.condition (f := f₁) (g := f₂)
    rw [Category.assoc, ← h2, ← Category.assoc, ← h1, Category.assoc]
    exact (h₁ _).mp ⟨_, rfl⟩
  obtain ⟨k, hk⟩ := (h₂ _).mpr hE
  refine ⟨k v, ?_⟩
  rw [← hw₂, ← Scheme.Hom.comp_apply, hk, Scheme.Hom.comp_apply]

end Langlands.AlgebraicGeometry.FppfClosedLocusDescent

namespace Langlands.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
open FppfClosedLocusDescent in
/-- fppf descent of loci cut out by immersions: let `E` be an fppf-closed sieve on `Y` and `R`
an fppf covering sieve such that on every member of `R` the pullback of `E` is cut out by an
immersion. Then `E` is cut out by an immersion into `Y`. -/
theorem fppfImmersionLocusDescent (Y : Scheme.{u}) (E : Sieve Y)
    (hE : Scheme.fppfTopology.IsClosed E) (R : Sieve Y) (hR : R ∈ Scheme.fppfTopology Y)
    (h : ∀ ⦃Y' : Scheme.{u}⦄ (f : Y' ⟶ Y), R f →
      ∃ (Z : Scheme.{u}) (ι : Z ⟶ Y'), IsImmersion ι ∧
        ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ Y'), (∃ k : T ⟶ Z, k ≫ ι = g) ↔ E (g ≫ f)) :
    ∃ (Z : Scheme.{u}) (ι : Z ⟶ Y), IsImmersion ι ∧
      ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ Y), (∃ k : T ⟶ Z, k ≫ ι = g) ↔ E g := by
  choose Z ι hι hfac using h
  -- The points of `Y` under the local representatives.
  let S : Set Y :=
    {y | ∃ (Y' : Scheme.{u}) (f : Y' ⟶ Y) (hf : R f) (z : Z f hf), f (ι f hf z) = y}
  have hpre {Y' : Scheme.{u}} (f : Y' ⟶ Y) (hf : R f) : f ⁻¹' S = Set.range (ι f hf) := by
    ext y
    constructor
    · rintro ⟨Y'', f', hf', z, hz⟩
      exact mem_range_of_mem_range E f' f (ι f' hf') (ι f hf) (hfac f' hf') (hfac f hf) hz
        ⟨z, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨Y', f, hf, z, rfl⟩
  have : (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}).IsMultiplicative :=
    { id_mem := fun _ ↦ ⟨inferInstance, inferInstance⟩
      comp_mem := fun f g hf hg ↦ by
        have := hf.1
        have := hf.2
        have := hg.1
        have := hg.2
        exact ⟨inferInstance, inferInstance⟩ }
  obtain ⟨𝒰, hle⟩ := (Scheme.mem_grothendieckTopology_iff
    (P := (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}))).mp hR
  have hR𝒰 (i : 𝒰.I₀) : R (𝒰.f i) := hle _ _ (Presieve.ofArrows.mk i)
  have hopen (i : 𝒰.I₀) : IsOpenMap (𝒰.f i) := by
    have := (𝒰.map_prop i).1
    have := (𝒰.map_prop i).2
    exact (𝒰.f i).isOpenMap
  -- `S` is locally closed: its coborder is open.
  have hW : IsOpen (coborder S) := by
    have hcov : coborder S = ⋃ i, 𝒰.f i '' (𝒰.f i ⁻¹' coborder S) := by
      ext y
      constructor
      · intro hy
        obtain ⟨i, y', rfl⟩ := 𝒰.exists_eq y
        exact Set.mem_iUnion.mpr ⟨i, y', hy, rfl⟩
      · intro hy
        obtain ⟨i, y', hy', rfl⟩ := Set.mem_iUnion.mp hy
        exact hy'
    rw [hcov]
    refine isOpen_iUnion fun i ↦ hopen i _ ?_
    rw [← coborder_preimage (hopen i) (𝒰.f i).continuous, hpre _ (hR𝒰 i)]
    have := hι _ (hR𝒰 i)
    exact (ι _ (hR𝒰 i)).isLocallyClosed_range.isOpen_coborder
  let W : Y.Opens := ⟨coborder S, hW⟩
  -- `S` is closed in `W`.
  have hclosed : IsClosed (W.ι ⁻¹' S) := by
    have heq : W.ι ⁻¹' S = W.ι ⁻¹' closure S := by
      ext x
      refine ⟨fun hx ↦ subset_closure hx, fun hx ↦ ?_⟩
      have hxW : W.ι x ∈ coborder S := by
        have : W.ι x ∈ Set.range W.ι := ⟨x, rfl⟩
        rwa [Scheme.Opens.range_ι] at this
      exact (mem_coborder_iff_imp (s := S)).mp hxW hx
    rw [heq]
    exact isClosed_closure.preimage W.ι.continuous
  have hloc : ∀ ⦃V : Scheme.{u}⦄ (f : V ⟶ W), (R.pullback W.ι) f →
      ∃ (Z' : Scheme.{u}) (ι' : Z' ⟶ V), IsClosedImmersion ι' ∧
        ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ V), (∃ k : T ⟶ Z', k ≫ ι' = g) ↔
          (E.pullback W.ι) (g ≫ f) := by
    intro V f hf
    have := hι _ hf
    refine ⟨Z (f ≫ W.ι) hf, ι _ hf, .of_isPreimmersion _ ?_, fun T g ↦ ?_⟩
    · rw [← hpre _ hf]
      have hcomp : (f ≫ W.ι) ⁻¹' S = f ⁻¹' (W.ι ⁻¹' S) := by
        ext x
        simp only [Set.mem_preimage, Scheme.Hom.comp_apply]
      rw [hcomp]
      exact hclosed.preimage f.continuous
    · rw [hfac _ hf g, Sieve.pullback_apply, Category.assoc]
  obtain ⟨Z₀, ι₀, hι₀, hrep⟩ := fppfClosedLocusDescent W.toScheme (E.pullback W.ι)
    (Scheme.fppfTopology.isClosed_pullback _ _ hE)
    ⟨R.pullback W.ι, Scheme.fppfTopology.pullback_stable _ hR, hloc⟩
  have := hι₀
  refine ⟨Z₀, ι₀ ≫ W.ι, inferInstance, fun T g ↦ ⟨?_, fun hg ↦ ?_⟩⟩
  · rintro ⟨k, rfl⟩
    have hk := (hrep (k ≫ ι₀)).mp ⟨k, rfl⟩
    rw [Sieve.pullback_apply, Category.assoc] at hk
    exact hk
  · have hrange : Set.range g ⊆ Set.range W.ι := by
      rintro _ ⟨t, rfl⟩
      rw [Scheme.Opens.range_ι]
      obtain ⟨i, y, hy⟩ := 𝒰.exists_eq (g t)
      obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback t y hy.symm
      obtain ⟨k, hk⟩ := (hfac _ (hR𝒰 i) (pullback.snd g (𝒰.f i))).mpr (by
        rw [← pullback.condition]
        exact E.downward_closed hg _)
      refine subset_coborder ⟨_, 𝒰.f i, hR𝒰 i, k w, ?_⟩
      rw [← hy, ← hw₂, ← hk, Scheme.Hom.comp_apply]
    obtain ⟨k, hk⟩ := (hrep (IsOpenImmersion.lift W.ι g hrange)).mpr (by
      rw [Sieve.pullback_apply, IsOpenImmersion.lift_fac]
      exact hg)
    exact ⟨k, by rw [← Category.assoc, hk, IsOpenImmersion.lift_fac]⟩

end Langlands.AlgebraicGeometry
