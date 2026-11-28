import Langlands.AlgebraicGeometry.ClosedEqualizerFamily
import Langlands.AlgebraicGeometry.DenseGroupMultiplication
import Langlands.GroupScheme.FiniteEtaleImage
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Extension of a compatible map on a fibrewise dense group chart -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.AlgebraicGeometry.DenseGroupMultiplication

open Langlands.GroupScheme.FiniteEtaleImage (liftOver liftOver_fac)

variable {S : Scheme.{u}}

private theorem smooth_of_open_factor {X Y Z : Scheme.{u}} (i : Y ⟶ Z) [IsOpenImmersion i]
    (g : X ⟶ Y) (h : Smooth (g ≫ i)) : Smooth g :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Smooth)
    (IsPullback.of_horiz_isIso_mono
      (show CommSq (𝟙 X) g (g ≫ i) i from ⟨by simp⟩)) h

private theorem ext_of_smooth_dense_image {W U T : Over S} (z : W ⟶ U)
    [Smooth z.left] [Smooth U.hom] [IsSeparated T.hom]
    (hz : FibreGenerizationDense U.hom (Set.range z.left)) {g h : U ⟶ T}
    (he : z ≫ g = z ≫ h) : g = h := by
  let V : U.left.Opens := ⟨Set.range z.left, z.left.isOpenMap.isOpen_range⟩
  let i : Over.mk (V.ι ≫ U.hom) ⟶ U := Over.homMk V.ι rfl
  have : IsOpenImmersion i.left := inferInstanceAs (IsOpenImmersion V.ι)
  have hi : Set.range i.left = Set.range z.left := Scheme.Opens.range_ι V
  let l := liftOver i z hi.ge
  have hl : l ≫ i = z := liftOver_fac _ _ _
  have hl' : l.left ≫ i.left = z.left := congrArg Over.Hom.left hl
  have : Surjective l.left := by
    refine ⟨fun v => ?_⟩
    have hv : i.left v ∈ Set.range z.left := hi ▸ Set.mem_range_self v
    obtain ⟨w, hw⟩ := hv
    exact ⟨w, i.left.isOpenEmbedding.injective (by rwa [← Scheme.Hom.comp_apply, hl'])⟩
  have : Smooth l.left := smooth_of_open_factor i.left l.left (hl' ▸ ‹Smooth z.left›)
  have : Epi l := Over.epi_of_epi_left l
  have hDense : FibreGenerizationDense U.hom i.left.opensRange := by
    change FibreGenerizationDense U.hom (Set.range i.left)
    rwa [hi]
  have : IsSchemeTheoreticallyDominant i.left := hDense.schematicallyDominant U.hom i.left
  apply overHom_ext_of_schematicallyDominant i
  apply (cancel_epi l).mp
  simpa only [← Category.assoc, hl] using he

/-- A map of a dense group chart extends if it respects multiplication on a fibrewise dense
open of pairs, where the products are represented by points of the same chart. -/
theorem exists_hom_of_compatible_products {G H : Langlands.GroupScheme S} {U W : Over S}
    [Smooth G.X.hom] [IsSeparated H.X.hom]
    (a : U ⟶ G.X) (b : U ⟶ H.X) [IsOpenImmersion a.left]
    (ha : FibreGenerizationDense G.X.hom a.left.opensRange)
    (j : W ⟶ U ⊗ U) [IsOpenImmersion j.left]
    (hj : FibreGenerizationDense (U ⊗ U).hom j.left.opensRange)
    (z : W ⟶ U) (hG : j ≫ openProduct G a = z ≫ a)
    (hH : j ≫ openProduct H b = z ≫ b) :
    ∃ c : G ⟶ H, a ≫ c.hom.hom = b := by
  let P := U ⊗ U
  let p := openProduct G a
  let q := openProduct H b
  have : Smooth U.hom := by rw [← Over.w a]; infer_instance
  have : Smooth P.hom := by change Smooth ((U ⊗ U).hom); rw [Over.tensorObj_hom]; infer_instance
  have : IsOpenImmersion (a ⊗ₘ a).left := isOpenImmersion_tensorHom a a
  have : Smooth μ[G.X].left := smooth_mul G
  have : Smooth p.left := inferInstanceAs (Smooth ((a ⊗ₘ a).left ≫ μ[G.X].left))
  have : Surjective p.left := surjective_openProduct G a ha
  have : Mono a := Over.mono_of_mono_left a
  let K : Over S := Over.mk (pullback.fst p.left p.left ≫ P.hom)
  let k₁ : K ⟶ P := Over.homMk (pullback.fst p.left p.left) rfl
  let k₂ : K ⟶ P := Over.homMk (pullback.snd p.left p.left) (by
    change pullback.snd p.left p.left ≫ P.hom = pullback.fst p.left p.left ≫ P.hom
    rw [← Over.w p, ← pullback.condition_assoc])
  have hk : k₁ ≫ p = k₂ ≫ p := Over.OverMorphism.ext pullback.condition
  have : Smooth k₁.left := inferInstanceAs (Smooth (pullback.fst p.left p.left))
  have : Smooth k₂.left := inferInstanceAs (Smooth (pullback.snd p.left p.left))
  have : Smooth K.hom := by rw [← Over.w k₁]; infer_instance
  let V := (k₁.left ⁻¹ᵁ j.left.opensRange) ⊓ (k₂.left ⁻¹ᵁ j.left.opensRange)
  let i : Over.mk (V.ι ≫ K.hom) ⟶ K := Over.homMk V.ι rfl
  have : IsOpenImmersion i.left := inferInstanceAs (IsOpenImmersion V.ι)
  have hV : FibreGenerizationDense K.hom V :=
    (Over.w k₁ ▸ hj.preimage_flat k₁.left).inf (Over.w k₂ ▸ hj.preimage_flat k₂.left)
  have hi : FibreGenerizationDense K.hom i.left.opensRange := by
    change FibreGenerizationDense K.hom (Set.range V.ι)
    simpa only [Scheme.Opens.range_ι] using hV
  have : IsSchemeTheoreticallyDominant i.left := hi.schematicallyDominant K.hom i.left
  have hi₁ : Set.range (i ≫ k₁).left ⊆ Set.range j.left := by
    rintro _ ⟨x, rfl⟩
    exact x.2.1
  have hi₂ : Set.range (i ≫ k₂).left ⊆ Set.range j.left := by
    rintro _ ⟨x, rfl⟩
    exact x.2.2
  let l₁ := liftOver j (i ≫ k₁) hi₁
  let l₂ := liftOver j (i ≫ k₂) hi₂
  have hl₁ : l₁ ≫ j = i ≫ k₁ := liftOver_fac _ _ _
  have hl₂ : l₂ ≫ j = i ≫ k₂ := liftOver_fac _ _ _
  have hz : l₁ ≫ z = l₂ ≫ z := by
    apply (cancel_mono a).mp
    simpa only [Category.assoc, ← hG, ← reassoc_of% hl₁, ← reassoc_of% hl₂] using
      congrArg (i ≫ ·) hk
  have hco : k₁ ≫ q = k₂ ≫ q := by
    apply overHom_ext_of_schematicallyDominant i
    calc
      i ≫ k₁ ≫ q = l₁ ≫ z ≫ b := by rw [← reassoc_of% hl₁, hH]
      _ = l₂ ≫ z ≫ b := (reassoc_of% hz) b
      _ = i ≫ k₂ ≫ q := by rw [← reassoc_of% hl₂, hH]
  have hco' : pullback.fst p.left p.left ≫ q.left = pullback.snd p.left p.left ≫ q.left :=
    congrArg Over.Hom.left hco
  have hdesc {T : Scheme.{u}} (f g : T ⟶ P.left) (h : f ≫ p.left = g ≫ p.left) :
      f ≫ q.left = g ≫ q.left := by
    simpa only [pullback.lift_fst_assoc, pullback.lift_snd_assoc] using
      congrArg (pullback.lift f g h ≫ ·) hco'
  let c₀ := EffectiveEpi.desc p.left q.left hdesc
  have hc₀ : p.left ≫ c₀ = q.left := EffectiveEpi.fac _ _ hdesc
  let c : G.X ⟶ H.X := Over.homMk c₀ (by
    apply (cancel_epi p.left).mp
    rw [← Category.assoc, hc₀, Over.w q, Over.w p])
  have hc : p ≫ c = q := Over.OverMorphism.ext hc₀
  have hzc : z ≫ a ≫ c = z ≫ b := by
    have hGp : j ≫ p = z ≫ a := hG
    rw [← Category.assoc, ← hGp, Category.assoc, hc]
    exact hH
  have hzsm : Smooth z.left := by
    apply smooth_of_open_factor a.left
    rw [show z.left ≫ a.left = j.left ≫ p.left from congrArg Over.Hom.left hG.symm]
    infer_instance
  have hzDense : FibreGenerizationDense U.hom (Set.range z.left) := by
    intro x
    obtain ⟨y, hy⟩ := p.left.surjective (a.left x)
    obtain ⟨_, ⟨w, rfl⟩, hw, hwy⟩ := hj y
    have hprod : p.left (j.left w) = a.left (z.left w) :=
      congrArg (fun v : W ⟶ G.X => v.left w) hG
    refine ⟨z.left w, ⟨w, rfl⟩, ?_, ?_⟩
    · have hp : U.hom (z.left w) = P.hom (j.left w) := by
        exact congrArg (fun v : W.left ⟶ S => v w) ((Over.w z).trans (Over.w j).symm)
      have hpy : P.hom y = U.hom x := by
        rw [← Over.w p, ← Over.w a, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hy]
      exact hp.trans (hw.trans hpy)
    · apply a.left.isOpenEmbedding.isEmbedding.specializes_iff.mp
      rw [← hprod, ← hy]
      exact hwy.map p.left.continuous
  have hac : a ≫ c = b := ext_of_smooth_dense_image z hzDense hzc
  have hprodDense := fibreDense_tensorHom a a ha ha
  have : Smooth (G.X ⊗ G.X).hom := by rw [Over.tensorObj_hom]; infer_instance
  have : IsSchemeTheoreticallyDominant (a ⊗ₘ a).left :=
    hprodDense.schematicallyDominant (G.X ⊗ G.X).hom (a ⊗ₘ a).left
  have hmul : μ[G.X] ≫ c = (c ⊗ₘ c) ≫ μ[H.X] := by
    apply overHom_ext_of_schematicallyDominant (a ⊗ₘ a)
    simpa only [p, q, openProduct, Category.assoc, tensorHom_comp_tensorHom_assoc, hac] using hc
  have hpreserves {T : Over S} (x y : T ⟶ G.X) :
      (x * y) ≫ c = (x ≫ c) * (y ≫ c) := by
    rw [Hom.mul_def, Category.assoc, hmul, ← Category.assoc, Hom.mul_def]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have hunit : η[G.X] ≫ c = η[H.X] := by
    let u : 𝟙_ (Over S) ⟶ G.X := 1
    have hu := hpreserves u u
    rw [show u * u = u from one_mul _] at hu
    have he : u ≫ c = 1 := mul_left_cancel (hu.symm.trans (mul_one _).symm)
    simpa only [u, Hom.one_def, toUnit_unit, Category.assoc, Category.id_comp] using he
  exact ⟨Grp.homMk'' c hunit hmul, hac⟩

end Langlands.AlgebraicGeometry.DenseGroupMultiplication
