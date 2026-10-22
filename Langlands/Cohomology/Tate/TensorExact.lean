import Langlands.Cohomology.Tate.TensorNaturality

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory TensorProduct

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- A retract of a short exact sequence of modules is short exact. -/
lemma moduleShortExact_of_retract {S T : ShortComplex (ModuleCat.{u} R)}
    (i : S ⟶ T) (p : T ⟶ S) (hip : i ≫ p = 𝟙 S) (hT : T.ShortExact) :
    S.ShortExact := by
  have h₁ (x : S.X₁) : p.τ₁ (i.τ₁ x) = x :=
    ConcreteCategory.congr_hom (congrArg ShortComplex.Hom.τ₁ hip) x
  have h₂ (x : S.X₂) : p.τ₂ (i.τ₂ x) = x :=
    ConcreteCategory.congr_hom (congrArg ShortComplex.Hom.τ₂ hip) x
  have h₃ (x : S.X₃) : p.τ₃ (i.τ₃ x) = x :=
    ConcreteCategory.congr_hom (congrArg ShortComplex.Hom.τ₃ hip) x
  refine
    { exact := (ShortComplex.moduleCat_exact_iff S).mpr ?_
      mono_f := (ModuleCat.mono_iff_injective S.f).mpr ?_
      epi_g := (ModuleCat.epi_iff_surjective S.g).mpr ?_ }
  · intro x hx
    have hz : T.g (i.τ₂ x) = 0 := by
      exact (ConcreteCategory.congr_hom i.comm₂₃ x).trans
        ((congrArg (fun z : S.X₃ => i.τ₃ z) hx).trans (map_zero i.τ₃.hom))
    obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff T).mp hT.exact _ hz
    refine ⟨p.τ₁ y, ?_⟩
    exact (ConcreteCategory.congr_hom p.comm₁₂ y).trans
      ((congrArg (fun z : T.X₂ => p.τ₂ z) hy).trans (h₂ x))
  · intro x y h
    have ht : T.f (i.τ₁ x) = T.f (i.τ₁ y) := by
      exact (ConcreteCategory.congr_hom i.comm₁₂ x).trans
        ((congrArg (fun z : S.X₂ => i.τ₂ z) h).trans
          (ConcreteCategory.congr_hom i.comm₁₂ y).symm)
    exact (h₁ x).symm.trans
      ((congrArg (fun z : T.X₁ => p.τ₁ z) (hT.moduleCat_injective_f ht)).trans (h₁ y))
  · intro x
    obtain ⟨y, hy⟩ := hT.moduleCat_surjective_g (i.τ₃ x)
    refine ⟨p.τ₂ y, ?_⟩
    exact (ConcreteCategory.congr_hom p.comm₂₃ y).trans
      ((congrArg (fun z : T.X₃ => p.τ₃ z) hy).trans (h₃ x))

/-- Tensor a sequence of modules with a linear coefficient map. -/
def moduleTensorSequenceMap (S : ShortComplex (ModuleCat.{u} R))
    {B C : ModuleCat.{u} R} (f : B ⟶ C) :
    S.map (MonoidalCategory.tensorRight B) ⟶
      S.map (MonoidalCategory.tensorRight C) where
  τ₁ := 𝟙 S.X₁ ⊗ₘ f
  τ₂ := 𝟙 S.X₂ ⊗ₘ f
  τ₃ := 𝟙 S.X₃ ⊗ₘ f
  comm₁₂ := by
    change (𝟙 _ ⊗ₘ f) ≫ (S.f ⊗ₘ 𝟙 _) = (S.f ⊗ₘ 𝟙 _) ≫ (𝟙 _ ⊗ₘ f)
    simp only [MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  comm₂₃ := by
    change (𝟙 _ ⊗ₘ f) ≫ (S.g ⊗ₘ 𝟙 _) = (S.g ⊗ₘ 𝟙 _) ≫ (𝟙 _ ⊗ₘ f)
    simp only [MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]

lemma tensorRight_shortExact_of_retract (S : ShortComplex (ModuleCat.{u} R))
    {B C : ModuleCat.{u} R} (i : B ⟶ C) (p : C ⟶ B) (hip : i ≫ p = 𝟙 B)
    (hC : (S.map (MonoidalCategory.tensorRight C)).ShortExact) :
    (S.map (MonoidalCategory.tensorRight B)).ShortExact := by
  apply moduleShortExact_of_retract (moduleTensorSequenceMap S i) (moduleTensorSequenceMap S p)
    _ hC
  apply ShortComplex.hom_ext
  all_goals
    change (𝟙 _ ⊗ₘ i) ≫ (𝟙 _ ⊗ₘ p) = 𝟙 _
    simp only [MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp, hip]
    exact MonoidalCategory.id_tensorHom_id _ _

variable {G : Type u} [Group G] [Fintype G]

/-- Untwisted scalar coordinates for a tensor with a coinduced module. -/
def tensorCoinducedScalarCoordinates (A : ModuleCat.{u} R) (B : Rep.{u} R G) :
    (A ⊗[R] coinduced B) ≃ₗ[R] (G → A ⊗[R] B) := by
  classical
  exact (TensorProduct.congr (LinearEquiv.refl R A) (coinducedFunctions B).symm).trans
    (TensorProduct.piRight R R A (fun _ : G => B))

lemma tensorCoinducedScalarCoordinates_tmul (A : ModuleCat.{u} R) (B : Rep.{u} R G)
    (a : A) (b : coinduced B) (g : G) :
    tensorCoinducedScalarCoordinates A B (a ⊗ₜ[R] b) g = a ⊗ₜ[R] b.1 g := by
  classical
  rfl

lemma tensorCoinducedScalarCoordinates_naturality {A A' : ModuleCat.{u} R}
    (f : A ⟶ A') (B : Rep.{u} R G) (x : A ⊗[R] coinduced B) (g : G) :
    tensorCoinducedScalarCoordinates A' B ((f ⊗ₘ 𝟙 (ModuleCat.of R (coinduced B))) x) g =
      (f ⊗ₘ 𝟙 (ModuleCat.of R B)) (tensorCoinducedScalarCoordinates A B x g) := by
  let l : A ⊗[R] coinduced B →ₗ[R] A' ⊗[R] B :=
    (LinearMap.proj g).comp ((tensorCoinducedScalarCoordinates A' B).toLinearMap.comp
      (f ⊗ₘ 𝟙 (ModuleCat.of R (coinduced B))).hom)
  let r : A ⊗[R] coinduced B →ₗ[R] A' ⊗[R] B :=
    (f ⊗ₘ 𝟙 (ModuleCat.of R B)).hom.comp
      ((LinearMap.proj g).comp (tensorCoinducedScalarCoordinates A B).toLinearMap)
  have hlr : l = r := by
    apply TensorProduct.ext'
    intro a b
    change tensorCoinducedScalarCoordinates A' B (f.hom a ⊗ₜ[R] b) g =
      (f ⊗ₘ 𝟙 (ModuleCat.of R B)) (tensorCoinducedScalarCoordinates A B (a ⊗ₜ[R] b) g)
    rw [tensorCoinducedScalarCoordinates_tmul, tensorCoinducedScalarCoordinates_tmul]
    rfl
  exact LinearMap.congr_fun hlr x

lemma moduleTensorCoinduced_shortExact (S : ShortComplex (ModuleCat.{u} R))
    (B : Rep.{u} R G) (hB : (S.map (MonoidalCategory.tensorRight (ModuleCat.of R B))).ShortExact) :
    (S.map (MonoidalCategory.tensorRight (ModuleCat.of R (coinduced B)))).ShortExact := by
  classical
  let E := S.map (MonoidalCategory.tensorRight (ModuleCat.of R B))
  let F := S.map (MonoidalCategory.tensorRight (ModuleCat.of R (coinduced B)))
  let e₁ := tensorCoinducedScalarCoordinates S.X₁ B
  let e₂ := tensorCoinducedScalarCoordinates S.X₂ B
  let e₃ := tensorCoinducedScalarCoordinates S.X₃ B
  have hf (x : F.X₁) (g : G) : e₂ (F.f x) g = E.f (e₁ x g) :=
    tensorCoinducedScalarCoordinates_naturality S.f B x g
  have hg (x : F.X₂) (g : G) : e₃ (F.g x) g = E.g (e₂ x g) :=
    tensorCoinducedScalarCoordinates_naturality S.g B x g
  refine
    { exact := (ShortComplex.moduleCat_exact_iff F).mpr ?_
      mono_f := (ModuleCat.mono_iff_injective F.f).mpr ?_
      epi_g := (ModuleCat.epi_iff_surjective F.g).mpr ?_ }
  · intro x hx
    have hz (g : G) : E.g (e₂ x g) = 0 := by
      rw [← hg, hx, map_zero, Pi.zero_apply]
    choose y hy using fun g => (ShortComplex.moduleCat_exact_iff E).mp hB.exact _ (hz g)
    refine ⟨e₁.symm y, e₂.injective ?_⟩
    funext g
    rw [hf, e₁.apply_symm_apply]
    exact hy g
  · intro x y h
    apply e₁.injective
    funext g
    apply hB.moduleCat_injective_f
    rw [← hf, ← hf, h]
  · intro x
    choose y hy using fun g => hB.moduleCat_surjective_g (e₃ x g)
    refine ⟨e₂.symm y, e₃.injective ?_⟩
    funext g
    rw [hg, e₂.apply_symm_apply]
    exact hy g

/-- Tensor exactness is preserved on replacing a coefficient by its coinduced module. -/
lemma tensorCoinduced_shortExact (S : ShortComplex (Rep.{u} R G)) (B : Rep.{u} R G)
    (hB : (S.map (MonoidalCategory.tensorRight B)).ShortExact) :
    (S.map (MonoidalCategory.tensorRight (coinduced B))).ShortExact := by
  let U := forget₂ (Rep.{u} R G) (ModuleCat.{u} R)
  have h := moduleTensorCoinduced_shortExact (S.map U) B (hB.map_of_exact U)
  exact CategoryTheory.ShortExact.reflects_shortExact_of_faithful U h

/-- Tensor exactness is preserved by the positive scalar-split coefficient shift. -/
lemma tensorShiftUp_shortExact (S : ShortComplex (Rep.{u} R G)) (B : Rep.{u} R G)
    (hB : (S.map (MonoidalCategory.tensorRight B)).ShortExact) :
    (S.map (MonoidalCategory.tensorRight (shiftUp B))).ShortExact := by
  let U := forget₂ (Rep.{u} R G) (ModuleCat.{u} R)
  let s := shiftUpSequence_scalarSplitting B
  have h := tensorRight_shortExact_of_retract (S.map U) s.s
    (U.map (shiftUpSequence B).g) s.s_g ((tensorCoinduced_shortExact S B hB).map_of_exact U)
  exact CategoryTheory.ShortExact.reflects_shortExact_of_faithful U h

/-- Tensor exactness is preserved by the negative scalar-split coefficient shift. -/
lemma tensorShiftDown_shortExact (S : ShortComplex (Rep.{u} R G)) (B : Rep.{u} R G)
    (hB : (S.map (MonoidalCategory.tensorRight B)).ShortExact) :
    (S.map (MonoidalCategory.tensorRight (shiftDown B))).ShortExact := by
  let U := forget₂ (Rep.{u} R G) (ModuleCat.{u} R)
  let s := shiftDownSequence_scalarSplitting B
  have h := tensorRight_shortExact_of_retract (S.map U)
    (U.map (shiftDownSequence B).f) s.r s.f_r
    ((tensorCoinduced_shortExact S B hB).map_of_exact U)
  exact CategoryTheory.ShortExact.reflects_shortExact_of_faithful U h

omit [Fintype G] in
lemma tensorLeft_shortExact_iff (S : ShortComplex (Rep.{u} R G)) (A : Rep.{u} R G) :
    (S.map (MonoidalCategory.tensorLeft A)).ShortExact ↔
      (S.map (MonoidalCategory.tensorRight A)).ShortExact :=
  ShortComplex.shortExact_iff_of_iso
    (S.mapNatIso (BraidedCategory.tensorLeftIsoTensorRight A))

lemma coinducedTensor_shortExact (S : ShortComplex (Rep.{u} R G)) (A : Rep.{u} R G)
    (hA : (S.map (MonoidalCategory.tensorLeft A)).ShortExact) :
    (S.map (MonoidalCategory.tensorLeft (coinduced A))).ShortExact :=
  (tensorLeft_shortExact_iff S (coinduced A)).mpr
    (tensorCoinduced_shortExact S A ((tensorLeft_shortExact_iff S A).mp hA))

lemma shiftUpTensor_shortExact (S : ShortComplex (Rep.{u} R G)) (A : Rep.{u} R G)
    (hA : (S.map (MonoidalCategory.tensorLeft A)).ShortExact) :
    (S.map (MonoidalCategory.tensorLeft (shiftUp A))).ShortExact :=
  (tensorLeft_shortExact_iff S (shiftUp A)).mpr
    (tensorShiftUp_shortExact S A ((tensorLeft_shortExact_iff S A).mp hA))

lemma shiftDownTensor_shortExact (S : ShortComplex (Rep.{u} R G)) (A : Rep.{u} R G)
    (hA : (S.map (MonoidalCategory.tensorLeft A)).ShortExact) :
    (S.map (MonoidalCategory.tensorLeft (shiftDown A))).ShortExact :=
  (tensorLeft_shortExact_iff S (shiftDown A)).mpr
    (tensorShiftDown_shortExact S A ((tensorLeft_shortExact_iff S A).mp hA))

end Langlands.Tate
