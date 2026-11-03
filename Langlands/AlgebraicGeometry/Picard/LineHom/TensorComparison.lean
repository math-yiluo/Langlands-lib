import Langlands.AlgebraicGeometry.Picard.LineHom.SectionsTensor
import Langlands.AlgebraicGeometry.Picard.LineHom.GaugeComplex
import Langlands.AlgebraicGeometry.Picard.LineHom.FrameHom
import Langlands.AlgebraicGeometry.Picard.CocycleLineBundlePullback
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom

/-! # Gauge coordinates after base change

For a morphism `q : Z ⟶ Y` and families of transition functions `α`, `β` on an ordered affine
cover `𝒰` of `Y`, `pulledGaugeD q α β` is the gauge differential with the pulled-back transition
functions; its zeros are the gauge families of `pullbackCocycle q α` and `pullbackCocycle q β`.

For `p : Y ⟶ Spec R` and a test `T` over `Spec R`, with base change `Z = T ×_{Spec R} Y` and
second projection `q`, the maps `tensorGauge0` and `tensorGauge1` send `x ⊗ b` to the family of
products of the pulled-back sections `x` and `b`. They intertwine `gaugeD p α β` tensored with
`Γ(T, ⊤)` and `pulledGaugeD q α β`, are natural in `T`, and are bijective when `T` is affine
(the second needs `p` separated).
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard.LineHom

open CocycleGluing

section Pulled

variable {Y Z : Scheme.{u}} (q : Z ⟶ Y) (𝒰 : Y.OrderedAffineCover)

/-- The gauge differential with the transition functions pulled back along `q`. -/
def pulledGaugeD (α β : ∀ i j : 𝒰.ι, (Γ(Y, 𝒰.U i ⊓ 𝒰.U j))ˣ)
    (a : ∀ i : 𝒰.ι, Γ(Z, q ⁻¹ᵁ 𝒰.U i)) (t : 𝒰.Idx 1) :
    Γ(Z, q ⁻¹ᵁ 𝒰.U (t.1 0) ⊓ q ⁻¹ᵁ 𝒰.U (t.1 1)) :=
  Z.presheaf.map (homOfLE (inf_le_left : q ⁻¹ᵁ 𝒰.U (t.1 0) ⊓ q ⁻¹ᵁ 𝒰.U (t.1 1) ≤
      q ⁻¹ᵁ 𝒰.U (t.1 0))).op (a (t.1 0)) *
      (pullbackCocycle q α (t.1 0) (t.1 1) : Γ(Z, q ⁻¹ᵁ 𝒰.U (t.1 0) ⊓ q ⁻¹ᵁ 𝒰.U (t.1 1))) -
    (pullbackCocycle q β (t.1 0) (t.1 1) : Γ(Z, q ⁻¹ᵁ 𝒰.U (t.1 0) ⊓ q ⁻¹ᵁ 𝒰.U (t.1 1))) *
      Z.presheaf.map (homOfLE (inf_le_right : q ⁻¹ᵁ 𝒰.U (t.1 0) ⊓ q ⁻¹ᵁ 𝒰.U (t.1 1) ≤
        q ⁻¹ᵁ 𝒰.U (t.1 1))).op (a (t.1 1))

variable {𝒰}

lemma pulledGaugeD_zero (α β : ∀ i j : 𝒰.ι, (Γ(Y, 𝒰.U i ⊓ 𝒰.U j))ˣ) :
    pulledGaugeD q 𝒰 α β 0 = 0 := by
  funext t
  simp only [pulledGaugeD, Pi.zero_apply, map_zero, zero_mul, mul_zero, sub_zero]

lemma pulledGaugeD_add (α β : ∀ i j : 𝒰.ι, (Γ(Y, 𝒰.U i ⊓ 𝒰.U j))ˣ)
    (a a' : ∀ i : 𝒰.ι, Γ(Z, q ⁻¹ᵁ 𝒰.U i)) :
    pulledGaugeD q 𝒰 α β (a + a') = pulledGaugeD q 𝒰 α β a + pulledGaugeD q 𝒰 α β a' := by
  funext t
  simp only [pulledGaugeD, Pi.add_apply, map_add]
  ring

/-- The increasing pair `(i, j)` for `i < j`, as an index of degree one. -/
def pairIdx {i j : 𝒰.ι} (h : i < j) : 𝒰.Idx 1 :=
  ⟨![i, j], Fin.strictMono_iff_lt_succ.mpr (fun k => by fin_cases k; simpa using h)⟩

/-- The zeros of the pulled-back gauge differential are the gauge families of the pulled-back
transition functions. -/
lemma pulledGaugeD_eq_zero_iff {α β : ∀ i j : 𝒰.ι, (Γ(Y, 𝒰.U i ⊓ 𝒰.U j))ˣ}
    (hα : IsCocycle α) (hβ : IsCocycle β) (a : ∀ i : 𝒰.ι, Γ(Z, q ⁻¹ᵁ 𝒰.U i)) :
    pulledGaugeD q 𝒰 α β a = 0 ↔
      IsGaugeFamily (pullbackCocycle q α) (pullbackCocycle q β) a := by
  rw [isGaugeFamily_iff_of_lt (IsCocycle.pullback q hα) (IsCocycle.pullback q hβ)]
  constructor
  · intro h i j hij
    exact sub_eq_zero.1 (congrFun h (pairIdx hij))
  · intro h
    funext t
    exact sub_eq_zero.2 (h _ _ (t.2 (show (0 : Fin 2) < 1 by decide)))

end Pulled

section Tensor

attribute [local instance] FiniteLinearEquations.sectionsAlgebra

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of R))
  (𝒰 : Y.OrderedAffineCover)

/-- The degree-zero comparison `Γ(T, ⊤) ⊗ GaugeC0 → ∏ᵢ Γ(Z, q⁻¹ Uᵢ)`, sending `x ⊗ b` to the
family of products of the pulled-back sections `x` and `b i`. -/
def tensorGauge0 (T : Over (Spec (.of R))) :
    Γ(T.left, ⊤) ⊗[R] GaugeC0 p 𝒰 →+
      ∀ i : 𝒰.ι, Γ(pullback T.hom p, pullback.snd T.hom p ⁻¹ᵁ 𝒰.U i) :=
  letI := fun i : 𝒰.ι ↦ Scheme.TwoAffineOpenCover.algebraOfHom p (𝒰.U i)
  (AddMonoidHom.pi fun i ↦ (sectionsTensorHom p T (𝒰.U i)).comp
      (Pi.evalAddMonoidHom (fun i : 𝒰.ι ↦ Γ(T.left, ⊤) ⊗[R] Γ(Y, 𝒰.U i)) i)).comp
    (TensorProduct.piRight R R Γ(T.left, ⊤) fun i : 𝒰.ι ↦ Γ(Y, 𝒰.U i)).toLinearMap.toAddMonoidHom

/-- The degree-one comparison `Γ(T, ⊤) ⊗ GaugeC1 → ∏ₜ Γ(Z, q⁻¹ U_{t 0} ⊓ q⁻¹ U_{t 1})`. -/
def tensorGauge1 (T : Over (Spec (.of R))) :
    Γ(T.left, ⊤) ⊗[R] GaugeC1 p 𝒰 →+
      ∀ t : 𝒰.Idx 1, Γ(pullback T.hom p,
        pullback.snd T.hom p ⁻¹ᵁ 𝒰.U (t.1 0) ⊓ pullback.snd T.hom p ⁻¹ᵁ 𝒰.U (t.1 1)) :=
  letI := fun t : 𝒰.Idx 1 ↦
    Scheme.TwoAffineOpenCover.algebraOfHom p (𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 1))
  (AddMonoidHom.pi fun t : 𝒰.Idx 1 ↦
      (sectionsTensorHom p T (𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 1))).comp
        (Pi.evalAddMonoidHom
          (fun t : 𝒰.Idx 1 ↦ Γ(T.left, ⊤) ⊗[R] Γ(Y, 𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 1))) t)).comp
    (TensorProduct.piRight R R Γ(T.left, ⊤)
      fun t : 𝒰.Idx 1 ↦ Γ(Y, 𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 1))).toLinearMap.toAddMonoidHom

variable {𝒰}

lemma tensorGauge0_apply (T : Over (Spec (.of R))) (z : Γ(T.left, ⊤) ⊗[R] GaugeC0 p 𝒰)
    (i : 𝒰.ι) :
    letI := fun i : 𝒰.ι ↦ Scheme.TwoAffineOpenCover.algebraOfHom p (𝒰.U i)
    tensorGauge0 p 𝒰 T z i = sectionsTensorHom p T (𝒰.U i)
      (TensorProduct.piRight R R Γ(T.left, ⊤) (fun i : 𝒰.ι ↦ Γ(Y, 𝒰.U i)) z i) :=
  rfl

lemma tensorGauge0_tmul (T : Over (Spec (.of R))) (x : Γ(T.left, ⊤)) (b : GaugeC0 p 𝒰)
    (i : 𝒰.ι) :
    tensorGauge0 p 𝒰 T (x ⊗ₜ b) i =
      (pullback.fst T.hom p).appLE ⊤ (pullback.snd T.hom p ⁻¹ᵁ 𝒰.U i) (le_preimage_top _ _) x *
        (pullback.snd T.hom p).app (𝒰.U i) (b i) :=
  rfl

lemma tensorGauge1_tmul (T : Over (Spec (.of R))) (x : Γ(T.left, ⊤)) (c : GaugeC1 p 𝒰)
    (t : 𝒰.Idx 1) :
    tensorGauge1 p 𝒰 T (x ⊗ₜ c) t =
      (pullback.fst T.hom p).appLE ⊤
          (pullback.snd T.hom p ⁻¹ᵁ 𝒰.U (t.1 0) ⊓ pullback.snd T.hom p ⁻¹ᵁ 𝒰.U (t.1 1))
          (le_preimage_top _ _) x *
        (pullback.snd T.hom p).appLE (𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 1))
          (pullback.snd T.hom p ⁻¹ᵁ 𝒰.U (t.1 0) ⊓ pullback.snd T.hom p ⁻¹ᵁ 𝒰.U (t.1 1)) le_rfl
          (c t) := by
  change (pullback.fst T.hom p).appLE ⊤ _ (le_preimage_top _ _) x *
    (pullback.snd T.hom p).app (𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 1)) (c t) = _
  rw [Scheme.Hom.app_eq_appLE]
  rfl

/-- The comparison maps intertwine the gauge differential tensored with `Γ(T, ⊤)` and the
pulled-back gauge differential. -/
lemma pulledGaugeD_tensorGauge0 (α β : ∀ i j : 𝒰.ι, (Γ(Y, 𝒰.U i ⊓ 𝒰.U j))ˣ)
    (T : Over (Spec (.of R))) (z : Γ(T.left, ⊤) ⊗[R] GaugeC0 p 𝒰) :
    pulledGaugeD (pullback.snd T.hom p) 𝒰 α β (tensorGauge0 p 𝒰 T z) =
      tensorGauge1 p 𝒰 T ((gaugeD p α β).lTensor Γ(T.left, ⊤) z) := by
  induction z with
  | add z z' hz hz' => rw [map_add, map_add, map_add, pulledGaugeD_add, hz, hz']
  | tmul x b =>
    funext t
    rw [LinearMap.lTensor_tmul, tensorGauge1_tmul, gaugeD_apply]
    simp only [pulledGaugeD, tensorGauge0_tmul, map_mul, map_sub, res_appLE, res_app,
      pullbackCocycle_val, appLE_res]
    ring

/-- The degree-zero comparison is natural in the test object. -/
lemma tensorGauge0_naturality {T' T : Over (Spec (.of R))} (g : T' ⟶ T)
    (w : Γ(T.left, ⊤) ⊗[R] GaugeC0 p 𝒰) (i : 𝒰.ι)
    (h : pullback.snd T'.hom p ⁻¹ᵁ 𝒰.U i ≤
      ((Over.pullback p).map g).left ⁻¹ᵁ (pullback.snd T.hom p ⁻¹ᵁ 𝒰.U i)) :
    tensorGauge0 p 𝒰 T'
        (TensorProduct.map (FiniteLinearEquations.pullSections g).toLinearMap LinearMap.id w) i =
      ((Over.pullback p).map g).left.appLE (pullback.snd T.hom p ⁻¹ᵁ 𝒰.U i)
        (pullback.snd T'.hom p ⁻¹ᵁ 𝒰.U i) h (tensorGauge0 p 𝒰 T w i) := by
  let := fun i : 𝒰.ι ↦ Scheme.TwoAffineOpenCover.algebraOfHom p (𝒰.U i)
  induction w with
  | tmul x b =>
    have H := sectionsTensorHom_naturality p g (𝒰.U i) h (x ⊗ₜ b i)
    rw [TensorProduct.map_tmul] at H
    rw [TensorProduct.map_tmul]
    exact H.symm
  | add w w' hw hw' => simp only [map_add, Pi.add_apply, hw, hw']

/-- For affine `T`, the degree-zero comparison is bijective. -/
lemma tensorGauge0_bijective (T : Over (Spec (.of R))) [IsAffine T.left] :
    Function.Bijective (tensorGauge0 p 𝒰 T) := by
  let := fun i : 𝒰.ι ↦ Scheme.TwoAffineOpenCover.algebraOfHom p (𝒰.U i)
  have h1 : Function.Bijective (Pi.map fun i : 𝒰.ι ↦ sectionsTensorHom p T (𝒰.U i)) :=
    Function.Bijective.piMap fun i ↦ sectionsTensorHom_bijective p T (𝒰.isAffineOpen i)
  exact h1.comp
    (TensorProduct.piRight R R Γ(T.left, ⊤) fun i : 𝒰.ι ↦ Γ(Y, 𝒰.U i)).bijective

/-- For affine `T` and separated `p`, the degree-one comparison is bijective. -/
lemma tensorGauge1_bijective (T : Over (Spec (.of R))) [IsAffine T.left] [IsSeparated p] :
    Function.Bijective (tensorGauge1 p 𝒰 T) := by
  let := fun t : 𝒰.Idx 1 ↦
    Scheme.TwoAffineOpenCover.algebraOfHom p (𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 1))
  have h1 : Function.Bijective (Pi.map fun t : 𝒰.Idx 1 ↦
      sectionsTensorHom p T (𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 1))) :=
    Function.Bijective.piMap fun t ↦ sectionsTensorHom_bijective p T
      (Scheme.OrderedAffineCover.isAffineOpen_inf_of_isSeparated p (𝒰.isAffineOpen _)
        (𝒰.isAffineOpen _))
  exact h1.comp (TensorProduct.piRight R R Γ(T.left, ⊤)
    fun t : 𝒰.Idx 1 ↦ Γ(Y, 𝒰.U (t.1 0) ⊓ 𝒰.U (t.1 1))).bijective

/-- For affine `T` and separated `p`, `tensorGauge0` maps the kernel of the gauge differential
tensored with `Γ(T, ⊤)` bijectively onto the zeros of the pulled-back gauge differential. -/
lemma tensorGauge0_ker_bijective (α β : ∀ i j : 𝒰.ι, (Γ(Y, 𝒰.U i ⊓ 𝒰.U j))ˣ)
    (T : Over (Spec (.of R))) [IsAffine T.left] [IsSeparated p] :
    Function.Bijective (fun w : LinearMap.ker ((gaugeD p α β).lTensor Γ(T.left, ⊤)) ↦
      (⟨tensorGauge0 p 𝒰 T w, (pulledGaugeD_tensorGauge0 p α β T w).trans
        (by rw [LinearMap.mem_ker.1 w.2, map_zero])⟩ :
        {a // pulledGaugeD (pullback.snd T.hom p) 𝒰 α β a = 0})) := by
  constructor
  · intro w w' hw
    exact Subtype.ext ((tensorGauge0_bijective p T).1 (congrArg Subtype.val hw))
  · rintro ⟨a, ha⟩
    obtain ⟨w, rfl⟩ := (tensorGauge0_bijective p T).2 a
    refine ⟨⟨w, LinearMap.mem_ker.2 ((tensorGauge1_bijective p T).1 ?_)⟩, rfl⟩
    rw [← pulledGaugeD_tensorGauge0, ha, map_zero]

end Tensor

end Langlands.AlgebraicGeometry.Picard.LineHom
