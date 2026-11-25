/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedCoupleMapConstruction
import Mathlib.CategoryTheory.Abelian.Refinements

/-!
# Exactness of the induced maps on images and cycle quotients

Source: Stacks Project, Lemma 12.21.2 (Tag 011R), Remark 12.21.5 (Tag 0AMJ).
-/

@[expose] public section

universe u v

open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] {s : ℕ}

private theorem exact_of_image_eq_kernel {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : imageSubobject f = kernelSubobject g) :
    ∃ hfg : f ≫ g = 0, (ShortComplex.mk f g hfg).Exact := by
  have hfg : f ≫ g = 0 := (kernelSubobject_factors_iff g f).mp (by
    rw [← h]
    simpa using imageSubobject_factors_comp_self f (𝟙 X))
  exact ⟨hfg, (ShortComplex.exact_iff_image_eq_kernel _).mpr h⟩

-- The first chase: lift through f, lift to cycles, then pass to the quotient.
private theorem exact_image_restriction {E B T U K Q I J : C}
    (f : E ⟶ B) (a : B ⟶ T) (g : B ⟶ U)
    (k : K ⟶ E) (P : K ⟶ Q) (i : I ⟶ B) (j : J ⟶ T)
    (F : Q ⟶ I) (α : I ⟶ J) [Mono i] [Mono j] [Epi P]
    (hkg : k ≫ (f ≫ g) = 0)
    (hk : IsLimit (KernelFork.ofι k hkg))
    (hfa : f ≫ a = 0) (hig : i ≫ g = 0)
    (hf : (ShortComplex.mk f a hfa).Exact)
    (hF : P ≫ F ≫ i = k ≫ f) (hα : α ≫ j = i ≫ a) :
    imageSubobject F = kernelSubobject α := by
  have hzero : F ≫ α = 0 := by
    apply (cancel_epi P).mp
    apply (cancel_mono j).mp
    simp only [Category.assoc, zero_comp, comp_zero]
    rw [hα]
    simpa only [Category.assoc, hfa, comp_zero] using hF =≫ a
  apply (ShortComplex.exact_iff_image_eq_kernel (ShortComplex.mk F α hzero)).mp
  apply (ShortComplex.exact_iff_exact_up_to_refinements _).mpr
  intro A x hx
  have hxa : (x ≫ i) ≫ a = 0 := by
    rw [Category.assoc, ← hα, ← Category.assoc, hx, zero_comp]
  obtain ⟨A', π, hπ, y, hy⟩ := hf.exact_up_to_refinements (x ≫ i) hxa
  have hyg : y ≫ (f ≫ g) = 0 := by
    rw [← Category.assoc, ← hy]
    simp only [Category.assoc, hig, comp_zero]
  obtain ⟨z, hz⟩ := KernelFork.IsLimit.lift' hk y hyg
  refine ⟨A', π, hπ, z ≫ P, ?_⟩
  apply (cancel_mono i).mp
  simp only [Category.assoc]
  rw [hF]
  dsimp only [KernelFork.ι_ofι] at hz
  simpa only [Category.assoc] using hy.trans (hz =≫ f).symm

-- The second chase: lift a quotient class to cycles, then lift through g.
private theorem exact_cycle_quotient {A E K Q I J B : C}
    (g : A ⟶ E) (f : E ⟶ B) (k : K ⟶ E) (P : K ⟶ Q)
    (r : A ⟶ I) (G : A ⟶ K) (back : I ⟶ Q) (F : Q ⟶ J) (j : J ⟶ B)
    [Mono k] [Mono j] [Epi P] [Epi r]
    (hgf : g ≫ f = 0) (hg : (ShortComplex.mk g f hgf).Exact)
    (hG : G ≫ k = g) (hback : r ≫ back = G ≫ P)
    (hF : P ≫ F ≫ j = k ≫ f) :
    imageSubobject back = kernelSubobject F := by
  have hzero : back ≫ F = 0 := by
    apply (cancel_epi r).mp
    apply (cancel_mono j).mp
    simp only [Category.assoc, zero_comp, comp_zero]
    rw [← Category.assoc r, hback, Category.assoc, hF,
      ← Category.assoc, hG, hgf]
  apply (ShortComplex.exact_iff_image_eq_kernel (ShortComplex.mk back F hzero)).mp
  apply (ShortComplex.exact_iff_exact_up_to_refinements _).mpr
  intro A' x hx
  obtain ⟨A₁, π₁, hπ₁, z, hz⟩ := surjective_up_to_refinements_of_epi P x
  have hzf : (z ≫ k) ≫ f = 0 := by
    rw [Category.assoc, ← hF, ← Category.assoc z, ← Category.assoc, ← hz,
      Category.assoc π₁, hx, comp_zero, zero_comp]
  obtain ⟨A₂, π₂, hπ₂, y, hy⟩ := hg.exact_up_to_refinements (z ≫ k) hzf
  have hyG : y ≫ G = π₂ ≫ z := by
    apply (cancel_mono k).mp
    simpa only [Category.assoc, hG] using hy.symm
  refine ⟨A₂, π₂ ≫ π₁, inferInstance, y ≫ r, ?_⟩
  simp only [Category.assoc, hz, hback]
  rw [← Category.assoc y, hyG, Category.assoc]

-- The third chase: subtract an incoming boundary before lifting through alpha.
private theorem exact_corrected_lift {A B E V K Q H I : C}
    (a : A ⟶ B) (g : A ⟶ E) (f : V ⟶ A) (b : V ⟶ K)
    (k : K ⟶ E) (P : K ⟶ Q) (r : A ⟶ I) (i : I ⟶ B)
    (h : H ⟶ A) (α : H ⟶ I) (G : A ⟶ K) (back : I ⟶ Q)
    [Mono k] [Mono i] [Epi r]
    (hbP : b ≫ P = 0) (hP : IsColimit (CokernelCofork.ofπ P hbP))
    (hr : r ≫ i = a) (hα : α ≫ i = h ≫ a)
    (hG : G ≫ k = g) (hback : r ≫ back = G ≫ P)
    (hb : b ≫ k = f ≫ g) (hfa : f ≫ a = 0)
    (hhg : h ≫ g = 0) (hh : (ShortComplex.mk h g hhg).Exact) :
    imageSubobject α = kernelSubobject back := by
  have hαr : α = h ≫ r := by
    apply (cancel_mono i).mp
    rw [hα, Category.assoc, hr]
  have hzero : α ≫ back = 0 := by
    rw [hαr, Category.assoc, hback, ← Category.assoc h]
    have hhG : h ≫ G = 0 := by
      apply (cancel_mono k).mp
      rw [Category.assoc, hG, hhg, zero_comp]
    rw [hhG, zero_comp]
  apply (ShortComplex.exact_iff_image_eq_kernel (ShortComplex.mk α back hzero)).mp
  apply (ShortComplex.exact_iff_exact_up_to_refinements _).mpr
  intro T x hx
  obtain ⟨T₁, π₁, hπ₁, y, hy⟩ := surjective_up_to_refinements_of_epi r x
  have hyP : (y ≫ G) ≫ P = 0 := by
    rw [Category.assoc, ← hback, ← Category.assoc, ← hy, Category.assoc, hx, comp_zero]
  obtain ⟨T₂, π₂, hπ₂, z, hz⟩ :=
    (CokernelCofork.IsColimit.comp_π_eq_zero_iff_up_to_refinements hP (y ≫ G)).mp hyP
  let y' := π₂ ≫ y - z ≫ f
  have hy'g : y' ≫ g = 0 := by
    dsimp only [y']
    rw [Preadditive.sub_comp, Category.assoc, ← hG, ← Category.assoc y,
      ← Category.assoc π₂, hz, Category.assoc, hb]
    simp only [Category.assoc, hG, sub_self]
  obtain ⟨T₃, π₃, hπ₃, w, hw⟩ := hh.exact_up_to_refinements y' hy'g
  refine ⟨T₃, π₃ ≫ π₂ ≫ π₁, inferInstance, w, ?_⟩
  apply (cancel_mono i).mp
  simp only [Category.assoc, hα, ← Category.assoc w h, ← hw]
  have hy'a : y' ≫ a = π₂ ≫ y ≫ a := by
    dsimp only [y']
    rw [Preadditive.sub_comp, Category.assoc z, hfa, comp_zero, sub_zero,
      Category.assoc]
  rw [hy'a, ← hr]
  simpa only [Category.assoc] using π₃ ≫= π₂ ≫= (hy =≫ i)

/-- The induced maps are exact, provided they satisfy the defining descent equations.
Source: Stacks Project, Lemma 12.21.2, Tag 011R, and Remark 12.21.5, Tag 0AMJ
(blueprint: lem-sp-derived-map-exactness).

Proof. Use generalized elements with epimorphic refinements, which detect images
and kernels in an abelian category. At the image of `a`, an element annihilated
by the restricted `a` lifts through `f`, by `ha`. The lift is a cycle, because
its `f`-image lies in the incoming image of `a`, annihilated by `g`. Its cycle
class maps to the original element by `f_comm`; the converse follows from `haf`.
At the cycle quotient, lift an element through the epi cycle projection. If its
`forward`-image is zero, `f_comm` and mono image cancellation imply that its
cycle lift is killed by `f`. Lift it through `g` using `hf`, then apply the
incoming image epimorphism of `a`. The equation `g_comm` identifies the resulting
`backward`-image with the original class. Conversely, that image is killed by
`forward`, by `hg` and the equations.
At the next image of `a`, lift an element killed by `backward` through the epi
image factorization of the incoming `a`. Its `g`-image is a boundary, by `g_comm`
and the kernel description of the cycle quotient. Lift that boundary through
its defining incoming differential; subtract the resulting `f`-image from the
chosen lift. This does not change its image under `a`, by `haf`, and kills its
`g`-image by the boundary equality `hβeq`. By `hgg` the corrected lift comes
from the preceding `a`. The equation `alpha_comm` gives an `alpha`-preimage
of the element. Conversely an `alpha`-image is killed by `backward` by `hga`.
These image and kernel inclusions descend along epimorphisms: every subobject
of an abelian category is the kernel of its cokernel. They prove all three
subobject equalities, with the indices transported as in the stated equations. -/
theorem derivedCoupleMapData_exact (D E : ℤ → ℤ → C)
    (a : ∀ p q, D p q ⟶ D (p - 1) (q + 1))
    (f : ∀ p q, E p q ⟶ D (p + 2) (q - 1))
    (g : ∀ p q, D p q ⟶ E (p + s) (q - s))
    (β : ∀ p q, E (p - s - 2) (q + s + 1) ⟶ E p q)
    (hβ : ∀ p q, β p q ≫ f p q ≫ g (p + 2) (q - 1) = 0)
    (hg : ∀ p q, g p q ≫ f (p + s) (q - s) = 0)
    (haf : ∀ p q, f p q ≫ a (p + 2) (q - 1) = 0)
    (hga : ∀ p q, a p q ≫ g (p - 1) (q + 1) = 0)
    (ha : ∀ p q, imageSubobject (f p q) = kernelSubobject (a (p + 2) (q - 1)))
    (hf : ∀ p q, imageSubobject (g p q) = kernelSubobject (f (p + s) (q - s)))
    (hgg : ∀ p q, imageSubobject (a p q) = kernelSubobject (g (p - 1) (q + 1)))
    (hβeq : ∀ p q, β p q =
      (f (p - s - 2) (q + s + 1) ≫ g ((p - s - 2) + 2) ((q + s + 1) - 1)) ≫
        eqToHom (by congr 1 <;> omega))
    (M : DerivedCoupleMapData D E a f g β hβ hg) :
    (∀ p q, imageSubobject (M.forward p q) =
      kernelSubobject (M.alpha (p + 2) (q - 1))) ∧
    (∀ p q, imageSubobject (M.backward p q) =
      kernelSubobject (M.forward (p + (s + 1)) (q - (s + 1)))) ∧
    (∀ p q, imageSubobject (M.alpha p q) =
      kernelSubobject (M.backward (p - 1) (q + 1))) := by
  let I : ∀ p q, image (a (p + 1) (q - 1)) ⟶ D p q := fun p q ↦
    image.ι (a (p + 1) (q - 1)) ≫ eqToHom (by congr 1 <;> omega)
  have hIg : ∀ p q, I p q ≫ g p q = 0 := by
    intro p q
    have ht := (eqToHom_naturality (fun i : ℤ × ℤ ↦ g i.1 i.2)
      (congrArg₂ Prod.mk (show (p + 1) - 1 = p by omega)
        (show (q - 1) + 1 = q by omega))).symm
    dsimp only [I]
    rw [Category.assoc, ht, ← Category.assoc,
      image_ι_comp_eq_zero (hga (p + 1) (q - 1)), zero_comp]
  have hfirst : ∀ p q, imageSubobject (M.forward p q) =
      kernelSubobject (M.alpha (p + 2) (q - 1)) := by
    intro p q
    obtain ⟨hz, he⟩ := exact_of_image_eq_kernel _ _ (ha p q)
    exact exact_image_restriction (f p q) (a (p + 2) (q - 1))
      (g (p + 2) (q - 1)) (kernel.ι (f p q ≫ g (p + 2) (q - 1)))
      (cokernel.π (kernel.lift (f p q ≫ g (p + 2) (q - 1)) (β p q) (hβ p q)))
      (I (p + 2) (q - 1)) (I ((p + 2) - 1) ((q - 1) + 1))
      (M.forward p q) (M.alpha (p + 2) (q - 1))
      (kernel.condition _) (kernelIsKernel _) (haf p q) (hIg _ _) he
      (M.f_comm p q) (by
        simpa only [I, Category.assoc] using M.alpha_comm (p + 2) (q - 1))
  let K := fun p q ↦ kernel (f p q ≫ g (p + 2) (q - 1))
  let Q := fun p q ↦ cokernel
    (kernel.lift (f p q ≫ g (p + 2) (q - 1)) (β p q) (hβ p q))
  let P : ∀ p q, K p q ⟶ Q p q := fun p q ↦ cokernel.π
    (kernel.lift (f p q ≫ g (p + 2) (q - 1)) (β p q) (hβ p q))
  have hsecond : ∀ p q, imageSubobject (M.backward p q) =
      kernelSubobject (M.forward (p + (s + 1)) (q - (s + 1))) := by
    intro p q
    let r := (p + 1) + (s : ℤ)
    let t := (q - 1) - (s : ℤ)
    let r' := p + ((s + 1 : ℕ) : ℤ)
    let t' := q - ((s + 1 : ℕ) : ℤ)
    have hp : r = r' := by dsimp [r, r']; omega
    have hq : t = t' := by dsimp [t, t']; omega
    let eQ : Q r t ⟶ Q r' t' := eqToHom (congrArg₂ Q hp hq)
    let eD : D (r + 2) (t - 1) ⟶ D (r' + 2) (t' - 1) :=
      eqToHom (congrArg₂ (fun p q ↦ D (p + 2) (q - 1)) hp hq)
    let G : D (p + 1) (q - 1) ⟶ K r t := kernel.lift
      (f r t ≫ g (r + 2) (t - 1)) (g (p + 1) (q - 1))
      (by dsimp only [r, t]; rw [← Category.assoc, hg, zero_comp])
    have hF : (P r t ≫ eQ) ≫ M.forward r' t' ≫ I (r' + 2) (t' - 1) =
        kernel.ι (f r t ≫ g (r + 2) (t - 1)) ≫ (f r t ≫ eD) := by
      have ht := (eqToHom_naturality
        (fun i : ℤ × ℤ ↦ M.forward i.1 i.2 ≫ I (i.1 + 2) (i.2 - 1))
        (congrArg₂ Prod.mk hp hq)).symm
      dsimp only [eQ, eD]
      simp only [Category.assoc]
      rw [ht, ← Category.assoc (P r t)]
      change (P r t ≫ M.forward r t ≫ I (r + 2) (t - 1)) ≫ _ = _
      rw [M.f_comm]
      simp only [Category.assoc]
    obtain ⟨hz, he⟩ := exact_of_image_eq_kernel (g (p + 1) (q - 1)) (f r t ≫ eD)
      (by rw [kernelSubobject_comp_mono]; exact hf (p + 1) (q - 1))
    exact exact_cycle_quotient (g (p + 1) (q - 1)) (f r t ≫ eD)
      (kernel.ι (f r t ≫ g (r + 2) (t - 1))) (P r t ≫ eQ)
      (factorThruImage (a (p + 1) (q - 1))) G (M.backward p q)
      (M.forward r' t') (I (r' + 2) (t' - 1)) hz he (kernel.lift_ι _ _ _)
      (M.g_comm p q) hF
  refine ⟨hfirst, hsecond, ?_⟩
  intro p q
  let bp := p - 1
  let bq := q + 1
  have hp : p = bp + 1 := by dsimp [bp]; omega
  have hq : q = bq - 1 := by dsimp [bq]; omega
  let eI : image (a p q) ⟶ image (a (bp + 1) (bq - 1)) :=
    eqToHom (congrArg₂ (fun p q ↦ image (a p q)) hp hq)
  let r := factorThruImage (a p q) ≫ eI
  let eQ : Q (bp + (s + 1)) (bq - (s + 1)) ⟶ Q (p + s) (q - s) :=
    eqToHom (by dsimp [bp, bq]; congr 1 <;> omega)
  let G : D p q ⟶ K (p + s) (q - s) := kernel.lift
    (f (p + s) (q - s) ≫ g ((p + s) + 2) ((q - s) - 1)) (g p q)
    (by rw [← Category.assoc, hg, zero_comp])
  let b := kernel.lift
    (f (p + s) (q - s) ≫ g ((p + s) + 2) ((q - s) - 1))
    (β (p + s) (q - s)) (hβ (p + s) (q - s))
  let fp := (p + (s : ℤ)) - s - 2
  let fq := (q - (s : ℤ)) + s + 1
  have hfp : fp + 2 = p := by dsimp [fp]; omega
  have hfq : fq - 1 = q := by dsimp [fq]; omega
  let eD : D (fp + 2) (fq - 1) ⟶ D p q := eqToHom (congrArg₂ D hfp hfq)
  let f₀ := f fp fq ≫ eD
  have hr : r ≫ I bp bq = a p q := by
    have ht := (eqToHom_naturality
      (fun i : ℤ × ℤ ↦ image.ι (a i.1 i.2)) (congrArg₂ Prod.mk hp hq)).symm
    dsimp only [r, eI, I]
    simp only [Category.assoc]
    rw [reassoc_of% ht]
    simp only [eqToHom_trans, eqToHom_refl, Category.comp_id]
    exact image.fac _
  have hback : r ≫ (M.backward bp bq ≫ eQ) = G ≫ P (p + s) (q - s) := by
    let T : ∀ p q, D p q ⟶ Q (p + s) (q - s) := fun p q ↦
      kernel.lift (f (p + s) (q - s) ≫ g ((p + s) + 2) ((q - s) - 1))
        (g p q) (by rw [← Category.assoc, hg, zero_comp]) ≫ P (p + s) (q - s)
    have hfac := (eqToHom_naturality
      (fun i : ℤ × ℤ ↦ factorThruImage (a i.1 i.2)) (congrArg₂ Prod.mk hp hq)).symm
    have ht := (eqToHom_naturality (fun i : ℤ × ℤ ↦ T i.1 i.2)
      (congrArg₂ Prod.mk hp hq)).symm
    have hm := M.g_comm bp bq
    rw [← Category.assoc] at hm
    change factorThruImage (a (bp + 1) (bq - 1)) ≫ M.backward bp bq =
      T (bp + 1) (bq - 1) ≫ _ at hm
    dsimp only [r, eI]
    rw [← Category.assoc, ← hfac]
    simp only [Category.assoc]
    rw [reassoc_of% hm, reassoc_of% ht]
    simp only [eQ, eqToHom_trans, eqToHom_refl, Category.comp_id]
    rfl
  have hb : b ≫ kernel.ι (f (p + s) (q - s) ≫
      g ((p + s) + 2) ((q - s) - 1)) = f₀ ≫ g p q := by
    have ht := (eqToHom_naturality (fun i : ℤ × ℤ ↦ g i.1 i.2)
      (congrArg₂ Prod.mk hfp hfq)).symm
    dsimp only [b, f₀, eD]
    rw [kernel.lift_ι, hβeq]
    simp only [Category.assoc]
    rw [ht]
  have hf₀a : f₀ ≫ a p q = 0 := by
    have ht := (eqToHom_naturality (fun i : ℤ × ℤ ↦ a i.1 i.2)
      (congrArg₂ Prod.mk hfp hfq)).symm
    dsimp only [f₀, eD]
    rw [Category.assoc, ht, ← Category.assoc, haf, zero_comp]
  have hh : (ShortComplex.mk (I p q) (g p q) (hIg p q)).Exact := by
    obtain ⟨hz, he⟩ := exact_of_image_eq_kernel _ _ (hgg (p + 1) (q - 1))
    let φ : ShortComplex.mk (a (p + 1) (q - 1))
        (g ((p + 1) - 1) ((q - 1) + 1)) hz ⟶
        ShortComplex.mk (I p q) (g p q) (hIg p q) :=
      { τ₁ := factorThruImage (a (p + 1) (q - 1))
        τ₂ := eqToHom (show D ((p + 1) - 1) ((q - 1) + 1) = D p q by
          congr 1 <;> omega)
        τ₃ := eqToHom (show E (((p + 1) - 1) + s) (((q - 1) + 1) - s) =
            E (p + s) (q - s) by congr 1 <;> omega)
        comm₁₂ := by simp only [I, image.fac_assoc]
        comm₂₃ := by
          exact (eqToHom_naturality (fun i : ℤ × ℤ ↦ g i.1 i.2)
            (congrArg₂ Prod.mk (show (p + 1) - 1 = p by omega)
              (show (q - 1) + 1 = q by omega))).symm }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp he
  have hthird := exact_corrected_lift (a p q) (g p q) f₀ b
    (kernel.ι (f (p + s) (q - s) ≫ g ((p + s) + 2) ((q - s) - 1)))
    (P (p + s) (q - s)) r (I bp bq) (I p q) (M.alpha p q) G
    (M.backward bp bq ≫ eQ) (cokernel.condition b) (cokernelIsCokernel b)
    hr (by simpa only [I, bp, bq, Category.assoc] using M.alpha_comm p q)
    (kernel.lift_ι _ _ _) hback hb hf₀a (hIg p q) hh
  simpa only [kernelSubobject_comp_mono] using hthird

end CategoryTheory
