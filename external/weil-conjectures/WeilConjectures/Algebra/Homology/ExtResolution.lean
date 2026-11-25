/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.Additive

/-!
# Ext classes of cocycles on a resolution

Let `K` be a chain complex in an abelian category, augmented by `ε : K₀ ⟶ A`, which is a
resolution of `A`: the augmented complex `⋯ ⟶ K₁ ⟶ K₀ ⟶ A ⟶ 0` is exact
(`ChainComplex.IsResolution`). The terms of `K` need not be projective. Write
`B₀ = A` and `B_{n + 1} = ker(Kₙ ⟶ Bₙ)`, so that there are short exact sequences
`0 ⟶ B_{n + 1} ⟶ Kₙ ⟶ Bₙ ⟶ 0`, with extension classes `eₙ ∈ Ext¹(Bₙ, B_{n + 1})`. A cocycle
`φ : K_q ⟶ F` (i.e. `d ≫ φ = 0`) factors through `K_q ⟶ B_q` and defines the class
`e₀ ⋯ e_{q - 1} φ̄ ∈ Ext^q(A, F)` (`ChainComplex.IsResolution.cocycleClass`).

These classes vanish on coboundaries, are natural in `F` and in morphisms of resolutions, are
compatible with the connecting homomorphisms of short exact sequences and with exact functors, and
in degree `0` they identify `Hom(A, F)` with the cocycles `K₀ ⟶ F`.

When `K` is the free resolution of the constant sheaf attached to a hypercover, these are the
classes of hypercover cocycles in sheaf cohomology.

## Implementation

The products `e₀ ⋯ e_{n - 1}` are defined for an arbitrary family of short exact sequences
`0 ⟶ X (n + 1) ⟶ Y n ⟶ X n ⟶ 0` (`CategoryTheory.Abelian.Splicing`); they are natural with
respect to morphisms of such families (`Splicing.extClass_comp_mk₀`) and compatible with exact
functors (`Splicing.extClass_map`). Comparing an arbitrary splicing mapping to `K` with the
canonical one (`ChainComplex.IsResolution.splicing_extClass_comp_mk₀`) gives naturality and
compatibility with exact functors of the classes of cocycles.
-/

@[expose] public section

universe w w' v u v' u'

open CategoryTheory Limits Abelian

namespace CategoryTheory.Abelian

/-- A splicing of short exact sequences `0 ⟶ X (n + 1) ⟶ Y n ⟶ X n ⟶ 0`, `n : ℕ`. Composing
their extension classes gives elements of `Ext^n(X 0, X n)` (`Splicing.extClass`). -/
structure Splicing (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] where
  /-- The outer terms. -/
  X : ℕ → 𝒜
  /-- The middle terms. -/
  Y : ℕ → 𝒜
  /-- The monomorphisms `X (n + 1) ⟶ Y n`. -/
  f (n : ℕ) : X (n + 1) ⟶ Y n
  /-- The epimorphisms `Y n ⟶ X n`. -/
  g (n : ℕ) : Y n ⟶ X n
  w (n : ℕ) : f n ≫ g n = 0
  shortExact (n : ℕ) : (ShortComplex.mk (f n) (g n) (w n)).ShortExact

namespace Splicing

attribute [reassoc (attr := simp)] w

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] (P : Splicing 𝒜)

instance (n : ℕ) : Epi (P.g n) := (P.shortExact n).epi_g

instance (n : ℕ) : Mono (P.f n) := (P.shortExact n).mono_f

variable [HasExt.{w} 𝒜]

/-- The Yoneda product `e₀ ⋯ e_{n - 1} ∈ Ext^n(X 0, X n)` of the extension classes. -/
noncomputable def extClass : (n : ℕ) → Ext.{w} (P.X 0) (P.X n) n
  | 0 => Ext.mk₀ (𝟙 _)
  | n + 1 => (extClass n).comp (P.shortExact n).extClass rfl

/-- `Splicing.extClass` in degree `0`. -/
@[simp]
lemma extClass_zero : P.extClass 0 = Ext.mk₀ (𝟙 _) := rfl

/-- The recursive description of `Splicing.extClass`. -/
lemma extClass_succ (n : ℕ) :
    P.extClass (n + 1) = (P.extClass n).comp (P.shortExact n).extClass rfl := rfl

/-- Naturality of `Splicing.extClass` with respect to morphisms of splicings. -/
lemma extClass_comp_mk₀ (Q : Splicing 𝒜) (a : ∀ n, P.X n ⟶ Q.X n) (b : ∀ n, P.Y n ⟶ Q.Y n)
    (ha : ∀ n, P.f n ≫ b n = a (n + 1) ≫ Q.f n) (hb : ∀ n, P.g n ≫ a n = b n ≫ Q.g n)
    (n : ℕ) :
    (P.extClass n).comp (Ext.mk₀ (a n)) (add_zero n) =
      (Ext.mk₀ (a 0)).comp (Q.extClass n) (zero_add n) := by
  induction n with
  | zero => simp [Ext.mk₀_comp_mk₀]
  | succ n ih =>
    rw [extClass_succ, extClass_succ, Ext.comp_assoc_of_third_deg_zero,
      (P.shortExact n).extClass_naturality (Q.shortExact n)
        { τ₁ := a (n + 1), τ₂ := b n, τ₃ := a n, comm₁₂ := (ha n).symm,
          comm₂₃ := (hb n).symm },
      ← Ext.comp_assoc_of_second_deg_zero, ih]
    exact Ext.comp_assoc _ _ _ _ _ (by lia)

variable {ℬ : Type u'} [Category.{v'} ℬ] [Abelian ℬ]

/-- The image of a splicing under an exact functor. -/
@[simps]
def map (G : 𝒜 ⥤ ℬ) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    Splicing ℬ where
  X n := G.obj (P.X n)
  Y n := G.obj (P.Y n)
  f n := G.map (P.f n)
  g n := G.map (P.g n)
  w n := by rw [← G.map_comp, P.w, G.map_zero]
  shortExact n := (P.shortExact n).map_of_exact G

/-- Exact functors are compatible with `Splicing.extClass`. -/
lemma extClass_map [HasExt.{w'} ℬ] (G : 𝒜 ⥤ ℬ) [G.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] (n : ℕ) :
    (P.map G).extClass n = (P.extClass n).mapExactFunctor G := by
  induction n with
  | zero =>
    simp only [extClass_zero, Ext.mapExactFunctor_mk₀, G.map_id]
    rfl
  | succ n ih =>
    rw [extClass_succ, extClass_succ, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass, ih]

end Splicing

end CategoryTheory.Abelian

namespace ChainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- `K` augmented by `ε : K₀ ⟶ A` is a resolution of `A`: `⋯ ⟶ K₁ ⟶ K₀ ⟶ A ⟶ 0` is exact. -/
structure IsResolution (K : ChainComplex 𝒜 ℕ) {A : 𝒜} (ε : K.X 0 ⟶ A) : Prop where
  d_comp : K.d 1 0 ≫ ε = 0
  exactAt (n : ℕ) : K.ExactAt (n + 1)
  exact_zero : (ShortComplex.mk (K.d 1 0) ε d_comp).Exact
  epi : Epi ε

namespace IsResolution

variable {K : ChainComplex 𝒜 ℕ} {A : 𝒜} {ε : K.X 0 ⟶ A}

/-- The targets of the differentials of the augmented complex: `A` in degree `0` and `Kₙ` in
degree `n + 1`. -/
def augX (_hK : IsResolution K ε) : ℕ → 𝒜
  | 0 => A
  | n + 1 => K.X n

/-- The differentials `Kₙ ⟶ augX n` of the augmented complex. -/
def augD (hK : IsResolution K ε) : (n : ℕ) → (K.X n ⟶ hK.augX n)
  | 0 => ε
  | n + 1 => K.d (n + 1) n

/-- The augmented complex is a complex. -/
lemma d_augD (hK : IsResolution K ε) (n : ℕ) : K.d (n + 1) n ≫ hK.augD n = 0 := by
  cases n with
  | zero => exact hK.d_comp
  | succ n => exact K.d_comp_d _ _ _

/-- The augmented complex is exact. -/
lemma exact_augD (hK : IsResolution K ε) (n : ℕ) :
    (ShortComplex.mk (K.d (n + 1) n) (hK.augD n) (hK.d_augD n)).Exact := by
  cases n with
  | zero => exact hK.exact_zero
  | succ n => exact (K.exactAt_iff' (n + 2) (n + 1) n (by simp) (by simp)).1 (hK.exactAt n)

/-- The objects `B₀ = A` and `B_{n + 1} = ker(Kₙ ⟶ Bₙ)`. -/
noncomputable def B (hK : IsResolution K ε) : ℕ → 𝒜
  | 0 => A
  | n + 1 => kernel (hK.augD n)

/-- The epimorphisms `Kₙ ⟶ Bₙ`. -/
noncomputable def π (hK : IsResolution K ε) : (n : ℕ) → (K.X n ⟶ hK.B n)
  | 0 => ε
  | n + 1 => kernel.lift (hK.augD n) (K.d (n + 1) n) (hK.d_augD n)

/-- The monomorphisms `B_{n + 1} ⟶ Kₙ`. -/
noncomputable def ι (hK : IsResolution K ε) (n : ℕ) : hK.B (n + 1) ⟶ K.X n :=
  kernel.ι (hK.augD n)

/-- The monomorphisms `Bₙ ⟶ augX n`. -/
noncomputable def j (hK : IsResolution K ε) : (n : ℕ) → (hK.B n ⟶ hK.augX n)
  | 0 => 𝟙 A
  | n + 1 => hK.ι n

/-- `π (n + 1)` lifts the differential. -/
@[reassoc (attr := simp)]
lemma π_ι (hK : IsResolution K ε) (n : ℕ) : hK.π (n + 1) ≫ hK.ι n = K.d (n + 1) n :=
  kernel.lift_ι _ _ _

/-- `π 0` is the augmentation. -/
@[simp]
lemma π_zero (hK : IsResolution K ε) : hK.π 0 = ε := rfl

/-- `augD n` factors through `π n`. -/
@[reassoc]
lemma π_j (hK : IsResolution K ε) (n : ℕ) : hK.π n ≫ hK.j n = hK.augD n := by
  cases n with
  | zero => exact Category.comp_id _
  | succ n => exact hK.π_ι n

instance (hK : IsResolution K ε) (n : ℕ) : Mono (hK.ι n) := by
  dsimp [ι]
  infer_instance

/-- The composition `B_{n + 1} ⟶ Kₙ ⟶ Bₙ` vanishes. -/
@[reassoc (attr := simp)]
lemma ι_π (hK : IsResolution K ε) (n : ℕ) : hK.ι n ≫ hK.π n = 0 := by
  cases n with
  | zero => exact kernel.condition _
  | succ n =>
    rw [← cancel_mono (hK.ι n), Category.assoc, π_ι, zero_comp]
    exact kernel.condition (hK.augD (n + 1))

instance (hK : IsResolution K ε) (n : ℕ) : Epi (hK.π n) := by
  cases n with
  | zero => exact hK.epi
  | succ n => exact (hK.exact_augD n).epi_kernelLift

/-- The kernel property of `ι n`. -/
noncomputable def isLimitι (hK : IsResolution K ε) :
    (n : ℕ) → IsLimit (KernelFork.ofι (hK.ι n) (hK.ι_π n))
  | 0 => kernelIsKernel ε
  | n + 1 => isKernelOfComp (hK.ι n) (hK.augD (n + 1)) (kernelIsKernel _) _ (hK.π_ι n)

/-- The short exact sequences `0 ⟶ B_{n + 1} ⟶ Kₙ ⟶ Bₙ ⟶ 0`. -/
lemma shortExact (hK : IsResolution K ε) (n : ℕ) :
    (ShortComplex.mk (hK.ι n) (hK.π n) (hK.ι_π n)).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (hK.isLimitι n)
  mono_f := by
    dsimp
    infer_instance
  epi_g := by
    dsimp
    infer_instance

/-- The splicing `0 ⟶ B_{n + 1} ⟶ Kₙ ⟶ Bₙ ⟶ 0` attached to a resolution. -/
@[simps]
noncomputable def splicing (hK : IsResolution K ε) : Splicing 𝒜 where
  X := hK.B
  Y := K.X
  f := hK.ι
  g := hK.π
  w := hK.ι_π
  shortExact := hK.shortExact

/-- A cocycle `φ : K_q ⟶ F` factors through `π q : K_q ⟶ B_q`. -/
noncomputable def desc (hK : IsResolution K ε) (q : ℕ) {F : 𝒜} (φ : K.X q ⟶ F)
    (hφ : K.d (q + 1) q ≫ φ = 0) : hK.B q ⟶ F :=
  (hK.shortExact q).exact.desc (S := ShortComplex.mk (hK.ι q) (hK.π q) (hK.ι_π q)) φ (by
    rw [← cancel_epi (hK.π (q + 1)), comp_zero, ← Category.assoc, π_ι, hφ])

/-- The defining property of `desc`. -/
@[reassoc (attr := simp)]
lemma π_desc (hK : IsResolution K ε) (q : ℕ) {F : 𝒜} (φ : K.X q ⟶ F)
    (hφ : K.d (q + 1) q ≫ φ = 0) : hK.π q ≫ hK.desc q φ hφ = φ :=
  (hK.shortExact q).exact.g_desc (S := ShortComplex.mk (hK.ι q) (hK.π q) (hK.ι_π q)) _ _

/-- Lift a morphism `x : W ⟶ Kₙ` with `x ≫ augD n = 0` to `B_{n + 1}`. -/
noncomputable def liftB (hK : IsResolution K ε) (n : ℕ) {W : 𝒜} (x : W ⟶ K.X n)
    (hx : x ≫ hK.augD n = 0) : W ⟶ hK.B (n + 1) :=
  kernel.lift (hK.augD n) x hx

/-- The defining property of `liftB`. -/
@[reassoc (attr := simp)]
lemma liftB_ι (hK : IsResolution K ε) (n : ℕ) {W : 𝒜} (x : W ⟶ K.X n)
    (hx : x ≫ hK.augD n = 0) : hK.liftB n x hx ≫ hK.ι n = x :=
  kernel.lift_ι _ _ _

/-- Comparison maps from a splicing `P` mapping to `K` into the canonical splicing of `K`. -/
noncomputable def compMap (hK : IsResolution K ε) (P : Splicing 𝒜) (τ : ∀ n, P.Y n ⟶ K.X n)
    (a₀ : P.X 0 ⟶ A) (h₀ : P.g 0 ≫ a₀ = τ 0 ≫ ε)
    (hτ : ∀ n, τ (n + 1) ≫ K.d (n + 1) n = P.g (n + 1) ≫ P.f n ≫ τ n) :
    (n : ℕ) → {a : P.X n ⟶ hK.B n // P.g n ≫ a = τ n ≫ hK.π n}
  | 0 => ⟨a₀, h₀⟩
  | n + 1 => ⟨hK.liftB n (P.f n ≫ τ n) (by
      rw [Category.assoc, ← π_j, ← Category.assoc (τ n),
        ← (hK.compMap P τ a₀ h₀ hτ n).2, Category.assoc, P.w_assoc, zero_comp]), by
      rw [← cancel_mono (hK.ι n), Category.assoc, Category.assoc, π_ι, hτ, liftB_ι]⟩

variable [HasExt.{w} 𝒜]

/-- The class in `Ext^q(A, F)` of a cocycle `φ : K_q ⟶ F` of a resolution `K` of `A`. -/
noncomputable def cocycleClass (hK : IsResolution K ε) (q : ℕ) {F : 𝒜} (φ : K.X q ⟶ F)
    (hφ : K.d (q + 1) q ≫ φ = 0) : Ext A F q :=
  (hK.splicing.extClass q).comp (Ext.mk₀ (hK.desc q φ hφ)) (add_zero q)

variable (hK : IsResolution K ε)
include hK

/-- Comparison of a splicing `P` mapping to `K` with the canonical splicing of `K`. -/
lemma splicing_extClass_comp_mk₀ (P : Splicing 𝒜) (τ : ∀ n, P.Y n ⟶ K.X n)
    (a₀ : P.X 0 ⟶ A) (h₀ : P.g 0 ≫ a₀ = τ 0 ≫ ε)
    (hτ : ∀ n, τ (n + 1) ≫ K.d (n + 1) n = P.g (n + 1) ≫ P.f n ≫ τ n) (q : ℕ) {F : 𝒜}
    (φ : K.X q ⟶ F) (hφ : K.d (q + 1) q ≫ φ = 0) (φ' : P.X q ⟶ F)
    (hφ' : P.g q ≫ φ' = τ q ≫ φ) :
    (P.extClass q).comp (Ext.mk₀ φ') (add_zero q) =
      (Ext.mk₀ a₀).comp (hK.cocycleClass q φ hφ) (zero_add q) := by
  obtain rfl : φ' = (hK.compMap P τ a₀ h₀ hτ q).1 ≫ hK.desc q φ hφ := by
    rw [← cancel_epi (P.g q), hφ', ← Category.assoc, (hK.compMap P τ a₀ h₀ hτ q).2,
      Category.assoc, π_desc]
  rw [← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_third_deg_zero,
    P.extClass_comp_mk₀ hK.splicing (fun n ↦ (hK.compMap P τ a₀ h₀ hτ n).1) τ
      (fun n ↦ (hK.liftB_ι _ _ _).symm)
      (fun n ↦ (hK.compMap P τ a₀ h₀ hτ n).2)]
  exact Ext.comp_assoc _ _ _ _ _ (by lia)

/-- Additivity of the class of cocycles. -/
lemma cocycleClass_add (q : ℕ) {F : 𝒜} (φ ψ : K.X q ⟶ F) (hφ : K.d (q + 1) q ≫ φ = 0)
    (hψ : K.d (q + 1) q ≫ ψ = 0) :
    hK.cocycleClass q (φ + ψ) (by simp [hφ, hψ]) =
      hK.cocycleClass q φ hφ + hK.cocycleClass q ψ hψ := by
  have : hK.desc q (φ + ψ) (by simp [hφ, hψ]) = hK.desc q φ hφ + hK.desc q ψ hψ := by
    rw [← cancel_epi (hK.π q)]
    simp
  rw [cocycleClass, this, Ext.mk₀_add, Ext.comp_add]
  rfl

/-- The class of a coboundary vanishes. -/
lemma cocycleClass_d (q : ℕ) {F : 𝒜} (ψ : K.X q ⟶ F) :
    hK.cocycleClass (q + 1) (K.d (q + 1) q ≫ ψ) (by simp) = 0 := by
  have h : hK.desc (q + 1) (K.d (q + 1) q ≫ ψ) (by simp) = hK.splicing.f q ≫ ψ := by
    rw [← cancel_epi (hK.π (q + 1))]
    simp
  rw [cocycleClass, h, ← Ext.mk₀_comp_mk₀, Splicing.extClass_succ,
    Ext.comp_assoc_of_third_deg_zero,
    ← Ext.comp_assoc_of_second_deg_zero]
  rw [(hK.splicing.shortExact q).extClass_comp, Ext.zero_comp, Ext.comp_zero]

/-- Naturality in the target. -/
lemma cocycleClass_comp (q : ℕ) {F G : 𝒜} (φ : K.X q ⟶ F) (hφ : K.d (q + 1) q ≫ φ = 0)
    (g : F ⟶ G) :
    hK.cocycleClass q (φ ≫ g) (by simp [reassoc_of% hφ]) =
      (hK.cocycleClass q φ hφ).comp (Ext.mk₀ g) (add_zero q) := by
  have h : hK.desc q (φ ≫ g) (by simp [reassoc_of% hφ]) = hK.desc q φ hφ ≫ g := by
    rw [← cancel_epi (hK.π q)]
    simp
  rw [cocycleClass, cocycleClass, h, ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_third_deg_zero]

/-- Naturality in the resolution: the classes are compatible with morphisms of resolutions of `A`
(which need not be unique up to homotopy, since the terms need not be projective). -/
lemma cocycleClass_naturality {K' : ChainComplex 𝒜 ℕ} {ε' : K'.X 0 ⟶ A}
    (hK' : IsResolution K' ε') (f : K' ⟶ K) (hf : f.f 0 ≫ ε = ε') (q : ℕ) {F : 𝒜}
    (φ : K.X q ⟶ F) (hφ : K.d (q + 1) q ≫ φ = 0) :
    hK'.cocycleClass q (f.f q ≫ φ) (by rw [← HomologicalComplex.Hom.comm_assoc, hφ, comp_zero]) =
      hK.cocycleClass q φ hφ := by
  rw [← Ext.mk₀_id_comp (hK.cocycleClass q φ hφ)]
  exact hK.splicing_extClass_comp_mk₀ hK'.splicing f.f (𝟙 A) ((Category.comp_id _).trans hf.symm)
    (fun n ↦ by simp [f.comm]) q φ hφ _ (by simp)

/-- Compatibility with connecting homomorphisms: if `φ' : K_q ⟶ S.X₂` lifts a cocycle
`φ' ≫ S.g : K_q ⟶ S.X₃` and `ψ : K_{q + 1} ⟶ S.X₁` satisfies `ψ ≫ S.f = d ≫ φ'`, then `ψ` is a
cocycle whose class is the image of the class of `φ' ≫ S.g` under the connecting map. -/
lemma cocycleClass_extClass {S : ShortComplex 𝒜} (hS : S.ShortExact) (q : ℕ)
    (φ' : K.X q ⟶ S.X₂) (hφ' : K.d (q + 1) q ≫ φ' ≫ S.g = 0) (ψ : K.X (q + 1) ⟶ S.X₁)
    (hψ : ψ ≫ S.f = K.d (q + 1) q ≫ φ') (hψ' : K.d (q + 2) (q + 1) ≫ ψ = 0) :
    hK.cocycleClass (q + 1) ψ hψ' =
      (hK.cocycleClass q (φ' ≫ S.g) hφ').comp hS.extClass rfl := by
  have h := (hK.splicing.shortExact q).extClass_naturality hS
    { τ₁ := hK.desc (q + 1) ψ hψ'
      τ₂ := φ'
      τ₃ := hK.desc q (φ' ≫ S.g) hφ'
      comm₁₂ := by
        rw [← cancel_epi (hK.π (q + 1))]
        simp [hψ]
      comm₂₃ := by simp }
  rw [cocycleClass, cocycleClass, Splicing.extClass_succ, Ext.comp_assoc_of_third_deg_zero]
  dsimp at h
  rw [h]
  exact (Ext.comp_assoc _ _ _ _ _ (by lia)).symm

/-- In degree `0`, the classes of the cocycles `K₀ ⟶ F` are exactly the elements of
`Ext⁰(A, F) = Hom(A, F)`, each attained exactly once. -/
lemma bijective_cocycleClass_zero (F : 𝒜) :
    Function.Bijective (fun φ : {φ : K.X 0 ⟶ F // K.d 1 0 ≫ φ = 0} ↦
      hK.cocycleClass 0 φ.1 φ.2) := by
  have h (φ : {φ : K.X 0 ⟶ F // K.d 1 0 ≫ φ = 0}) :
      hK.cocycleClass 0 φ.1 φ.2 = Ext.mk₀ (hK.desc 0 φ.1 φ.2) := by
    simp [cocycleClass]
  have hε : Epi ε := hK.epi
  refine ⟨fun φ ψ hφψ ↦ ?_, fun x ↦ ?_⟩
  · simp only [h] at hφψ
    have := hK.π_desc 0 φ.1 φ.2
    rw [(Ext.mk₀_bijective _ _).1 hφψ, π_desc] at this
    exact Subtype.ext this.symm
  · obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective A F).2 x
    refine ⟨⟨ε ≫ g, by rw [← Category.assoc, hK.d_comp, zero_comp]⟩, (h _).trans ?_⟩
    congr 1
    rw [← cancel_epi ε]
    exact hK.π_desc 0 _ _

omit [HasExt.{w} 𝒜] in
/-- An exact functor maps resolutions to resolutions. -/
lemma map {ℬ : Type u'} [Category.{v'} ℬ] [Abelian ℬ] (G : 𝒜 ⥤ ℬ) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    ChainComplex.IsResolution ((G.mapHomologicalComplex _).obj K) (G.map ε) where
  d_comp := by simp [← G.map_comp, hK.d_comp]
  exactAt n := (hK.exactAt n).map G
  exact_zero := hK.exact_zero.map G
  epi := by
    have := hK.epi
    infer_instance

/-- Exact functors map classes of cocycles to classes of cocycles. -/
lemma mapExt_cocycleClass {ℬ : Type u'} [Category.{v'} ℬ] [Abelian ℬ] [HasExt.{w} ℬ]
    (G : 𝒜 ⥤ ℬ) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (q : ℕ) {F : 𝒜} (φ : K.X q ⟶ F) (hφ : K.d (q + 1) q ≫ φ = 0) :
    (hK.cocycleClass q φ hφ).mapExactFunctor G =
      (hK.map G).cocycleClass q (G.map φ)
        (by simp [← G.map_comp, hφ]) := by
  rw [← Ext.mk₀_id_comp ((hK.map G).cocycleClass q (G.map φ) _), cocycleClass,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, ← Splicing.extClass_map]
  exact (hK.map G).splicing_extClass_comp_mk₀ (hK.splicing.map G) (fun n ↦ 𝟙 _) (𝟙 _) (by simp [π])
    (fun n ↦ by simp [← G.map_comp]) q (G.map φ) _ _ (by simp [← G.map_comp])

end IsResolution

end ChainComplex
