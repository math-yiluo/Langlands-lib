/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# The bilinear product on the homology of a total tensor complex

Source: Stacks Project, More on Algebra, Tag 068G, the construction of
`equation-simple-tor-product`, and Varieties, Tag 0BED, `equation-kunneth-on-cech`.
(blueprint: lem-sc-tensor-homology-pairing)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace HomologicalComplex

private theorem descend_bilinear {k : Type u} [CommRing k]
    (S₁ S₂ : ShortComplex (ModuleCat.{u} k)) (M : ModuleCat.{u} k)
    (c : S₁.cycles →ₗ[k] S₂.cycles →ₗ[k] M)
    (h₁ : ∀ x b, c (S₁.toCycles x) b = 0)
    (h₂ : ∀ a y, c a (S₂.toCycles y) = 0) :
    ∃ d : S₁.homology →ₗ[k] S₂.homology →ₗ[k] M,
      ∀ a b, d (S₁.homologyπ a) (S₂.homologyπ b) = c a b := by
  classical
  let t : S₁.homology →ₗ[k] S₂.cycles →ₗ[k] M :=
    (S₁.descHomology (ModuleCat.ofHom c) (by
      ext x b
      exact h₁ x b)).hom
  have ht (a : S₁.cycles) : t (S₁.homologyπ a) = c a :=
    congrArg (fun f ↦ f a) (S₁.π_descHomology (ModuleCat.ofHom c) _)
  have hπ₁ : Function.Surjective S₁.homologyπ :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  have hπ₂ : Function.Surjective S₂.homologyπ :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  have ht₂ (a : S₁.homology) : S₂.toCycles ≫ ModuleCat.ofHom (t a) = 0 := by
    obtain ⟨a, rfl⟩ := hπ₁ a
    ext y
    change t (S₁.homologyπ a) (S₂.toCycles y) = 0
    rw [ht]
    exact h₂ a y
  let g (a : S₁.homology) : S₂.homology →ₗ[k] M :=
    (S₂.descHomology (ModuleCat.ofHom (t a)) (ht₂ a)).hom
  have hg (a : S₁.homology) (b : S₂.cycles) : g a (S₂.homologyπ b) = t a b :=
    congrArg (fun f ↦ f b) (S₂.π_descHomology (ModuleCat.ofHom (t a)) (ht₂ a))
  let d : S₁.homology →ₗ[k] S₂.homology →ₗ[k] M :=
    { toFun := g
      map_add' := by
        intro a a'
        ext b
        obtain ⟨b, rfl⟩ := hπ₂ b
        simp only [hg, map_add, LinearMap.add_apply]
      map_smul' := by
        intro r a
        ext b
        obtain ⟨b, rfl⟩ := hπ₂ b
        simp only [hg, map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  exact ⟨d, fun a b ↦ by change g _ _ = _; rw [hg, ht]⟩

private theorem tensor_cycles_lift {k : Type u} [CommRing k]
    (A B : CochainComplex (ModuleCat.{u} k) ℤ) (n : ℤ)
    (s : {pq : ℤ × ℤ // pq.1 + pq.2 = n})
    (a : A.cycles s.1.1) (b : B.cycles s.1.2) :
    ∃ z : (mapBifunctor A B (curriedTensor (ModuleCat.{u} k))
        (ComplexShape.up ℤ)).cycles n,
      (mapBifunctor A B (curriedTensor (ModuleCat.{u} k))
        (ComplexShape.up ℤ)).iCycles n z =
      ιMapBifunctor A B (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)
        s.1.1 s.1.2 n s.2 ((A.iCycles s.1.1 a) ⊗ₜ[k] (B.iCycles s.1.2 b)) := by
  let T := mapBifunctor A B (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)
  let x := ιMapBifunctor A B (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)
    s.1.1 s.1.2 n s.2 ((A.iCycles s.1.1 a) ⊗ₜ[k] (B.iCycles s.1.2 b))
  have ha : A.d s.1.1 (s.1.1 + 1) (A.iCycles s.1.1 a) = 0 :=
    congrArg (fun f ↦ f a) (A.iCycles_d s.1.1 (s.1.1 + 1))
  have hb : B.d s.1.2 (s.1.2 + 1) (B.iCycles s.1.2 b) = 0 :=
    congrArg (fun f ↦ f b) (B.iCycles_d s.1.2 (s.1.2 + 1))
  have hx : T.d n (n + 1) x = 0 := by
    dsimp only [T, x]
    rw [mapBifunctor.d_eq]
    change ((ιMapBifunctor A B (curriedTensor (ModuleCat.{u} k))
      (ComplexShape.up ℤ) s.1.1 s.1.2 n s.2 ≫
      (mapBifunctor.D₁ A B (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) n (n + 1) +
       mapBifunctor.D₂ A B (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) n (n + 1)))
      ((A.iCycles s.1.1 a) ⊗ₜ[k] (B.iCycles s.1.2 b))) = 0
    rw [Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂]
    rw [mapBifunctor.d₁_eq' A B _ _ (show (ComplexShape.up ℤ).Rel s.1.1 (s.1.1 + 1) from rfl),
      mapBifunctor.d₂_eq' A B _ _ s.1.1
        (show (ComplexShape.up ℤ).Rel s.1.2 (s.1.2 + 1) from rfl)]
    simp [curriedTensor, ha, hb]
  have hx' : ((forget₂ (ModuleCat k) Ab).map (T.sc n).g) x = 0 := by
    change T.d n ((ComplexShape.up ℤ).next n) x = 0
    rwa [(ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl)]
  refine ⟨(T.sc n).cyclesMk x hx', ?_⟩
  exact (T.sc n).i_cyclesMk x hx'

/-- The class of a tensor of cocycles depends bilinearly on their homology classes.
Source: Stacks Project, Tag 068G, construction preceding Lemma 068K;
Tag 0BED, `equation-kunneth-on-cech`.
(blueprint: lem-sc-tensor-homology-pairing)

Proof: Put T = Tot(A tensor B). For cocycles a and b the signed Leibniz formula
makes the inclusion of a tensor b a cocycle of T. The kernel property of iCycles
gives its unique lift z. Taking homology gives a bilinear map on the two cycle
spaces: addition and scalar multiplication follow from the linearity of the
inclusion, the injectivity of iCycles, and the linearity of homologyπ.
If a = d_A a', then the included a tensor b is d_T of the inclusion of a' tensor b
in degree n-1. Its class is therefore zero. If b = d_B b', its inclusion is
(-1)^p times d_T of the inclusion of a tensor b', and again its class is zero.
Thus this bilinear map annihilates boundaries in either variable. Descend it through
Z(A)/B(A) and Z(B)/B(B), using the quotient universal property in each variable,
and identify these quotients with the abstract homology modules. This gives c.
The lift of the tensor of the two cycles supplies z in the conclusion, and the
quotient descent gives the displayed representative equation. -/
theorem tensor_homology_pairing {k : Type u} [CommRing k]
    (A B : CochainComplex (ModuleCat.{u} k) ℤ) (p q n : ℤ) (hpq : p + q = n) :
    ∃ c : A.homology p →ₗ[k] B.homology q →ₗ[k]
        (mapBifunctor A B (curriedTensor (ModuleCat.{u} k))
          (ComplexShape.up ℤ)).homology n,
      ∀ (a : A.cycles p) (b : B.cycles q),
        ∃ z : (mapBifunctor A B (curriedTensor (ModuleCat.{u} k))
          (ComplexShape.up ℤ)).cycles n,
        (mapBifunctor A B (curriedTensor (ModuleCat.{u} k))
          (ComplexShape.up ℤ)).iCycles n z =
          ιMapBifunctor A B (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)
            p q n hpq ((A.iCycles p a) ⊗ₜ[k] (B.iCycles q b)) ∧
        c (A.homologyπ p a) (B.homologyπ q b) =
          (mapBifunctor A B (curriedTensor (ModuleCat.{u} k))
            (ComplexShape.up ℤ)).homologyπ n z := by
  classical
  let T := mapBifunctor A B (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)
  let I : A.cycles p ⊗ B.cycles q ⟶ T.X n :=
    (A.iCycles p ⊗ₘ B.iCycles q) ≫
      ιMapBifunctor A B (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ) p q n hpq
  have hI : I ≫ T.d n (n + 1) = 0 := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro a b
    obtain ⟨z, hz⟩ := tensor_cycles_lift A B n ⟨(p, q), hpq⟩ a b
    change T.d n (n + 1)
      (ιMapBifunctor A B (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)
        p q n hpq ((A.iCycles p a) ⊗ₜ[k] (B.iCycles q b))) = 0
    rw [← hz]
    exact congrArg (fun f ↦ f z) (T.iCycles_d n (n + 1))
  let t : A.cycles p ⊗ B.cycles q ⟶ T.cycles n :=
    T.liftCycles I (n + 1) ((ComplexShape.up ℤ).next_eq' rfl) hI
  have ht : t ≫ T.iCycles n = I := T.liftCycles_i _ _ _ _
  let c₀ : A.cycles p →ₗ[k] B.cycles q →ₗ[k] T.homology n :=
    TensorProduct.curry (t ≫ T.homologyπ n).hom
  have h₁ : ∀ x b, c₀ ((A.sc p).toCycles x) b = 0 := by
    intro x b
    let r := (ComplexShape.up ℤ).prev p
    have hr : r + 1 = p := by
      dsimp only [r]
      rw [(ComplexShape.up ℤ).prev_eq' (show
        (ComplexShape.up ℤ).Rel (p - 1) p by change p - 1 + 1 = p; omega)]
      omega
    let w := ιMapBifunctor A B (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)
      r q (n - 1) (by change r + q = n - 1; omega)
      (x ⊗ₜ[k] (B.iCycles q b))
    have hw : T.d (n - 1) n w = I (((A.sc p).toCycles x) ⊗ₜ[k] b) := by
      have hb : B.d q (q + 1) (B.iCycles q b) = 0 :=
        congrArg (fun f ↦ f b) (B.iCycles_d q (q + 1))
      dsimp only [w, T]
      rw [mapBifunctor.d_eq]
      change ((ιMapBifunctor A B (curriedTensor (ModuleCat.{u} k))
        (ComplexShape.up ℤ) r q (n - 1) _ ≫
        (mapBifunctor.D₁ A B _ _ (n - 1) n +
         mapBifunctor.D₂ A B _ _ (n - 1) n)) (x ⊗ₜ[k] (B.iCycles q b))) = _
      rw [Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
        mapBifunctor.d₁_eq A B _ _ (show (ComplexShape.up ℤ).Rel r p from hr) q n hpq,
        mapBifunctor.d₂_eq' A B _ _ r
          (show (ComplexShape.up ℤ).Rel q (q + 1) from rfl)]
      have ha : A.iCycles p ((A.sc p).toCycles x) = A.d r p x :=
        congrArg (fun f ↦ f x) (A.sc p).toCycles_i
      simp [curriedTensor, hb, I, ha]
    have heq : t (((A.sc p).toCycles x) ⊗ₜ[k] b) = T.toCycles (n - 1) n w := by
      apply (ModuleCat.mono_iff_injective (T.iCycles n)).mp inferInstance
      have ht' := congrArg (fun f ↦ f (((A.sc p).toCycles x) ⊗ₜ[k] b)) ht
      have hw' := congrArg (fun f ↦ f w) (T.toCycles_i (n - 1) n)
      exact ht'.trans (hw.symm.trans hw'.symm)
    change T.homologyπ n (t (((A.sc p).toCycles x) ⊗ₜ[k] b)) = 0
    rw [heq]
    exact congrArg (fun f ↦ f w) (T.toCycles_comp_homologyπ (n - 1) n)
  have h₂ : ∀ a y, c₀ a ((B.sc q).toCycles y) = 0 := by
    intro a y
    let r := (ComplexShape.up ℤ).prev q
    have hr : r + 1 = q := by
      dsimp only [r]
      rw [(ComplexShape.up ℤ).prev_eq' (show
        (ComplexShape.up ℤ).Rel (q - 1) q by change q - 1 + 1 = q; omega)]
      omega
    let ε := ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (p, r)
    let w := ιMapBifunctor A B (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)
      p r (n - 1) (by change p + r = n - 1; omega)
      ((A.iCycles p a) ⊗ₜ[k] y)
    have hw : T.d (n - 1) n w = ε • I (a ⊗ₜ[k] ((B.sc q).toCycles y)) := by
      have ha : A.d p (p + 1) (A.iCycles p a) = 0 :=
        congrArg (fun f ↦ f a) (A.iCycles_d p (p + 1))
      dsimp only [w, T]
      rw [mapBifunctor.d_eq]
      change ((ιMapBifunctor A B (curriedTensor (ModuleCat.{u} k))
        (ComplexShape.up ℤ) p r (n - 1) _ ≫
        (mapBifunctor.D₁ A B _ _ (n - 1) n +
         mapBifunctor.D₂ A B _ _ (n - 1) n)) ((A.iCycles p a) ⊗ₜ[k] y)) = _
      rw [Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
        mapBifunctor.d₁_eq' A B _ _
          (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl),
        mapBifunctor.d₂_eq A B _ _ p
          (show (ComplexShape.up ℤ).Rel r q from hr) n hpq]
      have hb : B.iCycles q ((B.sc q).toCycles y) = B.d r q y :=
        congrArg (fun f ↦ f y) (B.sc q).toCycles_i
      simp [curriedTensor, ha, I, hb, ε]
    have heq : ε • t (a ⊗ₜ[k] ((B.sc q).toCycles y)) = T.toCycles (n - 1) n w := by
      apply (ModuleCat.mono_iff_injective (T.iCycles n)).mp inferInstance
      have ht' := congrArg (fun f ↦ f (a ⊗ₜ[k] ((B.sc q).toCycles y))) ht
      have hw' := congrArg (fun f ↦ f w) (T.toCycles_i (n - 1) n)
      change T.iCycles n (t (a ⊗ₜ[k] ((B.sc q).toCycles y))) =
        I (a ⊗ₜ[k] ((B.sc q).toCycles y)) at ht'
      rw [Units.smul_def, map_zsmul]
      rw [ht']
      exact hw.symm.trans hw'.symm
    have hz : ε • T.homologyπ n (t (a ⊗ₜ[k] ((B.sc q).toCycles y))) = 0 := by
      rw [Units.smul_def, ← map_zsmul, ← Units.smul_def, heq]
      exact congrArg (fun f ↦ f w) (T.toCycles_comp_homologyπ (n - 1) n)
    change T.homologyπ n (t (a ⊗ₜ[k] ((B.sc q).toCycles y))) = 0
    exact (smul_eq_zero_iff_eq ε).mp hz
  obtain ⟨c, hc⟩ := descend_bilinear (A.sc p) (B.sc q) (T.homology n) c₀ h₁ h₂
  refine ⟨c, ?_⟩
  intro a b
  refine ⟨t (a ⊗ₜ[k] b), ?_, ?_⟩
  · exact congrArg (fun f ↦ f (a ⊗ₜ[k] b)) ht
  · change c ((A.sc p).homologyπ a) ((B.sc q).homologyπ b) =
      T.homologyπ n (t (a ⊗ₜ[k] b))
    exact hc a b

end HomologicalComplex
