/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits

import WeilConjectures.Algebra.Homology.FreeComplexCover
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.Embedding.Extend

/-!
# Successive free-cover columns

Source: Stacks Project, Tag 09KP, the kernel iteration before totalization.
(blueprint: lem-pc-derived-free-cover-columns)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

private theorem cycle_lift {A : Type u} [CommRing A]
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (q : ℤ)
    (x : P.X q) (hx : P.d q (q + 1) x = 0) :
    ∃ y : P.cycles q, P.iCycles q y = x := by
  let f : ModuleCat.of A A ⟶ P.X q :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton A (P.X q) x)
  have hf : f ≫ P.d q (q + 1) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    simp [f, hx]
  refine ⟨P.liftCycles f (q + 1) (by simp) hf (1 : A), ?_⟩
  have h := congrArg (fun t : ModuleCat.of A A ⟶ P.X q ↦ t (1 : A))
    (P.liftCycles_i f (q + 1) (by simp) hf)
  change P.iCycles q (P.liftCycles f (q + 1) (by simp) hf (1 : A)) = f (1 : A) at h
  exact h.trans (by change (1 : A) • x = x; exact one_smul A x)

private theorem cycles_surj {A : Type u} [CommRing A]
    {P N : CochainComplex (ModuleCat.{u} A) ℤ} (f : P ⟶ N)
    (hf : ∀ (q : ℤ) (z : N.X q), N.d q (q + 1) z = 0 →
      ∃ x : P.X q, P.d q (q + 1) x = 0 ∧ f.f q x = z) (q : ℤ) :
    Function.Surjective (HomologicalComplex.cyclesMap f q).hom := by
  intro z
  have hz : N.d q (q + 1) (N.iCycles q z) = 0 := by
    have h := congrArg (fun t ↦ t z) (N.iCycles_d q (q + 1))
    change N.d q (q + 1) (N.iCycles q z) = 0 at h
    exact h
  obtain ⟨x, hx, hfx⟩ := hf q (N.iCycles q z) hz
  obtain ⟨y, hy⟩ := cycle_lift P q x hx
  refine ⟨y, ?_⟩
  apply (ModuleCat.mono_iff_injective (N.iCycles q)).mp inferInstance
  have h := congrArg (fun t ↦ t y) (HomologicalComplex.cyclesMap_i f q)
  change N.iCycles q (HomologicalComplex.cyclesMap f q y) = f.f q (P.iCycles q y) at h
  rw [hy, hfx] at h
  exact h

private theorem kernel_terms {A : Type u} [CommRing A]
    {P N : CochainComplex (ModuleCat.{u} A) ℤ} (f : P ⟶ N) (q : ℤ) :
    Function.Exact ((kernel.ι f).f q).hom (f.f q).hom := by
  let E := HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ) q
  let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
  have h : (S.map E).Exact :=
    (S.map E).exact_of_f_is_kernel (isLimitOfHasKernelOfPreservesLimit E f)
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map E)).mp h
private theorem kernel_cycles {A : Type u} [CommRing A]
    {P N : CochainComplex (ModuleCat.{u} A) ℤ} (f : P ⟶ N) (q : ℤ) :
    Function.Exact (HomologicalComplex.cyclesMap (kernel.ι f) q).hom
      (HomologicalComplex.cyclesMap f q).hom := by
  intro z
  constructor
  · intro hz
    have hx : f.f q (P.iCycles q z) = 0 := by
      have h := congrArg (fun t ↦ t z) (HomologicalComplex.cyclesMap_i f q)
      change N.iCycles q (HomologicalComplex.cyclesMap f q z) =
        f.f q (P.iCycles q z) at h
      rw [hz, map_zero] at h
      exact h.symm
    obtain ⟨y, hy⟩ := (kernel_terms f q (P.iCycles q z)).mp hx
    have hinj : Function.Injective ((kernel.ι f).f (q + 1)) := by
      apply (ModuleCat.mono_iff_injective _).mp
      exact Functor.map_mono (HomologicalComplex.eval _ _ (q + 1)) (kernel.ι f)
    have hdy : (kernel f).d q (q + 1) y = 0 := by
      apply hinj
      have h := congrArg (fun t ↦ t y) ((kernel.ι f).comm q (q + 1))
      change P.d q (q + 1) ((kernel.ι f).f q y) =
        (kernel.ι f).f (q + 1) ((kernel f).d q (q + 1) y) at h
      rw [hy] at h
      have hz' := congrArg (fun t ↦ t z) (P.iCycles_d q (q + 1))
      change P.d q (q + 1) (P.iCycles q z) = 0 at hz'
      rw [hz'] at h
      exact h.symm.trans (map_zero _).symm
    obtain ⟨w, hw⟩ := cycle_lift (kernel f) q y hdy
    refine ⟨w, ?_⟩
    apply (ModuleCat.mono_iff_injective (P.iCycles q)).mp inferInstance
    have h := congrArg (fun t ↦ t w) (HomologicalComplex.cyclesMap_i (kernel.ι f) q)
    change P.iCycles q (HomologicalComplex.cyclesMap (kernel.ι f) q w) =
      (kernel.ι f).f q ((kernel f).iCycles q w) at h
    rw [hw, hy] at h
    exact h
  · rintro ⟨w, rfl⟩
    have h : HomologicalComplex.cyclesMap (kernel.ι f) q ≫
        HomologicalComplex.cyclesMap f q = 0 := by
      rw [← HomologicalComplex.cyclesMap_comp, kernel.condition,
        HomologicalComplex.cyclesMap_zero]
    have h' := congrArg (fun t ↦ t w) h
    exact h'

private theorem exact_pre_surj {X Y Z W : Type*} [Zero W]
    {f : Y → Z} {g : Z → W} (h : Function.Exact f g)
    {e : X → Y} (he : Function.Surjective e) : Function.Exact (f ∘ e) g := by
  intro z
  rw [h z]
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := he y
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨e x, rfl⟩


private theorem kernel_mono {A : Type u} [CommRing A]
    {P N : CochainComplex (ModuleCat.{u} A) ℤ} (f : P ⟶ N) : Mono (kernel.ι f) := by
  infer_instance

private theorem exact_iso {A : Type u} [CommRing A]
    {P₁ P₂ P₃ Q₁ Q₂ Q₃ : ModuleCat.{u} A}
    (e₁ : Q₁ ≅ P₁) (e₂ : Q₂ ≅ P₂) (e₃ : Q₃ ≅ P₃)
    (f : P₁ ⟶ P₂) (g : P₂ ⟶ P₃) (h : Function.Exact f.hom g.hom) :
    Function.Exact (e₁.hom ≫ f ≫ e₂.inv).hom (e₂.hom ≫ g ≫ e₃.inv).hom := by
  have hm := (LinearEquiv.conj_symm_exact_iff_exact f.hom g.hom e₂.toLinearEquiv).mpr h
  have hp := exact_pre_surj hm e₁.toLinearEquiv.surjective
  have hq := hp.comp_injective (⇑e₃.toLinearEquiv.symm) e₃.toLinearEquiv.symm.injective
    (e₃.toLinearEquiv.symm.map_zero)
  exact hq

private theorem exact_functor_iso {A : Type u} [CommRing A]
    (F : CochainComplex (ModuleCat.{u} A) ℤ ⥤ ModuleCat.{u} A)
    {P₁ P₂ P₃ Q₁ Q₂ Q₃ : CochainComplex (ModuleCat.{u} A) ℤ}
    (e₁ : Q₁ ≅ P₁) (e₂ : Q₂ ≅ P₂) (e₃ : Q₃ ≅ P₃)
    (f : P₁ ⟶ P₂) (g : P₂ ⟶ P₃)
    (h : Function.Exact (F.map f).hom (F.map g).hom) :
    Function.Exact (F.map (e₁.hom ≫ f ≫ e₂.inv)).hom
      (F.map (e₂.hom ≫ g ≫ e₃.inv)).hom := by
  simpa only [Functor.map_comp, Functor.mapIso_hom, Functor.mapIso_inv] using
    exact_iso (F.mapIso e₁) (F.mapIso e₂) (F.mapIso e₃) (F.map f) (F.map g) h

/-- The kernel iteration produces an augmented bicomplex exact on terms and cycles.
Source: Stacks Project, Differential Graded Algebra, Tag 09KP, proof, the successive
short exact sequences before totalization, using Tag 09KN.
(blueprint: lem-pc-derived-free-cover-columns)

Proof. Set `N₀ = M`. Apply `exists_freeComplexCover` to `Nᵢ`, retaining its
short complex `Sᵢ`, map `bᵢ : Sᵢ.X₂ ⟶ Nᵢ`, degreewise and cycle surjectivity,
and split two-step sequence. Put `Pᵢ = Sᵢ.X₂` and take `Nᵢ₊₁ = kernel bᵢ`.
Use `bᵢ₊₁` followed by the kernel inclusion as the map `Pᵢ₊₁ ⟶ Pᵢ`.
Its composite with `bᵢ` is zero. The kernel inclusion is degreewise injective;
the evaluation functors preserve kernels. Degreewise surjectivity of `bᵢ₊₁`
therefore gives exactness at `Pᵢ`. The same argument at `P₀` gives exactness
before the augmentation `b₀`, which is degreewise surjective.

For exactness on cycles, take a cycle in the kernel of the outgoing map. Its
unique lift to the kernel complex is a cycle: apply the injective kernel
inclusion to its differential and use commutation with the differential.
The cycle-surjectivity clause for `bᵢ₊₁` lifts that kernel cycle to a cycle
in `Pᵢ₊₁`. This proves equality of image and kernel on cycles; the other
inclusion follows from the zero composite. The cover of `M` also supplies
surjectivity on cycles at the augmentation.

Place `Pᵢ` at horizontal degree `-i`, set positive columns to the zero complex,
and use the constructed maps for consecutive nonpositive columns and zero
elsewhere. The zero composites give the horizontal complex identities, and
commutation with vertical differentials holds because all maps are cochain maps.
Take `a = b₀`. For each nonpositive column retain `Sᵢ` with its identity
identification of the middle object, its short exactness, all evaluation
splittings, and its two decompositions into coproducts of single copies of `A`.
This construction also works for the zero ring and the zero complex; no
boundedness, finite generation, or nonzero-ring hypothesis is used.
-/
theorem exists_freeCoverColumns {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    ∃ K : HomologicalComplex₂ (ModuleCat.{u} A) (ComplexShape.up ℤ) (ComplexShape.up ℤ),
      ∃ a : K.X 0 ⟶ M,
        (∀ p : ℤ, 0 < p → IsZero (K.X p)) ∧
        (∀ (p q : ℤ), p < -1 →
          Function.Exact ((K.d p (p + 1)).f q).hom ((K.d (p + 1) (p + 2)).f q).hom) ∧
        (∀ q : ℤ, Function.Exact ((K.d (-1) 0).f q).hom (a.f q).hom) ∧
        (∀ q : ℤ, Function.Surjective (a.f q).hom) ∧
        (∀ (p q : ℤ), p < -1 →
          Function.Exact (HomologicalComplex.cyclesMap (K.d p (p + 1)) q).hom
            (HomologicalComplex.cyclesMap (K.d (p + 1) (p + 2)) q).hom) ∧
        (∀ q : ℤ, Function.Exact (HomologicalComplex.cyclesMap (K.d (-1) 0) q).hom
          (HomologicalComplex.cyclesMap a q).hom) ∧
        (∀ q : ℤ, Function.Surjective (HomologicalComplex.cyclesMap a q).hom) ∧
        (∀ p : ℤ, p ≤ 0 →
      ∃ S : ShortComplex (CochainComplex (ModuleCat.{u} A) ℤ),
        Nonempty (S.X₂ ≅ K.X p) ∧ S.ShortExact ∧
        (∀ k : ℤ,
          Nonempty
            (S.map (HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ) k)).Splitting) ∧
        ∃ (I₁ I₃ : Type u) (d₁ : I₁ → ℤ) (d₃ : I₃ → ℤ),
          Nonempty (S.X₁ ≅ ∐ (fun i : I₁ ↦
            (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) (d₁ i)).obj
              (ModuleCat.of A A))) ∧
          Nonempty (S.X₃ ≅ ∐ (fun i : I₃ ↦
            (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) (d₃ i)).obj
              (ModuleCat.of A A)))) := by
  classical
  choose S b hb hc hs ht I₁ I₃ d₁ d₃ h₁ h₃ using
    (fun N : CochainComplex (ModuleCat.{u} A) ℤ ↦ exists_freeComplexCover N)
  let step (T : CochainComplex (ModuleCat.{u} A) ℤ) :
      CochainComplex (ModuleCat.{u} A) ℤ := kernel (b T)
  let N : ℕ → CochainComplex (ModuleCat.{u} A) ℤ :=
    Nat.rec M (fun _ T ↦ step T)
  let P (n : ℕ) : CochainComplex (ModuleCat.{u} A) ℤ := (S (N n)).X₂
  let f (n : ℕ) : P n ⟶ N n := b (N n)
  let i (n : ℕ) : N (n + 1) ⟶ P n := by
    change kernel (b (N n)) ⟶ (S (N n)).X₂
    exact kernel.ι (b (N n))
  let d (n : ℕ) : P (n + 1) ⟶ P n := f (n + 1) ≫ i n
  have hd (n : ℕ) : d (n + 1) ≫ d n = 0 := by
    dsimp [d, i, f]
    simp only [Category.assoc, kernel.condition_assoc, zero_comp, comp_zero]
  let L : ChainComplex (CochainComplex (ModuleCat.{u} A) ℤ) ℕ :=
    ChainComplex.of P d hd
  let K := L.extend ComplexShape.embeddingDownNat
  let e (n : ℕ) : K.X (-(n : ℤ)) ≅ P n :=
    L.extendXIso ComplexShape.embeddingDownNat (by rfl)
  let a : K.X 0 ⟶ M := (e 0).hom ≫ f 0
  have he_d (n : ℕ) : K.d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) =
      (e (n + 1)).hom ≫ d n ≫ (e n).inv := by
    simpa only [K, e, L, ChainComplex.of_d] using
      L.extend_d_eq ComplexShape.embeddingDownNat
        (i := n + 1) (j := n)
        (i' := -((n + 1 : ℕ) : ℤ)) (j' := -(n : ℤ)) rfl rfl
  have hterms (n : ℕ) (q : ℤ) :
      Function.Exact ((d n).f q).hom ((f n).f q).hom := by
    exact exact_pre_surj (kernel_terms (f n) q) (hb (N (n + 1)) q)
  let Z (q : ℤ) := HomologicalComplex.cyclesFunctor (ModuleCat.{u} A) (ComplexShape.up ℤ) q
  have hcycles (n : ℕ) (q : ℤ) :
      Function.Exact ((Z q).map (d n)).hom ((Z q).map (f n)).hom := by
    dsimp only [Z, HomologicalComplex.cyclesFunctor]
    simpa only [d, i, f, id_eq,
      HomologicalComplex.cyclesMap_comp, ModuleCat.hom_comp, LinearMap.coe_comp] using
      exact_pre_surj (kernel_cycles (f n) q) (cycles_surj (f (n + 1)) (hc _) q)
  have hi (n : ℕ) : Mono (i n) := by
    simpa only [i, id_eq] using kernel_mono (b (N n))
  have hi_eval (n : ℕ) (q : ℤ) : Mono ((i n).f q) :=
    Functor.map_mono (HomologicalComplex.eval _ _ q) (i n)
  have hterms₂ (n : ℕ) (q : ℤ) :
      Function.Exact ((d (n + 1)).f q).hom ((d n).f q).hom := by
    exact (hterms (n + 1) q).comp_injective ((i n).f q).hom
      ((ModuleCat.mono_iff_injective _).mp (hi_eval n q)) (map_zero _)
  have hi_cycles (n : ℕ) (q : ℤ) : Mono ((Z q).map (i n)) := by
    dsimp only [Z, HomologicalComplex.cyclesFunctor]
    have := hi_eval n q
    infer_instance
  have hcycles₂ (n : ℕ) (q : ℤ) :
      Function.Exact ((Z q).map (d (n + 1))).hom ((Z q).map (d n)).hom := by
    have h := (hcycles (n + 1) q).comp_injective ((Z q).map (i n)).hom
      ((ModuleCat.mono_iff_injective _).mp (hi_cycles n q)) (map_zero _)
    simp only [d, Functor.map_comp, ModuleCat.hom_comp, LinearMap.coe_comp] at h ⊢
    exact h
  refine ⟨K, a, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact L.isZero_extend_X _ p (by
      intro n
      simp only [ComplexShape.embeddingDownNat_f]
      omega)
  · intro p q hp
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = -((n + 2 : ℕ) : ℤ) :=
      ⟨(-p - 2).toNat, by omega⟩
    have hp₁ : -((n + 2 : ℕ) : ℤ) + 1 = -((n + 1 : ℕ) : ℤ) := by omega
    have hp₂ : -((n + 2 : ℕ) : ℤ) + 2 = -(n : ℤ) := by omega
    rw [hp₁, hp₂, he_d (n + 1), he_d n]
    exact exact_functor_iso (HomologicalComplex.eval _ _ q)
      (e (n + 2)) (e (n + 1)) (e n) (d (n + 1)) (d n) (hterms₂ n q)
  · intro q
    have hd₀ := he_d 0
    change K.d (-1) 0 = (e 1).hom ≫ d 0 ≫ (e 0).inv at hd₀
    rw [hd₀]
    have h := exact_functor_iso (HomologicalComplex.eval _ _ q)
      (e 1) (e 0) (Iso.refl M) (d 0) (f 0) (hterms 0 q)
    dsimp only [HomologicalComplex.eval] at h
    simp only [Iso.refl_inv, Category.comp_id] at h
    exact h
  · intro q
    exact (hb M q).comp ((ModuleCat.epi_iff_surjective ((e 0).hom.f q)).mp
      (inferInstance : Epi ((e 0).hom.f q)))
  · intro p q hp
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = -((n + 2 : ℕ) : ℤ) :=
      ⟨(-p - 2).toNat, by omega⟩
    have hp₁ : -((n + 2 : ℕ) : ℤ) + 1 = -((n + 1 : ℕ) : ℤ) := by omega
    have hp₂ : -((n + 2 : ℕ) : ℤ) + 2 = -(n : ℤ) := by omega
    rw [hp₁, hp₂, he_d (n + 1), he_d n]
    have h := exact_functor_iso (Z q)
      (e (n + 2)) (e (n + 1)) (e n) (d (n + 1)) (d n) (hcycles₂ n q)
    dsimp only [Z, HomologicalComplex.cyclesFunctor] at h
    exact h
  · intro q
    have hd₀ := he_d 0
    change K.d (-1) 0 = (e 1).hom ≫ d 0 ≫ (e 0).inv at hd₀
    rw [hd₀]
    have h := exact_functor_iso (Z q)
      (e 1) (e 0) (Iso.refl M) (d 0) (f 0) (hcycles 0 q)
    simp only [Iso.refl_inv, Category.comp_id] at h
    dsimp only [Z, HomologicalComplex.cyclesFunctor] at h
    exact h
  · intro q
    have hf : Function.Surjective ((Z q).map (f 0)).hom := cycles_surj (b M) (hc M) q
    have he : Function.Surjective ((Z q).map (e 0).hom).hom :=
      (ModuleCat.epi_iff_surjective _).mp (inferInstance : Epi ((Z q).map (e 0).hom))
    have h := hf.comp he
    have ha : (Z q).map a = (Z q).map (e 0).hom ≫ (Z q).map (f 0) :=
      (Z q).map_comp _ _
    have h' : Function.Surjective ((Z q).map a).hom := by
      rw [ha]
      exact h
    dsimp only [Z, HomologicalComplex.cyclesFunctor] at h'
    exact h'
  · intro p hp
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = -(n : ℤ) := ⟨(-p).toNat, by omega⟩
    refine ⟨S (N n), ⟨(e n).symm⟩, hs _, ht _,
      I₁ _, I₃ _, d₁ _, d₃ _, h₁ _, h₃ _⟩


end CochainComplex
