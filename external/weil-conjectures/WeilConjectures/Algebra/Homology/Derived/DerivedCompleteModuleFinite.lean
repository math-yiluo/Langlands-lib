/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.DerivedCompleteModuleComplex
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Module.Torsion.Basic
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import WeilConjectures.RingTheory.FiniteModuleComplete
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Finiteness of derived-complete modules with finite residue

Source: Stacks Project, More on Algebra, Tag 09BA (`lemma-derived-complete-finite`),
specialized to an `I`-adically complete Noetherian ring
(blueprint: lem-weil-derived-complete-module-finite).
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace ModuleCat

private def sequenceDifference {A : Type u} [CommRing A]
    {M : Type v} [AddCommGroup M] [Module A M] (f : A) :
    (ℕ → M) →ₗ[A] (ℕ → M) where
  toFun a n := a n - f • a (n + 1)
  map_add' a b := by ext n; simp [smul_add, sub_add_sub_comm]
  map_smul' r a := by
    ext n
    change r • a n - f • (r • a (n + 1)) = r • (a n - f • a (n + 1))
    rw [smul_sub, smul_comm f r]

private theorem difference_quotient {A : Type u} [CommRing A]
    {M : Type v} [AddCommGroup M] [Module A M] (N : Submodule A M) (f : A)
    (hM : Function.Bijective (sequenceDifference (M := M) f))
    (hN : Function.Bijective (sequenceDifference (M := N) f)) :
    Function.Bijective (sequenceDifference (M := M ⧸ N) f) := by
  classical
  have hzero : ∀ a : ℕ → M ⧸ N, sequenceDifference f a = 0 → a = 0 := by
    intro a ha
    choose x hx using fun n ↦ N.mkQ_surjective (a n)
    have hxN (n : ℕ) : sequenceDifference f x n ∈ N := by
      apply (Submodule.Quotient.mk_eq_zero N).mp
      change N.mkQ (x n - f • x (n + 1)) = 0
      rw [map_sub, map_smul, hx, hx]
      exact congrFun ha n
    obtain ⟨y, hy⟩ := hN.2 (fun n ↦ ⟨sequenceDifference f x n, hxN n⟩)
    have hxy : sequenceDifference f (x - fun n ↦ (y n : M)) = 0 := by
      ext n
      have hn := congrArg Subtype.val (congrFun hy n)
      change (x n - (y n : M)) - f • (x (n + 1) - (y (n + 1) : M)) = 0
      change (y n : M) - f • (y (n + 1) : M) = x n - f • x (n + 1) at hn
      calc
        _ = (x n - f • x (n + 1)) -
            ((y n : M) - f • (y (n + 1) : M)) := by rw [smul_sub]; abel
        _ = 0 := sub_eq_zero.mpr hn.symm
    have he := hM.1 (show sequenceDifference f (x - fun n ↦ (y n : M)) =
        sequenceDifference f 0 by simpa using hxy)
    ext n
    have hn : x n = (y n : M) := sub_eq_zero.mp (congrFun he n)
    rw [← hx n, hn]
    exact (Submodule.Quotient.mk_eq_zero N).mpr (y n).property
  constructor
  · intro a b hab
    have hz : sequenceDifference f (a - b) = 0 := by rw [map_sub, hab, sub_self]
    exact sub_eq_zero.mp (hzero _ hz)
  · intro b
    choose x hx using fun n ↦ N.mkQ_surjective (b n)
    obtain ⟨a, ha⟩ := hM.2 x
    refine ⟨fun n ↦ N.mkQ (a n), ?_⟩
    ext n
    have hn := congrArg N.mkQ (congrFun ha n)
    simpa [sequenceDifference, map_sub, map_smul, hx] using hn

private theorem difference_range {A : Type u} [CommRing A]
    {X M : Type v} [AddCommGroup X] [Module A X] [AddCommGroup M] [Module A M]
    (g : X →ₗ[A] M) (f : A)
    (hX : Function.Bijective (sequenceDifference (M := X) f))
    (hM : Function.Bijective (sequenceDifference (M := M) f)) :
    Function.Bijective (sequenceDifference (M := LinearMap.range g) f) := by
  constructor
  · intro a b hab
    have heq := congrArg (fun z : ℕ → LinearMap.range g ↦ fun n ↦ (z n : M)) hab
    have he : (fun n ↦ (a n : M)) = (fun n ↦ (b n : M)) := hM.1 heq
    ext n
    exact congrFun he n
  · intro b
    choose x hx using fun n ↦ (b n).property
    obtain ⟨a, ha⟩ := hX.2 x
    refine ⟨fun n ↦ ⟨g (a n), a n, rfl⟩, ?_⟩
    ext n
    have hn := congrArg g (congrFun ha n)
    simpa [sequenceDifference, map_sub, map_smul, hx] using hn

private theorem zero_of_surjective_smul {A : Type u} [CommRing A]
    {M : Type v} [AddCommGroup M] [Module A M] (f : A)
    (hM : Function.Injective (sequenceDifference (M := M) f))
    (hsurj : Function.Surjective (fun x : M ↦ f • x)) : Subsingleton M := by
  classical
  choose pre hpre using hsurj
  change ∀ x, f • pre x = x at hpre
  have hzero (m : M) : m = 0 := by
    let a : ℕ → M := fun n ↦ pre^[n] m
    have ha : sequenceDifference f a = 0 := by
      ext n
      change pre^[n] m - f • pre^[n + 1] m = 0
      rw [Function.iterate_succ_apply', hpre, sub_self]
    have he := hM (show sequenceDifference f a = sequenceDifference f 0 by simpa using ha)
    exact congrFun he 0
  exact ⟨fun x y ↦ (hzero x).trans (hzero y).symm⟩

private theorem sequence_nakayama {A : Type u} [CommRing A]
    (I : Ideal A) (s : Finset A) (hs : ∀ f ∈ s, f ∈ I)
    (M : Type v) [AddCommGroup M] [Module A M]
    (hM : ∀ f ∈ I, Function.Bijective (sequenceDifference (M := M) f))
    (hgen : (Ideal.span (s : Set A)) • (⊤ : Submodule A M) = ⊤) :
    Subsingleton M := by
  classical
  induction s using Finset.induction generalizing M with
  | empty =>
    have he : (⊥ : Submodule A M) = ⊤ := by simpa using hgen
    refine ⟨fun x y ↦ sub_eq_zero.mp ?_⟩
    have hz : x - y ∈ (⊥ : Submodule A M) := by rw [he]; trivial
    exact hz
  | @insert f s hfs ih =>
    let g : M →ₗ[A] M := f • LinearMap.id
    let N := LinearMap.range g
    have hQ : ∀ a ∈ I,
        Function.Bijective (sequenceDifference (M := M ⧸ N) a) := by
      intro a ha
      exact difference_quotient N a (hM a ha) (difference_range g a (hM a ha) (hM a ha))
    have hfN (x : M) : f • x ∈ N := ⟨x, rfl⟩
    have heN : (Ideal.span {f}) • (⊤ : Submodule A M) ≤ N := by
      rw [Submodule.smul_le]
      intro r hr x hx
      induction hr using Submodule.span_induction with
      | mem r hr => simpa only [Set.mem_singleton_iff.mp hr] using hfN x
      | zero => simp
      | add r t hr ht ir it => simpa [add_smul] using N.add_mem ir it
      | smul a r hr ir => simpa [mul_smul] using N.smul_mem a ir
    have hgenQ : (Ideal.span (s : Set A)) • (⊤ : Submodule A (M ⧸ N)) = ⊤ := by
      have he := congrArg (Submodule.map N.mkQ) hgen
      rw [Finset.coe_insert, Ideal.span_insert, Submodule.sup_smul, Submodule.map_sup,
        Submodule.map_smul'', Submodule.map_smul'', Submodule.map_top,
        Submodule.range_mkQ] at he
      have hz : ((Ideal.span {f}) • (⊤ : Submodule A M)).map N.mkQ = ⊥ := by
        apply le_antisymm
        · exact (Submodule.map_le_iff_le_comap).mpr (by simpa using heN)
        · exact bot_le
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at hz
      rwa [hz, bot_sup_eq] at he
    have : Subsingleton (M ⧸ N) := ih (fun a ha ↦ hs a (Finset.mem_insert_of_mem ha))
      (M ⧸ N) hQ hgenQ
    apply zero_of_surjective_smul f (hM f (hs f (Finset.mem_insert_self f s))).1
    intro x
    have hx : x ∈ N := (Submodule.Quotient.mk_eq_zero N).mp (Subsingleton.elim _ _)
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, hy⟩

private theorem difference_of_complete {A : Type u} [CommRing A]
    (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M] [IsAdicComplete I M]
    (f : A) (hf : f ∈ I) : Function.Bijective (sequenceDifference (M := M) f) := by
  classical
  constructor
  · suffices hz : ∀ a : ℕ → M, sequenceDifference f a = 0 → a = 0 by
      intro a b hab
      exact sub_eq_zero.mp (hz (a - b) (by rw [map_sub, hab, sub_self]))
    intro a ha
    have he (n k : ℕ) : a n = f ^ k • a (n + k) := by
      induction k generalizing n with
      | zero => simp
      | succ k ih =>
        have hn : a n = f • a (n + 1) := sub_eq_zero.mp (congrFun ha n)
        rw [hn, ih (n + 1), ← mul_smul, ← pow_succ']
        congr 2; omega
    ext n
    apply IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := I) (M := M))
    intro k
    apply SModEq.zero.mpr
    rw [he n k]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow hf k) Submodule.mem_top
  · intro b
    let S (n k : ℕ) : M := ∑ j ∈ Finset.range k, f ^ j • b (n + j)
    have hc (n : ℕ) : ∀ k l, k ≤ l →
        S n k ≡ S n l [SMOD (I ^ k • ⊤ : Submodule A M)] := by
      intro k l hkl
      rw [SModEq.sub_mem]
      dsimp [S]
      rw [← Nat.add_sub_of_le hkl, Finset.sum_range_add, ← sub_sub, sub_self,
        zero_sub, neg_mem_iff]
      apply Submodule.sum_mem
      intro j hj
      rw [pow_add, mul_smul]
      exact Submodule.smul_mem_smul (Ideal.pow_mem_pow hf k) Submodule.mem_top
    choose a ha using fun n ↦ IsPrecomplete.prec
      (IsAdicComplete.toIsPrecomplete (I := I) (M := M))
      (f := S n) (fun {k l} h ↦ hc n k l h)
    refine ⟨a, ?_⟩
    ext n
    change a n - f • a (n + 1) = b n
    rw [IsHausdorff.eq_iff_smodEq (I := I)]
    intro k
    have hs : S n (k + 1) = b n + f • S (n + 1) k := by
      simp only [S, Finset.sum_range_succ', pow_zero, one_smul, Nat.add_zero,
        Finset.smul_sum, pow_succ', mul_smul]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Nat.add_left_comm, Nat.add_comm]
    have h1 : S n (k + 1) ≡ a n [SMOD (I ^ k • ⊤ : Submodule A M)] :=
      (ha n (k + 1)).mono (Submodule.pow_smul_top_le I M k.le_succ)
    calc
      a n - f • a (n + 1) ≡ S n (k + 1) - f • S (n + 1) k
          [SMOD (I ^ k • ⊤ : Submodule A M)] := h1.symm.sub ((ha (n + 1) k).smul f).symm
      _ = b n := by rw [hs]; abel

private theorem finite_of_difference {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    (M : Type v) [AddCommGroup M] [Module A M]
    (hM : ∀ f ∈ I, Function.Bijective (sequenceDifference (M := M) f))
    (hfinite : Module.Finite (A ⧸ I) (M ⧸ (I • ⊤ : Submodule A M))) :
    Module.Finite A M := by
  classical
  let P : Submodule A M := I • ⊤
  let : Module.Finite (A ⧸ I) (M ⧸ P) := hfinite
  let : Module.Finite A (M ⧸ P) := Module.Finite.trans (A ⧸ I) (M ⧸ P)
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule A (M ⧸ P)).FG)
  choose pre hpre using P.mkQ_surjective
  change ∀ x, Submodule.Quotient.mk (pre x) = x at hpre
  let t : Finset M := s.image pre
  let N : Submodule A M := Submodule.span A (t : Set M)
  have hN : N.FG := ⟨t, rfl⟩
  have hmap : N.map P.mkQ = ⊤ := by
    simpa [N, t, Submodule.map_span, Set.image_image, Function.comp_def, hpre] using hs
  have hsum : N ⊔ P = ⊤ := by
    have he := congrArg (Submodule.comap P.mkQ) hmap
    simpa [Submodule.comap_map_eq, sup_comm] using he
  let : Module.Finite A N := Module.Finite.of_fg hN
  let : IsAdicComplete I N := finite_module_complete_over_complete_noetherian A I N
  have hQN : ∀ f ∈ I, Function.Bijective (sequenceDifference (M := M ⧸ N) f) := by
    intro f hf
    exact difference_quotient N f (hM f hf) (difference_of_complete I N f hf)
  have hgenQ : I • (⊤ : Submodule A (M ⧸ N)) = ⊤ := by
    have he := congrArg (Submodule.map N.mkQ) hsum
    simpa [P, Submodule.map_sup, Submodule.map_smul''] using he
  obtain ⟨r, hr⟩ := (isNoetherianRing_iff_ideal_fg A).mp inferInstance I
  have hzero : Subsingleton (M ⧸ N) :=
    sequence_nakayama I r (fun f hf ↦ hr ▸ Submodule.subset_span hf)
      (M ⧸ N) hQN (hr ▸ hgenQ)
  have htop : N = ⊤ := (Submodule.Quotient.subsingleton_iff (p := N)).mp hzero
  exact Module.Finite.of_fg_top (htop ▸ hN)

private theorem module_countableAB4Star {A : Type u} [CommRing A] :
    CountableAB4Star (ModuleCat.{v} A) := by
  let F := forget₂ (ModuleCat.{v} A) AddCommGrpCat.{v}
  let : F.PreservesEpimorphisms := ⟨fun {X Y} f _ ↦ by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    exact (ModuleCat.epi_iff_surjective f).mp inferInstance⟩
  let := Functor.preservesHomology_of_preservesEpis_and_kernels F
  let := Functor.preservesFiniteColimits_of_preservesHomology F
  exact ⟨fun J ↦ HasExactLimitsOfShape.domain_of_functor (Discrete J) F⟩

set_option backward.isDefEq.respectTransparency false in
private theorem difference_of_derived_complete {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{v} A)] (I : Ideal A)
    (M : Type v) [AddCommGroup M] [Module A M]
    (hM : IsDerivedComplete I (ModuleCat.of A M)) (f : A) (hf : f ∈ I) :
    Function.Bijective (sequenceDifference (M := M) f) := by
  classical
  let : CountableAB4Star (ModuleCat.{v} A) := module_countableAB4Star
  obtain ⟨hP, hprops⟩ := derivedCategory_countableProducts_and_towerLimit (ModuleCat.{v} A)
  let := hP
  let F := DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0
  let G := DerivedCategory.singleFunctor (ModuleCat.{v} A) 0
  let K := G.obj (ModuleCat.of A M)
  let _ : Limits.PreservesLimitsOfShape (Discrete ℕ) F := hprops.2.1 ℕ 0
  let d := towerTransitionEndomorphism (K := fun _ : ℕ ↦ K) (fun _ ↦ f • 𝟙 K)
  have hd : IsIso d := by
    obtain ⟨L, p, δ, hT⟩ := Pretriangulated.distinguished_cocone_triangle₁ d
    exact (Pretriangulated.Triangle.isZero₁_iff_isIso₂ _ hT).mp
      (hM f hf L ⟨p, δ, hT⟩)
  let e : F.obj K ≅ ModuleCat.of A M :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{v} A) 0).app _
  let E : F.obj (Limits.piObj (fun _ : ℕ ↦ K)) ≅ ModuleCat.of A (ℕ → M) :=
    Limits.PreservesProduct.iso F (fun _ : ℕ ↦ K) ≪≫
      Limits.Pi.mapIso (fun _ : ℕ ↦ e) ≪≫ ModuleCat.piIsoPi (fun _ : ℕ ↦ ModuleCat.of A M)
  have hE (n : ℕ) : E.hom ≫ ModuleCat.ofHom (LinearMap.proj n) =
      F.map (Limits.Pi.π (fun _ : ℕ ↦ K) n) ≫ e.hom := by
    simp [E, Category.assoc]
  have hnat : F.map (f • 𝟙 K) ≫ e.hom = e.hom ≫ (f • 𝟙 (ModuleCat.of A M)) := by
    have hn := (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{v} A) 0).hom.naturality (f • 𝟙 (ModuleCat.of A M))
    simpa [F, G, K, e, Functor.map_smul] using hn
  have hconj : E.inv ≫ F.map d ≫ E.hom = ModuleCat.ofHom (sequenceDifference f) := by
    apply (cancel_epi E.hom).mp
    simp only [Iso.hom_inv_id_assoc]
    apply ModuleCat.hom_ext
    ext a n
    have hn := congrArg (fun k ↦ k.hom a) (show
        F.map d ≫ E.hom ≫ ModuleCat.ofHom (LinearMap.proj n) =
          E.hom ≫ ModuleCat.ofHom (LinearMap.proj n) -
            E.hom ≫ ModuleCat.ofHom (LinearMap.proj (n + 1)) ≫
              (f • 𝟙 (ModuleCat.of A M)) by
      rw [hE, ← Category.assoc, ← F.map_comp, (towerTransitionEndomorphism_eq_iff _ d).mp rfl n,
        F.map_sub, F.map_comp, Preadditive.sub_comp, Category.assoc, hnat,
        ← hE, ← Category.assoc, ← hE, Category.assoc])
    simpa [sequenceDifference] using hn
  have : IsIso (ModuleCat.ofHom (sequenceDifference (M := M) f)) := by
    rw [← hconj]
    infer_instance
  exact (ConcreteCategory.isIso_iff_bijective _).mp this

/-- Over a complete Noetherian ring, a derived-complete module with finite reduction
modulo the ideal is finite, and its canonical map to its adic completion is bijective.
The completion consists of compatible residue classes, with componentwise operations.
Source: Stacks Project, More on Algebra, Tag 09BA (`lemma-derived-complete-finite`),
specialized to a complete ring (blueprint: lem-weil-derived-complete-module-finite).

Proof:
1. Exact countable products of modules give countable products in the derived category,
   preserved by cohomology, by `lemma-reduction-derived-nakayama`. Complete the tower
   endomorphism `1 - s` to a Roos triangle. Derived completeness makes its first vertex
   zero, hence `1 - s` is invertible. Apply degree-zero cohomology and identify the
   product of degree-zero modules with sequences: the resulting invertible linear map
   is `Δ_f(a)_n = a_n - f • a_(n+1)` for each `f ∈ I`.
2. Bijectivity of `Δ_f` passes to the range of a map between two modules satisfying it:
   lift a sequence in the range, solve upstairs, and apply the map. It also passes to
   a quotient by a submodule satisfying it: lift a sequence, and solve its difference
   in the submodule to prove injectivity; solve a lift to prove surjectivity.
3. An ordinarily complete module satisfies this bijectivity: the Cauchy partial sums
   `sum_{j<k} f^j • b_(n+j)` converge to a solution, and separatedness makes the kernel
   zero. This is the geometric-series argument of Stacks, Tag 091R.
4. For a finite generating set of an ideal, induct by quotienting out the range of
   multiplication by its first generator. The quotient still satisfies all the
   sequence conditions by step 2. If the ideal times the module is the whole module,
   induction makes this quotient zero. Multiplication by the first generator is then
   surjective; iterating a choice of preimage of any element produces a sequence in
   the kernel of `Δ_f`, so the original module is zero. The empty set case is immediate.
   This is the derived Nakayama argument of Stacks, Tag 09B9, in sequence form.
5. Lift a finite set of residue generators and let `N` be their finite span in `M`.
   The existing finite-module completion theorem makes `N` ordinarily complete, so
   steps 1--3 give the sequence conditions on `M/N`. Residue generation gives
   `I • (M/N) = M/N`. Noetherianity and step 4 give `M/N = 0`, hence `N = M` is finite.
6. Apply `lem-weil-pbc-finite-module-complete-over-complete-noetherian` to `M` and
   translate ordinary completeness to bijectivity of `AdicCompletion.of I M`. -/
theorem finite_and_completion_bijective_of_isDerivedComplete
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [HasDerivedCategory.{w} (ModuleCat.{v} A)] (I : Ideal A)
    (hA : Function.Bijective (AdicCompletion.of I A))
    (M : Type v) [AddCommGroup M] [Module A M]
    (hM : IsDerivedComplete I (ModuleCat.of A M))
    (hfinite : Module.Finite (A ⧸ I) (M ⧸ (I • ⊤ : Submodule A M))) :
    Module.Finite A M ∧ Function.Bijective (AdicCompletion.of I M) := by
  let : IsAdicComplete I A := AdicCompletion.of_bijective_iff.mp hA
  have hfin : Module.Finite A M := finite_of_difference I M
    (fun f hf ↦ difference_of_derived_complete I M hM f hf) hfinite
  let : Module.Finite A M := hfin
  let : IsAdicComplete I M := finite_module_complete_over_complete_noetherian A I M
  exact ⟨hfin, AdicCompletion.of_bijective_iff.mpr inferInstance⟩

end ModuleCat
