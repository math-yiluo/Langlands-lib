import Langlands.AlgebraicGeometry.Modules.LineBundleSectionClearingStatement
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof
import Langlands.AlgebraicGeometry.Modules.PullbackTensorUnitProofs
import Langlands.AlgebraicGeometry.Modules.TensorUnitorLaws
import Langlands.AlgebraicGeometry.Picard.RigidifiedInverse
import Langlands.AlgebraicGeometry.Picard.AffineGenerationLocusIntersectionProof
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Clearing a scalar section on a line-bundle generation open -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Langlands.Scheme.Modules Langlands.AlgebraicGeometry.Picard

set_option backward.isDefEq.respectTransparency false

namespace Langlands.SchemeModule.SectionClearing

variable {X : Scheme.{u}}

/-- Multiplication by a global section `s` of `L`, as a morphism `N ⟶ L ⊗ N`. -/
def sectionMul (L : X.Modules) (s : GlobalSections L) (N : X.Modules) :
    N ⟶ tensorObj L N :=
  (tensorLeftUnitor N).inv ≫ tensorMap (sectionHom L s) (𝟙 N)

/-- Multiplication by `s` between consecutive tensor powers. -/
def sectionMulPow (L : X.Modules) (s : GlobalSections L) (m : ℕ) :
    tensorPow L m ⟶ tensorPow L (m + 1) :=
  sectionMul L s (tensorPow L m)

/-- Multiplying the `m`-th power of `s` by `s` gives the next power. -/
lemma sectionMul_app_sectionPow (L : X.Modules) (s : GlobalSections L) (m : ℕ) :
    (sectionMul L s (tensorPow L m)).app ⊤ (sectionPow L s m) = sectionPow L s (m + 1) := by
  apply sectionHom_injective
  rw [sectionHom_naturality, sectionPow_succ, sectionHom_tensorSection, sectionMul]
  let p : structureSheaf X ⟶ tensorPow L m := sectionHom (tensorPow L m) (sectionPow L s m)
  let σ : structureSheaf X ⟶ L := sectionHom L s
  change p ≫ (tensorLeftUnitor (tensorPow L m)).inv ≫ tensorMap σ (𝟙 (tensorPow L m)) =
    (tensorLeftUnitor (structureSheaf X)).inv ≫ tensorMap σ p
  rw [← Category.assoc, ← Langlands.Scheme.Modules.tensorLeftUnitor_inv_naturality, Category.assoc, tensorMap_comp,
    Category.id_comp, Category.comp_id]

/-! ### Restriction bookkeeping -/

lemma presheaf_map_map (Y : Scheme.{u}) {W₁ W₂ W₃ : Y.Opens} (h₁ : W₂ ≤ W₁) (h₂ : W₃ ≤ W₂)
    (x : Γ(Y, W₁)) :
    Y.presheaf.map (homOfLE h₂).op (Y.presheaf.map (homOfLE h₁).op x) =
      Y.presheaf.map (homOfLE (h₂.trans h₁)).op x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- Restriction of a function to the same open is the identity. -/
lemma presheaf_map_id (Y : Scheme.{u}) {W : Y.Opens} (h : W ≤ W) (x : Γ(Y, W)) :
    Y.presheaf.map (homOfLE h).op x = x := by
  rw [show (homOfLE h).op = 𝟙 (op W) from rfl, CategoryTheory.Functor.map_id]
  rfl

/-- Two restrictions of a module section compose to one restriction. -/
lemma modules_map_map {Y : Scheme.{u}} (M : Y.Modules) {W₁ W₂ W₃ : Y.Opens} (h₁ : W₂ ≤ W₁)
    (h₂ : W₃ ≤ W₂) (d : Γ(M, W₁)) :
    M.presheaf.map (homOfLE h₂).op (M.presheaf.map (homOfLE h₁).op d) =
      M.presheaf.map (homOfLE (h₂.trans h₁)).op d := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restriction of a module section to the same open is the identity. -/
lemma modules_map_id {Y : Scheme.{u}} (M : Y.Modules) {W : Y.Opens} (h : W ≤ W)
    (d : Γ(M, W)) :
    M.presheaf.map (homOfLE h).op d = d := by
  rw [show (homOfLE h).op = 𝟙 (op W) from rfl, CategoryTheory.Functor.map_id]
  rfl

/-- Module morphisms commute with restriction of sections. -/
lemma hom_app_map {Y : Scheme.{u}} {M M' : Y.Modules} (f : M ⟶ M') {W₁ W₂ : Y.Opens}
    (h : W₂ ≤ W₁) (d : Γ(M, W₁)) :
    f.app W₂ (M.presheaf.map (homOfLE h).op d) =
      M'.presheaf.map (homOfLE h).op (f.app W₁ d) :=
  ConcreteCategory.congr_hom (f.mapPresheaf.naturality (homOfLE h).op) d

/-! ### Gluing from local charts -/

section Gluing

variable (N : ℕ → X.Modules) (μ : ∀ m, N m ⟶ N (m + 1))

/-- The iterated multiplication `N n ⟶ N (n + k)`. -/
def powMul (n : ℕ) : (k : ℕ) → (N n ⟶ N (n + k))
  | 0 => 𝟙 (N n)
  | k + 1 => powMul n k ≫ μ (n + k)

/-- One more multiplication step. -/
lemma powMul_succ_app (n k : ℕ) (W : X.Opens) (d : Γ(N n, W)) :
    (powMul N μ n (k + 1)).app W d = (μ (n + k)).app W ((powMul N μ n k).app W d) := rfl

variable {N μ}

/-- Iterated multiplication sends the `n`-th power section to the `(n + k)`-th. -/
lemma powMul_app_top (p : ∀ m, Γ(N m, ⊤)) (hp : ∀ m, (μ m).app ⊤ (p m) = p (m + 1))
    (n k : ℕ) : (powMul N μ n k).app ⊤ (p n) = p (n + k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [powMul_succ_app, ih]
    exact hp (n + k)

/-- Once a power of the multiplication kills a section, all larger powers do. -/
lemma powMul_app_eq_zero_of_le {n k₀ : ℕ} {W : X.Opens} {d : Γ(N n, W)}
    (h : (powMul N μ n k₀).app W d = 0) {k : ℕ} (hk : k₀ ≤ k) :
    (powMul N μ n k).app W d = 0 := by
  induction k, hk using Nat.le_induction with
  | base => exact h
  | succ k _ ih => rw [powMul_succ_app, ih, map_zero]

/-- Multiplying a local solution by powers of the section gives local solutions. -/
lemma powMul_good (p : ∀ m, Γ(N m, ⊤)) (hp : ∀ m, (μ m).app ⊤ (p m) = p (m + 1))
    (U : X.Opens) (r : Γ(X, U)) {V : X.Opens} {n : ℕ} (b : Γ(N n, V))
    (hb : (N n).presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op b =
      X.presheaf.map (homOfLE (inf_le_right : V ⊓ U ≤ U)).op r •
        (N n).presheaf.map (homOfLE (le_top : V ⊓ U ≤ ⊤)).op (p n)) (k : ℕ) :
    (N (n + k)).presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op
        ((powMul N μ n k).app V b) =
      X.presheaf.map (homOfLE (inf_le_right : V ⊓ U ≤ U)).op r •
        (N (n + k)).presheaf.map (homOfLE (le_top : V ⊓ U ≤ ⊤)).op (p (n + k)) := by
  rw [← hom_app_map, hb, Scheme.Modules.Hom.app_smul, hom_app_map, powMul_app_top p hp]

variable (N μ) in
/-- Coordinates for the sections of the `N m` over opens inside `T`, in which `μ` becomes
multiplication by `c`. -/
structure LocalChart (T : X.Opens) (c : Γ(X, T)) where
  /-- The coordinate map. -/
  E : ∀ (m : ℕ) (W : X.Opens), W ≤ T → Γ(N m, W) → Γ(X, W)
  injective : ∀ m W hW, Function.Injective (E m W hW)
  surjective : ∀ m W hW, Function.Surjective (E m W hW)
  res : ∀ m (W₁ W₂ : X.Opens) (h₁ : W₁ ≤ T) (h : W₂ ≤ W₁) (d : Γ(N m, W₁)),
    E m W₂ (h.trans h₁) ((N m).presheaf.map (homOfLE h).op d) =
      X.presheaf.map (homOfLE h).op (E m W₁ h₁ d)
  smul : ∀ m W hW (t : Γ(X, W)) (d : Γ(N m, W)), E m W hW (t • d) = t * E m W hW d
  mul : ∀ m W hW (d : Γ(N m, W)),
    E (m + 1) W hW ((μ m).app W d) = E m W hW d * X.presheaf.map (homOfLE hW).op c

namespace LocalChart

variable {T : X.Opens} {c : Γ(X, T)} (C : LocalChart N μ T c)

include C

/-- Coordinates send zero to zero. -/
lemma E_zero (m : ℕ) (W : X.Opens) (hW : W ≤ T) : C.E m W hW 0 = 0 := by
  have h := C.smul m W hW 0 0
  rwa [zero_smul, zero_mul] at h

/-- In coordinates, `k` multiplications multiply by the `k`-th power of `c`. -/
lemma E_powMul (n k : ℕ) (W : X.Opens) (hW : W ≤ T) (d : Γ(N n, W)) :
    C.E (n + k) W hW ((powMul N μ n k).app W d) =
      C.E n W hW d * (X.presheaf.map (homOfLE hW).op c) ^ k := by
  induction k with
  | zero => rw [pow_zero, mul_one]; rfl
  | succ k ih =>
    show C.E (n + k + 1) W hW ((μ (n + k)).app W ((powMul N μ n k).app W d)) = _
    rw [C.mul, ih, pow_succ, mul_assoc]

/-- Coordinates of the power sections. -/
lemma E_pow (p : ∀ m, Γ(N m, ⊤)) (hp : ∀ m, (μ m).app ⊤ (p m) = p (m + 1))
    (m : ℕ) (W : X.Opens) (hW : W ≤ T) :
    C.E m W hW ((N m).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (p m)) =
      C.E 0 W hW ((N 0).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (p 0)) *
        (X.presheaf.map (homOfLE hW).op c) ^ m := by
  induction m with
  | zero => rw [pow_zero, mul_one]
  | succ m ih =>
    rw [← hp m, ← hom_app_map, C.mul, ih, pow_succ, mul_assoc]

/-- A section vanishing on `W ∩ U` is killed by a power of the section. -/
lemma exists_powMul_eq_zero (U : X.Opens) (hc : X.basicOpen c = T ⊓ U)
    {W : X.Opens} (hW : W ≤ T) (hWc : IsCompact (W : Set X)) {n : ℕ} (d : Γ(N n, W))
    (hd : (N n).presheaf.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op d = 0) :
    ∃ k, (powMul N μ n k).app W d = 0 := by
  have hB : X.basicOpen (X.presheaf.map (homOfLE hW).op c) = W ⊓ U := by
    rw [Scheme.basicOpen_res, hc, ← inf_assoc, inf_eq_left.mpr hW]
  have h0 : (C.E n W hW d) |_ (X.basicOpen (X.presheaf.map (homOfLE hW).op c)) = 0 := by
    change X.presheaf.map (homOfLE (X.basicOpen_le _)).op (C.E n W hW d) = 0
    rw [← C.res n W _ hW (X.basicOpen_le _)]
    have : (N n).presheaf.map (homOfLE (X.basicOpen_le
        (X.presheaf.map (homOfLE hW).op c))).op d = 0 := by
      rw [← modules_map_map (N n) (inf_le_left : W ⊓ U ≤ W) hB.le, hd, map_zero]
    rw [this, E_zero]
  obtain ⟨k, hk⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X hWc _ _ h0
  refine ⟨k, C.injective (n + k) W hW ?_⟩
  rw [C.E_powMul, E_zero, mul_comm, hk]

/-- On an affine open inside the chart, `r` is cleared by a power of the section. -/
lemma exists_local (p : ∀ m, Γ(N m, ⊤)) (hp : ∀ m, (μ m).app ⊤ (p m) = p (m + 1))
    (U : X.Opens) (hc : X.basicOpen c = T ⊓ U) {V : X.Opens} (hV : IsAffineOpen V)
    (hVT : V ≤ T) (r : Γ(X, U)) :
    ∃ (n : ℕ) (b : Γ(N n, V)), (N n).presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op b =
      X.presheaf.map (homOfLE (inf_le_right : V ⊓ U ≤ U)).op r •
        (N n).presheaf.map (homOfLE (le_top : V ⊓ U ≤ ⊤)).op (p n) := by
  have hB : X.basicOpen (X.presheaf.map (homOfLE hVT).op c) = V ⊓ U := by
    rw [Scheme.basicOpen_res, hc, ← inf_assoc, inf_eq_left.mpr hVT]
  obtain ⟨n, y, hy⟩ := exists_eq_pow_mul_of_isAffineOpen X V hV
    (X.presheaf.map (homOfLE hVT).op c)
    (X.presheaf.map (homOfLE (hB.le.trans inf_le_right)).op r)
  have hy' : X.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op y =
      (X.presheaf.map (homOfLE (inf_le_left.trans hVT : V ⊓ U ≤ T)).op c) ^ n *
        X.presheaf.map (homOfLE (inf_le_right : V ⊓ U ≤ U)).op r := by
    have := congrArg (fun z => X.presheaf.map (homOfLE hB.ge).op z) hy
    dsimp only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict] at this
    simp only [map_mul, map_pow, presheaf_map_map] at this
    exact this
  have hu : C.E 0 (V ⊓ U) (inf_le_left.trans hVT)
      ((N 0).presheaf.map (homOfLE (le_top : V ⊓ U ≤ ⊤)).op (p 0)) =
      X.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op
        (C.E 0 V hVT ((N 0).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (p 0))) := by
    rw [← C.res 0 V (V ⊓ U) hVT inf_le_left, modules_map_map]
  obtain ⟨b, hb⟩ := C.surjective n V hVT
    (y * C.E 0 V hVT ((N 0).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (p 0)))
  refine ⟨n, b, C.injective n (V ⊓ U) (inf_le_left.trans hVT) ?_⟩
  rw [C.res n V (V ⊓ U) hVT inf_le_left, hb, C.smul, C.E_pow p hp n (V ⊓ U), hu, map_mul, hy']
  ring

end LocalChart

/-- Gluing the local solutions provided by charts around every point. -/
theorem exists_global_of_charts [CompactSpace X] [QuasiSeparatedSpace X]
    (p : ∀ m, Γ(N m, ⊤)) (hp : ∀ m, (μ m).app ⊤ (p m) = p (m + 1)) (U : X.Opens)
    (hchart : ∀ x : X, ∃ (T : X.Opens) (c : Γ(X, T)), x ∈ T ∧ X.basicOpen c = T ⊓ U ∧
      Nonempty (LocalChart N μ T c))
    (r : Γ(X, U)) :
    ∃ (m : ℕ) (a : Γ(N m, ⊤)), (N m).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op a =
      r • (N m).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (p m) := by
  choose T c hxT hc hC using hchart
  have hV : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ T x := fun x => by
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVT⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (hxT x) (T x).2
    exact ⟨V, hV, hxV, hVT⟩
  choose V hVa hxV hVT using hV
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X))
    (fun x => (V x).2) (fun x _ => Set.mem_iUnion.2 ⟨x, hxV x⟩)
  have hcov : ∀ y : X, ∃ i : t, y ∈ V i.1 := fun y => by
    have hy := ht (Set.mem_univ y)
    simp only [Set.mem_iUnion] at hy
    obtain ⟨x, hx, hyx⟩ := hy
    exact ⟨⟨x, hx⟩, hyx⟩
  -- Step 1: local solutions with a common exponent.
  have h1 : ∀ i : t, ∀ᶠ n in Filter.atTop, ∃ b : Γ(N n, V i.1),
      (N n).presheaf.map (homOfLE (inf_le_left : V i.1 ⊓ U ≤ V i.1)).op b =
        X.presheaf.map (homOfLE (inf_le_right : V i.1 ⊓ U ≤ U)).op r •
          (N n).presheaf.map (homOfLE (le_top : V i.1 ⊓ U ≤ ⊤)).op (p n) := fun i => by
    obtain ⟨n₀, b₀, hb₀⟩ :=
      (hC i.1).some.exists_local p hp U (hc i.1) (hVa i.1) (hVT i.1) r
    refine Filter.eventually_atTop.2 ⟨n₀, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact ⟨_, powMul_good p hp U r b₀ hb₀ k⟩
  obtain ⟨e, he⟩ := (Filter.eventually_all.2 h1).exists
  choose b hb using he
  -- Step 2: kill the differences on the overlaps.
  have h2 : ∀ ij : t × t, ∀ᶠ k in Filter.atTop,
      (powMul N μ e k).app (V ij.1.1 ⊓ V ij.2.1)
        ((N e).presheaf.map (homOfLE (inf_le_left : V ij.1.1 ⊓ V ij.2.1 ≤ V ij.1.1)).op
            (b ij.1) -
          (N e).presheaf.map (homOfLE (inf_le_right : V ij.1.1 ⊓ V ij.2.1 ≤ V ij.2.1)).op
            (b ij.2)) = 0 := fun ij => by
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := ij
    have hcpt : IsCompact ((V i ⊓ V j : X.Opens) : Set X) :=
      (hVa i).isCompact.inter_of_isOpen (hVa j).isCompact (V i).2 (V j).2
    have hd : (N e).presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ⊓ U ≤ V i ⊓ V j)).op
        ((N e).presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (b ⟨i, hi⟩) -
          (N e).presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (b ⟨j, hj⟩)) =
        0 := by
      rw [map_sub, modules_map_map, modules_map_map]
      have e1 := congrArg (fun z => (N e).presheaf.map
        (homOfLE (show V i ⊓ V j ⊓ U ≤ V i ⊓ U from
          inf_le_inf_right U inf_le_left)).op z) (hb ⟨i, hi⟩)
      have e2 := congrArg (fun z => (N e).presheaf.map
        (homOfLE (show V i ⊓ V j ⊓ U ≤ V j ⊓ U from
          inf_le_inf_right U inf_le_right)).op z) (hb ⟨j, hj⟩)
      simp only [modules_map_map, Scheme.Modules.map_smul, presheaf_map_map] at e1 e2
      rw [e1, e2, sub_self]
    obtain ⟨k₀, hk₀⟩ := (hC i).some.exists_powMul_eq_zero U (hc i)
      (inf_le_left.trans (hVT i)) hcpt _ hd
    exact Filter.eventually_atTop.2 ⟨k₀, fun k hk => powMul_app_eq_zero_of_le hk₀ hk⟩
  obtain ⟨k, hk⟩ := (Filter.eventually_all.2 h2).exists
  -- Step 3: glue.
  let F : TopCat.Sheaf Ab X := ⟨(N (e + k)).presheaf, (N (e + k)).isSheaf⟩
  let a' : ∀ i : t, Γ(N (e + k), V i.1) := fun i => (powMul N μ e k).app (V i.1) (b i)
  have hcompat : TopCat.Presheaf.IsCompatible F.1 (fun i : t => V i.1) a' := by
    intro i j
    have := hk (i, j)
    rw [map_sub, sub_eq_zero, hom_app_map, hom_app_map] at this
    exact this
  have hcover : (⊤ : X.Opens) ≤ iSup (fun i : t => V i.1) := by
    intro y _
    obtain ⟨i, hi⟩ := hcov y
    exact Opens.mem_iSup.2 ⟨i, hi⟩
  obtain ⟨a, ha, -⟩ := F.existsUnique_gluing' (fun i : t => V i.1) ⊤
    (fun i => homOfLE le_top) hcover a' hcompat
  refine ⟨e + k, a, ?_⟩
  have hcoverU : U ≤ iSup (fun i : t => V i.1 ⊓ U) := by
    intro y hy
    obtain ⟨i, hi⟩ := hcov y
    exact Opens.mem_iSup.2 ⟨i, hi, hy⟩
  refine F.eq_of_locally_eq' (fun i : t => V i.1 ⊓ U) U (fun i => homOfLE inf_le_right)
    hcoverU _ _ (fun i => ?_)
  change (N (e + k)).presheaf.map (homOfLE inf_le_right).op
      ((N (e + k)).presheaf.map (homOfLE le_top).op a) =
    (N (e + k)).presheaf.map (homOfLE inf_le_right).op
      (r • (N (e + k)).presheaf.map (homOfLE le_top).op (p (e + k)))
  have hai : (N (e + k)).presheaf.map (homOfLE (le_top : V i.1 ≤ ⊤)).op a = a' i := ha i
  rw [modules_map_map, Scheme.Modules.map_smul, modules_map_map,
    ← modules_map_map (N (e + k)) (le_top : V i.1 ≤ ⊤) inf_le_left, hai]
  exact powMul_good p hp U r (b i) (hb i) k

end Gluing

/-! ### Charts from trivializations of all the `N m` over an open -/

section Casts

variable {Y : Scheme.{u}}

/-- A section of the structure module, viewed as a function. -/
def toT {W : Y.Opens} (z : Γ(structureSheaf Y, W)) : Γ(Y, W) := z

/-- A function, viewed as a section of the structure module. -/
def ofT {W : Y.Opens} (z : Γ(Y, W)) : Γ(structureSheaf Y, W) := z

/-- The two casts are inverse. -/
lemma toT_ofT {W : Y.Opens} (z : Γ(Y, W)) : toT (ofT z) = z := rfl

/-- The module action on the structure module is multiplication. -/
lemma toT_smul {W : Y.Opens} (r : Γ(Y, W)) (z : Γ(structureSheaf Y, W)) :
    toT (r • z) = r * toT z := rfl

/-- Restriction in the structure module is restriction of functions. -/
lemma toT_map {W₁ W₂ : Y.Opens} (h : W₂ ≤ W₁) (z : Γ(structureSheaf Y, W₁)) :
    toT ((structureSheaf Y).presheaf.map (homOfLE h).op z) =
      Y.presheaf.map (homOfLE h).op (toT z) := rfl

/-- An endomorphism of the structure module multiplies by its coefficient. -/
lemma toT_app (φ : structureSheaf Y ⟶ structureSheaf Y) (W : Y.Opens)
    (z : Γ(structureSheaf Y, W)) :
    toT (φ.app W z) =
      toT z * Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (unitEndCoefficient φ ⊤) := by
  exact (unitEndCoefficient_app φ W (toT z)).trans (congrArg (fun k => toT z * k)
    (unitEndCoefficient_res φ (homOfLE (le_top : W ≤ ⊤))))

variable {T : X.Opens}

/-- A section over the image of an open of `T`, viewed as a section of the restriction. -/
def ofImage (M : X.Modules) {W' : T.toScheme.Opens} (d : Γ(M, T.ι ''ᵁ W')) :
    Γ(M.restrict T.ι, W') := d

/-- A section of the restriction, viewed as a section over the image. -/
def toImage (M : X.Modules) {W' : T.toScheme.Opens} (d : Γ(M.restrict T.ι, W')) :
    Γ(M, T.ι ''ᵁ W') := d

/-- The two casts are inverse. -/
lemma ofImage_toImage (M : X.Modules) {W' : T.toScheme.Opens} (d : Γ(M.restrict T.ι, W')) :
    ofImage M (toImage M d) = d := rfl

/-- Restriction maps of the restricted module are those of the module. -/
lemma ofImage_map (M : X.Modules) {W₁' W₂' : T.toScheme.Opens} (h : W₂' ≤ W₁')
    (d : Γ(M, T.ι ''ᵁ W₁')) :
    ofImage M (M.presheaf.map (homOfLE (T.ι.image_mono h)).op d) =
      (M.restrict T.ι).presheaf.map (homOfLE h).op (ofImage M d) := rfl

/-- Restricted morphisms act on sections as the original morphisms. -/
lemma ofImage_app {M M' : X.Modules} (f : M ⟶ M') {W' : T.toScheme.Opens}
    (d : Γ(M, T.ι ''ᵁ W')) :
    ofImage M' (f.app (T.ι ''ᵁ W') d) =
      ((Scheme.Modules.restrictFunctor T.ι).map f).app W' (ofImage M d) := rfl

/-- The action of functions on sections of the restricted module. -/
lemma ofImage_smul (M : X.Modules) {W' : T.toScheme.Opens} (t : Γ(X, T.ι ''ᵁ W'))
    (d : Γ(M, T.ι ''ᵁ W')) :
    ofImage M (t • d) = (T.ι.appIso W').hom t • ofImage M d := by
  change _ = ofImage M ((T.ι.appIso W').inv ((T.ι.appIso W').hom t) • d)
  rw [Iso.hom_inv_id_apply]

/-- Naturality of the identification of functions on `T` with functions on `X`. -/
lemma appIso_inv_res {W₁' W₂' : T.toScheme.Opens} (h : W₂' ≤ W₁')
    (x : Γ(T.toScheme, W₁')) :
    (T.ι.appIso W₂').inv (T.toScheme.presheaf.map (homOfLE h).op x) =
      X.presheaf.map (homOfLE (T.ι.image_mono h)).op ((T.ι.appIso W₁').inv x) :=
  ConcreteCategory.congr_hom (T.ι.appIso_inv_naturality (homOfLE h).op) x

end Casts

section RestrictChart

variable {T : X.Opens}

/-- An open inside `T` lies in the image of its preimage. -/
lemma le_image_preimage {W : X.Opens} (hW : W ≤ T) : W ≤ T.ι ''ᵁ (T.ι ⁻¹ᵁ W) := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact le_inf hW le_rfl

variable {M : X.Modules} (Ψ : M.restrict T.ι ≅ structureSheaf T.toScheme)

/-- The coordinate of a section of `M` over an open inside `T`. -/
def chartE (W : X.Opens) (hW : W ≤ T) (d : Γ(M, W)) : Γ(X, W) :=
  X.presheaf.map (homOfLE (le_image_preimage hW)).op ((T.ι.appIso (T.ι ⁻¹ᵁ W)).inv
    (toT (Ψ.hom.app (T.ι ⁻¹ᵁ W)
      (ofImage M (M.presheaf.map (homOfLE (T.ι.image_preimage_le W)).op d)))))

/-- The section of `M` with a given coordinate. -/
def chartF (W : X.Opens) (hW : W ≤ T) (z : Γ(X, W)) : Γ(M, W) :=
  M.presheaf.map (homOfLE (le_image_preimage hW)).op (toImage M (Ψ.inv.app (T.ι ⁻¹ᵁ W)
    (ofT ((T.ι.appIso (T.ι ⁻¹ᵁ W)).hom
      (X.presheaf.map (homOfLE (T.ι.image_preimage_le W)).op z)))))

/-- `chartF` is a right inverse of `chartE`. -/
lemma chartE_chartF (W : X.Opens) (hW : W ≤ T) (z : Γ(X, W)) :
    chartE Ψ W hW (chartF Ψ W hW z) = z := by
  unfold chartE chartF
  rw [modules_map_map, modules_map_id, ofImage_toImage]
  have h : ∀ y, Ψ.hom.app (T.ι ⁻¹ᵁ W) (Ψ.inv.app (T.ι ⁻¹ᵁ W) y) = y := fun y => by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.inv_hom_id]
    rfl
  rw [h, toT_ofT, Iso.hom_inv_id_apply, presheaf_map_map, presheaf_map_id]

/-- `chartF` is a left inverse of `chartE`. -/
lemma chartF_chartE (W : X.Opens) (hW : W ≤ T) (d : Γ(M, W)) :
    chartF Ψ W hW (chartE Ψ W hW d) = d := by
  unfold chartE chartF
  rw [presheaf_map_map, presheaf_map_id, Iso.inv_hom_id_apply]
  have h : ∀ y, toImage M (Ψ.inv.app (T.ι ⁻¹ᵁ W) (ofT (toT (Ψ.hom.app (T.ι ⁻¹ᵁ W)
      (ofImage M y))))) = y := fun y => by
    change Ψ.inv.app (T.ι ⁻¹ᵁ W) (Ψ.hom.app (T.ι ⁻¹ᵁ W) (ofImage M y)) = ofImage M y
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id]
    rfl
  rw [h, modules_map_map, modules_map_id]

/-- Coordinates commute with restriction. -/
lemma chartE_res (W₁ W₂ : X.Opens) (h₁ : W₁ ≤ T) (h : W₂ ≤ W₁) (d : Γ(M, W₁)) :
    chartE Ψ W₂ (h.trans h₁) (M.presheaf.map (homOfLE h).op d) =
      X.presheaf.map (homOfLE h).op (chartE Ψ W₁ h₁ d) := by
  unfold chartE
  have h' : T.ι ⁻¹ᵁ W₂ ≤ T.ι ⁻¹ᵁ W₁ := T.ι.preimage_mono h
  rw [modules_map_map, ← modules_map_map M (T.ι.image_preimage_le W₁) (T.ι.image_mono h'),
    ofImage_map M h', hom_app_map Ψ.hom h', toT_map h', appIso_inv_res h', presheaf_map_map,
    presheaf_map_map]

/-- Coordinates are linear over functions. -/
lemma chartE_smul (W : X.Opens) (hW : W ≤ T) (t : Γ(X, W)) (d : Γ(M, W)) :
    chartE Ψ W hW (t • d) = t * chartE Ψ W hW d := by
  unfold chartE
  rw [Scheme.Modules.map_smul, ofImage_smul, Scheme.Modules.Hom.app_smul, toT_smul, map_mul,
    Iso.hom_inv_id_apply, map_mul, presheaf_map_map, presheaf_map_id]

end RestrictChart

section LocalChartOf

variable {N : ℕ → X.Modules} {μ : ∀ m, N m ⟶ N (m + 1)} {T : X.Opens}
  (Ψ : ∀ m, (N m).restrict T.ι ≅ structureSheaf T.toScheme)
  (φ : structureSheaf T.toScheme ⟶ structureSheaf T.toScheme)
  (hΨ : ∀ m, (Scheme.Modules.restrictFunctor T.ι).map (μ m) ≫ (Ψ (m + 1)).hom =
    (Ψ m).hom ≫ φ)

/-- The coefficient of an endomorphism of `𝒪_T`, as a function on `T ⊆ X`. -/
def chartCoeff : Γ(X, T) :=
  X.presheaf.map (homOfLE T.ι_image_top.ge).op ((T.ι.appIso ⊤).inv (unitEndCoefficient φ ⊤))

/-- The chart coefficient is the coefficient transported by `topIso`. -/
lemma chartCoeff_eq : chartCoeff φ = T.topIso.hom (unitEndCoefficient φ ⊤) := by
  unfold chartCoeff
  rw [Scheme.Opens.ι_appIso, Scheme.Opens.topIso_hom]
  rfl

include hΨ in
/-- In coordinates, `μ` is multiplication by the chart coefficient. -/
lemma chartE_mul (m : ℕ) (W : X.Opens) (hW : W ≤ T) (d : Γ(N m, W)) :
    chartE (Ψ (m + 1)) W hW ((μ m).app W d) =
      chartE (Ψ m) W hW d * X.presheaf.map (homOfLE hW).op (chartCoeff φ) := by
  unfold chartE chartCoeff
  have h : ∀ y, (Ψ (m + 1)).hom.app (T.ι ⁻¹ᵁ W)
      (((Scheme.Modules.restrictFunctor T.ι).map (μ m)).app (T.ι ⁻¹ᵁ W) y) =
      φ.app (T.ι ⁻¹ᵁ W) ((Ψ m).hom.app (T.ι ⁻¹ᵁ W) y) := fun y => by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, hΨ m]
    rfl
  rw [← hom_app_map, ofImage_app, h, toT_app, map_mul, appIso_inv_res, map_mul,
    presheaf_map_map, presheaf_map_map]

/-- The chart built from compatible trivializations of all the `N m` over `T`. -/
def localChartOf : LocalChart N μ T (chartCoeff φ) where
  E m W hW := chartE (Ψ m) W hW
  injective m W hW := Function.LeftInverse.injective (chartF_chartE (Ψ m) W hW)
  surjective m W hW := Function.RightInverse.surjective (chartE_chartF (Ψ m) W hW)
  res m W₁ W₂ h₁ h d := chartE_res (Ψ m) W₁ W₂ h₁ h d
  smul m W hW t d := chartE_smul (Ψ m) W hW t d
  mul m W hW d := chartE_mul Ψ φ hΨ m W hW d

end LocalChartOf

/-! ### Compatible trivializations of the tensor powers -/

section Trivialization

variable (T : X.Opens) (L : X.Modules)
  (e : L.restrict T.ι ≅ SheafOfModules.unit T.toScheme.ringCatSheaf)

/-- The pullback tensor comparison along an open inclusion, as an isomorphism. -/
def pullbackTensorIso (M N : X.Modules) :
    (Scheme.Modules.pullback T.ι).obj (tensorObj M N) ≅
      tensorObj ((Scheme.Modules.pullback T.ι).obj M)
        ((Scheme.Modules.pullback T.ι).obj N) :=
  haveI := pullbackTensorComparisonIsIso T.ι
  (asIso (pullbackTensorComparison T.ι)).app (M, N)

/-- The trivialization of the pulled-back module. -/
def pullbackTriv : (Scheme.Modules.pullback T.ι).obj L ≅ structureSheaf T.toScheme :=
  ((Scheme.Modules.restrictFunctorIsoPullback T.ι).app L).symm ≪≫ e

/-- A morphism `𝒪_X ⟶ L` read in the trivialization. -/
def chartMulOf (σ : structureSheaf X ⟶ L) :
    structureSheaf T.toScheme ⟶ structureSheaf T.toScheme :=
  (pullbackUnitIso T.ι).inv ≫ (Scheme.Modules.pullback T.ι).map σ ≫ (pullbackTriv T L e).hom

/-- The induced trivializations of the pulled-back tensor powers. -/
def powTriv : (m : ℕ) →
    ((Scheme.Modules.pullback T.ι).obj (tensorPow L m) ≅ structureSheaf T.toScheme)
  | 0 => pullbackUnitIso T.ι
  | m + 1 => pullbackTensorIso T L (tensorPow L m) ≪≫
      (tensorFunctor T.toScheme).mapIso ((pullbackTriv T L e).prod (powTriv m)) ≪≫
      tensorLeftUnitor (structureSheaf T.toScheme)

/-- In the trivializations, tensoring with `σ` becomes the endomorphism `chartMulOf σ`. -/
lemma pullback_mul_comp (σ : structureSheaf X ⟶ L) (N : X.Modules)
    (Θ : (Scheme.Modules.pullback T.ι).obj N ≅ structureSheaf T.toScheme) :
    (Scheme.Modules.pullback T.ι).map ((tensorLeftUnitor N).inv ≫ tensorMap σ (𝟙 N)) ≫
      pullbackTensorComparisonApp T.ι L N ≫ tensorMap (pullbackTriv T L e).hom Θ.hom ≫
        (tensorLeftUnitor (structureSheaf T.toScheme)).hom =
    Θ.hom ≫ chartMulOf T L e σ := by
  have hU := pullbackTensorLeftUnitor T.toScheme X T.ι N
  have hA : tensorMap (pullbackUnitIso T.ι).hom (𝟙 ((Scheme.Modules.pullback T.ι).obj N)) ≫
      tensorMap (pullbackUnitIso T.ι).inv (𝟙 ((Scheme.Modules.pullback T.ι).obj N)) =
      𝟙 _ := by
    rw [tensorMap_comp, Iso.hom_inv_id, Category.id_comp]
    exact (tensorFunctor _).map_id _
  have hU' : (Scheme.Modules.pullback T.ι).map (tensorLeftUnitor N).inv ≫
      pullbackTensorComparisonApp T.ι (structureSheaf X) N =
      (tensorLeftUnitor ((Scheme.Modules.pullback T.ι).obj N)).inv ≫
        tensorMap (pullbackUnitIso T.ι).inv (𝟙 ((Scheme.Modules.pullback T.ι).obj N)) := by
    calc _ = (Scheme.Modules.pullback T.ι).map (tensorLeftUnitor N).inv ≫
          (pullbackTensorComparisonApp T.ι (structureSheaf X) N ≫
            tensorMap (pullbackUnitIso T.ι).hom (𝟙 ((Scheme.Modules.pullback T.ι).obj N)) ≫
            (tensorLeftUnitor ((Scheme.Modules.pullback T.ι).obj N)).hom) ≫
          (tensorLeftUnitor ((Scheme.Modules.pullback T.ι).obj N)).inv ≫
            tensorMap (pullbackUnitIso T.ι).inv
              (𝟙 ((Scheme.Modules.pullback T.ι).obj N)) := by
          simp only [Category.assoc, Iso.hom_inv_id_assoc, hA]
          exact congrArg (fun g => (Scheme.Modules.pullback T.ι).map (tensorLeftUnitor N).inv ≫ g)
            (Category.comp_id _).symm
      _ = _ := by
          rw [hU, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
            CategoryTheory.Functor.map_id, Category.id_comp]
  have hnat := pullbackTensorComparisonApp_naturality T.ι σ (𝟙 N)
  have hT : tensorMap (pullbackUnitIso T.ι).inv (𝟙 ((Scheme.Modules.pullback T.ι).obj N)) ≫
      tensorMap ((Scheme.Modules.pullback T.ι).map σ)
        ((Scheme.Modules.pullback T.ι).map (𝟙 N)) ≫
      tensorMap (pullbackTriv T L e).hom Θ.hom =
      tensorMap (𝟙 (structureSheaf T.toScheme)) Θ.hom ≫
        tensorMap (chartMulOf T L e σ) (𝟙 (structureSheaf T.toScheme)) := by
    rw [tensorMap_comp, tensorMap_comp, tensorMap_comp, CategoryTheory.Functor.map_id]
    simp only [Category.id_comp, Category.comp_id]
    rfl
  rw [Functor.map_comp, Category.assoc, reassoc_of% hnat, reassoc_of% hU', reassoc_of% hT,
    ← Category.assoc, Langlands.Scheme.Modules.tensorLeftUnitor_inv_naturality, tensorUnitors_equal,
    tensorRightUnitor_naturality, ← tensorUnitors_equal, Category.assoc,
    Iso.inv_hom_id_assoc]

/-- The trivializations of the restricted tensor powers. -/
def chartIso (m : ℕ) : (tensorPow L m).restrict T.ι ≅ structureSheaf T.toScheme :=
  (Scheme.Modules.restrictFunctorIsoPullback T.ι).app (tensorPow L m) ≪≫ powTriv T L e m

/-- Multiplication by `s` is `chartMulOf (sectionHom L s)` in the trivializations. -/
lemma chartIso_succ (s : GlobalSections L) (m : ℕ) :
    (Scheme.Modules.restrictFunctor T.ι).map (sectionMulPow L s m) ≫
        (chartIso T L e (m + 1)).hom =
      (chartIso T L e m).hom ≫ chartMulOf T L e (sectionHom L s) := by
  simp only [chartIso, Iso.trans_hom, Iso.app_hom]
  rw [← Category.assoc, (Scheme.Modules.restrictFunctorIsoPullback T.ι).hom.naturality,
    Category.assoc, Category.assoc]
  congr 1
  exact pullback_mul_comp T L e (sectionHom L s) (tensorPow L m) (powTriv T L e m)

end Trivialization

/-- On a trivializing open, the generation open of a line-bundle section is the basic open
of the chart coefficient. -/
theorem basicOpen_chartCoeff (T : X.Opens) (L : LineBundle X) (s : GlobalSections L.obj)
    (e : L.obj.restrict T.ι ≅ SheafOfModules.unit T.toScheme.ringCatSheaf) :
    X.basicOpen (chartCoeff (chartMulOf T L.obj e (sectionHom L.obj s))) =
      T ⊓ trivializationOpen L.obj s := by
  have hψ (y : T.toScheme) :
      IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} y).map
        (chartMulOf T L.obj e (sectionHom L.obj s)).mapPresheaf) ↔
        IsStalkFrame L.obj s (T.ι y) := by
    have hdecomp : chartMulOf T L.obj e (sectionHom L.obj s) =
        ((pullbackUnitIso T.ι).inv ≫
          ((Scheme.Modules.restrictFunctorIsoPullback T.ι).app _).inv) ≫
          (Scheme.Modules.restrictFunctor T.ι).map (sectionHom L.obj s) ≫ e.hom := by
      unfold chartMulOf pullbackTriv
      simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Category.assoc]
      rw [NatTrans.naturality_assoc]
    change IsIso (((Scheme.Modules.toPresheaf T.toScheme) ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} y).map
        (chartMulOf T L.obj e (sectionHom L.obj s))) ↔ _
    rw [hdecomp]
    simp only [Functor.map_comp, isIso_comp_left_iff, isIso_comp_right_iff]
    exact isIso_stalk_restrict_iff (sectionHom L.obj s) T y
  have hframe (x : X) : IsStalkFrame L.obj s x ↔ x ∈ trivializationOpen L.obj s :=
    Set.ext_iff.mp (lineBundle_stalkFrame_set_eq L s) x
  rw [chartCoeff_eq, ← Scheme.Opens.ι_image_basicOpen_topIso_inv, Iso.hom_inv_id_apply]
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact ⟨y.2, (hframe _).mp ((hψ y).mp ((unitEnd_stalkIso_iff_mem_basicOpen _ y).mpr hy))⟩
  · rintro x ⟨hxW, hxs⟩
    refine ⟨⟨x, hxW⟩, ?_, rfl⟩
    exact (unitEnd_stalkIso_iff_mem_basicOpen _ _).mp ((hψ _).mpr ((hframe x).mpr hxs))

end Langlands.SchemeModule.SectionClearing

namespace Langlands.SchemeModule

open SectionClearing

/-- Clearing a regular function on the generation open of a line-bundle section by a power
of the section, on a quasi-compact quasi-separated scheme. -/
theorem lineBundleSectionClearing : LineBundleSectionClearingStatement.{u} := by
  intro X _ _ L s r
  refine exists_global_of_charts (N := tensorPow L.obj)
    (μ := sectionMulPow L.obj s) (sectionPow L.obj s)
    (sectionMul_app_sectionPow L.obj s) _ ?_ r
  intro x
  obtain ⟨T, hxT, ⟨e⟩⟩ := L.property x
  exact ⟨T, _, hxT, basicOpen_chartCoeff T L s e,
    ⟨localChartOf (fun m => chartIso T L.obj e m) _ (chartIso_succ T L.obj e s)⟩⟩

end Langlands.SchemeModule
