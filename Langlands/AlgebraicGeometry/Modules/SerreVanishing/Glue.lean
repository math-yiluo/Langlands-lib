import Langlands.AlgebraicGeometry.Modules.LineBundleSectionClearingProof
import Langlands.AlgebraicGeometry.Modules.QuasicoherentLocal.Basic

/-! # Gluing lifts of twisted sections from module charts -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Langlands.Scheme.Modules Langlands.SchemeModule Langlands.SchemeModule.SectionClearing
open Langlands.AlgebraicGeometry.Modules.QuasicoherentLocal

namespace Langlands.AlgebraicGeometry.Modules.SerreVanishing

variable {X : Scheme.{u}}

section Systems

variable {N : ℕ → X.Modules} {μ : ∀ m, N m ⟶ N (m + 1)}

/-- Iterated multiplication sends a compatible family of sections to itself. -/
lemma powMul_app_family {W : X.Opens} (p : ∀ m, Γ(N m, W))
    (hp : ∀ m, (μ m).app W (p m) = p (m + 1)) (n k : ℕ) :
    (powMul N μ n k).app W (p n) = p (n + k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [powMul_succ_app, ih]
    exact hp (n + k)

variable {N' : ℕ → X.Modules} {μ' : ∀ m, N' m ⟶ N' (m + 1)}

/-- Morphisms of systems commute with iterated multiplication. -/
lemma powMul_comp_hom (π : ∀ m, N m ⟶ N' m) (hπ : ∀ m, π m ≫ μ' m = μ m ≫ π (m + 1))
    (n k : ℕ) : powMul N μ n k ≫ π (n + k) = π n ≫ powMul N' μ' n k := by
  induction k with
  | zero => exact (Category.id_comp _).trans (Category.comp_id _).symm
  | succ k ih =>
    change (powMul N μ n k ≫ μ (n + k)) ≫ π (n + k + 1) = π n ≫ powMul N' μ' n k ≫ μ' (n + k)
    rw [Category.assoc, ← hπ, ← Category.assoc, ih, Category.assoc]

/-- Morphisms of systems commute with iterated multiplication, on sections. -/
lemma powMul_hom_app (π : ∀ m, N m ⟶ N' m) (hπ : ∀ m, π m ≫ μ' m = μ m ≫ π (m + 1))
    (n k : ℕ) (W : X.Opens) (d : Γ(N n, W)) :
    (π (n + k)).app W ((powMul N μ n k).app W d) =
      (powMul N' μ' n k).app W ((π n).app W d) := by
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, powMul_comp_hom π hπ,
    Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]

end Systems

section ModChart

variable (N : ℕ → X.Modules) (μ : ∀ m, N m ⟶ N (m + 1))

/-- Coordinates for the sections of the `N m` over opens inside `T`, with values in the
sections of a reference module `R`, in which `μ` becomes multiplication by `c`. -/
structure ModChart (R : X.Modules) (T : X.Opens) (c : Γ(X, T)) where
  /-- The coordinate map. -/
  E : ∀ (m : ℕ) (W : X.Opens), W ≤ T → Γ(N m, W) → Γ(R, W)
  injective : ∀ m W hW, Function.Injective (E m W hW)
  surjective : ∀ m W hW, Function.Surjective (E m W hW)
  res : ∀ m (W₁ W₂ : X.Opens) (h₁ : W₁ ≤ T) (h : W₂ ≤ W₁) (d : Γ(N m, W₁)),
    E m W₂ (h.trans h₁) ((N m).presheaf.map (homOfLE h).op d) =
      R.presheaf.map (homOfLE h).op (E m W₁ h₁ d)
  smul : ∀ m W hW (t : Γ(X, W)) (d : Γ(N m, W)), E m W hW (t • d) = t • E m W hW d
  mul : ∀ m W hW (d : Γ(N m, W)),
    E (m + 1) W hW ((μ m).app W d) = X.presheaf.map (homOfLE hW).op c • E m W hW d

namespace ModChart

variable {N μ} {R : X.Modules} {T : X.Opens} {c : Γ(X, T)} (C : ModChart N μ R T c)

include C

/-- Coordinates send zero to zero. -/
lemma E_zero (m : ℕ) (W : X.Opens) (hW : W ≤ T) : C.E m W hW 0 = 0 := by
  have h := C.smul m W hW 0 0
  rwa [zero_smul, zero_smul] at h

/-- In coordinates, `k` multiplications multiply by the `k`-th power of `c`. -/
lemma E_powMul (n k : ℕ) (W : X.Opens) (hW : W ≤ T) (d : Γ(N n, W)) :
    C.E (n + k) W hW ((powMul N μ n k).app W d) =
      (X.presheaf.map (homOfLE hW).op c) ^ k • C.E n W hW d := by
  induction k with
  | zero => rw [pow_zero, one_smul]; rfl
  | succ k ih =>
    show C.E (n + k + 1) W hW ((μ (n + k)).app W ((powMul N μ n k).app W d)) = _
    rw [C.mul, ih, smul_smul, ← pow_succ']

/-- Coordinates of a compatible family of sections. -/
lemma E_family {W₀ : X.Opens} (p : ∀ m, Γ(N m, W₀))
    (hp : ∀ m, (μ m).app W₀ (p m) = p (m + 1)) (m : ℕ) (W : X.Opens) (hW : W ≤ T)
    (hW₀ : W ≤ W₀) :
    C.E m W hW ((N m).presheaf.map (homOfLE hW₀).op (p m)) =
      (X.presheaf.map (homOfLE hW).op c) ^ m •
        C.E 0 W hW ((N 0).presheaf.map (homOfLE hW₀).op (p 0)) := by
  induction m with
  | zero => rw [pow_zero, one_smul]
  | succ m ih =>
    rw [← hp m, ← hom_app_map, C.mul, ih, smul_smul, ← pow_succ']

/-- A section over `W ⊆ T` vanishing on the basic open of `c` is killed by a power of the
multiplication, when the reference module localizes over `W`. -/
lemma exists_powMul_eq_zero {W : X.Opens} (hW : W ≤ T) (hR : IsLocalizingAt R W) {n : ℕ}
    (d : Γ(N n, W))
    (hd : (N n).presheaf.map
      (homOfLE (X.basicOpen_le (X.presheaf.map (homOfLE hW).op c))).op d = 0) :
    ∃ k, (powMul N μ n k).app W d = 0 := by
  obtain ⟨k, hk⟩ := hR.exists_pow_smul_eq_zero (X.presheaf.map (homOfLE hW).op c)
    (C.E n W hW d) (by
      change R.presheaf.map (homOfLE _).op (C.E n W hW d) = 0
      rw [← C.res n W _ hW (X.basicOpen_le _), hd, E_zero])
  exact ⟨k, C.injective (n + k) W hW (by rw [C.E_powMul, hk, E_zero])⟩

omit C

variable {N' : ℕ → X.Modules} {μ' : ∀ m, N' m ⟶ N' (m + 1)} {R' : X.Modules}

/-- On an affine open inside a chart, a compatible family of sections over `X` of the
target system lifts, after a power of the multiplication, to a section that agrees with a
given compatible family of lifts on the basic open. -/
lemma exists_local_lift (C : ModChart N μ R T c) (C' : ModChart N' μ' R' T c)
    (π : ∀ m, N m ⟶ N' m) (ρ : R ⟶ R')
    (hcomp : ∀ m W hW d, C'.E m W hW ((π m).app W d) = ρ.app W (C.E m W hW d))
    {V : X.Opens} (hVT : V ≤ T) (hR : IsLocalizingAt R V) (hR' : IsLocalizingAt R' V)
    (hρ : Function.Surjective (ρ.app V)) (U : X.Opens) (hc : X.basicOpen c = T ⊓ U)
    (p : ∀ m, Γ(N' m, ⊤)) (hp : ∀ m, (μ' m).app ⊤ (p m) = p (m + 1))
    (q : ∀ m, Γ(N m, U)) (hq : ∀ m, (μ m).app U (q m) = q (m + 1))
    (hpq : ∀ m, (π m).app U (q m) = (N' m).presheaf.map (homOfLE le_top).op (p m)) :
    ∃ (n : ℕ) (b : Γ(N n, V)),
      (π n).app V b = (N' n).presheaf.map (homOfLE le_top).op (p n) ∧
      (N n).presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op b =
        (N n).presheaf.map (homOfLE (inf_le_right : V ⊓ U ≤ U)).op (q n) := by
  set h := X.presheaf.map (homOfLE hVT).op c with hh
  have hB : X.basicOpen h = V ⊓ U := by
    rw [hh, Scheme.basicOpen_res, hc, ← inf_assoc, inf_eq_left.mpr hVT]
  have hDV : X.basicOpen h ≤ V := X.basicOpen_le h
  have hDU : X.basicOpen h ≤ U := hB.le.trans inf_le_right
  have hDT : X.basicOpen h ≤ T := hDV.trans hVT
  have ha : X.presheaf.map (homOfLE hDV).op h = X.presheaf.map (homOfLE hDT).op c :=
    presheaf_map_map X hVT hDV c
  set P0 := C'.E 0 V hVT ((N' 0).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (p 0))
  set Q0 := C.E 0 (X.basicOpen h) hDT ((N 0).presheaf.map (homOfLE hDU).op (q 0))
  obtain ⟨y, hy⟩ := hρ P0
  obtain ⟨n₁, t, ht⟩ := hR.exists_res_eq h (R.presheaf.map (homOfLE hDV).op y - Q0)
  replace ht : R.presheaf.map (homOfLE hDV).op t =
      (X.presheaf.map (homOfLE hDV).op h) ^ n₁ • (R.presheaf.map (homOfLE hDV).op y - Q0) :=
    ht
  have hz : ρ.app (X.basicOpen h) (R.presheaf.map (homOfLE hDV).op y - Q0) = 0 := by
    rw [map_sub, hom_app_map ρ hDV y, hy, ← C'.res 0 V _ hVT hDV, modules_map_map,
      ← hcomp 0 _ hDT, hom_app_map, hpq, modules_map_map, sub_self]
  obtain ⟨n₂, hn₂⟩ := hR'.exists_pow_smul_eq_zero h (ρ.app V t) (by
    change R'.presheaf.map (homOfLE hDV).op (ρ.app V t) = 0
    rw [← hom_app_map, ht, Scheme.Modules.Hom.app_smul, hz, smul_zero])
  obtain ⟨b, hb⟩ := C.surjective (n₁ + n₂) V hVT (h ^ (n₁ + n₂) • y - h ^ n₂ • t)
  refine ⟨n₁ + n₂, b, C'.injective _ V hVT ?_, ?_⟩
  · rw [hcomp, hb, map_sub, Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, hn₂,
      sub_zero, hy, C'.E_family p hp _ V hVT le_top]
  · have key : (N (n₁ + n₂)).presheaf.map (homOfLE hDV).op b =
        (N (n₁ + n₂)).presheaf.map (homOfLE hDU).op (q (n₁ + n₂)) := by
      apply C.injective _ _ hDT
      rw [C.res _ V _ hVT hDV, hb, C.E_family q hq _ _ hDT hDU, map_sub,
        Scheme.Modules.map_smul, Scheme.Modules.map_smul, ht, map_pow, map_pow, ha,
        smul_smul, ← pow_add, add_comm n₂ n₁, smul_sub, sub_sub_cancel]
    rw [← modules_map_map (N (n₁ + n₂)) hDV hB.ge b, key, modules_map_map]

end ModChart

/-- Gluing the local lifts provided by module charts around every point: a compatible family
of global sections of the target system, lifted compatibly over `U`, lifts globally after a
power of the multiplication. -/
theorem exists_global_lift [CompactSpace X] {N N' : ℕ → X.Modules}
    {μ : ∀ m, N m ⟶ N (m + 1)} {μ' : ∀ m, N' m ⟶ N' (m + 1)} (π : ∀ m, N m ⟶ N' m)
    (hπ : ∀ m, π m ≫ μ' m = μ m ≫ π (m + 1)) {R R' : X.Modules} (ρ : R ⟶ R') (U : X.Opens)
    (hchart : ∀ x : X, ∃ (T : X.Opens) (c : Γ(X, T)), x ∈ T ∧ X.basicOpen c = T ⊓ U ∧
      ∃ (C : ModChart N μ R T c) (C' : ModChart N' μ' R' T c),
        ∀ m W hW d, C'.E m W hW ((π m).app W d) = ρ.app W (C.E m W hW d))
    (hR : ∀ V : X.Opens, IsAffineOpen V → IsLocalizingAt R V)
    (hR' : ∀ V : X.Opens, IsAffineOpen V → IsLocalizingAt R' V)
    (hρ : ∀ V : X.Opens, IsAffineOpen V → Function.Surjective (ρ.app V))
    (hinf : ∀ V V' : X.Opens, IsAffineOpen V → IsAffineOpen V' → IsAffineOpen (V ⊓ V'))
    (p : ∀ m, Γ(N' m, ⊤)) (hp : ∀ m, (μ' m).app ⊤ (p m) = p (m + 1))
    (q : ∀ m, Γ(N m, U)) (hq : ∀ m, (μ m).app U (q m) = q (m + 1))
    (hpq : ∀ m, (π m).app U (q m) = (N' m).presheaf.map (homOfLE le_top).op (p m)) :
    ∃ (m : ℕ) (a : Γ(N m, ⊤)), (π m).app ⊤ a = p m := by
  choose T c hxT hc C C' hCC' using hchart
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
  -- Step 1: local lifts with a common exponent.
  have h1 : ∀ i : t, ∀ᶠ n in Filter.atTop, ∃ b : Γ(N n, V i.1),
      (π n).app (V i.1) b = (N' n).presheaf.map (homOfLE le_top).op (p n) ∧
      (N n).presheaf.map (homOfLE (inf_le_left : V i.1 ⊓ U ≤ V i.1)).op b =
        (N n).presheaf.map (homOfLE (inf_le_right : V i.1 ⊓ U ≤ U)).op (q n) := fun i => by
    obtain ⟨n₀, b₀, hb₀, hb₀'⟩ := ModChart.exists_local_lift (C i.1) (C' i.1) π ρ (hCC' i.1)
      (hVT i.1) (hR _ (hVa i.1)) (hR' _ (hVa i.1)) (hρ _ (hVa i.1)) U (hc i.1) p hp q hq hpq
    refine Filter.eventually_atTop.2 ⟨n₀, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    refine ⟨(powMul N μ n₀ k).app (V i.1) b₀, ?_, ?_⟩
    · rw [powMul_hom_app π hπ, hb₀, hom_app_map, powMul_app_family p hp]
    · rw [← hom_app_map, hb₀', hom_app_map, powMul_app_family q hq]
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
    have hWT : V i ⊓ V j ≤ T i := inf_le_left.trans (hVT i)
    have hB : X.basicOpen (X.presheaf.map (homOfLE hWT).op (c i)) = V i ⊓ V j ⊓ U := by
      rw [Scheme.basicOpen_res, hc, ← inf_assoc, inf_eq_left.mpr hWT]
    have hd : (N e).presheaf.map (homOfLE (X.basicOpen_le
          (X.presheaf.map (homOfLE hWT).op (c i)))).op
        ((N e).presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (b ⟨i, hi⟩) -
          (N e).presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (b ⟨j, hj⟩)) =
        0 := by
      rw [map_sub, modules_map_map, modules_map_map]
      have e1 := congrArg (fun z => (N e).presheaf.map
        (homOfLE (show X.basicOpen (X.presheaf.map (homOfLE hWT).op (c i)) ≤ V i ⊓ U from
          hB.le.trans (inf_le_inf_right U inf_le_left))).op z) (hb ⟨i, hi⟩).2
      have e2 := congrArg (fun z => (N e).presheaf.map
        (homOfLE (show X.basicOpen (X.presheaf.map (homOfLE hWT).op (c i)) ≤ V j ⊓ U from
          hB.le.trans (inf_le_inf_right U inf_le_right))).op z) (hb ⟨j, hj⟩).2
      simp only [modules_map_map] at e1 e2
      rw [e1, e2, sub_self]
    obtain ⟨k₀, hk₀⟩ := (C i).exists_powMul_eq_zero hWT
      (hR _ (hinf _ _ (hVa i) (hVa j))) _ hd
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
  let F' : TopCat.Sheaf Ab X := ⟨(N' (e + k)).presheaf, (N' (e + k)).isSheaf⟩
  refine F'.eq_of_locally_eq' (fun i : t => V i.1) ⊤ (fun i => homOfLE le_top)
    hcover _ _ (fun i => ?_)
  change (N' (e + k)).presheaf.map (homOfLE le_top).op ((π (e + k)).app ⊤ a) =
    (N' (e + k)).presheaf.map (homOfLE le_top).op (p (e + k))
  have hai : (N (e + k)).presheaf.map (homOfLE (le_top : V i.1 ≤ ⊤)).op a = a' i := ha i
  rw [← hom_app_map, hai, powMul_hom_app π hπ, (hb i).1, hom_app_map,
    powMul_app_family p hp]

end ModChart

end Langlands.AlgebraicGeometry.Modules.SerreVanishing
