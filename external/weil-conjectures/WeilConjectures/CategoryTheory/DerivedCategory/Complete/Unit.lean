/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Module.Injective
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.Algebra.Homology.DerivedCategory.InjectiveHom
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Perfect
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# A complete ring is derived complete

Let `R` be a principal ideal domain which is `ϖ`-adically complete. This file shows that the
complex `R[0]` of `D(R)` receives no nonzero morphism from an object on which `ϖ` acts
invertibly (`DerivedCategory.eq_zero_of_isIso_smul_of_singleFunctor`): in the terminology of
`DerivedCategory.derivedComplete_iff_rightOrthogonal`, `R` is derived `ϖ`-complete.

## Main statements

- `Module.exists_comp_eq_of_bijective_smul`: for a short exact sequence `0 ⟶ R ⟶ K ⟶ Q ⟶ 0` of
  `R`-modules, every map `V ⟶ Q` from a module on which `ϖ` acts bijectively lifts to `K`. This
  is where the completeness of `R` enters: it says `Ext¹_R(V, R) ⟶ Ext¹_R(V, K)` is injective.
- `DerivedCategory.eq_zero_of_homologyFunctor_map_eq_zero`,
  `DerivedCategory.exists_homologyFunctor_map_eq`: for an injective object `J`, morphisms
  `L ⟶ J[0]` of the derived category are the morphisms `H⁰(L) ⟶ J`.
- `DerivedCategory.eq_zero_of_isIso_smul_of_singleFunctor`: the statement above.

## Implementation notes

The proof uses the injective resolution `0 ⟶ R ⟶ K ⟶ K/R ⟶ 0`, with `K` the fraction field. A
morphism `f : L ⟶ R[0]` composed with `R ⟶ K` is determined by `H⁰(f) : H⁰(L) ⟶ R`, which
vanishes as `H⁰(L)` is `ϖ`-divisible and `R` is `ϖ`-adically separated. So `f` comes from a
morphism `L⟦1⟧ ⟶ (K/R)[0]`, which is determined by a map `H¹(L) ⟶ K/R`; that map lifts to `K`,
so `f` factors through two consecutive maps of a distinguished triangle and vanishes.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Pretriangulated

namespace Module

variable {R : Type*} [CommRing R]

/-- Over a principal ideal domain, a module in which every element is divisible by every
nonzero scalar is injective (Baer's criterion). -/
theorem injective_of_divisible [IsDomain R] [IsPrincipalIdealRing R] (D : Type*)
    [AddCommGroup D] [Module R D] (hD : ∀ r : R, r ≠ 0 → ∀ y : D, ∃ x : D, r • x = y) :
    Module.Injective R D := by
  refine Module.Baer.injective fun I g ↦ ?_
  obtain ⟨a, rfl⟩ := (IsPrincipalIdealRing.principal I).principal
  by_cases ha : a = 0
  · refine ⟨0, fun x hx ↦ ?_⟩
    have hx0 : x = 0 := by
      rw [ha] at hx
      simpa using hx
    subst hx0
    rw [LinearMap.zero_apply, ← g.map_zero]
    rfl
  obtain ⟨y, hy⟩ := hD a ha (g ⟨a, Submodule.mem_span_singleton_self a⟩)
  refine ⟨LinearMap.toSpanSingleton R D y, fun x hx ↦ ?_⟩
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hx
  rw [LinearMap.toSpanSingleton_apply, smul_assoc, hy, ← g.map_smul]
  rfl

variable {ϖ : R}

/-- A linear map from a module on which `ϖ` acts bijectively to a `ϖ`-adically separated
module vanishes: its image consists of infinitely `ϖ`-divisible elements. -/
theorem eq_zero_of_bijective_smul {V W : Type*} [AddCommGroup V] [Module R V] [AddCommGroup W]
    [Module R W] [IsHausdorff (Ideal.span {ϖ}) W] (hV : Function.Bijective fun v : V ↦ ϖ • v)
    (f : V →ₗ[R] W) : f = 0 := by
  ext v
  refine IsHausdorff.haus' (I := Ideal.span {ϖ}) _ fun n ↦ ?_
  rw [SModEq.zero, Ideal.span_singleton_pow]
  have hdiv (n : ℕ) (v : V) : ∃ w : V, ϖ ^ n • w = v := by
    induction n generalizing v with
    | zero => exact ⟨v, by rw [pow_zero, one_smul]⟩
    | succ n ih =>
      obtain ⟨w, rfl⟩ := hV.2 v
      obtain ⟨w', rfl⟩ := ih w
      exact ⟨w', by rw [pow_succ', mul_smul]⟩
  obtain ⟨w, rfl⟩ := hdiv n v
  rw [map_smul]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

variable [IsAdicComplete (Ideal.span {ϖ}) R] {K Q V : Type*} [AddCommGroup K] [Module R K]
  [AddCommGroup Q] [Module R Q] [AddCommGroup V] [Module R V]

/-- Let `R` be `ϖ`-adically complete and `0 ⟶ R ⟶ K ⟶ Q ⟶ 0` a short exact sequence of
`R`-modules. Every map `g : V ⟶ Q` from a module on which `ϖ` acts bijectively lifts to `K`.

For `v ∈ V` with `ϖ`-power roots `vₙ = ϖ⁻ⁿ v`, lift `g(vₙ)` to `yₙ ∈ K`; the defects
`ϖ yₙ₊₁ - yₙ` lie in `R`, and by completeness the lifts can be corrected to a compatible system
`zₙ` (`ϖ zₙ₊₁ = zₙ`), unique by separatedness. The lift is `v ↦ z₀`. -/
theorem exists_comp_eq_of_bijective_smul (ι : R →ₗ[R] K) (π : K →ₗ[R] Q)
    (hι : Function.Injective ι) (hπ : Function.Surjective π) (hex : LinearMap.ker π = ι.range)
    (hV : Function.Bijective fun v : V ↦ ϖ • v) (g : V →ₗ[R] Q) :
    ∃ h : V →ₗ[R] K, π ∘ₗ h = g := by
  let e : V ≃ₗ[R] V := LinearEquiv.ofBijective (ϖ • LinearMap.id) hV
  have he (v : V) : ϖ • e.symm v = v := e.apply_symm_apply v
  -- the `ϖ`-power roots of `v`
  let r (v : V) : ℕ → V := fun n ↦ (e.symm ^ n) v
  have hr (v : V) (n : ℕ) : ϖ • r v (n + 1) = r v n := by
    simp only [r]
    rw [pow_succ', LinearEquiv.mul_apply, he]
  have hr_add (v w : V) (n : ℕ) : r (v + w) n = r v n + r w n := map_add _ _ _
  have hr_smul (c : R) (v : V) (n : ℕ) : r (c • v) n = c • r v n := map_smul _ _ _
  -- compatible lifts
  let P (v : V) (z : ℕ → K) : Prop := (∀ n, π (z n) = g (r v n)) ∧ ∀ n, ϖ • z (n + 1) = z n
  have hmemι {x : K} (hx : π x = 0) : ∃ c, ι c = x := by
    have : x ∈ LinearMap.ker π := hx
    rwa [hex] at this
  have hexists (v : V) : ∃ z, P v z := by
    choose y hy using fun n ↦ hπ (g (r v n))
    choose c hc using fun n ↦ hmemι (x := ϖ • y (n + 1) - y n) (by
      rw [map_sub, map_smul, hy, hy, ← map_smul, hr, sub_self])
    obtain ⟨s, hs⟩ := exists_eq_add_mul_succ (ϖ := ϖ) c
    refine ⟨fun n ↦ y n + ι (s n), fun n ↦ ?_, fun n ↦ ?_⟩
    · rw [map_add, hy]
      have : π (ι (s n)) = 0 := by
        rw [← LinearMap.mem_ker, hex]
        exact ⟨s n, rfl⟩
      rw [this, add_zero]
    · have h1 : ι (s n) = ι (c n) + ϖ • ι (s (n + 1)) := by
        rw [hs n, map_add, ← map_smul, smul_eq_mul]
      beta_reduce
      rw [smul_add, h1, hc]
      abel
  have hunique (v : V) (z z' : ℕ → K) (hz : P v z) (hz' : P v z') : z 0 = z' 0 := by
    choose d hd using fun n ↦ hmemι (x := z n - z' n) (by rw [map_sub, hz.1, hz'.1, sub_self])
    have hd' (n : ℕ) : d n = ϖ * d (n + 1) := by
      apply hι
      rw [hd, ← smul_eq_mul, map_smul, hd, smul_sub, hz.2, hz'.2]
    have hpow (n : ℕ) : d 0 = ϖ ^ n * d n := by
      induction n with
      | zero => rw [pow_zero, one_mul]
      | succ n ih => rw [ih, hd' n, pow_succ, mul_assoc]
    have h0 : d 0 = 0 := by
      refine IsHausdorff.haus' (I := Ideal.span {ϖ}) _ fun n ↦ ?_
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton]
      exact ⟨d n, hpow n⟩
    rw [← sub_eq_zero, ← hd, h0, map_zero]
  choose z hz using hexists
  refine ⟨{ toFun := fun v ↦ z v 0, map_add' := fun v w ↦ ?_, map_smul' := fun c v ↦ ?_ }, ?_⟩
  · refine hunique (v + w) _ (fun n ↦ z v n + z w n) (hz _) ⟨fun n ↦ ?_, fun n ↦ ?_⟩
    · rw [map_add, (hz v).1, (hz w).1, hr_add, map_add]
    · rw [smul_add, (hz v).2, (hz w).2]
  · refine hunique (c • v) _ (fun n ↦ c • z v n) (hz _) ⟨fun n ↦ ?_, fun n ↦ ?_⟩
    · rw [map_smul, (hz v).1, hr_smul, map_smul]
    · rw [smul_comm, (hz v).2]
  · ext v
    have := (hz v).1 0
    simpa [r] using this

end Module

namespace DerivedCategory

section Injective

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

open TStructure

variable {J : C} [Injective J]

/-- A morphism `L ⟶ J[0]` to an injective object placed in degree `0` is determined by its
effect on `H⁰`. -/
lemma eq_zero_of_homologyFunctor_map_eq_zero {L : DerivedCategory C}
    (φ : L ⟶ (singleFunctor C 0).obj J) (h : (homologyFunctor C 0).map φ = 0) : φ = 0 := by
  have h₁ : (t.truncLTι 1).app L ≫ φ = 0 := by
    have : ((t.truncLT 1).obj L).IsLE 0 := t.isLE_truncLT_obj _ _ _
    refine (homologyFunctor_map_bijective_of_isLE_of_isGE (X := (t.truncLT 1).obj L)
      (Y := (singleFunctor C 0).obj J) 0).1 ?_
    simp only [Functor.map_comp, h, comp_zero, Functor.map_zero]
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ _ (t.triangleLTGE_distinguished 1 L) φ h₁
  have : ((t.truncGE 1).obj L).IsGE 1 := t.isGE_truncGE_obj _ _ _
  rw [hg, eq_zero_of_isGE_one_of_injective g, comp_zero]

/-- Every morphism `H⁰(L) ⟶ H⁰(J[0])` to the cohomology of an injective object placed in degree
`0` is the effect on `H⁰` of a morphism `L ⟶ J[0]`. -/
lemma exists_homologyFunctor_map_eq (L : DerivedCategory C)
    (g : (homologyFunctor C 0).obj L ⟶ (homologyFunctor C 0).obj ((singleFunctor C 0).obj J)) :
    ∃ φ : L ⟶ (singleFunctor C 0).obj J, (homologyFunctor C 0).map φ = g := by
  let ι := (t.truncLTι 1).app L
  have : IsIso ((homologyFunctor C 0).map ι) := isIso_homologyFunctor_map_truncLTι_app L 1 0
    (by lia)
  have : ((t.truncLT 1).obj L).IsLE 0 := t.isLE_truncLT_obj _ _ _
  obtain ⟨ψ, hψ⟩ := (homologyFunctor_map_bijective_of_isLE_of_isGE (X := (t.truncLT 1).obj L)
    (Y := (singleFunctor C 0).obj J) 0).2 ((homologyFunctor C 0).map ι ≫ g)
  have hT := inv_rot_of_distTriang _ (t.triangleLTGE_distinguished 1 L)
  have : (((t.triangleLTGE 1).obj L).invRotate.obj₁).IsGE 1 := by
    have : ((t.truncGE 1).obj L).IsGE 1 := t.isGE_truncGE_obj _ _ _
    have : t.IsGE (((t.triangleLTGE 1).obj L).invRotate.obj₁) 2 :=
      t.isGE_shift ((t.truncGE 1).obj L) 1 (-1) 2
    exact t.isGE_of_ge _ 1 2
  obtain ⟨φ, hφ⟩ := Triangle.yoneda_exact₂ _ hT ψ (eq_zero_of_isGE_one_of_injective _)
  refine ⟨φ, ?_⟩
  rw [← cancel_epi ((homologyFunctor C 0).map ι), ← Functor.map_comp]
  simp only at hψ
  rw [← hψ, hφ]
  rfl

end Injective

section Complete

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] {ϖ : R} [IsAdicComplete (Ideal.span {ϖ}) R]

omit [IsDomain R] [IsPrincipalIdealRing R] [IsAdicComplete (Ideal.span {ϖ}) R] in
/-- If `ϖ` acts invertibly on `L ∈ D(R)`, it acts bijectively on the cohomology modules of
`L`. -/
lemma bijective_smul_homologyFunctor_obj {L : DerivedCategory (ModuleCat.{u} R)}
    (hL : IsIso (ϖ • 𝟙 L)) (n : ℤ) :
    Function.Bijective fun x : (homologyFunctor (ModuleCat.{u} R) n).obj L ↦ ϖ • x := by
  have : IsIso ((homologyFunctor (ModuleCat.{u} R) n).map (ϖ • 𝟙 L)) := inferInstance
  rw [homologyFunctor_map_smul_id] at this
  have h := ConcreteCategory.bijective_of_isIso
    (ϖ • 𝟙 ((homologyFunctor (ModuleCat.{u} R) n).obj L))
  convert h using 1

/-- **`R` is derived `ϖ`-complete.** Let `R` be a principal ideal domain which is `ϖ`-adically
complete. If `ϖ` acts invertibly on `L ∈ D(R)`, every morphism `L ⟶ R[0]` vanishes. -/
theorem eq_zero_of_isIso_smul_of_singleFunctor {L : DerivedCategory (ModuleCat.{u} R)}
    (hL : IsIso (ϖ • 𝟙 L)) (f : L ⟶ (singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) :
    f = 0 := by
  let K := FractionRing R
  let ι : R →ₗ[R] K := Algebra.linearMap R K
  let Qm := K ⧸ LinearMap.range ι
  let π : K →ₗ[R] Qm := (LinearMap.range ι).mkQ
  have hι : Function.Injective ι := IsFractionRing.injective R K
  have hπ : Function.Surjective π := Submodule.mkQ_surjective _
  have hex : LinearMap.ker π = LinearMap.range ι := Submodule.ker_mkQ _
  have hdivK (r : R) (hr : r ≠ 0) (y : K) : ∃ x : K, r • x = y :=
    ⟨(algebraMap R K r)⁻¹ * y, by
      rw [Algebra.smul_def, ← mul_assoc, mul_inv_cancel₀ (by
        simpa using (IsFractionRing.injective R K).ne hr), one_mul]⟩
  have : Module.Injective R K := Module.injective_of_divisible K hdivK
  have : Module.Injective R Qm := Module.injective_of_divisible Qm fun r hr y ↦ by
    obtain ⟨y, rfl⟩ := hπ y
    obtain ⟨x, rfl⟩ := hdivK r hr y
    exact ⟨π x, (map_smul π r x).symm⟩
  let S : ShortComplex (ModuleCat.{u} R) :=
    ShortComplex.mk (ModuleCat.ofHom ι) (ModuleCat.ofHom π)
      (ModuleCat.hom_ext (LinearMap.ext fun x ↦ (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩))
  have hS : S.ShortExact :=
    { exact := (ShortComplex.moduleCat_exact_iff_ker_sub_range _).2 fun x hx ↦ by
        have : x ∈ LinearMap.range ι := hex ▸ hx
        exact this
      mono_f := (ModuleCat.mono_iff_injective _).2 hι
      epi_g := (ModuleCat.epi_iff_surjective _).2 hπ }
  have : Injective S.X₂ := Module.injective_object_of_injective_module (R := R) (M := K)
  have : Injective S.X₃ := Module.injective_object_of_injective_module (R := R) (M := Qm)
  let T := hS.singleTriangle
  have hT : T ∈ distTriang _ := hS.singleTriangle_distinguished
  let ε := singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0
  -- `f` followed by `R ⟶ K` vanishes
  have hnat₁ : (homologyFunctor (ModuleCat.{u} R) 0).map T.mor₁ ≫ ε.hom.app S.X₂ =
      ε.hom.app S.X₁ ≫ S.f := ε.hom.naturality S.f
  have hnat₂ : (homologyFunctor (ModuleCat.{u} R) 0).map T.mor₂ ≫ ε.hom.app S.X₃ =
      ε.hom.app S.X₂ ≫ S.g := ε.hom.naturality S.g
  have h₁ : f ≫ T.mor₁ = 0 := by
    refine eq_zero_of_homologyFunctor_map_eq_zero _ ?_
    have h0 : (homologyFunctor (ModuleCat.{u} R) 0).map f ≫ ε.hom.app S.X₁ = 0 :=
      ModuleCat.hom_ext
        (Module.eq_zero_of_bijective_smul (W := R) (bijective_smul_homologyFunctor_obj hL 0) _)
    rw [Functor.map_comp, ← cancel_mono (ε.hom.app S.X₂), Category.assoc, hnat₁,
      ← Category.assoc, h0, zero_comp, zero_comp]
  -- so `f⟦1⟧` factors through the connecting map `(K/R)[0] ⟶ R[1]`
  obtain ⟨G, hG⟩ := Triangle.coyoneda_exact₁ _ hT (f⟦(1 : ℤ)⟧') (by
    rw [← Functor.map_comp, h₁, Functor.map_zero])
  -- the map `G` lifts along `K ⟶ K/R`
  have hL1 : IsIso (ϖ • 𝟙 (L⟦(1 : ℤ)⟧)) := by
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_smul]
    infer_instance
  obtain ⟨h₀, hh₀⟩ := Module.exists_comp_eq_of_bijective_smul ι π hι hπ hex
    (bijective_smul_homologyFunctor_obj hL1 0)
    ((homologyFunctor (ModuleCat.{u} R) 0).map G ≫ ε.hom.app S.X₃).hom
  obtain ⟨φ, hφ⟩ := exists_homologyFunctor_map_eq (J := S.X₂) (L⟦(1 : ℤ)⟧)
    (ModuleCat.ofHom h₀ ≫ ε.inv.app S.X₂)
  have hφG : φ ≫ T.mor₂ = G := by
    rw [← sub_eq_zero]
    refine eq_zero_of_homologyFunctor_map_eq_zero _ ?_
    rw [Functor.map_sub, sub_eq_zero, Functor.map_comp, hφ, ← cancel_mono (ε.hom.app S.X₃),
      Category.assoc, Category.assoc, hnat₂, Iso.inv_hom_id_app_assoc]
    exact ModuleCat.hom_ext hh₀
  have h₂ : f⟦(1 : ℤ)⟧' = 0 := by
    rw [hG, ← hφG, Category.assoc, comp_distTriang_mor_zero₂₃ _ hT, comp_zero]
  exact (shiftFunctor _ (1 : ℤ)).map_injective (by rw [h₂, Functor.map_zero])

end Complete

end DerivedCategory
