import Langlands.Cohomology.ExtendScalarsLocalizationDescent
import Langlands.Cohomology.PerfectModuleComplexBaseChange
import Langlands.Cohomology.ModuleComplex.FibreH0RestrictionSpread.Homology
import Langlands.Cohomology.ModuleComplex.FibreH0RestrictionSpread.Split

/-!
# Spreading degree-zero bijectivity for finite free complexes

Over a commutative ring `A` with a ring map `φ : A →+* k` to a field, consider finite free
complexes `P`, `P₁`, `P₂` vanishing in degree `-1` with rank-one degree-zero terms, and chain maps
`χⱼ : P ⟶ Pⱼ`. If the fibre complex `P ⊗ k` has zero differentials, the degree-zero homology of
every scalar extension of `P₁` and `P₂` is free of rank one, `H⁰(χ₁ ⊗ k)` is bijective and the
maps `H¹(χⱼ ⊗ k)` are jointly injective, then after inverting one element `a` with `φ a ≠ 0` the
map `H⁰(χ₁ ⊗ T)` is bijective for every scalar extension.
-/

universe u

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace Langlands.Cohomology.ModuleComplex.FibreH0Spread

variable {A : Type u} [CommRing A]

/-- Ordinary extension of scalars preserves free modules. -/
lemma free_extendScalars {T : Type u} [CommRing T] (β : A →+* T) (M : ModuleCat.{u} A)
    [Module.Free A M] : Module.Free T ((ModuleCat.extendScalars β).obj M) := by
  let := β.toAlgebra
  change Module.Free T (TensorProduct A T M)
  infer_instance

/-- Extension of scalars of a module free of rank `n` is free of rank `n`. -/
lemma nonempty_extendScalars_equiv {T : Type u} [CommRing T] (β : A →+* T)
    {M : ModuleCat.{u} A} {n : ℕ} (e : M ≃ₗ[A] (Fin n → A)) :
    Nonempty ((ModuleCat.extendScalars β).obj M ≃ₗ[T] (Fin n → T)) := by
  obtain ⟨e'⟩ := nonempty_extendScalars_pi_equiv β n
  exact ⟨((ModuleCat.extendScalars β).mapIso e.toModuleIso).toLinearEquiv ≪≫ₗ e'⟩

/-- Extension of scalars of a module free of rank one is free of rank one. -/
lemma nonempty_extendScalars_equiv_self {T : Type u} [CommRing T] (β : A →+* T)
    {M : ModuleCat.{u} A} (e : M ≃ₗ[A] (Fin 1 → A)) :
    Nonempty ((ModuleCat.extendScalars β).obj M ≃ₗ[T] T) := by
  obtain ⟨e'⟩ := nonempty_extendScalars_equiv β e
  exact ⟨e' ≪≫ₗ LinearEquiv.funUnique (Fin 1) T T⟩

/-- The degree-zero differential of a scalar extension of a finite free complex vanishing in
degree `-1`, with rank-one degree-zero term and universally rank-one degree-zero homology,
vanishes. -/
lemma baseChange_d_zero_one {T : Type u} [CommRing T] (β : A →+* T)
    {Q : CochainComplex (ModuleCat.{u} A) ℤ} (hQ : IsFiniteFree Q) (hz : IsZero (Q.X (-1)))
    (e : Q.X 0 ≃ₗ[A] (Fin 1 → A)) (hH : Nonempty ((((baseChange β).obj Q).homology 0) ≃ₗ[T] T)) :
    ((baseChange β).obj Q).d 0 1 = 0 := by
  have := (hQ.2 1).2
  have : Module.Free T (((baseChange β).obj Q).X 1) := free_extendScalars β (Q.X 1)
  obtain ⟨e'⟩ := nonempty_extendScalars_equiv_self β e
  obtain ⟨eH⟩ := hH
  exact d_zero_one_eq_zero _ ((ModuleCat.extendScalars β).map_isZero hz) e' eH

/-- The incoming differential in degree `0` of a scalar extension of a complex vanishing in
degree `-1` vanishes. -/
lemma baseChange_d_neg_one {T : Type u} [CommRing T] (β : A →+* T)
    {Q : CochainComplex (ModuleCat.{u} A) ℤ} (hz : IsZero (Q.X (-1))) :
    ((baseChange β).obj Q).d (0 - 1) 0 = 0 :=
  ((ModuleCat.extendScalars β).map_isZero hz).eq_of_src _ _

/-- The algebraic core of the spreading argument for finite free models. -/
theorem exists_bijective_of_finiteFree {k : Type u} [Field k] (φ : A →+* k)
    {P P₁ P₂ : CochainComplex (ModuleCat.{u} A) ℤ}
    (hP : IsFiniteFree P) (hP₁ : IsFiniteFree P₁) (hP₂ : IsFiniteFree P₂)
    (χ₁ : P ⟶ P₁) (χ₂ : P ⟶ P₂)
    (hz : IsZero (P.X (-1))) (hz₁ : IsZero (P₁.X (-1))) (hz₂ : IsZero (P₂.X (-1)))
    (e : P.X 0 ≃ₗ[A] (Fin 1 → A)) (e₁ : P₁.X 0 ≃ₗ[A] (Fin 1 → A))
    (e₂ : P₂.X 0 ≃ₗ[A] (Fin 1 → A))
    (hd : ∀ i j : ℤ, ((baseChange φ).obj P).d i j = 0)
    (hH₁ : ∀ (T : Type u) [CommRing T] (β : A →+* T),
      Nonempty ((((baseChange β).obj P₁).homology 0) ≃ₗ[T] T))
    (hH₂ : ∀ (T : Type u) [CommRing T] (β : A →+* T),
      Nonempty ((((baseChange β).obj P₂).homology 0) ≃ₗ[T] T))
    (h0 : Function.Bijective
      (HomologicalComplex.homologyMap ((baseChange φ).map χ₁) 0).hom)
    (h1 : ∀ c : ((baseChange φ).obj P).homology 1,
      (HomologicalComplex.homologyMap ((baseChange φ).map χ₁) 1).hom c = 0 →
      (HomologicalComplex.homologyMap ((baseChange φ).map χ₂) 1).hom c = 0 → c = 0) :
    ∃ a : A, φ a ≠ 0 ∧ ∀ (T : Type u) [CommRing T] (β : A →+* T), IsUnit (β a) →
      Function.Bijective
        (HomologicalComplex.homologyMap ((baseChange β).map χ₁) 0).hom := by
  have := (hP.2 0).1
  have := (hP.2 0).2
  have := (hP.2 1).1
  have := (hP.2 1).2
  have := (hP₁.2 0).1
  have := (hP₁.2 0).2
  have := (hP₁.2 1).1
  have := (hP₁.2 1).2
  have := (hP₂.2 1).1
  have := (hP₂.2 1).2
  -- Degree zero: `χ₁⁰ ⊗ k` is injective, so `χ₁⁰` splits up to `a₀`.
  have inj0 := jointly_injective_f_of_homologyMap ((baseChange φ).map χ₁)
    ((baseChange φ).map χ₁) 0 (hd _ _) (hd _ _)
    (fun c hc _ ↦ h0.1 (hc.trans (map_zero _).symm))
  obtain ⟨a₀, ha₀, g₁, g₂, hg⟩ :=
    exists_split_of_extendScalars φ (χ₁.f 0) (χ₁.f 0) inj0
  -- Degree one: `(χ₁¹, χ₂¹) ⊗ k` is jointly injective, so it splits up to `a₁`.
  have inj1 := jointly_injective_f_of_homologyMap ((baseChange φ).map χ₁)
    ((baseChange φ).map χ₂) 1 (hd _ _) (hd _ _) h1
  obtain ⟨a₁, ha₁, f₁, f₂, hf⟩ :=
    exists_split_of_extendScalars φ (χ₁.f 1) (χ₂.f 1) inj1
  refine ⟨a₀ * a₁, by simpa using And.intro ha₀ ha₁, ?_⟩
  intro T _ β hβ
  rw [map_mul, IsUnit.mul_iff] at hβ
  -- The degree-zero differentials of the scalar extensions of `P₁` and `P₂` vanish.
  have d₁ := baseChange_d_zero_one β hP₁ hz₁ e₁ (hH₁ T β)
  have d₂ := baseChange_d_zero_one β hP₂ hz₂ e₂ (hH₂ T β)
  -- Hence so does the degree-zero differential of the scalar extension of `P`.
  have d : ((baseChange β).obj P).d 0 1 = 0 := by
    have hA : P.d 0 1 ≫ (a₁ • 𝟙 (P.X 1)) =
        (χ₁.f 0 ≫ P₁.d 0 1) ≫ f₁ + (χ₂.f 0 ≫ P₂.d 0 1) ≫ f₂ := by
      rw [← hf, Preadditive.comp_add, ← Category.assoc, ← Category.assoc, χ₁.comm, χ₂.comm]
    have key := congrArg (ModuleCat.extendScalars β).map hA
    simp only [Functor.map_comp, Functor.map_add, extendScalars_map_smul, Linear.comp_smul,
      Category.comp_id] at key
    have d₁' : (ModuleCat.extendScalars β).map (P₁.d 0 1) = 0 := d₁
    have d₂' : (ModuleCat.extendScalars β).map (P₂.d 0 1) = 0 := d₂
    simp only [d₁', d₂', Limits.comp_zero, Limits.zero_comp, add_zero] at key
    exact (hβ.2.smul_eq_zero).1 key
  have dP₀ := baseChange_d_neg_one β hz
  have dP₁₀ := baseChange_d_neg_one β hz₁
  rw [bijective_homologyMap_iff _ 0 dP₀ d dP₁₀ d₁]
  -- In degree zero, `χ₁⁰ ⊗ T` has a left inverse up to the unit `β a₀`.
  obtain ⟨eT⟩ := nonempty_extendScalars_equiv_self β e
  obtain ⟨e₁T⟩ := nonempty_extendScalars_equiv_self β e₁
  have key : (ModuleCat.extendScalars β).map (χ₁.f 0) ≫
      (ModuleCat.extendScalars β).map (g₁ + g₂) = β a₀ • 𝟙 _ := by
    rw [← Functor.map_comp, Preadditive.comp_add, hg, extendScalars_map_smul,
      CategoryTheory.Functor.map_id]
  refine bijective_of_comp_eq_smul eT e₁T ((ModuleCat.extendScalars β).map (χ₁.f 0)).hom
    ((ModuleCat.extendScalars β).map (g₁ + g₂)).hom (β a₀) hβ.1 ?_
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_smul, ModuleCat.hom_id] using
    congrArg ModuleCat.Hom.hom key

end Langlands.Cohomology.ModuleComplex.FibreH0Spread
