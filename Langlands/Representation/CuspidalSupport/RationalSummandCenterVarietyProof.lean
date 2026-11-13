import Langlands.Representation.CuspidalSupport.RationalSummandCenterVarietyStatement
import Langlands.Representation.CuspidalSupport.RationalSummandCenterGroupAlgebraProof
import Langlands.Representation.CuspidalSupport.RationalSummandEndCommutativeProof

/-! Renard VI.4.4, Proposition, last sentence: the center of `End(ind_{H⁰}^G ρ)` is the algebra
of polynomial functions on `Irr(G)[π]`. The published Proposition gives `e : ℂ[T/H⁰] ≃ Z`;
evaluation `t ↦ (ω ↦ ω(t))` maps `ℂ[T/H⁰]` injectively onto the `Stab`-invariant regular
functions on `X(G)`, by Dedekind's independence of the characters `ω ↦ ω(g)`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.CuspidalSupport

namespace CenterVariety

universe uG uX

section Generic

variable {G : Type uG} [Group G] {X : Type uX} [Monoid X] (H₀ : Subgroup G) [H₀.Normal]
  (ev : G →* (X →* ℂ)) (hker : H₀ ≤ ev.ker)

/-- The evaluation `q ↦ (ω ↦ ω(q))` on `G ⧸ H₀`, with values functions on `X`. -/
def quotientEval : G ⧸ H₀ →* (X → ℂ) :=
  (MonoidHom.coeFn X ℂ).comp (QuotientGroup.lift H₀ ev hker)

@[simp]
theorem quotientEval_mk (g : G) :
    quotientEval H₀ ev hker (QuotientGroup.mk g) = ⇑(ev g) := rfl

theorem quotientEval_mul_apply (q : G ⧸ H₀) (χ s : X) :
    quotientEval H₀ ev hker q (χ * s) =
      quotientEval H₀ ev hker q χ * quotientEval H₀ ev hker q s := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  simp

/-- Evaluation of finite formal combinations of points of `G ⧸ H₀` on `X`. -/
def quotientEvalAlg : MonoidAlgebra ℂ (G ⧸ H₀) →ₐ[ℂ] (X → ℂ) :=
  MonoidAlgebra.lift ℂ (X → ℂ) (G ⧸ H₀) (quotientEval H₀ ev hker)

theorem quotientEvalAlg_apply (c : MonoidAlgebra ℂ (G ⧸ H₀)) (χ : X) :
    quotientEvalAlg H₀ ev hker c χ =
      ∑ q ∈ c.coeff.support, c.coeff q * quotientEval H₀ ev hker q χ := by
  rw [quotientEvalAlg, MonoidAlgebra.lift_apply, Finsupp.sum, Finset.sum_apply]
  rfl

variable (hsep : ∀ g, ev g = 1 → g ∈ H₀)

include hsep in
/-- Dedekind independence: distinct points of `G ⧸ H₀` give distinct characters of `X`. -/
theorem quotientEval_linearIndependent :
    LinearIndependent ℂ (quotientEval H₀ ev hker) := by
  have hinj : Function.Injective (QuotientGroup.lift H₀ ev hker) := by
    rw [injective_iff_map_eq_one]
    intro q hq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    exact (QuotientGroup.eq_one_iff g).mpr (hsep g hq)
  exact (linearIndependent_monoidHom X ℂ).comp _ hinj

include hsep in
theorem quotientEvalAlg_injective : Function.Injective (quotientEvalAlg H₀ ev hker) := by
  have h := (quotientEval_linearIndependent H₀ ev hker hsep).finsuppLinearCombination_injective
  intro a b hab
  apply MonoidAlgebra.coeff_injective
  apply h
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
  simpa only [quotientEvalAlg, MonoidAlgebra.lift_apply] using hab

variable (T : Subgroup G)

/-- The inclusion `T ⧸ (H₀ ∩ T) → G ⧸ H₀`. -/
def subgroupQuotientMap : T ⧸ H₀.subgroupOf T →* G ⧸ H₀ :=
  QuotientGroup.map (H₀.subgroupOf T) H₀ T.subtype le_rfl

@[simp]
theorem subgroupQuotientMap_mk (t : T) :
    subgroupQuotientMap H₀ T (QuotientGroup.mk t) = QuotientGroup.mk (t : G) := rfl

theorem subgroupQuotientMap_injective : Function.Injective (subgroupQuotientMap H₀ T) := by
  rw [injective_iff_map_eq_one]
  intro q hq
  obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective q
  rw [subgroupQuotientMap_mk, QuotientGroup.eq_one_iff] at hq
  exact (QuotientGroup.eq_one_iff t).mpr hq

/-- Evaluation of finite formal combinations of points of `T ⧸ (H₀ ∩ T)` on `X`. -/
def subgroupEvalAlg : MonoidAlgebra ℂ (T ⧸ H₀.subgroupOf T) →ₐ[ℂ] (X → ℂ) :=
  (quotientEvalAlg H₀ ev hker).comp
    (MonoidAlgebra.mapDomainAlgHom ℂ ℂ (subgroupQuotientMap H₀ T))

@[simp]
theorem subgroupEvalAlg_of (t : T) :
    subgroupEvalAlg H₀ ev hker T (MonoidAlgebra.of ℂ _ (QuotientGroup.mk t)) = ⇑(ev t) := by
  simp [subgroupEvalAlg, quotientEvalAlg]

include hsep in
theorem subgroupEvalAlg_injective : Function.Injective (subgroupEvalAlg H₀ ev hker T) := by
  intro a b hab
  have h1 := quotientEvalAlg_injective H₀ ev hker hsep hab
  exact MonoidAlgebra.mapDomain_injective (subgroupQuotientMap_injective H₀ T) h1

variable (Stab : Set X) (hT : ∀ g, g ∈ T ↔ ∀ s ∈ Stab, ev g s = 1)

theorem subgroupEvalAlg_mem_adjoin (a : MonoidAlgebra ℂ (T ⧸ H₀.subgroupOf T)) :
    subgroupEvalAlg H₀ ev hker T a ∈ Algebra.adjoin ℂ (Set.range fun g => ⇑(ev g)) := by
  induction a using MonoidAlgebra.induction_on with
  | of q =>
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective q
    rw [subgroupEvalAlg_of]
    exact Algebra.subset_adjoin ⟨t, rfl⟩
  | add x y hx hy =>
    rw [map_add]
    exact Subalgebra.add_mem _ hx hy
  | smul r x hx =>
    rw [map_smul]
    exact Subalgebra.smul_mem _ hx r

include hT in
theorem subgroupEvalAlg_invariant (a : MonoidAlgebra ℂ (T ⧸ H₀.subgroupOf T))
    (s : X) (hs : s ∈ Stab) (χ : X) :
    subgroupEvalAlg H₀ ev hker T a (χ * s) = subgroupEvalAlg H₀ ev hker T a χ := by
  induction a using MonoidAlgebra.induction_on with
  | of q =>
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective q
    rw [subgroupEvalAlg_of, map_mul, (hT t).mp t.property s hs, mul_one]
  | add x y hx hy =>
    rw [map_add, Pi.add_apply, Pi.add_apply, hx, hy]
  | smul r x hx =>
    rw [map_smul, Pi.smul_apply, Pi.smul_apply, hx]

include hsep hT in
/-- The range of the evaluation on `T ⧸ (H₀ ∩ T)` is exactly the `Stab`-invariant part of the
algebra generated by the evaluations. -/
theorem subgroupEvalAlg_range :
    Set.range (subgroupEvalAlg H₀ ev hker T) =
      {φ | φ ∈ Algebra.adjoin ℂ (Set.range fun g => ⇑(ev g)) ∧
        ∀ s ∈ Stab, ∀ χ, φ (χ * s) = φ χ} := by
  apply Set.Subset.antisymm
  · rintro _ ⟨a, rfl⟩
    exact ⟨subgroupEvalAlg_mem_adjoin H₀ ev hker T a,
      fun s hs χ => subgroupEvalAlg_invariant H₀ ev hker T Stab hT a s hs χ⟩
  · rintro φ ⟨hφ, hinv⟩
    have hle : Algebra.adjoin ℂ (Set.range fun g => ⇑(ev g)) ≤
        (quotientEvalAlg H₀ ev hker).range := by
      apply Algebra.adjoin_le
      rintro _ ⟨g, rfl⟩
      exact ⟨MonoidAlgebra.of ℂ _ (QuotientGroup.mk g), by simp [quotientEvalAlg]⟩
    obtain ⟨c, hc⟩ := hle hφ
    change quotientEvalAlg H₀ ev hker c = φ at hc
    subst hc
    have hli := quotientEval_linearIndependent H₀ ev hker hsep
    -- every point of the support is fixed by every element of `Stab`
    have hfix : ∀ q ∈ c.coeff.support, ∀ s ∈ Stab, quotientEval H₀ ev hker q s = 1 := by
      intro q hq s hs
      have hsum : ∑ q ∈ c.coeff.support,
          (c.coeff q * (quotientEval H₀ ev hker q s - 1)) • quotientEval H₀ ev hker q = 0 := by
        funext χ
        have h1 := hinv s hs χ
        rw [quotientEvalAlg_apply, quotientEvalAlg_apply] at h1
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        rw [← sub_eq_zero.mpr h1, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro q _
        rw [quotientEval_mul_apply]
        ring
      have h2 := linearIndependent_iff'.mp hli _ _ hsum q hq
      have hc : c.coeff q ≠ 0 := Finsupp.mem_support_iff.mp hq
      exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left hc)
    have hrange : ↑c.coeff.support ⊆ Set.range (subgroupQuotientMap H₀ T) := by
      intro q hq
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      have hg : g ∈ T := (hT g).mpr fun s hs => hfix _ hq s hs
      exact ⟨QuotientGroup.mk ⟨g, hg⟩, rfl⟩
    refine ⟨MonoidAlgebra.ofCoeff (Finsupp.comapDomain (subgroupQuotientMap H₀ T) c.coeff
      (subgroupQuotientMap_injective H₀ T).injOn), ?_⟩
    change quotientEvalAlg H₀ ev hker (MonoidAlgebra.ofCoeff (Finsupp.mapDomain
      (subgroupQuotientMap H₀ T) (Finsupp.comapDomain (subgroupQuotientMap H₀ T) c.coeff
        (subgroupQuotientMap_injective H₀ T).injOn))) = _
    rw [Finsupp.mapDomain_comapDomain _ (subgroupQuotientMap_injective H₀ T) _ hrange]


include hsep hT in
/-- An algebra isomorphism `e : ℂ[T ⧸ (H₀ ∩ T)] ≃ Z` turns the evaluation into an injective
algebra map `Ψ = ev ∘ e⁻¹` on `Z` with range the `Stab`-invariant evaluation polynomials. -/
theorem exists_algHom_of_algEquiv {Z : Type*} [Semiring Z] [Algebra ℂ Z]
    (e : MonoidAlgebra ℂ (T ⧸ H₀.subgroupOf T) ≃ₐ[ℂ] Z) :
    ∃ Ψ : Z →ₐ[ℂ] (X → ℂ), Function.Injective Ψ ∧
      Set.range Ψ =
        {φ | φ ∈ Algebra.adjoin ℂ (Set.range fun g => ⇑(ev g)) ∧
          ∀ s ∈ Stab, ∀ χ, φ (χ * s) = φ χ} ∧
      ∀ a, Ψ (e a) = subgroupEvalAlg H₀ ev hker T a := by
  refine ⟨(subgroupEvalAlg H₀ ev hker T).comp e.symm.toAlgHom, ?_, ?_, fun a => ?_⟩
  · exact (subgroupEvalAlg_injective H₀ ev hker hsep T).comp e.symm.injective
  · rw [← subgroupEvalAlg_range H₀ ev hker hsep T Stab hT, AlgHom.coe_comp]
    exact e.symm.surjective.range_comp _
  · rw [AlgHom.comp_apply]
    exact congrArg _ (e.symm_apply_apply a)

end Generic

/-- A linear map on a monoid algebra that is a fixed multiple of `v` on the group elements, with
the multiple given by a linear form, is that multiple of `v` everywhere. -/
theorem linearMap_eq_smul_of_forall_of {M V : Type*} [Monoid M] [AddCommGroup V] [Module ℂ V]
    (L : MonoidAlgebra ℂ M →ₗ[ℂ] V) (f : MonoidAlgebra ℂ M →ₗ[ℂ] ℂ) (v : V)
    (h : ∀ m, L (MonoidAlgebra.of ℂ M m) = f (MonoidAlgebra.of ℂ M m) • v)
    (a : MonoidAlgebra ℂ M) : L a = f a • v := by
  induction a using MonoidAlgebra.induction_on with
  | of m => exact h m
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_smul]
  | smul r x hx => rw [map_smul, map_smul, hx, smul_eq_mul, mul_smul]

section Unramified

universe uH uI

variable {H : Type uH} [Group H] [TopologicalSpace H] {I : Type uI} (ν : I → (H →* ℝ≥0ˣ))

/-- The evaluation `g ↦ (ω ↦ ω(g))` of points of `H` on the unramified characters. -/
def unramifiedEvalHom : H →* (unramifiedCharacters ν →* ℂ) where
  toFun g :=
    { toFun := fun ω => ((ω.val g : ℂˣ) : ℂ)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  map_one' := by ext ω; simp
  map_mul' := fun g h => by
    ext ω
    change ((ω.val (g * h) : ℂˣ) : ℂ) = ((ω.val g : ℂˣ) : ℂ) * ((ω.val h : ℂˣ) : ℂ)
    rw [map_mul, Units.val_mul]

theorem unramifiedEvalHom_apply (g : H) (ω : unramifiedCharacters ν) :
    unramifiedEvalHom ν g ω = ((ω.val g : ℂˣ) : ℂ) := rfl

theorem commonNormKernel_le_unramifiedEvalHom_ker :
    commonNormKernel ν ≤ (unramifiedEvalHom ν).ker := by
  intro g hg
  rw [MonoidHom.mem_ker]
  ext ω
  have h1 : ω.val g = 1 := ω.property hg
  rw [unramifiedEvalHom_apply, h1, Units.val_one, MonoidHom.one_apply]

/-- If the characters of the discrete quotient `H ⧸ H⁰` separate its points, an element on which
every unramified character is trivial lies in `H⁰`. -/
theorem mem_commonNormKernel_of_unramifiedEvalHom_eq_one [IsTopologicalGroup H]
    (hopen : IsOpen (commonNormKernel ν : Set H))
    (hsep : ∀ q : H ⧸ commonNormKernel ν, q ≠ 1 →
      ∃ ω : (H ⧸ commonNormKernel ν) →* ℂˣ, ω q ≠ 1)
    (g : H) (hg : unramifiedEvalHom ν g = 1) : g ∈ commonNormKernel ν := by
  by_contra hng
  have hq : (QuotientGroup.mk g : H ⧸ commonNormKernel ν) ≠ 1 := by
    rwa [Ne, QuotientGroup.eq_one_iff]
  obtain ⟨ω, hω⟩ := hsep _ hq
  have := QuotientGroup.discreteTopology hopen
  let ω' : (H ⧸ commonNormKernel ν) →ₜ* ℂˣ :=
    { toMonoidHom := ω, continuous_toFun := continuous_of_discreteTopology }
  have h1 := DFunLike.congr_fun hg (quotientCharacterPullback ν ω')
  apply hω
  exact Units.ext h1

/-- The evaluation polynomials of `unramifiedEvalHom` generate `unramifiedRegularFunctions`. -/
theorem adjoin_range_unramifiedEvalHom :
    Algebra.adjoin ℂ (Set.range fun g => ⇑(unramifiedEvalHom ν g)) =
      unramifiedRegularFunctions ν := rfl

end Unramified

end CenterVariety

section Main

universe uF uV

open Aubert.General Aubert.General.RationalPointFamily GroupScheme Induction

/-- Renard VI.4.4, Proposition, last sentence: `Ψ = ev ∘ e⁻¹`, where `e : ℂ[T/H⁰] ≃ Z` is the
published algebra isomorphism and `ev` sends `t` to the function `ω ↦ ω(t)`. -/
theorem rationalSummandCenterVariety : RationalSummandCenterVarietyStatement.{uF, uV} := by
  intro F _ _ _ _ G hG S i hi _ _ _ ν hν hStandard hRoots hU h π hπ hcusp ρ hρ j hj I X Stab
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  let _ : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  have : IsTopologicalGroup (GroupScheme.rationalPoints G) := rationalPoint_isTopologicalGroup F G
  let T : Subgroup (GroupScheme.rationalPoints G) :=
    ⨅ (ω : unramifiedCharacters (fun χ => (rationalNormCharacters G χ).toMul))
      (_ : Nonempty (rationalUnramifiedTwist G ω π ≅ π)), ω.val.toMonoidHom.ker
  obtain ⟨e, he⟩ : ∃ e : MonoidAlgebra ℂ (T ⧸ (rationalCommonNormKernel G).subgroupOf T) ≃ₐ[ℂ]
      Subalgebra.center ℂ (End I), ∀ (t : T) (ω : X)
      (φ : I ⟶ rationalUnramifiedTwist G ω (rationalInertiaBaseLift G π)),
      (e (MonoidAlgebra.of ℂ _ (QuotientGroup.mk t)) : End I) ≫ φ =
        ((ω.val t : ℂˣ) : ℂ) • φ := by
    obtain ⟨e, he⟩ := rationalSummandCenterGroupAlgebra F G hG S i hi ν hν hStandard hRoots hU
      π hπ hcusp ρ hρ j hj
    exact ⟨e, fun t ω φ => (he t).2 ω φ⟩
  let ev := CenterVariety.unramifiedEvalHom (fun χ => (rationalNormCharacters G χ).toMul)
  have hker : rationalCommonNormKernel G ≤ ev.ker :=
    CenterVariety.commonNormKernel_le_unramifiedEvalHom_ker _
  have hsep : ∀ g, ev g = 1 → g ∈ rationalCommonNormKernel G :=
    CenterVariety.mem_commonNormKernel_of_unramifiedEvalHom_eq_one _
      (isOpen_rationalCommonNormKernel G) (rationalNormKernelQuotient_exists_character_ne_one G)
  have hT : ∀ g, g ∈ T ↔ ∀ s ∈ Stab, ev g s = 1 := by
    intro g
    simp only [T, Subgroup.mem_iInf, MonoidHom.mem_ker]
    constructor
    · intro hg s hs
      exact Units.val_eq_one.mpr (hg s hs)
    · intro hg s hs
      exact Units.val_eq_one.mp (hg s hs)
  obtain ⟨Ψ, hinj, hrange, hΨ⟩ :=
    CenterVariety.exists_algHom_of_algEquiv (rationalCommonNormKernel G) ev hker hsep T Stab hT e
  rw [← CenterVariety.adjoin_range_unramifiedEvalHom]
  refine ⟨Ψ, hinj, hrange, fun z ω φ => ?_⟩
  obtain ⟨a, rfl⟩ := e.surjective z
  rw [hΨ]
  let L : MonoidAlgebra ℂ (T ⧸ (rationalCommonNormKernel G).subgroupOf T) →ₗ[ℂ]
      (I ⟶ rationalUnramifiedTwist G ω (rationalInertiaBaseLift G π)) :=
    { toFun := fun a => (e a : End I) ≫ φ
      map_add' := fun x y => by
        rw [map_add e x y, Subalgebra.coe_add]
        exact Preadditive.add_comp _ _ _ _ _ _
      map_smul' := fun r x => by
        rw [map_smul e r x, Subalgebra.coe_smul, RingHom.id_apply]
        exact Linear.smul_comp _ _ _ _ _ _ }
  let f : MonoidAlgebra ℂ (T ⧸ (rationalCommonNormKernel G).subgroupOf T) →ₗ[ℂ] ℂ :=
    (LinearMap.proj ω).comp
      (CenterVariety.subgroupEvalAlg (rationalCommonNormKernel G) ev hker T).toLinearMap
  refine CenterVariety.linearMap_eq_smul_of_forall_of L f φ (fun q => ?_) a
  obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective q
  have h1 : f (MonoidAlgebra.of ℂ _ (QuotientGroup.mk t)) = ((ω.val t : ℂˣ) : ℂ) := by
    change CenterVariety.subgroupEvalAlg (rationalCommonNormKernel G) ev hker T
      (MonoidAlgebra.of ℂ _ (QuotientGroup.mk t)) ω = _
    rw [CenterVariety.subgroupEvalAlg_of]
    rfl
  rw [h1]
  exact he t ω φ

end Main

end Langlands.CuspidalSupport
