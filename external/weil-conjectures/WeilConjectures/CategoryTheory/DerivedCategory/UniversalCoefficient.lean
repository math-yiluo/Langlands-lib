/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Flat.TorsionFree
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Linear

/-!
# Universal coefficient sequences

Let `R` be a commutative ring and `x ∈ R`. For a distinguished triangle
`C ⟶[x] C ⟶ D ⟶ C⟦1⟧` of `D(R)` whose first map is the multiplication by `x` (for example
`D = C ⊗ᴸ R/(x)` when `x` is a nonzerodivisor), the long exact homology sequence breaks up into
the *universal coefficient sequences*

`0 ⟶ Hⁱ(C) ⊗_R R/(x) ⟶ Hⁱ(D) ⟶ Hⁱ⁺¹(C)[x] ⟶ 0`,

where `M[x]` is the `x`-torsion of `M`; for a nonzerodivisor `x` it is `Tor₁^R(M, R/(x))`.

## Main definitions

- `ModuleCat.universalCoefficientShortComplex`: the short complex
  `A ⊗ R/(x) ⟶ B ⟶ A'[x]` attached to maps `A ⟶ B ⟶ A'` with `A ⟶[x] A ⟶ B` and
  `B ⟶ A' ⟶[x] A'` zero.
- `DerivedCategory.universalCoefficientSequence`: the universal coefficient sequence of a
  triangle `C ⟶[x] C ⟶ D ⟶ C⟦1⟧`.

## Main statements

- `ModuleCat.universalCoefficientShortComplex_shortExact`: the short complex is short exact
  when `A ⟶[x] A ⟶ B ⟶ A' ⟶[x] A'` is exact.
- `DerivedCategory.universalCoefficientSequence_shortExact`: the universal coefficient sequence
  of a distinguished triangle is short exact.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped TensorProduct

namespace ModuleCat

variable {R : Type u} [CommRing R] (x : R)

section

variable {A B A' : ModuleCat.{u} R} (f : A ⟶ B) (g : B ⟶ A')

lemma smul_span_singleton_top_le_ker (hf : (x • 𝟙 A) ≫ f = 0) :
    Ideal.span {x} • (⊤ : Submodule R A) ≤ LinearMap.ker f.hom := by
  rw [Submodule.ideal_span_singleton_smul]
  rintro _ ⟨a, -, rfl⟩
  have := congr($(hf).hom a)
  exact this

lemma smul_apply_eq_zero (hg : g ≫ (x • 𝟙 A') = 0) (b : B) : x • g.hom b = 0 := by
  have := congr($(hg).hom b)
  exact this

/-- The map `A ⊗_R R/(x) ⟶ B` induced by `f : A ⟶ B` when `f ∘ x = 0`. -/
noncomputable def tensorQuotLift (hf : (x • 𝟙 A) ≫ f = 0) :
    A ⊗[R] (R ⧸ Ideal.span {x}) →ₗ[R] B :=
  (Submodule.liftQ _ f.hom (smul_span_singleton_top_le_ker x f hf)) ∘ₗ
    (TensorProduct.tensorQuotEquivQuotSMul A (Ideal.span {x})).toLinearMap

@[simp]
lemma tensorQuotLift_tmul (hf : (x • 𝟙 A) ≫ f = 0) (a : A) :
    tensorQuotLift x f hf (a ⊗ₜ 1) = f.hom a := by
  simp [tensorQuotLift, TensorProduct.tensorQuotEquivQuotSMul]

lemma range_tensorQuotLift (hf : (x • 𝟙 A) ≫ f = 0) :
    LinearMap.range (tensorQuotLift x f hf) = LinearMap.range f.hom := by
  rw [tensorQuotLift, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
    Submodule.range_liftQ]

/-- The universal coefficient short complex `A ⊗_R R/(x) ⟶ B ⟶ A'[x]` attached to maps
`f : A ⟶ B` and `g : B ⟶ A'` with `f g = 0`, `f ∘ x = 0` and `x ∘ g = 0`: the first map is
induced by `f`, the second is `g`, which lands in the `x`-torsion of `A'`. -/
noncomputable def universalCoefficientShortComplex (hf : (x • 𝟙 A) ≫ f = 0) (hfg : f ≫ g = 0)
    (hg : g ≫ (x • 𝟙 A') = 0) : ShortComplex (ModuleCat.{u} R) where
  X₁ := ModuleCat.of R (A ⊗[R] (R ⧸ Ideal.span {x}))
  X₂ := B
  X₃ := ModuleCat.of R (Submodule.torsionBy R A' x)
  f := ofHom (tensorQuotLift x f hf)
  g := ofHom (g.hom.codRestrict _ fun b ↦
    (Submodule.mem_torsionBy_iff _ _).2 (smul_apply_eq_zero x g hg b))
  zero := by
    refine hom_ext (TensorProduct.ext' fun a r ↦ ?_)
    induction r using Submodule.Quotient.induction_on with | H r => ?_
    have h₁ : a ⊗ₜ[R] (Ideal.Quotient.mk (Ideal.span {x}) r) = (r • a) ⊗ₜ 1 := by
      rw [TensorProduct.smul_tmul]
      congr 1
      exact Algebra.algebraMap_eq_smul_one (A := R ⧸ Ideal.span {x}) r
    have h₂ := congr($(hfg).hom a)
    apply Subtype.ext
    simp only [hom_comp, LinearMap.coe_comp, Function.comp_apply, hom_zero,
      LinearMap.zero_apply] at h₂ ⊢
    simp [h₁, tensorQuotLift_tmul, h₂]

/-- The universal coefficient short complex is short exact as soon as the sequence
`A ⟶[x] A ⟶ B ⟶ A' ⟶[x] A'` is exact. -/
theorem universalCoefficientShortComplex_shortExact (hf : (x • 𝟙 A) ≫ f = 0)
    (hfg : f ≫ g = 0) (hg : g ≫ (x • 𝟙 A') = 0) {a : A ⟶ A} (ha : a = x • 𝟙 A)
    {a' : A' ⟶ A'} (ha' : a' = x • 𝟙 A') {haf : a ≫ f = 0} {hga : g ≫ a' = 0}
    (h₁ : (ShortComplex.mk _ _ haf).Exact) (h₂ : (ShortComplex.mk _ _ hfg).Exact)
    (h₃ : (ShortComplex.mk _ _ hga).Exact) :
    (universalCoefficientShortComplex x f g hf hfg hg).ShortExact := by
  subst ha ha'
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h₁ h₂ h₃
  refine ModuleCat.shortComplex_shortExact _ (fun b ↦ ?_) ?_ ?_
  · change g.hom.codRestrict _ _ b = 0 ↔ b ∈ Set.range (tensorQuotLift x f hf)
    rw [← LinearMap.mem_ker, LinearMap.ker_codRestrict, LinearMap.mem_ker]
    erw [h₂ b]
    rw [← LinearMap.coe_range, ← LinearMap.coe_range, range_tensorQuotLift]
  · have hker : LinearMap.ker f.hom ≤ Ideal.span {x} • ⊤ := by
      intro a ha
      obtain ⟨a₀, rfl⟩ := (h₁ a).1 ha
      rw [Submodule.ideal_span_singleton_smul]
      exact ⟨a₀, trivial, by simp⟩
    exact (LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ f.hom
      (smul_span_singleton_top_le_ker x f hf) hker)).comp
      (LinearEquiv.injective _)
  · rintro ⟨a', ha'⟩
    obtain ⟨b, hb⟩ := (h₃ a').1 ((Submodule.mem_torsionBy_iff _ _).1 ha')
    exact ⟨b, Subtype.ext hb⟩

end


section Tor

open MonoidalCategory ZeroObject

/-- The terms of the projective resolution `0 ⟶ R ⟶[x] R` of `R/(x)`. -/
noncomputable def quotSpanSingletonResolutionX : ℕ → ModuleCat.{u} R
  | 0 => ModuleCat.of R R
  | 1 => ModuleCat.of R R
  | _ + 2 => 0

/-- The differentials of the projective resolution `0 ⟶ R ⟶[x] R` of `R/(x)`. -/
noncomputable def quotSpanSingletonResolutionD :
    ∀ n, quotSpanSingletonResolutionX (R := R) (n + 1) ⟶ quotSpanSingletonResolutionX n
  | 0 => ofHom (x • LinearMap.id : R →ₗ[R] R)
  | _ + 1 => 0

/-- The complex `0 ⟶ R ⟶[x] R`, concentrated in degrees `1` and `0`. -/
noncomputable def quotSpanSingletonResolutionComplex : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of _ (quotSpanSingletonResolutionD x) fun n ↦ by
    simp [quotSpanSingletonResolutionD]

lemma quotSpanSingletonResolutionComplex_d_one_zero :
    (quotSpanSingletonResolutionComplex x).d 1 0 =
      ofHom (x • LinearMap.id : R →ₗ[R] R) :=
  (ChainComplex.of_d (quotSpanSingletonResolutionX (R := R)) (quotSpanSingletonResolutionD x)
    0).trans rfl

lemma quotSpanSingletonResolutionComplex_d_succ_succ (n : ℕ) :
    (quotSpanSingletonResolutionComplex x).d (n + 2) (n + 1) = 0 :=
  (ChainComplex.of_d (quotSpanSingletonResolutionX (R := R)) (quotSpanSingletonResolutionD x)
    (n + 1)).trans rfl

lemma isZero_quotSpanSingletonResolutionComplex_X (n : ℕ) :
    IsZero ((quotSpanSingletonResolutionComplex x).X (n + 2)) :=
  isZero_zero (ModuleCat.{u} R)

instance (n : ℕ) : Projective ((quotSpanSingletonResolutionComplex x).X n) := by
  match n with
  | 0 => exact inferInstanceAs (Projective (ModuleCat.of R R))
  | 1 => exact inferInstanceAs (Projective (ModuleCat.of R R))
  | n + 2 => exact (isZero_quotSpanSingletonResolutionComplex_X x n).projective

/-- The augmentation `R ⟶ R/(x)` of the resolution `0 ⟶ R ⟶[x] R`. -/
noncomputable def quotSpanSingletonResolutionπ :
    quotSpanSingletonResolutionComplex x ⟶
      (ChainComplex.single₀ (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⧸ Ideal.span {x})) :=
  ((quotSpanSingletonResolutionComplex x).toSingle₀Equiv _).symm
    ⟨ofHom (Ideal.span {x}).mkQ, by
      rw [quotSpanSingletonResolutionComplex_d_one_zero]
      refine hom_ext (LinearMap.ext fun (r : R) ↦ ?_)
      change Submodule.Quotient.mk (x • r) = (0 : R ⧸ Ideal.span {x})
      rw [Submodule.Quotient.mk_eq_zero, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self x)⟩

lemma quotSpanSingletonResolutionπ_f_zero :
    (quotSpanSingletonResolutionπ x).f 0 = ofHom (Ideal.span {x}).mkQ :=
  rfl

variable {x}

lemma quasiIso_quotSpanSingletonResolutionπ (hx : x ∈ nonZeroDivisors R) :
    QuasiIso (quotSpanSingletonResolutionπ x) where
  quasiIsoAt m := by
    match m with
    | 0 =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros' _ rfl rfl rfl]
      refine ⟨?_, ?_⟩
      · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
        change LinearMap.range ((quotSpanSingletonResolutionComplex x).d 1 0).hom =
          LinearMap.ker ((quotSpanSingletonResolutionπ x).f 0).hom
        rw [quotSpanSingletonResolutionComplex_d_one_zero, quotSpanSingletonResolutionπ_f_zero,
          hom_ofHom, hom_ofHom, Submodule.ker_mkQ]
        ext (r : R)
        change (∃ y : R, x • y = r) ↔ r ∈ Ideal.span {x}
        rw [Ideal.mem_span_singleton']
        simp only [smul_eq_mul, mul_comm]
      · rw [ModuleCat.epi_iff_surjective]
        exact Submodule.mkQ_surjective _
    | m + 1 =>
      rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..),
        HomologicalComplex.exactAt_iff' _ (m + 2) (m + 1) m (by simp) (by simp)]
      match m with
      | 0 =>
        rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
        change LinearMap.range ((quotSpanSingletonResolutionComplex x).d 2 1).hom =
          LinearMap.ker ((quotSpanSingletonResolutionComplex x).d 1 0).hom
        rw [quotSpanSingletonResolutionComplex_d_succ_succ,
          quotSpanSingletonResolutionComplex_d_one_zero, hom_ofHom, hom_zero]
        refine (LinearMap.ker_eq_bot.2 fun (r : R) (s : R) h ↦ ?_).trans
          LinearMap.range_zero.symm |>.symm
        change x * r = x * s at h
        rw [← sub_eq_zero, ← mul_sub] at h
        exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff.1 hx).1 _ h)
      | m + 1 =>
        exact ShortComplex.exact_of_isZero_X₂ _
          (isZero_quotSpanSingletonResolutionComplex_X x m)

/-- The projective resolution `0 ⟶ R ⟶[x] R ⟶ R/(x)` of `R/(x)`, for a nonzerodivisor `x`. -/
noncomputable def quotSpanSingletonProjectiveResolution (hx : x ∈ nonZeroDivisors R) :
    ProjectiveResolution (ModuleCat.of R (R ⧸ Ideal.span {x})) where
  complex := quotSpanSingletonResolutionComplex x
  π := quotSpanSingletonResolutionπ x
  quasiIso := quasiIso_quotSpanSingletonResolutionπ hx

/-- The kernel of `M ⊗ (x : R ⟶ R)` is the `x`-torsion of `M`. -/
noncomputable def kerLTensorSmulEquiv (M : Type u) [AddCommGroup M] [Module R M] (x : R) :
    LinearMap.ker ((x • LinearMap.id : R →ₗ[R] R).lTensor M) ≃ₗ[R]
      Submodule.torsionBy R M x :=
  LinearEquiv.ofSubmodules (TensorProduct.rid R M) _ _ (by
    ext m
    rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, LinearMap.mem_ker,
      Submodule.mem_torsionBy_iff]
    have h : ∀ t : M ⊗[R] R, (x • LinearMap.id : R →ₗ[R] R).lTensor M t = x • t := by
      intro t
      rw [LinearMap.lTensor_smul, LinearMap.lTensor_id]
      rfl
    rw [LinearEquiv.coe_coe, h, ← map_smul, LinearEquiv.map_eq_zero_iff])

variable [Small.{u} R]

/-- `Tor₁^R(M, R/(x))` is the `x`-torsion `M[x]` of `M`, for a nonzerodivisor `x`: it is the
first homology of `M ⊗ (0 ⟶ R ⟶[x] R)`. -/
noncomputable def torOneQuotSpanSingletonIso (hx : x ∈ nonZeroDivisors R) (M : ModuleCat.{u} R) :
    ((Tor (ModuleCat.{u} R) 1).obj M).obj (ModuleCat.of R (R ⧸ Ideal.span {x})) ≅
      ModuleCat.of R (Submodule.torsionBy R M x) :=
  let K := (((tensoringLeft (ModuleCat.{u} R)).obj M).mapHomologicalComplex _).obj
    (quotSpanSingletonResolutionComplex x)
  have hK : K.d 2 1 = 0 := by
    change M ◁ (quotSpanSingletonResolutionComplex x).d 2 1 = 0
    rw [quotSpanSingletonResolutionComplex_d_succ_succ, MonoidalPreadditive.whiskerLeft_zero]
  (quotSpanSingletonProjectiveResolution hx).isoLeftDerivedObj _ 1 ≪≫
    (K.isoHomologyπ 2 1 (by simp) hK).symm ≪≫ K.cyclesIsoSc' 2 1 0 (by simp) (by simp) ≪≫
    (K.sc' 2 1 0).moduleCatCyclesIso ≪≫
    (LinearEquiv.toModuleIso (LinearEquiv.ofEq _ _ (by
      change LinearMap.ker (M ◁ (quotSpanSingletonResolutionComplex x).d 1 0).hom = _
      rw [quotSpanSingletonResolutionComplex_d_one_zero, hom_whiskerLeft, hom_ofHom]) ≪≫ₗ
      kerLTensorSmulEquiv M x))

omit [Small.{u} R] in
/-- The `x`-torsion of a flat module vanishes, for a nonzerodivisor `x`. -/
lemma isZero_torsionBy_of_flat (hx : x ∈ nonZeroDivisors R) (M : ModuleCat.{u} R)
    (hM : Module.Flat R M) : IsZero (ModuleCat.of R (Submodule.torsionBy R M x)) := by
  have := hM
  have h := (isSMulRegular_iff_torsionBy_eq_bot M x).1
    (Module.Flat.isSMulRegular_of_nonZeroDivisors hx)
  have : Subsingleton (Submodule.torsionBy R M x) := by
    rw [h]
    infer_instance
  exact ModuleCat.isZero_of_subsingleton _

/-- `Tor₁^R(M, R/(x))` vanishes for a flat module `M` and a nonzerodivisor `x`. -/
lemma isZero_torOneQuotSpanSingleton_of_flat (hx : x ∈ nonZeroDivisors R) (M : ModuleCat.{u} R)
    (hM : Module.Flat R M) :
    IsZero (((Tor (ModuleCat.{u} R) 1).obj M).obj (ModuleCat.of R (R ⧸ Ideal.span {x}))) :=
  (isZero_torsionBy_of_flat hx M hM).of_iso (torOneQuotSpanSingletonIso hx M)

end Tor

end ModuleCat

namespace DerivedCategory

variable {R : Type u} [CommRing R] [HasDerivedCategory (ModuleCat.{u} R)] (x : R)

lemma homologyFunctor_map_smul_id (C : DerivedCategory (ModuleCat.{u} R)) (n : ℤ) :
    (homologyFunctor (ModuleCat.{u} R) n).map (x • 𝟙 C) = x • 𝟙 _ := by
  rw [Functor.map_smul, CategoryTheory.Functor.map_id]

variable {x} {C D : DerivedCategory (ModuleCat.{u} R)} {g : C ⟶ D} {h : D ⟶ C⟦(1 : ℤ)⟧}
  (hT : Triangle.mk (x • 𝟙 C) g h ∈ distTriang _) (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁)

include hT in
lemma universalCoefficientSequence_hf :
    (x • 𝟙 _) ≫ (homologyFunctor (ModuleCat.{u} R) n₀).map g = 0 := by
  have h₀ : (x • 𝟙 C) ≫ g = 0 := comp_distTriang_mor_zero₁₂ _ hT
  rw [← homologyFunctor_map_smul_id, ← Functor.map_comp, h₀, Functor.map_zero]

include hT in
lemma universalCoefficientSequence_hg :
    HomologySequence.δ (Triangle.mk (x • 𝟙 C) g h) n₀ n₁ hn ≫ (x • 𝟙 _) = 0 := by
  rw [← homologyFunctor_map_smul_id]
  exact HomologySequence.δ_comp _ hT n₀ n₁ hn

/-- Blueprint `prop-pod-integral-degreewise-form` (the universal coefficient sequence): for a
distinguished triangle `C ⟶[x] C ⟶ D ⟶ C⟦1⟧` of `D(R)` whose first map is the multiplication
by `x`, the short complex

`Hⁿ(C) ⊗_R R/(x) ⟶ Hⁿ(D) ⟶ Hⁿ⁺¹(C)[x]`

of the long exact homology sequence, for `n₁ = n₀ + 1`. -/
noncomputable def universalCoefficientSequence : ShortComplex (ModuleCat.{u} R) :=
  ModuleCat.universalCoefficientShortComplex x ((homologyFunctor (ModuleCat.{u} R) n₀).map g)
    (HomologySequence.δ (Triangle.mk (x • 𝟙 C) g h) n₀ n₁ hn)
    (universalCoefficientSequence_hf hT n₀) (HomologySequence.comp_δ _ hT n₀ n₁ hn)
    (universalCoefficientSequence_hg hT n₀ n₁ hn)

/-- Blueprint `prop-pod-integral-degreewise-form` (the universal coefficient sequence): the
universal coefficient sequence `0 ⟶ Hⁿ(C) ⊗_R R/(x) ⟶ Hⁿ(D) ⟶ Hⁿ⁺¹(C)[x] ⟶ 0` of a
distinguished triangle `C ⟶[x] C ⟶ D ⟶ C⟦1⟧` is short exact. -/
theorem universalCoefficientSequence_shortExact :
    (universalCoefficientSequence hT n₀ n₁ hn).ShortExact :=
  ModuleCat.universalCoefficientShortComplex_shortExact _ _ _ _ _ _
    (homologyFunctor_map_smul_id x C n₀) (homologyFunctor_map_smul_id x C n₁)
    (HomologySequence.exact₂ _ hT n₀) (HomologySequence.exact₃ _ hT n₀ n₁ hn)
    (HomologySequence.exact₁ _ hT n₀ n₁ hn)

end DerivedCategory

namespace CategoryTheory.ShortComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C) {A₁ A₂ A₃ : C}
  (e₁ : S.X₁ ≅ A₁) (e₂ : S.X₂ ≅ A₂) (e₃ : S.X₃ ≅ A₃)

/-- The short complex `A₁ ⟶ A₂ ⟶ A₃` obtained from `S` by transport along isomorphisms
`S.Xᵢ ≅ Aᵢ` of its objects. -/
@[simps]
def transport : ShortComplex C where
  X₁ := A₁
  X₂ := A₂
  X₃ := A₃
  f := e₁.inv ≫ S.f ≫ e₂.hom
  g := e₂.inv ≫ S.g ≫ e₃.hom
  zero := by simp

/-- A short complex is isomorphic to its transport along isomorphisms of its objects. -/
@[simps!]
def transportIso : S ≅ S.transport e₁ e₂ e₃ :=
  isoMk e₁ e₂ e₃ (by simp) (by simp)

variable {S} in
lemma ShortExact.transport (h : S.ShortExact) : (S.transport e₁ e₂ e₃).ShortExact :=
  shortExact_of_iso (S.transportIso e₁ e₂ e₃) h

end CategoryTheory.ShortComplex
