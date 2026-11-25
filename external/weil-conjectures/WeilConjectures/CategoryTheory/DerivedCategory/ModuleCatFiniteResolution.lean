/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.ModuleCatGeneration

/-!
# Finite free resolutions and countable telescopes

Let `R` be a noetherian commutative ring and `M` a finitely generated `R`-module. Covering
successive kernels by finite free modules gives a projective resolution of `M` all of whose terms
are free of finite rank (`ModuleCat.finiteFreeResolution`).

Let `τ : F ⟶ G` be a natural transformation, compatible with the shifts, between triangulated
functors `D(R) ⥤ T` which preserve *countable* coproducts. If `τ` is an isomorphism at the free
modules of finite rank `(Fin n → R)[0]`, then it is an isomorphism at `M[0]` for every finitely
generated `M` (`DerivedCategory.isIso_app_singleFunctor_obj_of_finite`): `M` is the homotopy
colimit of the stupid truncations of its finite free resolution, bounded complexes of finite free
modules, along the telescope triangle, which only involves countable coproducts. Unlike
`DerivedCategory.isIso_app_singleFunctor_obj`, no infinite free modules and hence no
uncountable coproducts appear.
-/

@[expose] public section

universe w v

open CategoryTheory Category Limits Pretriangulated

namespace ModuleCat

variable (R : Type v) [CommRing R] [IsNoetherianRing R]

section FiniteFreeResolution

/-- The rank of a finite free module mapping onto a submodule `K` of `Rᵐ`. -/
noncomputable def finCoverRank {m : ℕ} (K : Submodule R (Fin m → R)) : ℕ :=
  (Module.Finite.exists_fin' R K).choose

/-- A linear map from a free module of finite rank onto a submodule `K` of `Rᵐ`. -/
noncomputable def finCover {m : ℕ} (K : Submodule R (Fin m → R)) :
    (Fin (finCoverRank R K) → R) →ₗ[R] (Fin m → R) :=
  K.subtype ∘ₗ (Module.Finite.exists_fin' R K).choose_spec.choose

lemma range_finCover {m : ℕ} (K : Submodule R (Fin m → R)) :
    LinearMap.range (finCover R K) = K := by
  rw [finCover, LinearMap.range_comp, LinearMap.range_eq_top.2
    (Module.Finite.exists_fin' R K).choose_spec.choose_spec, Submodule.map_top,
    Submodule.range_subtype]

variable (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- The rank of the free module of finite rank mapping onto `M`. -/
noncomputable def augmentationRank : ℕ := (Module.Finite.exists_fin' R M).choose

/-- A surjection from a free module of finite rank onto `M`. -/
noncomputable def augmentation : (Fin (augmentationRank R M) → R) →ₗ[R] M :=
  (Module.Finite.exists_fin' R M).choose_spec.choose

omit [IsNoetherianRing R] in
lemma augmentation_surjective : Function.Surjective (augmentation R M) :=
  (Module.Finite.exists_fin' R M).choose_spec.choose_spec

/-- The terms of the finite free resolution of `M`: the `n`-th term is `R^{rₙ}`, together with
the kernel of the map out of it. -/
noncomputable def finiteFreeResolutionStep : ℕ → Σ m : ℕ, Submodule R (Fin m → R)
  | 0 => ⟨augmentationRank R M, LinearMap.ker (augmentation R M)⟩
  | n + 1 => ⟨finCoverRank R (finiteFreeResolutionStep n).2,
      LinearMap.ker (finCover R (finiteFreeResolutionStep n).2)⟩

/-- The `n`-th term `R^{rₙ}` of the finite free resolution of `M`. -/
noncomputable abbrev finiteFreeResolutionX (n : ℕ) : ModuleCat.{v} R :=
  ModuleCat.of R (Fin (finiteFreeResolutionStep R M n).1 → R)

/-- The differential `R^{r_{n+1}} ⟶ R^{rₙ}` of the finite free resolution of `M`, a map onto the
kernel of the previous differential. -/
noncomputable def finiteFreeResolutionD (n : ℕ) :
    finiteFreeResolutionX R M (n + 1) ⟶ finiteFreeResolutionX R M n :=
  ModuleCat.ofHom (finCover R (finiteFreeResolutionStep R M n).2)

lemma range_finiteFreeResolutionD (n : ℕ) :
    LinearMap.range (finiteFreeResolutionD R M n).hom = (finiteFreeResolutionStep R M n).2 :=
  range_finCover R _

lemma ker_finiteFreeResolutionD (n : ℕ) :
    LinearMap.ker (finiteFreeResolutionD R M n).hom = (finiteFreeResolutionStep R M (n + 1)).2 :=
  rfl

lemma finiteFreeResolutionD_comp (n : ℕ) :
    finiteFreeResolutionD R M (n + 1) ≫ finiteFreeResolutionD R M n = 0 := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  have : (finiteFreeResolutionD R M (n + 1)).hom x ∈
      LinearMap.ker (finiteFreeResolutionD R M n).hom := by
    rw [ker_finiteFreeResolutionD, ← range_finiteFreeResolutionD]
    exact LinearMap.mem_range_self _ x
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply]
  exact this

/-- The finite free resolution of `M`, as a chain complex. -/
noncomputable def finiteFreeResolutionComplex : ChainComplex (ModuleCat.{v} R) ℕ :=
  ChainComplex.of (finiteFreeResolutionX R M) (finiteFreeResolutionD R M)
    (finiteFreeResolutionD_comp R M)

lemma finiteFreeResolutionComplex_d_succ (n : ℕ) :
    (finiteFreeResolutionComplex R M).d (n + 1) n = finiteFreeResolutionD R M n := by
  simp [finiteFreeResolutionComplex]

/-- The augmentation `R^{r₀} ⟶ M` of the finite free resolution. -/
noncomputable def finiteFreeResolutionπ :
    finiteFreeResolutionComplex R M ⟶ (ChainComplex.single₀ (ModuleCat.{v} R)).obj
      (ModuleCat.of R M) :=
  ((finiteFreeResolutionComplex R M).toSingle₀Equiv _).symm
    ⟨ModuleCat.ofHom (augmentation R M), by
      rw [finiteFreeResolutionComplex_d_succ]
      refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
      have : (finiteFreeResolutionD R M 0).hom x ∈ LinearMap.ker (augmentation R M) := by
        change _ ∈ (finiteFreeResolutionStep R M 0).2
        rw [← range_finiteFreeResolutionD]
        exact LinearMap.mem_range_self _ x
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
        ModuleCat.hom_zero, LinearMap.zero_apply]
      exact this⟩

lemma finiteFreeResolutionπ_f_zero :
    (finiteFreeResolutionπ R M).f 0 = ModuleCat.ofHom (augmentation R M) := by
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance quasiIso_finiteFreeResolutionπ : QuasiIso (finiteFreeResolutionπ R M) where
  quasiIsoAt m := by
    induction m with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros' _ rfl rfl rfl]
      constructor
      · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
        change LinearMap.range ((finiteFreeResolutionComplex R M).d 1 0).hom =
          LinearMap.ker ((finiteFreeResolutionπ R M).f 0).hom
        rw [finiteFreeResolutionComplex_d_succ, finiteFreeResolutionπ_f_zero,
          range_finiteFreeResolutionD]
        rfl
      · rw [ModuleCat.epi_iff_surjective]
        change Function.Surjective ((finiteFreeResolutionπ R M).f 0).hom
        rw [finiteFreeResolutionπ_f_zero]
        exact augmentation_surjective R M
    | succ m _ =>
      rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..),
        HomologicalComplex.exactAt_iff' _ (m + 2) (m + 1) m (by simp) (by simp)]
      rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
      change LinearMap.range ((finiteFreeResolutionComplex R M).d (m + 1 + 1) (m + 1)).hom =
        LinearMap.ker ((finiteFreeResolutionComplex R M).d (m + 1) m).hom
      rw [finiteFreeResolutionComplex_d_succ, finiteFreeResolutionComplex_d_succ,
        range_finiteFreeResolutionD, ker_finiteFreeResolutionD]

instance (n : ℕ) : Projective ((finiteFreeResolutionComplex R M).X n) :=
  inferInstanceAs (Projective (ModuleCat.of R (Fin (finiteFreeResolutionStep R M n).1 → R)))

/-- The finite free resolution of a finitely generated module `M` over a noetherian ring: a
projective resolution whose `n`-th term is free of finite rank. -/
noncomputable def finiteFreeResolution : ProjectiveResolution (ModuleCat.of R M) where
  complex := finiteFreeResolutionComplex R M
  π := finiteFreeResolutionπ R M

end FiniteFreeResolution

end ModuleCat

namespace DerivedCategory

open CochainComplex

variable {R : Type v} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
  {T : Type*} [Category* T] {F G : DerivedCategory (ModuleCat.{v} R) ⥤ T} (τ : F ⟶ G)
  [HasShift T ℤ] [F.CommShift ℤ] [G.CommShift ℤ] [NatTrans.CommShift τ ℤ]
  [Preadditive T] [HasZeroObject T] [∀ n : ℤ, (CategoryTheory.shiftFunctor T n).Additive]
  [Pretriangulated T] [F.IsTriangulated] [G.IsTriangulated]

/-- The telescope argument `DerivedCategory.isIso_app_Q_obj_of_telescope` for functors which
are only assumed to preserve countable coproducts: if a complex `L` is the union of an increasing
sequence of subcomplexes `N n` at which `τ` is an isomorphism, then `τ` is an isomorphism at
`L`. -/
lemma isIso_app_Q_obj_of_telescope_of_nat [PreservesColimitsOfShape (Discrete ℕ) F]
    [PreservesColimitsOfShape (Discrete ℕ) G]
    {L : CochainComplex (ModuleCat.{v} R) ℤ} (N : ℕ → L.SubcomplexFamily)
    (hN : ∀ n, N n ≤ N (n + 1)) (hL : ∀ i (x : L.X i), ∃ n, x ∈ (N n).N i)
    (h : ∀ n, IsIso (τ.app (Q.obj (subcomplex (N n))))) :
    IsIso (τ.app (Q.obj L)) := by
  have h₁ : IsIso (τ.app (Q.obj (∐ fun n ↦ subcomplex (N n)))) :=
    NatTrans.isIso_app_of_isColimit_cofan τ (isColimitCofanMkQObj (coproductIsCoproduct _)) h
  exact NatTrans.isIso_app_obj₃_of_isIso_app_obj₁₂ τ
    (triangleOfSES_distinguished (telescopeShortComplex_shortExact N hN hL)) h₁ h₁

omit [NatTrans.CommShift τ ℤ] in
/-- `τ` is an isomorphism at a zero module placed in degree `0`. -/
lemma isIso_app_singleFunctor_obj_of_isZero {M : ModuleCat.{v} R} (hM : IsZero M) :
    IsIso (τ.app ((singleFunctor _ 0).obj M)) :=
  have hZ := (singleFunctor (ModuleCat.{v} R) 0).map_isZero hM
  ⟨⟨0, (F.map_isZero hZ).eq_of_src _ _, (G.map_isZero hZ).eq_of_src _ _⟩⟩

/-- **Finitely generated modules from finite free modules, with countable coproducts.** Let
`R` be noetherian and `τ : F ⟶ G` a natural transformation, compatible with the shifts, between
triangulated functors `D(R) ⥤ T` which preserve countable coproducts. If `τ` is an isomorphism at
every free module of finite rank `(Fin n → R)[0]`, then it is an isomorphism at `M[0]` for every
finitely generated module `M`.

The finite free resolution `P` of `M` (`ModuleCat.finiteFreeResolution`) is the union of its
stupid truncations, bounded complexes of free modules of finite rank, at which `τ` is an
isomorphism by induction on the length; the telescope triangle
(`DerivedCategory.isIso_app_Q_obj_of_telescope_of_nat`) concludes. -/
theorem isIso_app_singleFunctor_obj_of_finite [IsNoetherianRing R]
    [PreservesColimitsOfShape (Discrete ℕ) F] [PreservesColimitsOfShape (Discrete ℕ) G]
    (h : ∀ n : ℕ, IsIso (τ.app ((singleFunctor _ 0).obj (ModuleCat.of R (Fin n → R)))))
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsIso (τ.app ((singleFunctor _ 0).obj (ModuleCat.of R M))) := by
  let Res := ModuleCat.finiteFreeResolution R M
  let P := Res.cochainComplex
  -- `τ` is an isomorphism at the terms of `P`
  have hX (i : ℤ) : IsIso (τ.app ((singleFunctor _ 0).obj (P.X i))) := by
    obtain hi | hi := le_or_gt i 0
    · obtain ⟨k, hk⟩ : ∃ k : ℕ, -(k : ℤ) = i := ⟨(-i).toNat, by lia⟩
      rw [← NatTrans.isIso_app_iff_of_iso τ
        ((singleFunctor _ 0).mapIso (Res.cochainComplexXIso i k hk).symm)]
      exact h _
    · exact isIso_app_singleFunctor_obj_of_isZero τ (P.isZero_of_isStrictlyLE 0 i hi)
  -- and at the terms of its stupid truncations
  have hX' (m : ℕ) (i : ℤ) :
      IsIso (τ.app ((singleFunctor _ 0).obj ((subcomplex (stupidTruncGEFamily P (-m))).X i))) := by
    by_cases hi : -(m : ℤ) ≤ i
    · have := isIso_subcomplexι_stupidTruncGEFamily_f (L := P) (Or.inl hi)
      rw [NatTrans.isIso_app_iff_of_iso τ ((singleFunctor _ 0).mapIso
        (asIso ((subcomplexι (stupidTruncGEFamily P (-m))).f i)))]
      exact hX i
    · exact isIso_app_singleFunctor_obj_of_isZero τ
        ((subcomplex (stupidTruncGEFamily P (-m))).isZero_of_isStrictlyGE (-m) i (by lia))
  have hP : IsIso (τ.app (Q.obj P)) :=
    isIso_app_Q_obj_of_telescope_of_nat τ (fun m ↦ stupidTruncGEFamily P (-m))
      (fun m ↦ stupidTruncGEFamily_le_of_le (by lia))
      (fun i x ↦ ⟨(-i).toNat, (mem_stupidTruncGEFamily_iff x).2 (Or.inl (by lia))⟩)
      fun m ↦ isIso_app_Q_obj_of_isStrictlyGE_of_isStrictlyLE τ _ (-m) 0 (hX' m)
  exact (NatTrans.isIso_app_iff_of_iso τ (asIso (Q.map Res.π'))).1 hP

end DerivedCategory
