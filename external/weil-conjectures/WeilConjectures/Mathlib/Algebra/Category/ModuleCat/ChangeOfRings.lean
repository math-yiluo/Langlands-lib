/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import WeilConjectures.Mathlib.Algebra.Category.Grp.ZModuleEquivalence

/-!
# Extension of scalars along an algebra map as a tensor product

For an `R`-algebra `S`, the object `(ModuleCat.extendScalars (algebraMap R S)).obj N` is the
tensor product `S ⊗[R] N` for the `R`-module structure on `S` coming from the algebra structure
(`ModuleCat.tensorEquivExtendScalars`). The two are not definitionally equal, since
`ModuleCat.extendScalars` uses the module structure on `S` obtained by restriction of scalars.

Coinduction `ModuleCat.coinduce R : AddCommGrpCat ⥤ ModuleCat R`, sending an abelian group `A` to
`Hom_ℤ(R, A)`, is right adjoint to the forgetful functor (`ModuleCat.forget₂CoinduceAdj`); as an
abelian group, `Hom_ℤ(R, A)` is `R →+ A` (`ModuleCat.coinduceObjAddEquiv`).
-/

@[expose] public section

universe u

open CategoryTheory TensorProduct

/-- For an `R`-algebra `S`, `S ⊗[R] N` is `(ModuleCat.extendScalars (algebraMap R S)).obj N`. -/
noncomputable def ModuleCat.tensorEquivExtendScalars (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (N : ModuleCat.{u} R) :
    S ⊗[R] N ≃ₗ[S] (ModuleCat.extendScalars (algebraMap R S)).obj N := by
  let T := (ModuleCat.extendScalars (algebraMap R S)).obj N
  let S' := (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)
  let toFun : S ⊗[R] N →ₗ[R] TensorProduct R S' N :=
    TensorProduct.lift
      { toFun s := TensorProduct.mk R S' N s
        map_add' s s' := (TensorProduct.mk R S' N).map_add s s'
        map_smul' r s :=
          (congrArg (TensorProduct.mk R S' N) (Algebra.smul_def r s)).trans
            ((TensorProduct.mk R S' N).map_smul r (s : S')) }
  let invFun : TensorProduct R S' N →ₗ[R] S ⊗[R] N :=
    TensorProduct.lift
      { toFun s := TensorProduct.mk R S N (show S from s)
        map_add' s s' := (TensorProduct.mk R S N).map_add (show S from s) (show S from s')
        map_smul' r s :=
          (congrArg (TensorProduct.mk R S N) (Algebra.smul_def r (show S from s)).symm).trans
            ((TensorProduct.mk R S N).map_smul r (show S from s)) }
  have h₁ : ∀ x, invFun (toFun x) = x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul s n => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have h₂ : ∀ x, toFun (invFun x) = x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul s n => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  exact
    { toFun := toFun
      invFun := invFun
      map_add' := toFun.map_add
      map_smul' s x := by
        induction x using TensorProduct.inductionOn with
        | tmul s' n => rfl
        | add x y hx hy =>
          rw [smul_add, map_add, hx, hy, map_add]
          exact (smul_add s _ _).symm
      left_inv := h₁
      right_inv := h₂ }

lemma ModuleCat.tensorEquivExtendScalars_tmul (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (N : ModuleCat.{u} R) (s : S) (n : N) :
    ModuleCat.tensorEquivExtendScalars R S N (s ⊗ₜ n) =
      TensorProduct.tmul R
        (M := (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S))
        s n :=
  rfl

namespace ModuleCat

variable {Λ : Type u} [CommRing Λ] (ϖ : Λ)

/-- For `f : Λ → Λ/(ϖ)`, the counit `Hom_Λ(Λ/ϖ, M) ⟶ M` of restriction and coextension of
scalars, evaluation at `1`, followed by multiplication by `ϖ`, as a short complex. -/
noncomputable def coextendQuotientShortComplex (M : ModuleCat.{u} Λ) :
    ShortComplex (ModuleCat.{u} Λ) :=
  ShortComplex.mk
    ((restrictCoextendScalarsAdj.{u} (Ideal.Quotient.mk (Ideal.span {ϖ}))).counit.app M)
    (ϖ • 𝟙 M) (by
      ext g
      change ϖ • (CoextendScalars.equiv _ M g) (1 : Λ ⧸ Ideal.span {ϖ}) = 0
      rw [← map_smul]
      change (CoextendScalars.equiv _ M g) (Ideal.Quotient.mk (Ideal.span {ϖ}) ϖ * 1) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self ϖ), zero_mul, map_zero])

lemma mono_coextendQuotientShortComplex_f (M : ModuleCat.{u} Λ) :
    Mono (coextendQuotientShortComplex ϖ M).f := by
  rw [mono_iff_injective]
  intro (g : (coextendScalars (Ideal.Quotient.mk (Ideal.span {ϖ}))).obj M)
    (g' : (coextendScalars (Ideal.Quotient.mk (Ideal.span {ϖ}))).obj M) h
  change g (1 : Λ ⧸ Ideal.span {ϖ}) = g' (1 : Λ ⧸ Ideal.span {ϖ}) at h
  refine CoextendScalars.ext (LinearMap.ext fun (s : Λ ⧸ Ideal.span {ϖ}) ↦ ?_)
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
  have e : ∀ g : (coextendScalars (Ideal.Quotient.mk (Ideal.span {ϖ}))).obj M,
      g (Ideal.Quotient.mk _ r) = r • g (1 : Λ ⧸ Ideal.span {ϖ}) :=
    fun g ↦ by
      rw [← map_smul]
      congr 1
      change _ = Ideal.Quotient.mk _ r * 1
      rw [mul_one]
  change g (Ideal.Quotient.mk _ r) = g' (Ideal.Quotient.mk _ r)
  rw [e, e, h]

lemma exact_coextendQuotientShortComplex (M : ModuleCat.{u} Λ) :
    (coextendQuotientShortComplex ϖ M).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  change ϖ • x = 0 at hx
  have hle : Ideal.span {ϖ} ≤ LinearMap.ker (LinearMap.toSpanSingleton Λ M x) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hx
  let φ : (restrictScalars (Ideal.Quotient.mk (Ideal.span {ϖ}))).obj
      (of (Λ ⧸ Ideal.span {ϖ}) (Λ ⧸ Ideal.span {ϖ})) →ₗ[Λ] M :=
    { toFun s := Submodule.liftQ _ (LinearMap.toSpanSingleton Λ M x) hle s
      map_add' a b := map_add _ a b
      map_smul' r s := by
        obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective s
        have h : Ideal.Quotient.mk (Ideal.span {ϖ}) r * Ideal.Quotient.mk _ t =
            Submodule.Quotient.mk (p := Ideal.span {ϖ}) (r * t) := (map_mul _ r t).symm
        change Submodule.liftQ _ _ hle (Ideal.Quotient.mk _ r * Ideal.Quotient.mk _ t) =
          r • Submodule.liftQ _ _ hle (Submodule.Quotient.mk t)
        rw [h, Submodule.liftQ_apply, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply,
          LinearMap.toSpanSingleton_apply, mul_smul] }
  refine ⟨(CoextendScalars.equiv _ M).symm φ, ?_⟩
  change φ (show Λ ⧸ Ideal.span {ϖ} from 1) = x
  change Submodule.liftQ _ _ hle (Submodule.Quotient.mk (1 : Λ)) = x
  rw [Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul]

end ModuleCat

namespace ModuleCat

open MonoidalCategory

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- For an `R`-algebra `S`, the tensor product `N ⊗[R] S` is the extension of scalars
`S ⊗[R] N` of `N` with its scalars restricted back to `R`. -/
noncomputable def tensorEquivRestrictScalarsExtendScalars (N : ModuleCat.{u} R) :
    N ⊗[R] S ≃ₗ[R] (restrictScalars (algebraMap R S)).obj
      ((extendScalars (algebraMap R S)).obj N) where
  __ := (TensorProduct.comm R N S).toAddEquiv.trans (tensorEquivExtendScalars R S N).toAddEquiv
  map_smul' r x := by
    change tensorEquivExtendScalars R S N (TensorProduct.comm R N S (r • x)) =
      algebraMap R S r • tensorEquivExtendScalars R S N (TensorProduct.comm R N S x)
    rw [← map_smul, map_smul, algebraMap_smul]

@[simp]
lemma tensorEquivRestrictScalarsExtendScalars_tmul (N : ModuleCat.{u} R) (n : N) (s : S) :
    tensorEquivRestrictScalarsExtendScalars R S N (n ⊗ₜ s) =
      TensorProduct.tmul R
        (M := (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)) s n :=
  rfl

/-- **Extension followed by restriction of scalars is tensoring with `S`.** For an `R`-algebra
`S`, extending the scalars of an `R`-module `N` to `S` and restricting them back to `R` gives
`N ⊗[R] S`, naturally in `N`. -/
noncomputable def extendScalarsCompRestrictScalarsIso' :
    extendScalars.{u, u, u} (algebraMap R S) ⋙ restrictScalars (algebraMap R S) ≅
      tensorRight (ModuleCat.of R S) :=
  NatIso.ofComponents (fun N ↦ (tensorEquivRestrictScalarsExtendScalars R S N).toModuleIso.symm)
    (fun {M N} f ↦ by
      ext x
      obtain ⟨y, rfl⟩ := (tensorEquivRestrictScalarsExtendScalars R S M).surjective x
      apply (tensorEquivRestrictScalarsExtendScalars R S N).injective
      induction y using TensorProduct.inductionOn with
      | tmul m s => rfl
      | add x y hx hy => simp only [map_add, hx, hy])

end ModuleCat

namespace ModuleCat

variable {R S : Type (u + 1)} [CommRing R] [CommRing S] (φ : R →+* S)

instance : Limits.PreservesLimitsOfSize.{u, u + 1}
    (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ) :=
  (ModuleCat.restrictCoextendScalarsAdj.{u + 1} φ).rightAdjoint_preservesLimits

/- Mathlib's instance is stated for `coextendScalars.{u₁, u₂, max u₂ w}`, and unifying
`u + 1 =?= max (u + 1) ?w` gets stuck, so instance search does not find it for modules in the
universe of the rings. -/
instance : (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ).IsRightAdjoint :=
  (ModuleCat.restrictCoextendScalarsAdj.{u + 1} φ).isRightAdjoint

end ModuleCat

namespace ModuleCat

variable (R : Type u) [Ring R]

/-- Coinduction from abelian groups to `R`-modules: an abelian group `A` is sent to
`Hom_ℤ(R, A)`, on which `R` acts through the source. -/
noncomputable def coinduce : AddCommGrpCat.{u} ⥤ ModuleCat.{u} R :=
  AddCommGrpCat.toModuleCatInt ⋙ coextendScalars (Int.castRingHom R)

/-- The underlying abelian group of an `R`-module is its underlying `ℤ`-module, obtained by
restriction of scalars along `ℤ → R`. -/
noncomputable def forget₂AddCommGrpIsoRestrictScalars :
    forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ≅
      restrictScalars.{u} (Int.castRingHom R) ⋙ forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u} :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

/-- Forgetting the `R`-module structure is left adjoint to coinduction. -/
noncomputable def forget₂CoinduceAdj : forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u} ⊣ coinduce R :=
  ((restrictCoextendScalarsAdj (Int.castRingHom R)).comp
    forget₂AddCommGrpToModuleCatIntAdj).ofNatIsoLeft (forget₂AddCommGrpIsoRestrictScalars R).symm

instance : (coinduce R).IsRightAdjoint :=
  (forget₂CoinduceAdj R).isRightAdjoint

/-- The coinduced module `Hom_ℤ(R, A)` is, as an abelian group, the group `R →+ A`. -/
noncomputable def coinduceObjAddEquiv (A : AddCommGrpCat.{u}) :
    (coinduce R).obj A ≃+ (R →+ A) where
  toFun f := LinearMap.toAddMonoidHom f
  invFun g :=
    { toFun := g
      map_add' := map_add g
      map_smul' n x := (congrArg g (Int.cast_smul_eq_zsmul R n (x : R))).trans (map_zsmul g n x) }
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp]
lemma coinduceObjAddEquiv_map_apply {A B : AddCommGrpCat.{u}} (g : A ⟶ B)
    (f : (coinduce R).obj A) (x : R) :
    coinduceObjAddEquiv R B ((coinduce R).map g f) x = g (coinduceObjAddEquiv R A f x) := by
  with_unfolding_all rfl

end ModuleCat
