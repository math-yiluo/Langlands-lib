/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.PerfectTower
public import WeilConjectures.Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsExistence
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Basic

/-!
# Normalized towers of perfect complexes over the quotients of a complete local ring

Let `R` be a local ring, complete for an ideal `I = (ϖ)` contained in its maximal ideal (the
intended case being `R = 𝒪_E` and `I = 𝔪_E`). This file specializes the results of
`WeilConjectures.Algebra.Homology.DerivedCategory.PerfectTower` to normalized towers of perfect
complexes over the tower of local rings `n ↦ R ⧸ Iⁿ⁺¹`: the derived limit of such a tower is
represented by a bounded complex of finite free `R`-modules and reduces to the levels, compatible
families of endomorphisms lift to the derived limit, and the trace of a lift is the limit of the
levelwise traces.

## Main definitions

- `Ideal.powSuccMk I n : R →+* R ⧸ Iⁿ⁺¹` and `Ideal.powSuccFactor I n : R ⧸ Iⁿ⁺² →+* R ⧸ Iⁿ⁺¹`:
  the tower of quotients.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated

namespace Ideal

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- The quotient map `R ⟶ R ⧸ Iⁿ⁺¹`, indexing the quotients by powers of `I` from `1`. -/
noncomputable abbrev powSuccMk (n : ℕ) : R →+* R ⧸ I ^ (n + 1) :=
  Ideal.Quotient.mk (I ^ (n + 1))

/-- The transition `R ⧸ Iⁿ⁺² ⟶ R ⧸ Iⁿ⁺¹` between the quotients indexed from `1`. -/
noncomputable abbrev powSuccFactor (n : ℕ) : R ⧸ I ^ (n + 1 + 1) →+* R ⧸ I ^ (n + 1) :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (n + 1).le_succ)

lemma powSuccMk_eq (n : ℕ) : I.powSuccMk n = (I.powSuccFactor n).comp (I.powSuccMk (n + 1)) :=
  (Ideal.Quotient.factor_comp_mk _).symm

lemma powSuccMk_surjective (n : ℕ) : Function.Surjective (I.powSuccMk n) :=
  Ideal.Quotient.mk_surjective

variable {I}

/-- The quotients `R ⧸ Iⁿ⁺¹` of a local ring by the powers of an ideal `I` in its maximal ideal
are local. -/
lemma isLocalRing_quotient_pow_succ [IsLocalRing R] (hle : I ≤ IsLocalRing.maximalIdeal R)
    (n : ℕ) : IsLocalRing (R ⧸ I ^ (n + 1)) :=
  have : Nontrivial (R ⧸ I ^ (n + 1)) := Ideal.Quotient.nontrivial_iff.2 fun h ↦
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top
      (top_le_iff.1 (h ▸ (Ideal.pow_le_self n.succ_ne_zero).trans hle))
  IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective

lemma ker_powSuccMk {ϖ : R} (hI : I = Ideal.span {ϖ}) (n : ℕ) :
    RingHom.ker (I.powSuccMk n) = Ideal.span {ϖ ^ (n + 1)} := by
  rw [Ideal.mk_ker, hI, Ideal.span_singleton_pow]

lemma exists_powSuccMk_eq [IsPrecomplete I R] (x : ∀ n : ℕ, R ⧸ I ^ (n + 1))
    (hx : ∀ n, I.powSuccFactor n (x (n + 1)) = x n) : ∃ r : R, ∀ n, I.powSuccMk n r = x n :=
  IsPrecomplete.exists_mk_eq_of_factor_eq x hx

lemma eq_zero_of_forall_powSuccMk_eq_zero [IsHausdorff I R] (r : R)
    (h : ∀ n, I.powSuccMk n r = 0) : r = 0 :=
  IsHausdorff.eq_zero_of_forall_mk_eq_zero r h

end Ideal

namespace ModuleCat.NormalizedPerfectTower

variable {R : Type (u + 1)} [CommRing R] {I : Ideal R} [IsLocalRing R] [IsAdicComplete I R]
  {ϖ : R} (hϖ : ϖ ∈ IsLocalRing.maximalIdeal R) (hI : I = Ideal.span {ϖ})
  (T : NormalizedPerfectTower I.powSuccMk I.powSuccFactor I.powSuccMk_eq)
  {c : Cone T.restrict} (hc : IsHomotopyLimit c)

omit [IsAdicComplete I R] in
include hϖ hI in
lemma isLocalRing_quotient_pow_succ_of_mem (n : ℕ) : IsLocalRing (R ⧸ I ^ (n + 1)) :=
  Ideal.isLocalRing_quotient_pow_succ
    (by rw [hI, Ideal.span_le, Set.singleton_subset_iff]; exact hϖ) n

omit [IsLocalRing R] [IsAdicComplete I R] in
/-- The derived limit `R lim_n Res Q_n` of a normalized tower of perfect complexes exists: the
derived category of `R`-modules has countable products, products of modules being exact
(`CategoryTheory.derivedCategory_hasCountableProducts`). -/
lemma exists_isHomotopyLimit_restrict : ∃ c : Cone T.restrict, IsHomotopyLimit c :=
  have : AB4StarOfSize.{0} (ModuleCat.{u + 1} R) := AB4StarOfSize_shrink.{0, u + 1} _
  have := derivedCategory_hasCountableProducts (ModuleCat.{u + 1} R)
  exists_isHomotopyLimit _

include hϖ hI hc in
/-- Stacks Tag 09AW, over the rings `R ⧸ Iⁿ⁺¹`: the derived limit `P = R lim_n Res Q_n` of a
normalized tower of perfect complexes is represented by a bounded complex of finite free
`R`-modules. -/
theorem exists_iso_Q_obj_of_isAdicComplete :
    ∃ (M : CochainComplex (ModuleCat.{u + 1} R) ℤ) (a b : ℤ), M.IsStrictlyGE a ∧
      M.IsStrictlyLE b ∧ (∀ i, Module.Free R (M.X i) ∧ Module.Finite R (M.X i)) ∧
      Nonempty (c.pt ≅ DerivedCategory.Q.obj M) :=
  have := isLocalRing_quotient_pow_succ_of_mem hϖ hI
  T.exists_iso_Q_obj_of_isHomotopyLimit I.powSuccMk_surjective (Ideal.ker_powSuccMk hI)
    Ideal.exists_powSuccMk_eq Ideal.eq_zero_of_forall_powSuccMk_eq_zero hc

include hϖ hI hc in
/-- Over the rings `R ⧸ Iⁿ⁺¹`: every leg `pr_n : P ⟶ Res Q_n` of the derived limit exhibits `Q_n` as
`P ⊗ᴸ_R R ⧸ Iⁿ⁺¹`, i.e. the adjoint map `π_n : P ⊗ᴸ_R R ⧸ Iⁿ⁺¹ ⟶ Q_n` is an isomorphism. -/
theorem isDerivedBaseChange_π_app_of_isAdicComplete (n : ℕ) :
    IsDerivedBaseChange (f := I.powSuccMk n) (c.π.app (op n)) :=
  have := isLocalRing_quotient_pow_succ_of_mem hϖ hI
  T.isDerivedBaseChange_π_app I.powSuccMk_surjective (Ideal.ker_powSuccMk hI)
    Ideal.exists_powSuccMk_eq Ideal.eq_zero_of_forall_powSuccMk_eq_zero hc n

include hϖ hI hc in
/-- Lifts over the rings `R ⧸ Iⁿ⁺¹`: every compatible family of endomorphisms of the levels lifts to
an endomorphism `V` of the derived limit, i.e. the isomorphisms `P ⊗ᴸ_R R ⧸ Iⁿ⁺¹ ≅ Q_n` intertwine
`V ⊗ᴸ R ⧸ Iⁿ⁺¹` with the levelwise endomorphisms. -/
theorem exists_isLift_of_isAdicComplete {f : ∀ n, T.obj n ⟶ T.obj n} (hf : T.IsCompatible f) :
    ∃ V : c.pt ⟶ c.pt, T.IsLift c f V :=
  have := isLocalRing_quotient_pow_succ_of_mem hϖ hI
  T.exists_isLift I.powSuccMk_surjective (Ideal.ker_powSuccMk hI) Ideal.exists_powSuccMk_eq
    Ideal.eq_zero_of_forall_powSuccMk_eq_zero hc hf

section Trace

/-! The braiding of the derived categories is the Koszul braiding
`DerivedCategory.braidedCategory'` of the derived tensor product. The trace statements below
hold for every choice of right duals; both are available by perfectness
(`ModuleCat.NormalizedPerfectTower.hasRightDualPt`,
`ModuleCat.NormalizedPerfectTower.hasRightDualObj`). -/

attribute [local instance] DerivedCategory.braidedCategory'

variable [HasRightDual c.pt] [∀ n, HasRightDual (T.obj n)]

include hϖ hI hc in
/-- The categorical trace `tr_R(V ∣ P)` of a lift `V` of a compatible family `f` reduces modulo
`Iⁿ⁺¹` to the traces `tr_{R ⧸ Iⁿ⁺¹}(f n ∣ Q_n)`, so that it is the element `(tr(f n ∣ Q_n))_n` of
`lim_n R ⧸ Iⁿ⁺¹ = R`. -/
theorem exists_trace_eq_of_isAdicComplete {f : ∀ n, T.obj n ⟶ T.obj n}
    (hf : T.IsCompatible f) {V : c.pt ⟶ c.pt} (hV : T.IsLift c f V) :
    ∃ r : R,
      MonoidalCategory.trace V =
        (algebraMap R (End (𝟙_ (DerivedCategory (ModuleCat.{u + 1} R)))) r).asHom ∧
      ∀ n, MonoidalCategory.trace (f n) =
        (algebraMap (R ⧸ I ^ (n + 1))
          (End (𝟙_ (DerivedCategory (ModuleCat.{u + 1} (R ⧸ I ^ (n + 1))))))
            (I.powSuccMk n r)).asHom :=
  have := isLocalRing_quotient_pow_succ_of_mem hϖ hI
  T.exists_trace_eq_of_isLift I.powSuccMk_surjective (Ideal.ker_powSuccMk hI)
    Ideal.exists_powSuccMk_eq Ideal.eq_zero_of_forall_powSuccMk_eq_zero hc hf hV

include hϖ hI hc in
/-- The categorical trace of a lift of a compatible family does not depend on the lift. -/
theorem trace_eq_of_isAdicComplete {f : ∀ n, T.obj n ⟶ T.obj n} (hf : T.IsCompatible f)
    {V V' : c.pt ⟶ c.pt} (hV : T.IsLift c f V) (hV' : T.IsLift c f V') :
    MonoidalCategory.trace V = MonoidalCategory.trace V' :=
  have := isLocalRing_quotient_pow_succ_of_mem hϖ hI
  T.trace_eq_of_isLift I.powSuccMk_surjective (Ideal.ker_powSuccMk hI)
    Ideal.exists_powSuccMk_eq Ideal.eq_zero_of_forall_powSuccMk_eq_zero hc hf hV hV'

end Trace

end ModuleCat.NormalizedPerfectTower
