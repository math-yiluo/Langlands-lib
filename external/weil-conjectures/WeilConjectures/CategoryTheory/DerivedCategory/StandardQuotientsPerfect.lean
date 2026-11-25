/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.NumberTheory.Padics.RingHoms
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr

set_option linter.privateModule false

/-!
# Perfectness of the standard coefficient quotients

Source: literature/blueprint/master/blueprint/sec-proper-base-change/sk-thm-properbasechange/
lem-weil-pbc-standard-quotients-perfect.md, node order 1254; Stacks Project, Tag 0657
(blueprint: lemma-reduction-derived-nakayama--1).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace AlgebraicGeometry

/-- An exact scalar presentation gives its normalized two-term finite-free resolution.
Source: Stacks Tags 0115 and 0657, the cohomology calculation in proof steps 3--4
(blueprint: lemma-reduction-derived-nakayama--1). -/
private theorem twoTermResolution {R : Type u} [CommRing R]
    (a : R) (M : ModuleCat.{u} R)
    (q : ModuleCat.of R R ⟶ M)
    (hw : ModuleCat.ofHom (LinearMap.mulLeft R a) ≫ q = 0)
    (hex : (ShortComplex.mk (ModuleCat.ofHom (LinearMap.mulLeft R a)) q hw).Exact)
    [Mono (ModuleCat.ofHom (LinearMap.mulLeft R a))] [Epi q] :
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ)
      (_hge : P.IsStrictlyGE (-1)) (_hle : P.IsStrictlyLE 0),
      (∀ i : ℤ, Module.Free R (P.X i) ∧ Module.Finite R (P.X i)) ∧
      ∃ (em : P.X (-1) ≅ ModuleCat.of R R) (e0 : P.X 0 ≅ ModuleCat.of R R),
        P.d (-1) 0 = em.hom ≫ ModuleCat.ofHom (LinearMap.mulLeft R a) ≫ e0.inv ∧
        ∃ ε : P ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M,
          QuasiIso ε ∧
          ε.f 0 ≫ (singleObjXSelf (.up ℤ) 0 M).hom = e0.hom ≫ q ∧
          (∀ i : ℤ, i ≠ 0 → ε.f i = 0) := by
  classical
  let f : ModuleCat.of R R ⟶ ModuleCat.of R R := ModuleCat.ofHom (LinearMap.mulLeft R a)
  have hrel : (ComplexShape.up ℤ).Rel (-1) 0 := by simp
  let P : CochainComplex (ModuleCat.{u} R) ℤ := double f hrel
  let em := doubleXIso₀ f hrel
  let e0 := doubleXIso₁ f hrel (by omega)
  have hz (i : ℤ) (hm : i ≠ -1) (h0 : i ≠ 0) : IsZero (P.X i) :=
    isZero_double_X f hrel i hm h0
  have hge : P.IsStrictlyGE (-1) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact hz i (by omega) (by omega)
  have hle : P.IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact hz i (by omega) (by omega)
  have hterms (i : ℤ) : Module.Free R (P.X i) ∧ Module.Finite R (P.X i) := by
    by_cases hm : i = -1
    · subst i
      exact ⟨Module.Free.of_equiv em.toLinearEquiv.symm,
        Module.Finite.equiv em.toLinearEquiv.symm⟩
    · by_cases h0 : i = 0
      · subst i
        exact ⟨Module.Free.of_equiv e0.toLinearEquiv.symm,
          Module.Finite.equiv e0.toLinearEquiv.symm⟩
      · have : Subsingleton (P.X i) := ModuleCat.subsingleton_of_isZero (hz i hm h0)
        exact ⟨inferInstance, inferInstance⟩
  let L := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M
  let e := singleObjXSelf (.up ℤ) 0 M
  have hL (i : ℤ) (hi : i ≠ 0) : IsZero (L.X i) :=
    isZero_single_obj_X (.up ℤ) 0 M i hi
  let ε : P ⟶ L := mkHomFromDouble hrel (by omega) 0 (q ≫ e.inv)
    (by change 0 ≫ L.d (-1) 0 = f ≫ q ≫ e.inv
        rw [zero_comp, ← Category.assoc, show f ≫ q = 0 from hw, zero_comp])
    (by intro i hi; exact (hL i (by simp only [ComplexShape.up_Rel] at hi; omega)).eq_of_tgt _ _)
  have hε0 : ε.f 0 ≫ e.hom = e0.hom ≫ q := by
    simp [ε, e0]
  have hεi (i : ℤ) (hi : i ≠ 0) : ε.f i = 0 := (hL i hi).eq_of_tgt _ _
  have hmono : Mono (P.d (-1) 0) := by
    dsimp [P]
    rw [double_d f hrel (by omega)]
    infer_instance
  have hε : QuasiIso ε := by
    rw [quasiIso_iff]
    intro i
    by_cases hi : i = 0
    · subst i
      rw [quasiIsoAt_iff' ε (-1) 0 1 (by simp) (by simp)]
      apply (ShortComplex.quasiIso_iff_of_zeros' _
        ((hz 1 (by omega) (by omega)).eq_of_tgt _ _)
        ((hL (-1) (by omega)).eq_of_src _ _)
        ((hL 1 (by omega)).eq_of_tgt _ _)).2
      have heq : P.d (-1) 0 ≫ ε.f 0 = 0 := by
        rw [← ε.comm]
        simp [hεi (-1) (by omega)]
      let S := ShortComplex.mk (P.d (-1) 0) (ε.f 0) heq
      let T := ShortComplex.mk f q hw
      let iso : S ≅ T := ShortComplex.isoMk em e0 e
        (by dsimp [S, T, P, em, e0]; rw [double_d f hrel (by omega)]; simp)
        hε0.symm
      have hs : S.Exact := (ShortComplex.exact_iff_of_iso iso).2 hex
      have : Epi (ε.f 0) := by
        have : Epi (ε.f 0 ≫ e.hom) := by rw [hε0]; infer_instance
        exact (epi_comp_iff_of_isIso (ε.f 0) e.hom).1 inferInstance
      exact ⟨hs, show Epi (ε.f 0) from inferInstance⟩
    · have hLex : L.ExactAt i := ExactAt.of_isZero (hL i hi)
      rw [quasiIsoAt_iff_exactAt' ε i hLex]
      by_cases hm : i = -1
      · subst i
        rw [HomologicalComplex.exactAt_iff' P (-2) (-1) 0 (by simp) (by simp)]
        apply (ShortComplex.exact_iff_mono _ ((hz (-2) (by omega) (by omega)).eq_of_src _ _)).2
        exact hmono
      · exact ExactAt.of_isZero (hz i hm hi)
  exact ⟨P, hge, hle, hterms, em, e0, double_d f hrel (by omega), ε, hε, hε0, hεi⟩

/-- A quotient whose kernel is a principal ideal is exact after scalar multiplication.
Source: the elementary divisibility calculation in proof step 2
(blueprint: lemma-reduction-derived-nakayama--1). -/
private theorem principalExact {R : Type u} [CommRing R]
    (a : R) (M : ModuleCat.{u} R) (q : ModuleCat.of R R ⟶ M)
    (hq : ∀ x : R, q x = 0 ↔ x ∈ Ideal.span ({a} : Set R)) :
    ∃ hw : ModuleCat.ofHom (LinearMap.mulLeft R a) ≫ q = 0,
      (ShortComplex.mk (ModuleCat.ofHom (LinearMap.mulLeft R a)) q hw).Exact := by
  have hw : ModuleCat.ofHom (LinearMap.mulLeft R a) ≫ q = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply (hq (a * x)).2
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton a))
  refine ⟨hw, ?_⟩
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  have : a ∣ x := (Ideal.mem_span_singleton).1 ((hq x).1 hx)
  obtain ⟨y, hy⟩ := this
  exact ⟨y, hy.symm⟩

/-- The recorded generator of the nonzero maximal ideal is nonzero.
Source: `Padic.extension_integers_dvr`, proof step 1
(blueprint: lemma-reduction-derived-nakayama--1). -/
private theorem uniformizer_ne_zero (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    Padic.coefficientExtensionUniformizer l E ≠ 0 := by
  let h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hm : Padic.coefficientExtensionMaximalIdeal l E ≠ ⊥ :=
    h.2.2.2.2.2.2.2.2.2.1
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
        Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  intro h0
  apply hm
  rw [← hgen, h0, Ideal.span_singleton_eq_bot]

end AlgebraicGeometry
