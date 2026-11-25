/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Homology.Double
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

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

/-- The canonical quotient identification retains the specified reduction homomorphism.
Source: Mathlib `PadicInt.ker_toZModPow`, proof step 1
(blueprint: lemma-reduction-derived-nakayama--1). -/
private theorem baseEquiv (l : ℕ) [Fact l.Prime] (n : ℕ) :
    ∃ e : ZMod (l ^ n) ≃+* PadicInt l ⧸
      (Ideal.span ({(l : PadicInt l)} : Set (PadicInt l))) ^ n,
      e.symm.toRingHom.comp (Ideal.Quotient.mk
        ((Ideal.span ({(l : PadicInt l)} : Set (PadicInt l))) ^ n)) =
          PadicInt.toZModPow n := by
  have hk : (Ideal.span ({(l : PadicInt l)} : Set (PadicInt l))) ^ n =
      RingHom.ker (PadicInt.toZModPow n) := by
    rw [Ideal.span_singleton_pow, PadicInt.ker_toZModPow]
  let e := (Ideal.quotEquivOfEq hk).trans
    (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective (PadicInt.toZModPow n)))
  refine ⟨e.symm, ?_⟩
  ext x
  simp [e]

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

set_option linter.unusedVariables false in
/-- The standard ℓ-adic and finite-extension quotient modules are represented by the
corresponding two-term finite-free complexes and are finite as sets.

Source: literature/blueprint/master/blueprint/sec-proper-base-change/sk-thm-properbasechange/
lem-weil-pbc-standard-quotients-perfect.md, Proof and Source note; Stacks Project, Tag 0657
(blueprint: lemma-reduction-derived-nakayama--1).

Proof plan (the five DAG steps):
1. By `def-weil-l-adic-numbers`, the base ring is a DVR with uniformizer `l` and
   quotient `ZMod (l ^ n)`. For the extension, use the absolute value and chosen
   uniformizer of `def-weil-l-adic-coefficient-extension` and apply
   `lem-weil-l-adic-extension-integers-dvr`. Both coefficient rings are domains,
   their uniformizers are nonzero, and the extension has finite residue field
   (`def-sc-discrete-valuation-ring`).
2. For either pair `(A,t)`, the domain property makes `t ^ n` nonzero, hence
   multiplication by it injective and A-linear. Induction using the ideal product
   of `def-weil-pbc-algebra-hom-quotient` gives `(tA)^n = t^n A`: products of
   generators give one inclusion, and `t^(n+1)c = (t^n c)t` gives the other.
   The surjective quotient map has kernel `t^n A`, the multiplication map's image.
3. Put A in degrees -1 and 0, zero elsewhere, with this multiplication differential.
   The quotient augmentation is a chain map since it kills `t^n A`. Its degree -1
   cohomology is zero by injectivity; its degree-zero cohomology is `A/t^n A`.
   The induced map sends the class of x to its quotient class; its inverse is
   well defined because two representatives differ by `t^n A`. All other
   cohomologies vanish. Thus the augmentation is a quasi-isomorphism and its
   image under Q is invertible (`def-weil-abstract-derived-category`). In the
   base case compose with the indicated quotient identification to `ZMod (l ^ n)`.
4. The two terms have basis 1, so they are finite free. For projectivity, lift a
   map from A through a surjection by lifting the image of 1 and extending
   A-linearly. Zero terms use the empty basis and zero lift. These bounded finite
   projective models give the two perfect objects by `def-pc-perfect-ring-complex`
   and Stacks Tag 0657, with exactly the displayed differentials and augmentations.
5. The base quotient is finite via its `ZMod (l ^ n)` identification. For the
   extension, `lem-weil-valued-dvr-finite-quotients` applies to its DVR, finite
   residue field and uniformizer and makes every positive quotient finite.
   This verifies precisely the ordinary-module perfectness and finite-set
   requirements of `def-weil-pbc-adic-coefficient-datum`, without asserting any
   comparison of completed and constant coefficient sheaf categories.
-/
theorem standard_quotients_perfect
    (l : ℕ) [Fact l.Prime] (n : ℕ) (hn : 1 ≤ n) :
    (∃ (e : ZMod (l ^ n) ≃+* PadicInt l ⧸
        (Ideal.span ({(l : PadicInt l)} : Set (PadicInt l))) ^ n),
      e.symm.toRingHom.comp
          (Ideal.Quotient.mkₐ (PadicInt l)
            ((Ideal.span ({(l : PadicInt l)} : Set (PadicInt l))) ^ n)).toRingHom =
        PadicInt.toZModPow n ∧
      ∃ (P : CochainComplex (ModuleCat (PadicInt l)) ℤ)
      (hPge : P.IsStrictlyGE (-1)) (hPle : P.IsStrictlyLE 0),
      (∀ i : ℤ, Module.Free (PadicInt l) (P.X i) ∧
        Module.Finite (PadicInt l) (P.X i)) ∧
      DerivedCategory.IsPerfectRingComplex
        ((DerivedCategory.singleFunctor (ModuleCat (PadicInt l)) 0).obj
          ((ModuleCat.restrictScalars (PadicInt.toZModPow n)).obj
            (ModuleCat.of (ZMod (l ^ n)) (ZMod (l ^ n))))) ∧
      ∃ (em : P.X (-1) ≅ ModuleCat.of (PadicInt l) (PadicInt l))
        (e0 : P.X 0 ≅ ModuleCat.of (PadicInt l) (PadicInt l)),
        P.d (-1) 0 = em.hom ≫
          ModuleCat.ofHom
            (LinearMap.mulLeft (PadicInt l) ((l : PadicInt l) ^ n)) ≫ e0.inv ∧
        ∃ (φ : DerivedCategory.Q.obj P ≅
            (DerivedCategory.singleFunctor (ModuleCat (PadicInt l)) 0).obj
              ((ModuleCat.restrictScalars (PadicInt.toZModPow n)).obj
                (ModuleCat.of (ZMod (l ^ n)) (ZMod (l ^ n)))))
          (ε : P ⟶ (CochainComplex.singleFunctor (ModuleCat (PadicInt l)) 0).obj
            ((ModuleCat.restrictScalars (PadicInt.toZModPow n)).obj
              (ModuleCat.of (ZMod (l ^ n)) (ZMod (l ^ n))))),
          DerivedCategory.Q.map ε = φ.hom ∧
          (∀ x : P.X 0, ε.f 0 x =
            e.symm (Ideal.Quotient.mk
              ((Ideal.span ({(l : PadicInt l)} : Set (PadicInt l))) ^ n)
              (e0.hom x))) ∧
          (∀ i : ℤ, i ≠ 0 → ε.f i = 0) ∧
        Finite (PadicInt l ⧸
          (Ideal.span ({(l : PadicInt l)} : Set (PadicInt l))) ^ n)) ∧
    (∀ (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E],
      ∃ (P : CochainComplex
          (ModuleCat (Padic.coefficientExtensionIntegers l E)) ℤ)
        (hPge : P.IsStrictlyGE (-1)) (hPle : P.IsStrictlyLE 0),
        (∀ i : ℤ,
          Module.Free (Padic.coefficientExtensionIntegers l E) (P.X i) ∧
            Module.Finite (Padic.coefficientExtensionIntegers l E) (P.X i)) ∧
        DerivedCategory.IsPerfectRingComplex
          ((DerivedCategory.singleFunctor
            (ModuleCat (Padic.coefficientExtensionIntegers l E)) 0).obj
            (ModuleCat.of (Padic.coefficientExtensionIntegers l E)
              (Padic.coefficientExtensionIntegers l E ⧸
                (Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set
                  (Padic.coefficientExtensionIntegers l E))) ^ n))) ∧
        ∃ (em : P.X (-1) ≅
            ModuleCat.of (Padic.coefficientExtensionIntegers l E)
              (Padic.coefficientExtensionIntegers l E))
          (e0 : P.X 0 ≅
            ModuleCat.of (Padic.coefficientExtensionIntegers l E)
              (Padic.coefficientExtensionIntegers l E)),
          P.d (-1) 0 = em.hom ≫
              ModuleCat.ofHom
                (LinearMap.mulLeft (Padic.coefficientExtensionIntegers l E)
                  ((Padic.coefficientExtensionUniformizer l E) ^ n)) ≫ e0.inv ∧
          ∃ (φ : DerivedCategory.Q.obj P ≅
              (DerivedCategory.singleFunctor
                (ModuleCat (Padic.coefficientExtensionIntegers l E)) 0).obj
                (ModuleCat.of (Padic.coefficientExtensionIntegers l E)
                  (Padic.coefficientExtensionIntegers l E ⧸
                    (Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set
                      (Padic.coefficientExtensionIntegers l E))) ^ n)))
            (ε : P ⟶ (CochainComplex.singleFunctor
                (ModuleCat (Padic.coefficientExtensionIntegers l E)) 0).obj
                (ModuleCat.of (Padic.coefficientExtensionIntegers l E)
                  (Padic.coefficientExtensionIntegers l E ⧸
                    (Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set
                      (Padic.coefficientExtensionIntegers l E))) ^ n))),
            DerivedCategory.Q.map ε = φ.hom ∧
            ε.f 0 = e0.hom ≫ ModuleCat.ofHom
              (AlgHom.toLinearMap
                (Ideal.Quotient.mkₐ (Padic.coefficientExtensionIntegers l E)
                  ((Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set
                    (Padic.coefficientExtensionIntegers l E))) ^ n))) ∧
            (∀ i : ℤ, i ≠ 0 → ε.f i = 0) ∧
          Finite (Padic.coefficientExtensionIntegers l E ⧸
            (Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set
              (Padic.coefficientExtensionIntegers l E))) ^ n)) := by
  classical
  constructor
  · obtain ⟨e, he⟩ := baseEquiv l n
    let R := PadicInt l
    let M : ModuleCat R :=
      (ModuleCat.restrictScalars (PadicInt.toZModPow n)).obj
        (ModuleCat.of (ZMod (l ^ n)) (ZMod (l ^ n)))
    let q : ModuleCat.of R R ⟶ M := ModuleCat.ofHom
      (X := ModuleCat.of R R) (Y := M)
      { toFun := PadicInt.toZModPow n
        map_add' := (PadicInt.toZModPow n).map_add
        map_smul' := fun a b ↦ (PadicInt.toZModPow n).map_mul a b }
    have hq (x : R) : q x = 0 ↔ x ∈ Ideal.span ({(l : R) ^ n} : Set R) := by
      change PadicInt.toZModPow n x = 0 ↔ _
      rw [← PadicInt.ker_toZModPow]
      exact RingHom.mem_ker.symm
    obtain ⟨hw, hex⟩ := principalExact ((l : R) ^ n) M q hq
    have : Mono (ModuleCat.ofHom (LinearMap.mulLeft R ((l : R) ^ n))) := by
      rw [ModuleCat.mono_iff_injective]
      exact mul_right_injective₀ (pow_ne_zero n (by
        exact_mod_cast (Fact.out : l.Prime).ne_zero))
    have : Epi q := (ModuleCat.epi_iff_surjective q).2
      (ZMod.ringHom_surjective (PadicInt.toZModPow n))
    obtain ⟨P, hge, hle, hterms, em, e0, hd, ε, hε, hε0, hεi⟩ :=
      twoTermResolution ((l : R) ^ n) M q hw hex
    have : IsIso (DerivedCategory.Q.map ε) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) ε).2 hε
    let φ : DerivedCategory.Q.obj P ≅ (DerivedCategory.singleFunctor (ModuleCat R) 0).obj M :=
      asIso (DerivedCategory.Q.map ε)
    have hperfect : DerivedCategory.IsPerfectRingComplex
        ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj M) := by
      refine ⟨P, -1, 0, hge, hle, ?_, ⟨φ.symm⟩⟩
      intro i
      have := (hterms i).1
      exact ⟨inferInstance, (hterms i).2⟩
    refine ⟨e, he, P, hge, hle, hterms, hperfect, em, e0, hd, φ, ε, rfl, ?_, hεi, ?_⟩
    · intro x
      have hx := congrArg (fun f ↦ f x) hε0
      have heq (y : R) : e.symm (Ideal.Quotient.mk
          ((Ideal.span ({(l : R)} : Set R)) ^ n) y) = PadicInt.toZModPow n y :=
        RingHom.congr_fun he y
      rw [heq]
      change ε.f 0 x = q (e0.hom x) at hx
      exact hx
    · have : Finite (ZMod (l ^ n)) := inferInstance
      exact Finite.of_equiv _ e.toEquiv
  · intro E _ _ _
    let R := Padic.coefficientExtensionIntegers l E
    let t := Padic.coefficientExtensionUniformizer l E
    let I : Ideal R := (Ideal.span ({t} : Set R)) ^ n
    let M : ModuleCat R := ModuleCat.of R (R ⧸ I)
    let q : ModuleCat.of R R ⟶ M := ModuleCat.ofHom
      (AlgHom.toLinearMap (Ideal.Quotient.mkₐ R I))
    have hq (x : R) : q x = 0 ↔ x ∈ Ideal.span ({t ^ n} : Set R) := by
      change Ideal.Quotient.mk I x = 0 ↔ _
      rw [Ideal.Quotient.eq_zero_iff_mem]
      rw [show I = Ideal.span ({t ^ n} : Set R) from Ideal.span_singleton_pow t n]
    obtain ⟨hw, hex⟩ := principalExact (t ^ n) M q hq
    have : Mono (ModuleCat.ofHom (LinearMap.mulLeft R (t ^ n))) := by
      rw [ModuleCat.mono_iff_injective]
      exact mul_right_injective₀ (pow_ne_zero n (uniformizer_ne_zero l E))
    have : Epi q := (ModuleCat.epi_iff_surjective q).2 Ideal.Quotient.mk_surjective
    obtain ⟨P, hge, hle, hterms, em, e0, hd, ε, hε, hε0, hεi⟩ :=
      twoTermResolution (t ^ n) M q hw hex
    have : IsIso (DerivedCategory.Q.map ε) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) ε).2 hε
    let φ : DerivedCategory.Q.obj P ≅ (DerivedCategory.singleFunctor (ModuleCat R) 0).obj M :=
      asIso (DerivedCategory.Q.map ε)
    have hperfect : DerivedCategory.IsPerfectRingComplex
        ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj M) := by
      refine ⟨P, -1, 0, hge, hle, ?_, ⟨φ.symm⟩⟩
      intro i
      have := (hterms i).1
      exact ⟨inferInstance, (hterms i).2⟩
    refine ⟨P, hge, hle, hterms, hperfect, em, e0, hd, φ, ε, rfl, ?_, hεi, ?_⟩
    · change ε.f 0 ≫ 𝟙 M = e0.hom ≫ q at hε0
      change ε.f 0 = e0.hom ≫ q
      exact (Category.comp_id (ε.f 0)).symm.trans hε0
    · exact Padic.finite_coefficientExtensionRing l E n hn

end AlgebraicGeometry
