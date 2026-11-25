import Langlands.Automorphic.CuspidalAdmissible.FixedFamily
import Langlands.Automorphic.CuspidalAdmissible.CentralEigen
import Langlands.Automorphic.CuspidalEnvelopingPreservation
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Finiteness of the cuspidal multiplicity space at fixed level and center ideal -/

noncomputable section
universe u w
open MeasureTheory
set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global ArchimedeanGL ContinuousRationalFunctions

theorem map_aeval_apply {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (A : Module.End ℂ V) (B : Module.End ℂ W) (i : V →ₗ[ℂ] W)
    (hi : ∀ v, i (A v) = B (i v)) (p : Polynomial ℂ) (v : V) :
    i (Polynomial.aeval A p v) = Polynomial.aeval B p (i v) := by
  induction p using Polynomial.induction_on with
  | C a =>
    simp only [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
      Module.End.one_apply, map_smul]
  | add p q hp hq =>
    simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial k a hk =>
    have he : Polynomial.C a * Polynomial.X ^ (k + 1) =
        Polynomial.X * (Polynomial.C a * Polynomial.X ^ k) := by
      rw [pow_succ, ← mul_assoc, mul_comm (Polynomial.C a * Polynomial.X ^ k)]
    simp only [map_mul, Module.End.mul_apply] at hk
    simp only [he, map_mul, Polynomial.aeval_X, Module.End.mul_apply, hi, hk]

private theorem finiteDimensional_of_annihilating_monic_of_finite_eigenspaces {V : Type*}
    [AddCommGroup V] [Module ℂ V] (A : Module.End ℂ V)
    (hA : ∀ a : ℂ, FiniteDimensional ℂ (LinearMap.ker (A - algebraMap ℂ (Module.End ℂ V) a)))
    (p : Polynomial ℂ) (hp : p.Monic) (hzero : Polynomial.aeval A p = 0) :
    FiniteDimensional ℂ V := by
  obtain ⟨s, hs⟩ := Polynomial.splits_iff_exists_multiset.mp (IsAlgClosed.splits p)
  have h (s : Multiset ℂ) :
      FiniteDimensional ℂ
        (LinearMap.ker (Polynomial.aeval A (s.map (Polynomial.X - Polynomial.C ·)).prod)) := by
    induction s using Multiset.induction with
    | empty =>
      rw [Multiset.map_zero, Multiset.prod_zero, map_one]
      change FiniteDimensional ℂ (LinearMap.ker (LinearMap.id : Module.End ℂ V))
      rw [LinearMap.ker_id]
      infer_instance
    | cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, map_mul, map_sub, Polynomial.aeval_X,
        Polynomial.aeval_C, Module.End.mul_eq_comp, LinearMap.ker_comp]
      have := hA a
      exact inferInstance
  rw [hp.leadingCoeff, Polynomial.C_1, one_mul] at hs
  have hf := h s
  rw [← hs, hzero, LinearMap.ker_zero] at hf
  exact Module.Finite.of_injective Submodule.topEquiv.symm.toLinearMap
    Submodule.topEquiv.symm.injective

private theorem apply_eq_smul_of_mem_ker_sub {V : Type*}
    [AddCommGroup V] [Module ℂ V] (A : Module.End ℂ V) (a : ℂ) {v : V}
    (hv : v ∈ LinearMap.ker (A - algebraMap ℂ (Module.End ℂ V) a)) :
    A v = a • v := by
  simpa only [LinearMap.mem_ker, LinearMap.sub_apply, Algebra.algebraMap_eq_smul_one,
    LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] using hv

private theorem exists_monic_aeval_mem_ideal {Z : Type*} [CommRing Z] [Algebra ℂ Z]
    (J : Ideal Z) (hfin : Module.Finite ℂ (Z ⧸ J.restrictScalars ℂ)) (z : Z) :
    ∃ p : Polynomial ℂ, p.Monic ∧ Polynomial.aeval z p ∈ J := by
  let q := Ideal.Quotient.mkₐ ℂ J
  have hfinite : Module.Finite ℂ (Z ⧸ J) := hfin
  obtain ⟨p, hp, hq⟩ := @IsIntegral.of_finite ℂ (Z ⧸ J) _ _ _ hfinite (q z)
  refine ⟨p, hp, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
  exact (Polynomial.aeval_algHom_apply q z p).symm.trans hq

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance fixedMultiplicityRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance fixedMultiplicityContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance fixedMultiplicityFiniteSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance fixedMultiplicityStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance fixedMultiplicityFormGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _

omit [NumberField F] in
private theorem envelopingConjugation_centralGenerator (g : InfiniteAdelicGL F n) :
    envelopingConjugation F n g (centralGenerator F n) = centralGenerator F n := by
  have he : realLieConjugation F n g (unitDirection F n) = unitDirection F n := by
    apply (realLieAlgebraToMatrix F n).injective
    rw [realLieAlgebraToMatrix_realLieConjugation, realLieAlgebraToMatrix_unitDirection,
      mul_one, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  simp only [centralGenerator, envelopingConjugation_generator,
    complexLieConjugation_complexify, he]

namespace OperatorRealization

variable (S : OperatorRealization F n)

local instance fixedMultiplicityRealizationGroup : AddCommGroup S.Space := Submodule.addCommGroup _

variable (J : Ideal (EnvelopingCenter F n)) (L : OpenSubgroup (FiniteAdelicGL F n))
variable {m : ℕ} (σ : Representation ℂ (standardInfiniteCompact F n) (Fin m → ℂ))

set_option maxHeartbeats 600000 in
private theorem centralGenerator_mem_valueSpan {f : S.Space}
    (hf : f ∈ S.multiplicityValueSpan J L.toSubgroup σ) :
    S.envelopingAction (centralGenerator F n) f ∈ S.multiplicityValueSpan J L.toSubgroup σ := by
  let D := S.envelopingAction (centralGenerator F n)
  let W := S.multiplicityValueSpan J L.toSubgroup σ
  have hle : W ≤ W.comap D := by
    apply iSup_le
    rintro T _ ⟨v, rfl⟩
    let P := D.comp T.val
    have hT := (S.mem_annihilatedMultiplicitySpace J L.toSubgroup σ T.val).mp T.property
    have hP : P ∈ S.annihilatedMultiplicitySpace J L.toSubgroup σ := by
      apply (S.mem_annihilatedMultiplicitySpace J L.toSubgroup σ P).mpr
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro w d
        change S.finiteRepresentation d.val (D (T.val w)) = D (T.val w)
        have hd := hT.1.1 w d
        change S.finiteRepresentation d.val (T.val w) = T.val w at hd
        exact (S.finiteRepresentation_envelopingAction d.val (centralGenerator F n)
          (T.val w)).trans (congrArg D hd)
      · intro k w
        change D (T.val (σ k w)) = S.compactRepresentation k (D (T.val w))
        have hc := S.compactRepresentation_envelopingAction k (centralGenerator F n) (T.val w)
        have he := congrArg
          (fun a : EnvelopingAlgebra F n => S.envelopingAction a (S.compactRepresentation k (T.val w)))
          (envelopingConjugation_centralGenerator k.val)
        exact (congrArg D (hT.1.2 k w)).trans (hc.trans he).symm
      · intro w z hz
        change S.envelopingAction (z : EnvelopingAlgebra F n) (D (T.val w)) = 0
        have he : (z : EnvelopingAlgebra F n) * centralGenerator F n =
            centralGenerator F n * (z : EnvelopingAlgebra F n) :=
          (centerInclusion_commute F n z (centralGenerator F n)).symm
        have hmul : S.envelopingAction (z : EnvelopingAlgebra F n) * D =
            D * S.envelopingAction (z : EnvelopingAlgebra F n) := by
          exact ((S.envelopingAction).map_mul (z : EnvelopingAlgebra F n)
            (centralGenerator F n)).symm.trans
            ((congrArg (fun a : EnvelopingAlgebra F n => S.envelopingAction a) he).trans
              ((S.envelopingAction).map_mul (centralGenerator F n) (z : EnvelopingAlgebra F n)))
        exact (LinearMap.congr_fun hmul (T.val w)).trans
          ((congrArg D (hT.2 w z hz)).trans (map_zero D))
    exact S.mem_multiplicityValueSpan J L.toSubgroup σ ⟨P, hP⟩ v
  exact hle hf

variable [CompactSpace (AdeleQuotient F)]
variable [MeasurableSpace (InfiniteAdelicGL F n)] [BorelSpace (InfiniteAdelicGL F n)]

set_option maxHeartbeats 800000 in
/-- A fixed-level space of realized cuspidal multiplicities with a cofinite annihilator
is finite-dimensional, including generalized central eigenvectors. -/
theorem finiteDimensional_annihilatedMultiplicitySpace
    (μ : Measure (InfiniteAdelicGL F n)) [μ.IsHaarMeasure] (hn : 0 < n) (hS : S.IsCuspidal)
    [Module.Finite ℂ (EnvelopingCenter F n ⧸ J.restrictScalars ℂ)] :
    FiniteDimensional ℂ (S.annihilatedMultiplicitySpace J L.toSubgroup σ) := by
  let W := S.multiplicityValueSpan J L.toSubgroup σ
  let D := S.envelopingAction (centralGenerator F n)
  let A : Module.End ℂ W := D.restrict (fun _ hf => S.centralGenerator_mem_valueSpan J L σ hf)
  obtain ⟨κ, hκ⟩ := S.exists_reproducingKernel_multiplicityValueSpan J L.toSubgroup σ μ
  have hfinite (a : ℂ) :
      FiniteDimensional ℂ (LinearMap.ker (A - algebraMap ℂ (Module.End ℂ W) a)) := by
    let Wₐ := W ⊓ (S.centralEigenspace a).toSubmodule
    have : FiniteDimensional ℂ Wₐ := by
      refine S.finiteDimensional_of_reproduced μ hS hn (ArchimedeanGL.continuous F n κ.val)
        κ.property L.toSubgroup L.isOpen a Wₐ ?_ ?_ ?_
      · intro f hf g l hl
        have h := S.multiplicityValueSpan_le_fixedVectors J L.toSubgroup σ hf.1 ⟨l, hl⟩
        change S.finiteRepresentation l f = f at h
        rw [← S.evaluate_finiteRepresentation, h]
      · intro f hf g
        exact hκ f hf.1 g
      · intro f hf
        exact S.evaluate_mul_centralTorus a f ((S.mem_centralEigenspace a f).mp hf.2)
    let P := LinearMap.ker (A - algebraMap ℂ (Module.End ℂ W) a)
    have hP (f : P) : f.val.val ∈ Wₐ := by
      have h := apply_eq_smul_of_mem_ker_sub A a f.property
      have he : D f.val.val = a • f.val.val := congrArg (fun w : W => w.val) h
      exact Submodule.mem_inf.mpr
        ⟨f.val.property, (S.mem_centralEigenspace a f.val.val).mpr he⟩
    let i : P →ₗ[ℂ] Wₐ := (W.subtype.comp P.subtype).codRestrict Wₐ hP
    haveI : IsNoetherian ℂ Wₐ := IsNoetherian.iff_fg.mpr ‹_›
    exact Module.Finite.of_injective i (fun _ _ h => Subtype.ext (Subtype.ext
      (congrArg (fun x : Wₐ => x.val) h)))
  let z := centralElement F n
  have hJ : Module.Finite ℂ (EnvelopingCenter F n ⧸ J.restrictScalars ℂ) := inferInstance
  obtain ⟨p, hp, hz⟩ := exists_monic_aeval_mem_ideal J hJ z
  let B := S.envelopingAction.comp (centerInclusion F n)
  have hzero : Polynomial.aeval A p = 0 := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    change W.subtype (Polynomial.aeval A p f) = 0
    rw [map_aeval_apply A D W.subtype (fun _ => rfl)]
    change Polynomial.aeval (B z) p f.val = 0
    rw [Polynomial.aeval_algHom_apply]
    exact S.multiplicityValueSpan_le_ker J L.toSubgroup σ _ hz f.property
  have : FiniteDimensional ℂ W :=
    finiteDimensional_of_annihilating_monic_of_finite_eigenspaces A hfinite p hp hzero
  let M := S.annihilatedMultiplicitySpace J L.toSubgroup σ
  let c : M →ₗ[ℂ] ((Fin m → ℂ) →ₗ[ℂ] W) :=
    { toFun := fun T => T.val.codRestrict W (S.mem_multiplicityValueSpan J L.toSubgroup σ T)
      map_add' := fun _ _ => LinearMap.ext fun _ => Subtype.ext rfl
      map_smul' := fun _ _ => LinearMap.ext fun _ => Subtype.ext rfl }
  haveI : FiniteDimensional ℂ ((Fin m → ℂ) →ₗ[ℂ] W) := LinearMap.finiteDimensional
  exact FiniteDimensional.of_injective c (fun _ _ h => Subtype.ext (LinearMap.ext fun v =>
    congrArg (fun T : (Fin m → ℂ) →ₗ[ℂ] W => (T v).val) h))

end OperatorRealization

section ActualForms

variable (F n) [CompactSpace (AdeleQuotient F)]
variable (J : Ideal (EnvelopingCenter F n)) (L : Subgroup (FiniteAdelicGL F n))
variable {m : ℕ} (σ : Representation ℂ (standardInfiniteCompact F n) (Fin m → ℂ))

/-- The cuspidal subspace of the published fixed-level multiplicity space. -/
def cuspidalAnnihilatedFormMultiplicitySpace :
    Submodule ℂ ((Fin m → ℂ) →ₗ[ℂ] AutomorphicForms F n) :=
  annihilatedFormMultiplicitySpace F n J L σ ⊓
    ⨅ v : Fin m → ℂ, (cuspidalAutomorphicSubrepresentation F n).toSubmodule.comap
      (LinearMap.applyₗ v)

theorem mem_cuspidalAnnihilatedFormMultiplicitySpace
    (T : (Fin m → ℂ) →ₗ[ℂ] AutomorphicForms F n) :
    T ∈ cuspidalAnnihilatedFormMultiplicitySpace F n J L σ ↔
      T ∈ annihilatedFormMultiplicitySpace F n J L σ ∧
        ∀ v, IsCuspidal F n (automorphicToContinuous F n (T v)) := by
  simp only [cuspidalAnnihilatedFormMultiplicitySpace, Submodule.mem_inf,
    Submodule.mem_iInf, Submodule.mem_comap]
  rfl

omit [CompactSpace (AdeleQuotient F)] in
/-- At rank zero evaluation at the identity determines every automorphic form. -/
theorem finiteDimensional_automorphicForms_zero : FiniteDimensional ℂ (AutomorphicForms F 0) := by
  let E : AutomorphicForms F 0 →ₗ[ℂ] ℂ :=
    (LinearMap.proj (1 : AdelicGL F 0)).comp
      ((ContinuousMap.coeFnLinearMap ℂ).comp
        ((ContinuousRationalFunctions.toContinuousMap F 0).comp (automorphicToContinuous F 0)))
  refine Module.Finite.of_injective E (fun f g h => ?_)
  apply automorphicToContinuous_injective F 0
  apply ContinuousRationalFunctions.toContinuousMap_injective F 0
  apply ContinuousMap.ext
  intro x
  have hx : x = 1 := Units.ext (Matrix.ext fun i _ => Fin.elim0 i)
  rw [hx]
  exact h

variable (L' : OpenSubgroup (FiniteAdelicGL F n))

set_option maxHeartbeats 800000 in
/-- The cuspidal part of the fixed-level multiplicity space in the published
automorphic form carrier is finite-dimensional for every cofinite center ideal. -/
theorem finiteDimensional_cuspidalAnnihilatedFormMultiplicitySpace
    (hJ : Module.Finite ℂ (EnvelopingCenter F n ⧸ J.restrictScalars ℂ)) :
    FiniteDimensional ℂ (cuspidalAnnihilatedFormMultiplicitySpace F n J L'.toSubgroup σ) := by
  by_cases hn : n = 0
  · subst n
    have : FiniteDimensional ℂ (AutomorphicForms F 0) := finiteDimensional_automorphicForms_zero F
    infer_instance
  let S := cuspidalOperatorRealization F n
  let : AddCommGroup S.Space := Submodule.addCommGroup _
  let : MeasurableSpace (InfiniteAdelicGL F n) := borel _
  let : BorelSpace (InfiniteAdelicGL F n) := ⟨rfl⟩
  let μ : Measure (InfiniteAdelicGL F n) := Measure.haar
  have : μ.IsHaarMeasure := by dsimp [μ]; infer_instance
  let M := S.annihilatedMultiplicitySpace J L'.toSubgroup σ
  have hM : Module.Finite ℂ M :=
    S.finiteDimensional_annihilatedMultiplicitySpace J L' σ μ (Nat.pos_of_ne_zero hn)
      (cuspidalOperatorRealization_isCuspidal (F := F) (n := n))
  have : IsNoetherian ℂ M :=
    @isNoetherian_of_isNoetherianRing_of_finite ℂ M _ _ _ _ hM
  let C := cuspidalAnnihilatedFormMultiplicitySpace F n J L'.toSubgroup σ
  have hform (T : C) (v : Fin m → ℂ) : T.val v ∈ S.fullFormImage := by
    apply (S.mem_fullFormImage_iff _).mpr
    exact ((mem_cuspidalAnnihilatedFormMultiplicitySpace F n J L'.toSubgroup σ T.val).mp
      T.property).2 v
  let lift (T : C) : (Fin m → ℂ) →ₗ[ℂ] S.Space :=
    S.fullFormEquiv.symm.toLinearMap.comp (T.val.codRestrict S.fullFormImage.toSubmodule (hform T))
  have hlift (T : C) (v : Fin m → ℂ) : S.formInclusion (lift T v) = T.val v :=
    congrArg Subtype.val (S.fullFormEquiv.apply_symm_apply ⟨T.val v, hform T v⟩)
  let A : C →ₗ[ℂ] ((Fin m → ℂ) →ₗ[ℂ] S.Space) :=
    { toFun := lift
      map_add' T U := by
        apply LinearMap.ext
        intro v
        apply S.formInclusion_injective
        simp only [LinearMap.add_apply, map_add, hlift]
        rfl
      map_smul' c T := by
        apply LinearMap.ext
        intro v
        apply S.formInclusion_injective
        simp only [LinearMap.smul_apply, map_smul, RingHom.id_apply, hlift]
        rfl }
  have hA (T : C) : A T ∈ S.annihilatedMultiplicitySpace J L'.toSubgroup σ := by
    have H := ((mem_cuspidalAnnihilatedFormMultiplicitySpace F n J L'.toSubgroup σ T.val).mp
      T.property).1
    have hK := (Langlands.mem_jointMultiplicitySpace (automorphicFiniteRightAction F n)
      (automorphicCompactRightAction F n) L'.toSubgroup σ T.val).mp H.1
    apply (S.mem_annihilatedMultiplicitySpace J L'.toSubgroup σ (A T)).mpr
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro v l
      apply S.formInclusion_injective
      change automorphicFiniteRightAction F n l.val (S.formInclusion (lift T v)) =
        S.formInclusion (lift T v)
      have hd := hK.1 v l
      change automorphicFiniteRightAction F n l.val (T.val v) = T.val v at hd
      simpa only [hlift] using hd
    · intro k v
      apply S.formInclusion_injective
      change S.formInclusion (lift T (σ k v)) =
        automorphicCompactRightAction F n k (S.formInclusion (lift T v))
      simpa only [hlift] using hK.2 k v
    · intro v z hz
      have hv : T.val v ∈ centerAnnihilatedForms F n J := (Submodule.mem_iInf _).mp H.2 v
      have hzv := (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hv z) hz
      apply S.formInclusion_injective
      change automorphicEnvelopingAction F n (z : EnvelopingAlgebra F n)
        (S.formInclusion (lift T v)) = S.formInclusion 0
      rw [hlift, map_zero]
      exact LinearMap.mem_ker.mp hzv
  let B : C →ₗ[ℂ] M := A.codRestrict M hA
  change Module.Finite ℂ C
  refine Module.Finite.of_injective B (fun T U h => ?_)
  apply Subtype.ext
  apply LinearMap.ext
  intro v
  have hv := congrArg (fun f : M => S.formInclusion (f.val v)) h
  change S.formInclusion (lift T v) = S.formInclusion (lift U v) at hv
  simpa only [hlift] using hv

end ActualForms

end Langlands.Automorphic
