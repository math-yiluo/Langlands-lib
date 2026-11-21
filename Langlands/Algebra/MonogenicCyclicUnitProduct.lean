import Langlands.Algebra.FiniteCyclicUnitProduct
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.Topology.Algebra.Module.Compact
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-! Lifting cyclic unit products in finite free algebras over compact discrete valuation rings. -/

noncomputable section

namespace Langlands

open IsLocalRing IsDiscreteValuationRing Module Polynomial

universe u v w

section FiniteFree

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R] [T2Space R] [Finite (ResidueField R)]
  {A : Type v} [CommRing A] [Algebra R A] {ι : Type w} [Finite ι]

/-- A periodic automorphism of a finite free algebra over a compact discrete
valuation ring has surjective cyclic product on its fixed units if its action on
scalars is continuous and has a scalar with pairwise unit conjugate differences. -/
theorem exists_prod_ringAut_eq_of_fixed_of_finiteFree (b : Basis ι R A)
    (σ : RingAut R) (τ : RingAut A) {l : ℕ} (hl : 0 < l) (hτ : τ ^ l = 1)
    (hσ : Continuous σ) (hστ : ∀ r, τ (algebraMap R A r) = algebraMap R A (σ r))
    (a : R) (ha : Pairwise fun i j : Fin l => IsUnit ((σ ^ (i : ℕ)) a - (σ ^ (j : ℕ)) a))
    (y : Aˣ) (hy : τ (y : A) = y) : ∃ x : Aˣ, (∏ i : Fin l, (τ ^ (i : ℕ)) (x : A)) = y := by
  classical
  let := Fintype.ofFinite ι
  let : Module.Finite R A := Module.Finite.of_basis b
  let : IsNoetherianRing A := IsNoetherianRing.of_finite R A
  let : TopologicalSpace A := moduleTopology R A
  let : IsModuleTopology R A := ⟨rfl⟩
  let : IsTopologicalRing A := IsModuleTopology.isTopologicalRing R A
  let : CompactSpace A := Module.Finite.compactSpace R A
  let : T2Space A := T2Space.of_injective_continuous (f := b.equivFun) b.equivFun.injective
    (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap)
  let I (n : ℕ) : Ideal A := (maximalIdeal R ^ n).map (algebraMap R A)
  have hI (n : ℕ) : (I n).map τ.toRingHom = I n := by
    have hcomm : τ.toRingHom.comp (algebraMap R A) = (algebraMap R A).comp σ.toRingHom :=
      RingHom.ext hστ
    dsimp only [I]
    rw [Ideal.map_map, hcomm, ← Ideal.map_map, Ideal.map_pow]
    rw [show (maximalIdeal R).map σ.toRingHom = maximalIdeal R from map_ringEquiv_maximalIdeal σ]
  have hfinite (n : ℕ) : Finite (A ⧸ I n) := by
    let : Algebra (R ⧸ maximalIdeal R ^ n) (A ⧸ I n) :=
      Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
    let : IsScalarTower R (R ⧸ maximalIdeal R ^ n) (A ⧸ I n) :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext fun _ => rfl)
    let : Module.Finite (R ⧸ maximalIdeal R ^ n) (A ⧸ I n) :=
      Module.Finite.of_restrictScalars_finite R _ _
    exact Module.finite_of_finite (R ⧸ maximalIdeal R ^ n)
  have hsep (x : A) (hx : ∀ n, x ∈ I n) : x = 0 := by
    obtain ⟨π, hπ⟩ := exists_irreducible R
    apply b.repr.injective
    ext i
    rw [map_zero, Finsupp.zero_apply]
    have hi : b.repr x i ∈ ⨅ n, maximalIdeal R ^ n := by
      rw [Ideal.mem_iInf]
      intro n
      have hn : maximalIdeal R ^ n = Ideal.span {π ^ n} := by
        rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
      have hx' := hx n
      dsimp only [I] at hx'
      rw [hn, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at hx'
      obtain ⟨z, hz⟩ := hx'
      rw [hz, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, hn,
        Ideal.mem_span_singleton]
      exact dvd_mul_right _ _
    rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top,
      Ideal.mem_bot] at hi
  let P (x : A) : A := ∏ i : Fin l, (τ ^ (i : ℕ)) x
  let C (n : ℕ) : Set A := {x | P x - (y : A) ∈ I n}
  have hτc : Continuous τ := by
    let τlinear : A →ₛₗ[σ.toRingHom] A :=
      { τ.toAddMonoidHom with
        map_smul' := fun r x => by
          change τ (r • x) = σ r • τ x
          simp only [Algebra.smul_def, map_mul, hστ] }
    exact IsModuleTopology.continuous_of_linearMapₛₗ hσ τlinear
  have hPc : Continuous P := continuous_finsetProd _ fun i _ => by
    rw [RingAut.coe_pow]
    exact hτc.iterate (i : ℕ)
  have hCn (n : ℕ) : (C n).Nonempty := by
    let := hfinite n
    let q : A →+* A ⧸ I n := Ideal.Quotient.mk (I n)
    let τq : RingAut (A ⧸ I n) := Ideal.quotientEquiv (I n) (I n) τ (hI n).symm
    have hqτ : Function.Semiconj q τ τq := fun x => (Ideal.quotientEquiv_mk _ _ _ _ x).symm
    have hqp (k : ℕ) (x : A) : q ((τ ^ k) x) = (τq ^ k) (q x) := by
      simpa only [RingAut.coe_pow] using hqτ.iterate_right k x
    have hτq : τq ^ l = 1 := by
      ext x
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective (I := I n) x
      change (τq ^ l) (q z) = _
      rw [← hqp, hτ, RingAut.one_apply, RingAut.one_apply]
    have hp (k : ℕ) (r : R) : (τ ^ k) (algebraMap R A r) = algebraMap R A ((σ ^ k) r) := by
      induction k with
      | zero => simp only [pow_zero, RingAut.one_apply]
      | succ k ih => simp only [pow_succ', RingAut.mul_apply, ih, hστ]
    have hqa : Pairwise fun i j : Fin l =>
        IsUnit ((τq ^ (i : ℕ)) (q (algebraMap R A a)) - (τq ^ (j : ℕ)) (q (algebraMap R A a))) := by
      intro i j hij
      rw [← hqp, ← hqp, hp, hp, ← map_sub, ← map_sub]
      exact ((ha hij).map (algebraMap R A)).map q
    let yq := Units.map q.toMonoidHom y
    have hyq : τq (↑yq) = ↑yq := by
      change τq (q ↑y) = q ↑y
      rw [← hqτ _, hy]
    obtain ⟨w, hw⟩ := exists_prod_ringAut_eq_of_fixed τq hl hτq (q (algebraMap R A a)) hqa yq hyq
    change (∏ i : Fin l, (τq ^ (i : ℕ)) (w : A ⧸ I n)) = q ↑y at hw
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (I := I n) (w : A ⧸ I n)
    change q z = (w : A ⧸ I n) at hz
    refine ⟨z, (Ideal.Quotient.eq (I := I n)).mp ?_⟩
    change q (P z) = q ↑y
    rw [show P z = ∏ i : Fin l, (τ ^ (i : ℕ)) z from rfl, map_prod]
    simpa only [hqp, hz] using hw
  have hCc (n : ℕ) : IsClosed (C n) :=
    (IsNoetherianRing.isClosed_ideal (I n)).preimage (hPc.sub continuous_const)
  obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C
    (fun n _ hx => Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ n)) hx)
    hCn (hCc 0).isCompact hCc
  have he : P z = (y : A) := sub_eq_zero.mp (hsep _ fun n => (Set.mem_iInter.mp hz n : z ∈ C n))
  have hprod : IsUnit (P z) := he ▸ y.isUnit
  have hzunit : IsUnit z := by
    have h := IsUnit.prod_univ_iff.mp hprod ⟨0, hl⟩
    simpa only [Fin.val_mk, pow_zero, RingAut.one_apply] using h
  exact ⟨hzunit.unit, by simpa only [IsUnit.unit_spec] using he⟩

end FiniteFree

section AdjoinRoot

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]

private theorem adjoinRootCoefficient_map (f : R[X]) (σ : S ≃ₐ[R] S) :
    (f.map (algebraMap R S)).map σ.toRingHom = f.map (algebraMap R S) := by
  rw [Polynomial.map_map, show σ.toRingHom.comp (algebraMap R S) = algebraMap R S from
    RingHom.ext σ.commutes]

/-- A scalar automorphism over the base acts on the monogenic algebra by acting
on the coefficients and fixing the adjoined root. -/
def adjoinRootCoefficientAut (f : R[X]) :
    (S ≃ₐ[R] S) →* RingAut (AdjoinRoot (f.map (algebraMap R S))) where
  toFun σ := AdjoinRoot.mapRingEquiv σ.toRingEquiv _ _ (by
    change Associated ((f.map (algebraMap R S)).map σ.toRingHom) _
    rw [adjoinRootCoefficient_map])
  map_one' := by
    apply RingEquiv.toRingHom_injective
    apply AdjoinRoot.ringHom_ext
    · ext x
      simp [AdjoinRoot.coe_mapRingEquiv]
    · simp [AdjoinRoot.coe_mapRingEquiv]
  map_mul' σ τ := by
    apply RingEquiv.toRingHom_injective
    apply AdjoinRoot.ringHom_ext
    · ext x
      simp [AdjoinRoot.coe_mapRingEquiv]
    · simp [AdjoinRoot.coe_mapRingEquiv]

@[simp] theorem adjoinRootCoefficientAut_root (f : R[X]) (σ : S ≃ₐ[R] S) :
    adjoinRootCoefficientAut f σ (AdjoinRoot.root (f.map (algebraMap R S))) =
      AdjoinRoot.root (f.map (algebraMap R S)) := by
  simp [adjoinRootCoefficientAut]

@[simp] theorem adjoinRootCoefficientAut_of (f : R[X]) (σ : S ≃ₐ[R] S) (a : S) :
    adjoinRootCoefficientAut f σ (AdjoinRoot.of (f.map (algebraMap R S)) a) =
      AdjoinRoot.of (f.map (algebraMap R S)) (σ a) := by
  simp [adjoinRootCoefficientAut]

/-- The root adjoined with a unit constant coefficient is a unit. -/
theorem isUnit_adjoinRoot_root_of_isUnit_coeff_zero (f : R[X]) (hf : IsUnit (f.coeff 0)) :
    IsUnit (AdjoinRoot.root f) := by
  have he := congrArg (AdjoinRoot.mk f) (X_mul_divX_add f)
  change AdjoinRoot.mk f (X * f.divX + C (f.coeff 0)) = _ at he
  rw [map_add, map_mul, AdjoinRoot.mk_self] at he
  change AdjoinRoot.root f * AdjoinRoot.mk f f.divX + AdjoinRoot.of f (f.coeff 0) = 0 at he
  exact isUnit_of_mul_isUnit_left ((eq_neg_of_add_eq_zero_left he) ▸ (hf.map (AdjoinRoot.of f)).neg)

variable [IsDomain S] [IsDiscreteValuationRing S] [TopologicalSpace S] [IsTopologicalRing S]
  [CompactSpace S] [T2Space S] [Finite (ResidueField S)]

/-- The adjoined root of a monic polynomial with unit constant coefficient is a
cyclic product of a unit under the coefficient action. -/
theorem exists_prod_adjoinRootCoefficientAut_eq_root (f : R[X]) (hf : f.Monic)
    (h0 : IsUnit (f.coeff 0)) (σ : S ≃ₐ[R] S) {l : ℕ} (hl : 0 < l) (hσ : σ ^ l = 1)
    (hcont : Continuous σ) (a : S)
    (ha : Pairwise fun i j : Fin l => IsUnit ((σ ^ (i : ℕ)) a - (σ ^ (j : ℕ)) a)) :
    ∃ x : (AdjoinRoot (f.map (algebraMap R S)))ˣ,
      (∏ i : Fin l, (adjoinRootCoefficientAut f σ ^ (i : ℕ)) (↑x : AdjoinRoot _)) =
        AdjoinRoot.root (f.map (algebraMap R S)) := by
  let g := f.map (algebraMap R S)
  let b := (AdjoinRoot.powerBasis' (hf.map (algebraMap R S))).basis
  have hroot : IsUnit (AdjoinRoot.root g) :=
    isUnit_adjoinRoot_root_of_isUnit_coeff_zero g (by simpa [g] using h0.map (algebraMap R S))
  have hp (i : ℕ) (r : S) : (σ.toRingEquiv ^ i) r = (σ ^ i) r := by
    rw [RingAut.coe_pow, AlgEquiv.coe_pow, AlgEquiv.coe_ringEquiv]
  obtain ⟨x, hx⟩ := exists_prod_ringAut_eq_of_fixed_of_finiteFree b σ.toRingEquiv
    (adjoinRootCoefficientAut f σ) hl (by rw [← map_pow, hσ, map_one]) hcont
    (adjoinRootCoefficientAut_of f σ) a (by simpa only [hp] using ha) hroot.unit
    (by simpa only [IsUnit.unit_spec] using adjoinRootCoefficientAut_root f σ)
  exact ⟨x, hx.trans hroot.unit_spec⟩

end AdjoinRoot

end Langlands
