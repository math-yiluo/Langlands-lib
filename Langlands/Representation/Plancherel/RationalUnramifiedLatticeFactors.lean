import Langlands.Representation.Plancherel.RationalUnitaryBasisCancellation
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.FreeModule.PID

/-! # Monomial binomials on the actual unramified character torus -/

noncomputable section

open AlgebraicGeometry CategoryTheory Topology
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj NNReal Polynomial

namespace Langlands.Plancherel

universe u

private theorem exists_basis_first_nat_smul
    {L : Type*} [AddCommGroup L] [Module.IsTorsionFree ℤ L]
    {m : ℕ} (B : Module.Basis (Fin m) ℤ L) {v : L} (hv : v ≠ 0) :
    ∃ (n : ℕ) (B' : Module.Basis (Fin (n + 1)) ℤ L) (k : ℕ), 0 < k ∧ v = k • B' 0 := by
  classical
  let N : Submodule ℤ L := ℤ ∙ v
  let _ : Module ℤ N := N.module
  have hrank : Module.finrank ℤ N = 1 :=
    (LinearEquiv.toSpanNonzeroSingleton ℤ L v hv).finrank_eq.symm.trans
      (CommSemiring.finrank_self ℤ)
  obtain ⟨r, S⟩ := N.smithNormalForm B
  rw [Module.finrank_eq_card_basis S.bN, Fintype.card_fin] at hrank
  subst r
  let x : N := ⟨v, Submodule.mem_span_singleton_self v⟩
  let i := S.f 0
  let d : ℤ := S.bN.repr x 0 * S.a 0
  have hx : v = S.bN.repr x 0 • (S.bN 0 : L) := by
    have hsum := congrArg (fun y : N => (y : L)) (S.bN.sum_repr x)
    simpa only [Fin.sum_univ_one, Submodule.coe_smul_of_tower] using hsum.symm
  have hvd : v = d • S.bM i := hx.trans (by rw [S.snf 0, smul_smul])
  have hd : d ≠ 0 := by
    intro h
    exact hv (hvd.trans (by rw [h, zero_smul]))
  cases m with
  | zero => exact Fin.elim0 i
  | succ n =>
    let B₀ := S.bM.reindex (Equiv.swap i 0)
    have hb : B₀ 0 = S.bM i := by simp [B₀, Module.Basis.reindex_apply]
    have hdir : v = d • B₀ 0 := hvd.trans (congrArg (fun w : L => d • w) hb).symm
    by_cases hp : 0 ≤ d
    · refine ⟨n, B₀, d.toNat, by omega, ?_⟩
      rw [← Nat.cast_smul_eq_nsmul ℤ, Int.toNat_of_nonneg hp]
      exact hdir
    · let B₁ := B₀.map (LinearEquiv.neg ℤ)
      have hn : 0 ≤ -d := by omega
      refine ⟨n, B₁, (-d).toNat, by omega, ?_⟩
      rw [← Nat.cast_smul_eq_nsmul ℤ, Int.toNat_of_nonneg hn]
      change v = -d • -(B₀ 0)
      exact hdir.trans (neg_smul_neg d (B₀ 0)).symm

private theorem x_pow_sub_C_factorization (k : ℕ) (hk : 0 < k) (a : Circle) :
    ∃ s : List Circle, (Polynomial.X ^ k - Polynomial.C (a : ℂ) : ℂ[X]) =
      (s.map (fun t : Circle => Polynomial.X - Polynomial.C (t : ℂ))).prod := by
  let p : ℂ[X] := Polynomial.X ^ k - Polynomial.C (a : ℂ)
  have hm : p.Monic := Polynomial.monic_X_pow_sub_C _ hk.ne'
  let s := p.roots.toList
  have hu (r : ℂ) (hr : r ∈ s) : ‖r‖ = 1 := by
    have hroot := (Polynomial.mem_roots hm.ne_zero).mp (Multiset.mem_toList.mp hr)
    have hp : r ^ k = (a : ℂ) := by
      apply sub_eq_zero.mp
      simpa [Polynomial.IsRoot, p] using hroot
    apply (pow_eq_one_iff_of_nonneg (norm_nonneg r) hk.ne').mp
    rw [← norm_pow, hp, Circle.norm_coe]
  let lift (r : {r : ℂ // r ∈ s}) : Circle :=
    ⟨r.val, mem_sphere_zero_iff_norm.mpr (hu r.val r.property)⟩
  let t : List Circle := s.attach.map lift
  have ht : t.map Circle.coeHom = s := by
    change (s.attach.map lift).map Circle.coeHom = s
    rw [List.map_map]
    have hval : s.attach.map (fun r => id r.val) = s.map id := List.attach_map_val
    exact hval.trans (List.map_id s)
  refine ⟨t, ?_⟩
  have hs :
      ((s.map (fun r => Polynomial.X - Polynomial.C r) : List ℂ[X]) : Multiset ℂ[X]) =
        p.roots.map (fun r => Polynomial.X - Polynomial.C r) := by
    rw [← Multiset.map_coe, Multiset.coe_toList]
  calc
    p = (p.roots.map (fun r => Polynomial.X - Polynomial.C r)).prod :=
      (IsAlgClosed.splits p).eq_prod_roots_of_monic hm
    _ = (s.map (fun r => Polynomial.X - Polynomial.C r)).prod := by
      simpa only [Multiset.prod_coe] using congrArg Multiset.prod hs.symm
    _ = (t.map (fun z : Circle => Polynomial.X - Polynomial.C (z : ℂ))).prod := by
      have hmap := congrArg (List.map (fun r : ℂ => Polynomial.X - Polynomial.C r)) ht.symm
      rw [List.map_map] at hmap
      exact congrArg List.prod hmap

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local instance latticeFactorsPointTopology : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

local notation "Λ" => Additive (rationalDiscreteValuationImage G)
set_option quotPrecheck false in
local notation "R" => unramifiedRegularFunctions (fun a => (rationalNormCharacters G a).toMul)
set_option quotPrecheck false in
local notation "Xu" => unitaryUnramifiedCharacters (fun a => (rationalNormCharacters G a).toMul)

/-- The regular monomial indexed by an element of the actual valuation image. -/
def rationalUnramifiedLatticeMonomial (v : Λ) : R :=
  rationalCanonicalUnramifiedCoordinateAlgebraEquiv G (AddMonoidAlgebra.single v 1)

@[simp]
theorem rationalUnramifiedLatticeMonomial_zero :
    rationalUnramifiedLatticeMonomial G 0 = 1 := by
  change rationalCanonicalUnramifiedCoordinateAlgebraEquiv G 1 = 1
  exact map_one _

theorem rationalUnramifiedLatticeMonomial_add (v w : Λ) :
    rationalUnramifiedLatticeMonomial G (v + w) =
      rationalUnramifiedLatticeMonomial G v * rationalUnramifiedLatticeMonomial G w := by
  unfold rationalUnramifiedLatticeMonomial
  rw [← map_mul, AddMonoidAlgebra.single_mul_single, one_mul]

theorem rationalUnramifiedLatticeMonomial_nsmul (k : ℕ) (v : Λ) :
    rationalUnramifiedLatticeMonomial G (k • v) =
      rationalUnramifiedLatticeMonomial G v ^ k := by
  induction k with
  | zero => simp
  | succ k hk =>
    rw [succ_nsmul, rationalUnramifiedLatticeMonomial_add, hk, pow_succ]

/-- The monomial evaluates as the unramified character at any lift of its
valuation-image exponent. -/
theorem rationalUnramifiedLatticeMonomial_eval_projection
    (g : GroupScheme.rationalPoints G)
    (z : unramifiedCharacters (fun a => (rationalNormCharacters G a).toMul)) :
    (rationalUnramifiedLatticeMonomial G
      (Additive.ofMul (rationalValuationImageProjection G g))).val z = (z.val g : ℂ) := by
  rw [rationalUnramifiedLatticeMonomial, rationalCanonicalUnramifiedCoordinateAlgebraEquiv,
    rationalUnramifiedCoordinateAlgebraEquiv_apply,
    rationalUnramifiedCoordinateEvaluation_single_projection, one_mul]

theorem norm_rationalUnramifiedLatticeMonomial_unitary (v : Λ) (z : Xu) :
    ‖rationalUnitaryRegularRestriction G (rationalUnramifiedLatticeMonomial G v) z‖ = 1 := by
  obtain ⟨g, hg⟩ := rationalValuationImageProjection_surjective G v.toMul
  have hv : Additive.ofMul (rationalValuationImageProjection G g) = v :=
    congrArg Additive.ofMul hg
  rw [← hv]
  change ‖(rationalUnramifiedLatticeMonomial G _).val ⟨z.val, z.property.1⟩‖ = 1
  rw [rationalUnramifiedLatticeMonomial_eval_projection]
  exact z.property.2 g

/-- Subtracting an off-circle constant from a monomial gives a denominator
factor nonvanishing on the full unitary subgroup. -/
theorem rationalUnramifiedLatticeMonomial_sub_nonvanishing
    (v : Λ) (a : ℂ) (ha : ‖a‖ ≠ 1) (z : Xu) :
    rationalUnitaryRegularRestriction G
      (rationalUnramifiedLatticeMonomial G v - algebraMap ℂ R a) z ≠ 0 := by
  intro hz
  rw [map_sub, Pi.sub_apply, (rationalUnitaryRegularRestriction G).commutes] at hz
  have he : rationalUnitaryRegularRestriction G (rationalUnramifiedLatticeMonomial G v) z = a :=
    sub_eq_zero.mp hz
  exact ha ((congrArg norm he).symm.trans (norm_rationalUnramifiedLatticeMonomial_unitary G v z))

private theorem rationalUnramifiedLatticeMonomial_eval_basis {n : ℕ}
    (B : Module.Basis (Fin n) ℤ Λ) (c : Fin n → Circle) (i : Fin n) :
    rationalUnitaryRegularRestriction G (rationalUnramifiedLatticeMonomial G (B i))
      (rationalUnitaryParameterOfBasis G B c) = (c i : ℂ) := by
  obtain ⟨g, hg⟩ := rationalValuationImageProjection_surjective G (B i).toMul
  have hv : Additive.ofMul (rationalValuationImageProjection G g) = B i :=
    congrArg Additive.ofMul hg
  rw [← hv]
  change (rationalUnramifiedLatticeMonomial G _).val
    ⟨(rationalUnitaryParameterOfBasis G B c).val, _⟩ = _
  rw [rationalUnramifiedLatticeMonomial_eval_projection, rationalUnitaryParameterOfBasis,
    rationalCanonicalUnitaryImageUnramifiedContinuousEquiv_apply, hg]
  change ((B.constr ℤ (fun j => Additive.ofMul (c j)) (B i)).toMul : ℂ) = _
  rw [Module.Basis.constr_basis]
  rfl

private theorem rationalUnramifiedBasisCoordinateRoot_eq_monomial_sub
    (hG : GroupScheme.IsConnectedReductive G) {n : ℕ}
    (B : Module.Basis (Fin (n + 1)) ℤ Λ) (a : Circle) :
    rationalUnramifiedBasisCoordinateRoot G B (Circle.toUnits a) =
      rationalUnramifiedLatticeMonomial G (B 0) - algebraMap ℂ R (a : ℂ) := by
  apply rationalUnitaryRegularRestriction_injective G hG
  funext z
  obtain ⟨c, rfl⟩ := rationalUnitaryParameterOfBasis_surjective G B z
  rw [← Fin.cons_self_tail c, rationalUnramifiedBasisCoordinateRoot_eval_cons,
    map_sub, Pi.sub_apply, rationalUnramifiedLatticeMonomial_eval_basis,
    (rationalUnitaryRegularRestriction G).commutes]
  rfl

/-- A nonzero actual valuation-lattice exponent and a circle-valued constant
give a product of actual basis-coordinate roots, with multiplicities. -/
theorem rationalUnramifiedLatticeMonomial_sub_factorization
    (hG : GroupScheme.IsConnectedReductive G) (v : Λ) (hv : v ≠ 0) (a : Circle) :
    ∃ (n : ℕ) (B : Module.Basis (Fin (n + 1)) ℤ Λ) (s : List Circle),
      rationalUnramifiedLatticeMonomial G v - algebraMap ℂ R (a : ℂ) =
        (s.map (fun t => rationalUnramifiedBasisCoordinateRoot G B (Circle.toUnits t))).prod := by
  obtain ⟨n, B, k, hk, hvB⟩ := exists_basis_first_nat_smul
    (rationalReductiveValuationBasis G hG) hv
  obtain ⟨s, hs⟩ := x_pow_sub_C_factorization k hk a
  let m := rationalUnramifiedLatticeMonomial G (B 0)
  let e := Polynomial.eval₂RingHom (algebraMap ℂ R) m
  have hmap (t : Circle) : e (Polynomial.X - Polynomial.C (t : ℂ)) =
      rationalUnramifiedBasisCoordinateRoot G B (Circle.toUnits t) := by
    rw [rationalUnramifiedBasisCoordinateRoot_eq_monomial_sub G hG]
    simp only [e, m, map_sub, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
      Polynomial.eval₂_C]
  refine ⟨n, B, s, ?_⟩
  calc
    rationalUnramifiedLatticeMonomial G v - algebraMap ℂ R (a : ℂ) =
        e (Polynomial.X ^ k - Polynomial.C (a : ℂ)) := by
      rw [hvB, rationalUnramifiedLatticeMonomial_nsmul]
      simp [e, m]
    _ = e ((s.map (fun t : Circle => Polynomial.X - Polynomial.C (t : ℂ))).prod) :=
      congrArg e hs
    _ = (s.map (fun t => rationalUnramifiedBasisCoordinateRoot G B (Circle.toUnits t))).prod := by
      rw [map_list_prod, List.map_map]
      exact congrArg List.prod (List.map_congr_left fun t _ => hmap t)

end Langlands.Plancherel
