import Langlands.Representation.Plancherel.RationalUnitaryBasisCancellation
import Langlands.Representation.Plancherel.RationalUnramifiedComplexChart
import Langlands.Representation.Plancherel.RationalUnramifiedOperatorContinuation

/-! # One-coordinate denominators for actual unramified operator families -/

noncomputable section

set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Plancherel

universe u uV uW

private theorem eval₂_comp_laurent
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (x : Sˣ) (g : S →+* T) (p : LaurentPolynomial R) :
    g (LaurentPolynomial.eval₂ f x p) =
      LaurentPolynomial.eval₂ (g.comp f) (Units.map g.toMonoidHom x) p := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single n a =>
    have he : g (↑(x ^ n) : S) = (↑(Units.map g.toMonoidHom x ^ n) : T) :=
      congrArg Units.val (map_zpow (Units.map g.toMonoidHom) x n)
    simp only [LaurentPolynomial.single_eq_C_mul_T, map_mul, LaurentPolynomial.eval₂_C,
      LaurentPolynomial.eval₂_T, RingHom.comp_apply, he]

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local instance coordinateSlicePointTopology : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

local notation "Λ" => Additive (rationalDiscreteValuationImage G)
set_option quotPrecheck false in
local notation "norms" => fun a => (rationalNormCharacters G a).toMul
local notation "X" => unramifiedCharacters norms
local notation "𝓡" => unramifiedRegularFunctions norms

/-- The complex-unit values on an arbitrary finite integral basis, with the
actual topology on the unramified character group. -/
def rationalUnramifiedBasisUnitCoordinates {n : ℕ}
    (B : Module.Basis (Fin n) ℤ Λ) : X ≃ₜ* (Fin n → ℂˣ) :=
  (rationalCanonicalImageUnramifiedContinuousEquiv G).symm.trans
    (rationalImageBasisUnitCoordinates G B)

local notation "e" => rationalUnramifiedBasisUnitCoordinates G

theorem rationalUnramifiedBasisLaurentEquiv_eval {n : ℕ}
    (B : Module.Basis (Fin n) ℤ Λ) (c : Fin n → ℂˣ)
    (p : AddMonoidAlgebra ℂ (Fin n → ℤ)) :
    (rationalUnramifiedBasisLaurentEquiv G B p).val ((e B).symm c) =
      finiteLaurentEvaluation c p := by
  classical
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, Subalgebra.coe_add, Pi.add_apply, hp, hq]
  | single m a =>
    let v : Λ := B.equivFun.symm m
    obtain ⟨g, hg⟩ := rationalValuationImageProjection_surjective G v.toMul
    have hv : Additive.ofMul (rationalValuationImageProjection G g) = v :=
      congrArg Additive.ofMul hg
    have hrepr (i : Fin n) : B.repr v i = m i :=
      congrFun (B.equivFun.apply_symm_apply m) i
    rw [rationalUnramifiedBasisLaurentEquiv, AlgEquiv.trans_apply,
      AddMonoidAlgebra.domCongr_single]
    change (rationalCanonicalUnramifiedCoordinateAlgebraEquiv G
      (AddMonoidAlgebra.single v a)).val ((e B).symm c) = _
    rw [← hv, rationalCanonicalUnramifiedCoordinateAlgebraEquiv,
      rationalUnramifiedCoordinateAlgebraEquiv_apply,
      rationalUnramifiedCoordinateEvaluation_single_projection]
    change a * (((rationalCanonicalImageUnramifiedContinuousEquiv G
      (rationalImageBasisCharacter G B c)).val g : ℂˣ) : ℂ) = _
    rw [rationalCanonicalImageUnramifiedContinuousEquiv_apply,
      rationalImageBasisCharacter_apply, hv, finiteLaurentEvaluation_single]
    simp only [hrepr, Units.coe_prod]

variable {n : ℕ}
  (B : Module.Basis (Fin (n + 1)) ℤ (Additive (rationalDiscreteValuationImage G)))
  (c : Fin n → ℂˣ)

/-- Keep the first coordinate and set the other coordinates to the given
complex units. This is a map of actual unramified parameters. -/
def rationalUnramifiedCoordinateSlice (z : X) : X :=
  (e B).symm (Fin.cons (e B z 0) c)

local notation "s" => rationalUnramifiedCoordinateSlice G B c

theorem continuous_rationalUnramifiedCoordinateSlice :
    Continuous (rationalUnramifiedCoordinateSlice G B c) := by
  have h : Continuous (fun z : X => (Fin.cons (e B z 0) c : Fin (n + 1) → ℂˣ)) := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Continuous (fun z : X => e B z 0)
      exact (continuous_apply 0).comp (e B).continuous
    · exact continuous_const
  exact (e B).symm.continuous.comp h

theorem rationalUnramifiedCoordinateSlice_first (z : X) :
    e B (s z) 0 = e B z 0 := by
  rw [rationalUnramifiedCoordinateSlice, ContinuousMulEquiv.apply_symm_apply, Fin.cons_zero]

theorem rationalUnramifiedCoordinateSlice_tail (z : X) :
    rationalUnramifiedCoordinateSlice G B (Fin.tail (e B z)) z = z := by
  rw [rationalUnramifiedCoordinateSlice, Fin.cons_self_tail, ContinuousMulEquiv.symm_apply_apply]

/-- Specialize a regular scalar to the given tail coordinates as a Laurent
polynomial in the first variable. -/
def rationalUnramifiedSliceLaurent (b : 𝓡) : LaurentPolynomial ℂ :=
  LaurentPolynomial.eval₂
    (LaurentPolynomial.C.comp (finiteLaurentEvaluation c).toRingHom)
    (LaurentPolynomial.isUnit_T (R := ℂ) (1 : ℤ)).unit
    (finiteLaurentSuccessorEquiv ℂ n ((rationalUnramifiedBasisLaurentEquiv G B).symm b))

theorem rationalUnramifiedSliceLaurent_eval (b : 𝓡) (z : X) :
    LaurentPolynomial.eval₂ (RingHom.id ℂ) (e B z 0)
      (rationalUnramifiedSliceLaurent G B c b) = b.val (s z) := by
  let a := e B z 0
  have hu : Units.map (LaurentPolynomial.eval₂ (RingHom.id ℂ) a).toMonoidHom
      (LaurentPolynomial.isUnit_T (R := ℂ) (1 : ℤ)).unit = a := by
    apply Units.ext
    change LaurentPolynomial.eval₂ (RingHom.id ℂ) a
      (↑(LaurentPolynomial.isUnit_T (R := ℂ) (1 : ℤ)).unit) = (a : ℂ)
    rw [IsUnit.unit_spec, LaurentPolynomial.eval₂_T, zpow_one]
  have hc : (LaurentPolynomial.eval₂ (RingHom.id ℂ) a).comp
      (LaurentPolynomial.C.comp (finiteLaurentEvaluation c).toRingHom) =
        (finiteLaurentEvaluation c).toRingHom :=
    RingHom.ext fun r => by simp only [RingHom.comp_apply, LaurentPolynomial.eval₂_C, RingHom.id_apply]
  rw [rationalUnramifiedSliceLaurent, eval₂_comp_laurent, hu, hc,
    ← finiteLaurentEvaluation_cons, ← rationalUnramifiedBasisLaurentEquiv_eval G B,
    AlgEquiv.apply_symm_apply]
  rfl

include B in
private def firstCoordinateUnit : 𝓡ˣ :=
  let g := Classical.choose (rationalValuationImageProjection_surjective G (B 0).toMul)
  { val := unramifiedEvaluationRegular norms g
    inv := unramifiedEvaluationRegular norms g⁻¹
    val_inv := by rw [← unramifiedEvaluationRegular_mul, mul_inv_cancel,
      unramifiedEvaluationRegular_one]
    inv_val := unramifiedEvaluationRegular_inv_mul norms g }

private def pointEvaluation (z : X) : 𝓡 →ₐ[ℂ] ℂ :=
  (Pi.evalAlgHom ℂ (fun _ : X => ℂ) z).comp (unramifiedRegularFunctions norms).val

private theorem pointEvaluation_firstCoordinateUnit (z : X) :
    Units.map (pointEvaluation G z).toMonoidHom (firstCoordinateUnit G B) = e B z 0 := by
  let g := Classical.choose (rationalValuationImageProjection_surjective G (B 0).toMul)
  have hg : rationalValuationImageProjection G g = (B 0).toMul :=
    Classical.choose_spec (rationalValuationImageProjection_surjective G (B 0).toMul)
  apply Units.ext
  change (z.val g : ℂ) =
    (((rationalCanonicalImageUnramifiedContinuousEquiv G).symm z ((B 0).toMul) : ℂˣ) : ℂ)
  rw [← hg, rationalCanonicalImageUnramifiedContinuousEquiv_symm_projection]

/-- Pull back one-variable Laurent polynomials along the first coordinate. -/
def rationalUnramifiedFirstCoordinatePullback : LaurentPolynomial ℂ →+* 𝓡 :=
  LaurentPolynomial.eval₂ (algebraMap ℂ 𝓡) (firstCoordinateUnit G B)

theorem rationalUnramifiedFirstCoordinatePullback_eval (d : LaurentPolynomial ℂ) (z : X) :
    (rationalUnramifiedFirstCoordinatePullback G B d).val z =
      LaurentPolynomial.eval₂ (RingHom.id ℂ) (e B z 0) d := by
  change (pointEvaluation G z).toRingHom (LaurentPolynomial.eval₂ _ _ d) = _
  have hc : (pointEvaluation G z).toRingHom.comp (algebraMap ℂ 𝓡) = RingHom.id ℂ :=
    RingHom.ext fun a => (pointEvaluation G z).commutes a
  rw [eval₂_comp_laurent, hc, pointEvaluation_firstCoordinateUnit G B]

/-- Restriction to the parameter slice preserves scalar regularity. -/
def rationalUnramifiedSliceRegular (b : 𝓡) : 𝓡 :=
  rationalUnramifiedFirstCoordinatePullback G B (rationalUnramifiedSliceLaurent G B c b)

theorem rationalUnramifiedSliceRegular_eval (b : 𝓡) (z : X) :
    (rationalUnramifiedSliceRegular G B c b).val z = b.val (s z) :=
  (rationalUnramifiedFirstCoordinatePullback_eval G B _ z).trans
    (rationalUnramifiedSliceLaurent_eval G B c b z)

open UnramifiedOperatorFamily

variable {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem IsPolynomialOperatorOn.coordinateSlice {N : X → V →ₗ[ℂ] W}
    (hN : IsPolynomialOperatorOn (Set.univ : Set X) (fun z => N z.val)) :
    IsPolynomialOperatorOn (Set.univ : Set X) (fun z => N (s z.val)) := by
  intro v
  obtain ⟨k, b, w, h⟩ := hN v
  refine ⟨k, fun i => rationalUnramifiedSliceRegular G B c (b i), w, fun z => ?_⟩
  simpa only [rationalUnramifiedSliceRegular_eval] using h ⟨s z.val, Set.mem_univ _⟩

variable
  {Ω : Set (unramifiedCharacters (fun psi => (rationalNormCharacters G psi).toMul))}
  {A : Ω → V →ₗ[ℂ] W}

set_option quotPrecheck false in
local notation "tailAt" => fun z : X => Fin.tail (e B z)

/-- If the initial operator depends only on the first coordinate, the global
polynomial numerator and denominator may both be restricted to a slice. The
new denominator is nonzero at the chosen starting point. The cross identity
holds on the entire ambient torus. -/
theorem continuation_cross_eq_coordinateSlice
    (hG : GroupScheme.IsConnectedReductive G) (hΩ : IsOpen Ω) (z₀ : Ω)
    (p : RationalOperatorContinuationData Ω A)
    (hdep : ∀ z w : Ω, e B z.val 0 = e B w.val 0 → A z = A w) :
    let c₀ := tailAt z₀.val
    let b : 𝓡 := rationalUnramifiedSliceRegular G B c₀ p.denominator
    let N := fun z : X => p.numerator (rationalUnramifiedCoordinateSlice G B c₀ z)
    b.val z₀.val ≠ 0 ∧ IsPolynomialOperatorOn (Set.univ : Set X) (fun z => N z.val) ∧
      ∀ z, b.val z • p.numerator z = p.denominator.val z • N z := by
  dsimp only
  let c₀ := Fin.tail (e B z₀.val)
  let S := rationalUnramifiedCoordinateSlice G B c₀
  let b := rationalUnramifiedSliceRegular G B c₀ p.denominator
  let N := fun z => p.numerator (S z)
  have hfix : S z₀.val = z₀.val := rationalUnramifiedCoordinateSlice_tail G B z₀.val
  have hb (z : X) : b.val z = p.denominator.val (S z) :=
    rationalUnramifiedSliceRegular_eval G B c₀ p.denominator z
  have hN : IsPolynomialOperatorOn Set.univ (fun z => N z.val) :=
    IsPolynomialOperatorOn.coordinateSlice G B c₀ p.polynomial
  have hb₀ : b.val z₀.val ≠ 0 := by
    rw [hb, hfix]
    exact p.denominator_nonzero z₀
  refine ⟨hb₀, hN, ?_⟩
  let U := Ω ∩ S ⁻¹' Ω
  have hU : IsOpen U := hΩ.inter (hΩ.preimage (continuous_rationalUnramifiedCoordinateSlice G B c₀))
  have hzS : S z₀.val ∈ Ω := hfix.symm ▸ z₀.property
  have hne : U.Nonempty := ⟨z₀.val, z₀.property, hzS⟩
  intro z
  apply LinearMap.ext
  intro v
  let f : ↥(Set.univ : Set X) → W := fun w =>
    b.val w.val • p.numerator w.val v - p.denominator.val w.val • N w.val v
  have hf : IsPolynomialOn (Set.univ : Set X) f :=
    ((p.polynomial v).regular_smul b).sub ((hN v).regular_smul p.denominator)
  have he := rationalUnramifiedPolynomial_eq_zero_of_isOpen G
    (continuous_rationalValuationImageProjection G) hG hU hne (fun _ _ => Set.mem_univ _)
    f hf (by
      intro w hw
      let z₁ : Ω := ⟨w, hw.1⟩
      let z₂ : Ω := ⟨S w, hw.2⟩
      have hA : A z₁ = A z₂ := hdep z₁ z₂
        (rationalUnramifiedCoordinateSlice_first G B c₀ w).symm
      change b.val w • p.numerator w v -
        p.denominator.val w • p.numerator (S w) v = 0
      rw [hb w, show p.numerator w = _ from p.clears z₁,
        show p.numerator (S w) = _ from p.clears z₂, hA]
      simp only [LinearMap.smul_apply, smul_smul]
      change (p.denominator.val (S w) * p.denominator.val w) • A z₂ v -
        (p.denominator.val w * p.denominator.val (S w)) • A z₂ v = 0
      rw [mul_comm (p.denominator.val (S w)) (p.denominator.val w), sub_self])
  exact sub_eq_zero.mp (he ⟨z, Set.mem_univ _⟩)

end Langlands.Plancherel
