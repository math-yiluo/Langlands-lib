import Langlands.Representation.Plancherel.LaurentUnitaryCoordinatePowers
import Langlands.Representation.Plancherel.RationalUnramifiedScalarCancellation

/-! # Actual unramified coordinate-root cancellation in any integral basis -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology
open scoped NNReal CategoryTheory.MonObj BigOperators

namespace Langlands.Plancherel

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local instance basisCancellationPointTopology : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

local notation "Λ" => Additive (rationalDiscreteValuationImage G)
set_option quotPrecheck false in
local notation "R" => unramifiedRegularFunctions (fun a => (rationalNormCharacters G a).toMul)
set_option quotPrecheck false in
local notation "Xu" => unitaryUnramifiedCharacters (fun a => (rationalNormCharacters G a).toMul)

/-- A finite integral basis of the actual valuation image gives Laurent
coordinates on the existing actual regular-function algebra. -/
def rationalUnramifiedBasisLaurentEquiv {n : ℕ} (B : Module.Basis (Fin n) ℤ Λ) :
    AddMonoidAlgebra ℂ (Fin n → ℤ) ≃ₐ[ℂ] R :=
  (AddMonoidAlgebra.domCongr ℂ ℂ B.equivFun.symm.toAddEquiv).trans
    (rationalCanonicalUnramifiedCoordinateAlgebraEquiv G)

/-- The circle character with prescribed values on the supplied integral
basis of the actual valuation image. -/
def rationalImageBasisUnitaryCharacter {n : ℕ} (B : Module.Basis (Fin n) ℤ Λ)
    (c : Fin n → Circle) : rationalUnitaryImageCharacters G where
  toFun a := (B.constr ℤ (fun i => Additive.ofMul (c i)) (Additive.ofMul a)).toMul
  map_one' := by
    change (B.constr ℤ (fun i => Additive.ofMul (c i)) (0 : Λ)).toMul = 1
    rw [map_zero]
    rfl
  map_mul' a b := by
    change (B.constr ℤ (fun i => Additive.ofMul (c i))
      (Additive.ofMul a + Additive.ofMul b)).toMul = _
    rw [map_add]
    rfl
  continuous_toFun := continuous_of_discreteTopology

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
theorem rationalImageBasisUnitaryCharacter_apply {n : ℕ}
    (B : Module.Basis (Fin n) ℤ Λ) (c : Fin n → Circle)
    (a : rationalDiscreteValuationImage G) :
    rationalImageBasisUnitaryCharacter G B c a =
      ∏ i, c i ^ (B.repr (Additive.ofMul a) i) := by
  change (B.constr ℤ (fun i => Additive.ofMul (c i)) (Additive.ofMul a)).toMul = _
  rw [Module.Basis.constr_apply_fintype]
  simp only [Module.Basis.equivFun_apply, toMul_sum, toMul_zsmul]
  rfl

/-- Reconstruct an actual unitary unramified parameter from its values on any
supplied finite integral basis. -/
def rationalUnitaryParameterOfBasis {n : ℕ} (B : Module.Basis (Fin n) ℤ Λ)
    (c : Fin n → Circle) : Xu :=
  rationalCanonicalUnitaryImageUnramifiedContinuousEquiv G
    (rationalImageBasisUnitaryCharacter G B c)

/-- Every actual unitary parameter is obtained from its values on the supplied
integral basis, including an empty basis. -/
theorem rationalUnitaryParameterOfBasis_surjective {n : ℕ}
    (B : Module.Basis (Fin n) ℤ Λ) :
    Function.Surjective (rationalUnitaryParameterOfBasis G B) := by
  intro z
  let e := rationalCanonicalUnitaryImageUnramifiedContinuousEquiv G
  let ξ := e.symm z
  let c : Fin n → Circle := fun i => ξ ((B i).toMul)
  refine ⟨c, ?_⟩
  have hchar : rationalImageBasisUnitaryCharacter G B c = ξ := by
    apply ContinuousMonoidHom.ext
    intro a
    have he := DFunLike.congr_fun
      (B.constr_self ℤ ξ.toMonoidHom.toAdditive.toIntLinearMap) (Additive.ofMul a)
    exact congrArg Additive.toMul he
  change e (rationalImageBasisUnitaryCharacter G B c) = z
  rw [hchar, ContinuousMulEquiv.apply_symm_apply]

theorem rationalUnramifiedBasisLaurentEquiv_eval_unitary {n : ℕ}
    (B : Module.Basis (Fin n) ℤ Λ) (c : Fin n → Circle)
    (p : AddMonoidAlgebra ℂ (Fin n → ℤ)) :
    rationalUnitaryRegularRestriction G (rationalUnramifiedBasisLaurentEquiv G B p)
        (rationalUnitaryParameterOfBasis G B c) =
      finiteLaurentEvaluation (fun i => Circle.toUnits (c i)) p := by
  classical
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq =>
      simp only [map_add, Pi.add_apply, hp, hq]
  | single m a =>
      let v : Λ := B.equivFun.symm m
      obtain ⟨g, hg⟩ := rationalValuationImageProjection_surjective G v.toMul
      have hvec : Additive.ofMul (rationalValuationImageProjection G g) = v :=
        congrArg Additive.ofMul hg
      have hrepr : ∀ i, B.repr v i = m i := by
        intro i
        exact congrFun (B.equivFun.apply_symm_apply m) i
      change (rationalCanonicalUnramifiedCoordinateAlgebraEquiv G
          (AddMonoidAlgebra.domCongr ℂ ℂ B.equivFun.symm.toAddEquiv
            (AddMonoidAlgebra.single m a))).val _ = _
      rw [AddMonoidAlgebra.domCongr_single]
      change (rationalCanonicalUnramifiedCoordinateAlgebraEquiv G
          (AddMonoidAlgebra.single v a)).val _ = _
      rw [← hvec]
      rw [rationalCanonicalUnramifiedCoordinateAlgebraEquiv,
        rationalUnramifiedCoordinateAlgebraEquiv_apply,
        rationalUnramifiedCoordinateEvaluation_single_projection]
      change a * (((rationalUnitaryParameterOfBasis G B c).val g : ℂˣ) : ℂ) = _
      rw [rationalUnitaryParameterOfBasis,
        rationalCanonicalUnitaryImageUnramifiedContinuousEquiv_apply,
        rationalImageBasisUnitaryCharacter_apply, hvec]
      simp only [hrepr, finiteLaurentEvaluation_single, ← map_zpow]
      change a * Circle.coeHom (∏ i, c i ^ m i) = a * ∏ i, Circle.coeHom (c i ^ m i)
      rw [map_prod]

/-- The actual regular root scalar associated with the first vector of an
integral basis and a specified nonzero complex root value. -/
def rationalUnramifiedBasisCoordinateRoot {n : ℕ}
    (B : Module.Basis (Fin (n + 1)) ℤ Λ) (a : ℂˣ) : R :=
  rationalUnramifiedBasisLaurentEquiv G B (finiteLaurentCoordinateRoot n a)

/-- The root scalar has its stated first-coordinate zero on actual parameters. -/
theorem rationalUnramifiedBasisCoordinateRoot_eval_cons {n : ℕ}
    (B : Module.Basis (Fin (n + 1)) ℤ Λ) (a : ℂˣ)
    (t : Circle) (c : Fin n → Circle) :
    rationalUnitaryRegularRestriction G (rationalUnramifiedBasisCoordinateRoot G B a)
        (rationalUnitaryParameterOfBasis G B (Fin.cons t c)) =
      (t : ℂ) - (a : ℂ) := by
  rw [rationalUnramifiedBasisCoordinateRoot,
    rationalUnramifiedBasisLaurentEquiv_eval_unitary]
  have hc : (fun i : Fin (n + 1) =>
      Circle.toUnits ((Fin.cons t c : Fin (n + 1) → Circle) i)) =
      Fin.cons (Circle.toUnits t) (fun i => Circle.toUnits (c i)) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [hc, finiteLaurentCoordinateRoot_eval_cons]
  rfl

theorem rationalUnramifiedBasisCoordinateRoot_ne_zero {n : ℕ}
    (B : Module.Basis (Fin (n + 1)) ℤ Λ) (a : Circle) :
    rationalUnramifiedBasisCoordinateRoot G B (Circle.toUnits a) ≠ 0 := by
  intro he
  have hi := (rationalUnramifiedBasisLaurentEquiv G B).injective
  exact finiteLaurentCoordinateRoot_ne_zero n a
    (hi (he.trans (map_zero (rationalUnramifiedBasisLaurentEquiv G B)).symm))

/-- A dense unitary bound cancels every prescribed power of an actual
basis-coordinate root in the scalar regular-function algebra. -/
theorem rationalUnramifiedBasisCoordinateRoot_pow_dvd_of_dense_unitary_bound
    {n : ℕ} (B : Module.Basis (Fin (n + 1)) ℤ Λ) (a : Circle) (k : ℕ)
    (p b : R) (D : Set Xu) (hD : Dense D) (C : ℝ)
    (hbound : ∀ z ∈ D,
      ‖rationalUnitaryRegularRestriction G p z‖ ≤
        C * ‖rationalUnitaryRegularRestriction G b z‖)
    (hb : rationalUnramifiedBasisCoordinateRoot G B (Circle.toUnits a) ^ k ∣ b) :
    rationalUnramifiedBasisCoordinateRoot G B (Circle.toUnits a) ^ k ∣ p := by
  let α := rationalUnramifiedBasisLaurentEquiv G B
  have hcont (s : R) : Continuous (rationalUnitaryRegularRestriction G s) :=
    (continuous_unramifiedRegularFunction _ s).comp
      (continuous_subtype_val.subtype_mk (fun z => z.property.1))
  have hglobal := norm_le_of_dense
    (rationalUnitaryRegularRestriction G p)
    (rationalUnitaryRegularRestriction G b)
    (hcont p) (hcont b) D hD C hbound
  have he (s : R) (c : Fin (n + 1) → Circle) :
      finiteLaurentEvaluation (fun i => Circle.toUnits (c i)) (α.symm s) =
        rationalUnitaryRegularRestriction G s (rationalUnitaryParameterOfBasis G B c) := by
    rw [← rationalUnramifiedBasisLaurentEquiv_eval_unitary G B,
      AlgEquiv.apply_symm_apply]
  have hb' : finiteLaurentCoordinateRoot n (Circle.toUnits a) ^ k ∣ α.symm b := by
    have h := map_dvd α.symm hb
    change α.symm (α (finiteLaurentCoordinateRoot n (Circle.toUnits a)) ^ k) ∣ α.symm b at h
    simpa only [map_pow, AlgEquiv.symm_apply_apply] using h
  have hp' := finiteLaurentCoordinateRoot_pow_dvd_of_dense_unitary_bound
    a k (α.symm p) (α.symm b) Set.univ dense_univ C
    (fun c _ => by
      rw [he p c, he b c]
      exact hglobal _) hb'
  have h := map_dvd α hp'
  change α (finiteLaurentCoordinateRoot n (Circle.toUnits a)) ^ k ∣ p
  simpa only [map_pow, AlgEquiv.apply_symm_apply] using h

end Langlands.Plancherel
