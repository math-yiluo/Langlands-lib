import Langlands.BaseChange.UnramifiedWeylJacquetSupport.Weyl
import Langlands.Correspondence.SphericalStandardModuleReduction
import Langlands.Correspondence.OrderedUnramifiedSphericalGenerationProof
import Langlands.Representation.Derivative.OrderedCuspidalProductNondegeneracyProof
import Langlands.Representation.Derivative.GeneralLinearDerivativeExactnessProof
import Langlands.Representation.Whittaker.TopDerivativeDual
import Langlands.Representation.Whittaker.Transport

/-! A spherical generic constituent has the full Weyl Jacquet multiset. -/

noncomputable section

namespace Langlands.BaseChange.WeylJacquet

open CategoryTheory GeneralLinear Correspondence Unramified Unramified.SphericalExistence
open Derivative Derivative.OrderedCuspidalProductNondegeneracy

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) {r : ℕ}

attribute [local instance] heckeFieldTopology heckeGeneralLinearTopology
  heckeGeneralLinearTopologicalGroup

set_option hygiene false in
local notation "T" => F.canonicalTopologicalData
set_option hygiene false in
local notation "G" => GeneralLinear (r + 1) F.Carrier

private theorem rankOneClass_ne_twist {a b : ℂˣ} (hab : ‖(a : ℂ)‖ ≤ ‖(b : ℂ)‖) :
    (rankOneSupercuspidalObject.{uF, 0} F (character F b)).isoClass ≠
      (T).supercuspidalClassRealPowerTwist 1 1
        (rankOneSupercuspidalObject.{uF, 0} F (character F a)).isoClass := by
  intro h
  let A := rankOneSupercuspidalObject.{uF, 0} F (character F a)
  let B := rankOneSupercuspidalObject.{uF, 0} F (character F b)
  let χ := (T).determinantPowerCharacter 1 1
  let A' := SupercuspidalRep.twist χ ((T).isOpen_ker_determinantPowerCharacter 1 1)
    ((T).ker_determinant_le_ker_determinantPowerCharacter 1 1) A
  change B.isoClass = A'.isoClass at h
  obtain ⟨iso⟩ := (SupercuspidalRep.isoClass_eq_iff B A').mp h
  let e := SmoothRep.equivOfIso ((supercuspidalProperty (F := F.Carrier) (n := 1)).ι.mapIso iso)
  let E : ULift.{0} ℂ ≃ₗ[ℂ] ULift.{0} ℂ := e.toLinearEquiv
  let ϖ := (T).uniformizerUnit
  let g : GeneralLinear 1 F.Carrier := scalar ϖ
  have hdet : determinant g = ϖ := by
    change Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) ϖ) = ϖ
    simp
  let v : ULift.{0} ℂ := ⟨1⟩
  have hv : v ≠ 0 := fun h₀ => one_ne_zero (congrArg ULift.down h₀)
  have hev : E v ≠ 0 := fun h₀ => hv (E.injective (h₀.trans (map_zero E).symm))
  have he := e.toIntertwiningMap.isIntertwining B.obj.representation A'.obj.representation g v
  change E ((character F b (determinant g) : ℂ) • v) =
    (χ g : ℂ) • ((character F a (determinant g) : ℂ) • E v) at he
  rw [map_smul, smul_smul, hdet, character_uniformizer, character_uniformizer] at he
  have hscalar := smul_left_injective ℂ hev he
  have hnorm : ‖(χ g : ℂ)‖ = (T).normalizedAbs (T).uniformizer := by
    have hn := (T).norm_determinantPowerCharacter_scalar 1 1 ϖ
    simp only [Nat.cast_one, one_mul, Real.rpow_one] at hn
    exact hn
  have hsmall : ‖(b : ℂ)‖ < ‖(a : ℂ)‖ := calc
    ‖(b : ℂ)‖ = (T).normalizedAbs (T).uniformizer * ‖(a : ℂ)‖ := by rw [hscalar, norm_mul, hnorm]
    _ < ‖(a : ℂ)‖ := mul_lt_of_lt_one_left (norm_pos_iff.mpr a.ne_zero) (uniformizer_norm_bounds F).2
  exact (not_lt_of_ge hab) hsmall

private def principalSeriesObject (z : Fin (r + 1) → ℂˣ) : SmoothRep.{0, uF, uF} ℂ G :=
  SmoothRep.of (principalSeriesOfTuple F z) (principalSeriesOfTuple_isAdmissible F z).1

set_option maxHeartbeats 650000 in
private theorem good_ordered_principalSeries (z : Fin (r + 1) → ℂˣ)
    (hz : Monotone fun i => ‖(z i : ℂ)‖) (ψ : NontrivialAdditiveCharacter F) :
    Good T ψ (principalSeriesObject F z) := by
  let B := borelShape r
  let A : ∀ i : Fin B.length, SupercuspidalRep.{uF, 0} (F := F.Carrier) (n := B.size i) :=
    fun i => rankOneSupercuspidalObject F (character F (z i))
  have hA : Ordered T B A := by
    intro i j hij h
    exact rankOneClass_ne_twist F (hz (le_of_lt hij)) (eq_of_heq (Sigma.mk.inj h).2)
  let σ := fun i => (A i).obj
  let X := ((T).normalizedProductInductionFunctor.{uF, 0} B).obj σ
  have hX : Good T ψ X := by
    have h := good_product T ψ r B rfl A hA r rfl
    rw [generalLinearRankCast_refl T (r + 1) rfl] at h
    exact h
  let e : X.representation.Equiv (principalSeriesOfTuple F z) :=
    ((T).normalizedProductInductionObjEquiv B σ).trans
      ((T).normalizedProductInducedEquiv B (fun i => FiniteRepresentation.characterLineEquiv.{uF, 0}
        (determinantQuasiCharacter F 1 (character F (z i)))))
  exact good_of_iso T ψ (Y := principalSeriesObject F z) (SmoothRep.mkIso e) hX

private theorem nontrivial_derivative_of_subrepresentation
    (ψ : NontrivialAdditiveCharacter F) (X : SmoothRep.{0, uF, uF} ℂ G) (hX : Good T ψ X)
    (S : Subrepresentation X.representation) (hS : S ≠ ⊥) :
    Nontrivial ((generalLinearDerivative T ψ (r + 1) (r + 1) le_rfl).obj
      (X.subrepresentation S)) := by
  let U : Subrepresentation ((generalLinearRestriction T r).obj X).representation :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule g v hv := S.apply_mem_toSubmodule g.val hv }
  have hU : U ≠ ⊥ := by
    intro h
    apply hS
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun W : Subrepresentation ((generalLinearRestriction T r).obj X).representation =>
      W.toSubmodule) h
  rw [RestrictionBridge.generalLinearDerivative_succ_obj_eq T ψ le_rfl
    ⟨Nat.succ_pos r, le_rfl⟩]
  exact nontrivial_subrepresentation_of_good T ψ X hX U hU

set_option maxHeartbeats 650000 in
/-- A generic quotient of a norm-increasing unramified principal series is the whole series. -/
theorem orderedPrincipalSeries_quotient_injective (z : Fin (r + 1) → ℂˣ)
    (hz : Monotone fun i => ‖(z i : ℂ)‖) (ψ : NontrivialAdditiveCharacter F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    (hρ : Whittaker.HasFunctional (N := upperUnipotent (r + 1) F.Carrier)
      (θ := Whittaker.standardCharacter ψ r) ρ)
    (q : (principalSeriesOfTuple F z).IntertwiningMap ρ) (hq : Function.Surjective q) :
    Function.Injective q := by
  let X := principalSeriesObject F z
  have hX := good_ordered_principalSeries F z hz ψ
  let S : Subrepresentation X.representation := q.ker
  let Q := X.quotient S
  let L := X.subrepresentation S
  let i := SmoothRep.subtype X S
  let q' := SmoothRep.mkQ X S
  have hi : Function.Injective (SmoothRep.hom i) := Subtype.val_injective
  have hq' : Function.Surjective (SmoothRep.hom q') := SmoothRep.mkQ_surjective X S
  have hex : LinearMap.range (SmoothRep.hom i).toLinearMap =
      LinearMap.ker (SmoothRep.hom q').toLinearMap := by
    change LinearMap.range S.toSubmodule.subtype = LinearMap.ker S.toSubmodule.mkQ
    rw [Submodule.range_subtype, Submodule.ker_mkQ]
  let e : Q.representation.Equiv ρ :=
    Representation.Equiv.mk (q.toLinearMap.quotKerEquivOfSurjective hq) (fun g => by
      apply Submodule.linearMap_qext
      apply LinearMap.ext
      intro v
      exact q.isIntertwining _ _ g v)
  let D := generalLinearDerivative T ψ (r + 1) (r + 1) le_rfl
  have hQ : Nontrivial (D.obj Q) :=
    (Whittaker.hasStandardFunctional_iff_nontrivial_topDerivative T ψ r Q).mp
      ((Whittaker.hasFunctional_iff_of_equiv e).mpr hρ)
  obtain ⟨hiD, hexD, hqD⟩ := generalLinearDerivativeExactness.{uF, uF} F T ψ (r + 1)
    (r + 1) le_rfl L X Q i q' hi hq' hex
  let iD := SmoothRep.hom (D.map i)
  let qD := SmoothRep.hom (D.map q')
  have hd : Module.finrank ℂ (D.obj X) = 1 := hX.2
  let : FiniteDimensional ℂ (D.obj X) := Module.finite_of_finrank_eq_succ hd
  let : FiniteDimensional ℂ (D.obj Q) := Module.Finite.of_surjective qD.toLinearMap hqD
  let : Nontrivial (D.obj Q) := hQ
  have hp : 0 < Module.finrank ℂ (D.obj Q) := Module.finrank_pos
  have hdim := qD.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hqD, finrank_top, ← hexD, hd,
    ← (LinearEquiv.ofInjective iD.toLinearMap hiD).finrank_eq] at hdim
  suffices hS : S = ⊥ from
    LinearMap.ker_eq_bot.mp (congrArg Subrepresentation.toSubmodule hS)
  by_contra hS
  let : Nontrivial (D.obj L) := nontrivial_derivative_of_subrepresentation F ψ X hX S hS
  let : FiniteDimensional ℂ (D.obj L) := Module.Finite.of_injective iD.toLinearMap hiD
  have hpos : 0 < Module.finrank ℂ (D.obj L) := Module.finrank_pos
  change Module.finrank ℂ (D.obj Q) + Module.finrank ℂ (D.obj L) = 1 at hdim
  omega

set_option maxHeartbeats 650000 in
/-- The Borel Jacquet multiset of a spherical generic subquotient is the full Weyl multiset. -/
theorem borelJacquetMultiset_of_spherical_generic (z : Fin (r + 1) → ℂˣ)
    (A : AutomorphicObject.{uF, uV} F r.succPNat) (hA : IsSphericalConstituent F z A)
    (ψ : NontrivialAdditiveCharacter F) (hψ : Whittaker.IsGeneric ψ r A.obj.representation) :
    borelJacquetMultiset F (r := r) A.obj.representation = weylTupleMultiset z := by
  let w := Tuple.sort (fun i => ‖(z i : ℂ)‖)
  let z' := z ∘ w
  have hz' : Monotone (fun i => ‖(z' i : ℂ)‖) :=
    Tuple.monotone_sort (fun i => ‖(z i : ℂ)‖)
  obtain ⟨B, hB⟩ := exists_sphericalConstituentOfTuple.{uF, uV} F z'
  obtain ⟨e⟩ := sphericalConstituentUniqueness.{uF, uV, uV} p F r z' z
    (Eigenvalues.ofTuple_reindex z w) B A hB hA
  have hA' := (isSphericalConstituent_iff_of_equiv F z' e).mp hB
  obtain ⟨q, hq⟩ := exists_principalSeries_quotient_of_generation F
    (orderedUnramifiedSphericalGeneration F) z' hz' A.obj.representation A.obj.isSmooth hA'.1 hA'.2
  let eq := q.ofBijective ⟨orderedPrincipalSeries_quotient_injective F z' hz' ψ hψ.2.2 q hq, hq⟩
  exact (borelJacquetMultiset_eq_of_equiv F A.property.2 eq.symm).trans
    ((principalSeries_borelJacquetMultiset F z').trans (weylTupleMultiset_reindex z w))

end Langlands.BaseChange.WeylJacquet
