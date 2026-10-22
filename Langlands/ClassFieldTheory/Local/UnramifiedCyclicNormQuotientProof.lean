import Langlands.ClassFieldTheory.Local.UnitNormStatement
import Langlands.ClassFieldTheory.Local.UnramifiedNormMembershipProof
import Langlands.LocalField.Normalization.Proof
import Mathlib.Topology.LocallyConstant.Basic

/-! The normalized-order construction of the cyclic norm quotient. -/

noncomputable section

namespace Langlands.LocalClassField

universe u v

private theorem ord_units_locallyConstant {p : ℕ} [Fact p.Prime]
    {F : PadicField.{u} p} (T : F.TopologicalData) :
    let := T.topology
    IsLocallyConstant (fun a : F.Carrierˣ => T.ord (a : F.Carrier)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let v := ValuativeRel.valuation F.Carrier
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro a
  refine ⟨{b : F.Carrierˣ | v.restrict (b : F.Carrier) = v.restrict (a : F.Carrier)},
    (v.isOpen_sphere (v.restrict.ne_zero_iff.mpr a.ne_zero)).preimage
      Units.continuous_val, rfl, ?_⟩
  intro b hb
  have hv : v (b : F.Carrier) = v (a : F.Carrier) := by
    simpa only [Valuation.embedding_restrict] using
      congrArg MonoidWithZeroHom.ValueGroup₀.embedding hb
  change -WithZero.log ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier)
    (v (b : F.Carrier))) =
      -WithZero.log ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier)
        (v (a : F.Carrier)))
  rw [hv]

private def orderMod {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p}
    (T : F.TopologicalData) (d : ℕ) : F.Carrierˣ →* Multiplicative (ZMod d) where
  toFun a := Multiplicative.ofAdd (T.ord (a : F.Carrier) : ZMod d)
  map_one' := by simp [T.ord_one]
  map_mul' a b := by
    change Multiplicative.ofAdd (T.ord ((a : F.Carrier) * b) : ZMod d) = _
    rw [T.ord_mul a.ne_zero b.ne_zero, Int.cast_add]
    rfl

private theorem orderMod_surjective {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p}
    (T : F.TopologicalData) (d : ℕ) : Function.Surjective (orderMod T d) := by
  intro z
  obtain ⟨n, hn⟩ := ZMod.intCast_surjective z.toAdd
  obtain ⟨x, hx, ho⟩ := T.ord_surjective_nonzero n
  refine ⟨Units.mk0 x hx, ?_⟩
  change Multiplicative.ofAdd (T.ord x : ZMod d) = z
  rw [ho, hn]
  rfl

/-- Normalized order modulo the extension degree identifies the actual
unramified norm quotient with the discrete cyclic group. -/
theorem unramifiedCyclicNormQuotient : UnramifiedCyclicNormQuotient.{u,v} := by
  intro p hp F E hAlg hTower hFinite T S hram
  let := T.topology
  let d := Module.finrank F.Carrier E.Carrier
  let : TopologicalSpace (Multiplicative (ZMod d)) := ⊥
  let : DiscreteTopology (Multiplicative (ZMod d)) := ⟨rfl⟩
  let f := orderMod T d
  have hk : normSubgroup F.Carrier E.Carrier = f.ker := by
    ext a
    rw [unramifiedNormMembership p F E T S hram a, MonoidHom.mem_ker]
    change (d : ℤ) ∣ T.ord (a : F.Carrier) ↔
      Multiplicative.ofAdd (T.ord (a : F.Carrier) : ZMod d) = Multiplicative.ofAdd 0
    rw [Multiplicative.ofAdd.injective.eq_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]
  let e : NormQuotient F.Carrier E.Carrier ≃* Multiplicative (ZMod d) :=
    (QuotientGroup.quotientMulEquivOfEq hk).trans
      (QuotientGroup.quotientKerEquivOfSurjective f (orderMod_surjective T d))
  have he : ∀ a : F.Carrierˣ,
      e (normQuotientProjection F.Carrier E.Carrier a) = f a := fun _ => rfl
  have hc : Continuous f :=
    ((ord_units_locallyConstant T).comp
      (fun n : ℤ => Multiplicative.ofAdd (n : ZMod d))).continuous
  have hce : Continuous e := by
    apply (QuotientGroup.isQuotientMap_mk (normSubgroup F.Carrier E.Carrier)).continuous_iff.mpr
    exact hc
  refine ⟨{ e with
    continuous_toFun := hce
    continuous_invFun := continuous_of_discreteTopology }, ?_⟩
  exact he

end Langlands.LocalClassField
