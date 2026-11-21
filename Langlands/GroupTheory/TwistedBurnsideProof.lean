import Langlands.GroupTheory.TwistedBurnside
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Incidence bijection for twisted Burnside counting
-/

noncomputable section

namespace Langlands

/-- A finite disjoint sum counts in `ℕ∞` even if some fibres are infinite. -/
theorem enatCardSigma {ι : Type*} [Fintype ι] (Y : ι → Type*) :
    ENat.card (Σ i, Y i) = ∑ i, ENat.card (Y i) := by
  classical
  by_cases h : ∀ i, Finite (Y i)
  · let (i : ι) : Fintype (Y i) := Fintype.ofFinite (Y i)
    simp only [ENat.card_eq_coe_fintype_card, Fintype.card_sigma, Nat.cast_sum]
  · obtain ⟨i, hi⟩ := not_forall.mp h
    let : Infinite (Y i) := not_finite_iff_infinite.mp hi
    let : Infinite (Σ i, Y i) := Infinite.of_injective (Sigma.mk i) fun _ _ hxy =>
      eq_of_heq ((Sigma.mk.inj_iff.mp hxy).2)
    rw [ENat.card_eq_top_of_infinite, eq_comm, ← top_le_iff]
    simpa only [ENat.card_eq_top_of_infinite (α := Y i)] using
      (Finset.single_le_sum (f := fun i => ENat.card (Y i))
        (fun _ _ => zero_le) (Finset.mem_univ i))

open MulAction

variable {G X : Type*} [Group G] [MulAction G X] (F : X → X)
  (hF : ∀ x y, orbitRel G X x y → orbitRel G X (F x) (F y))

local notation "Ω" => orbitRel.Quotient G X
local notation "mkOrbit" => @Quotient.mk'' X (orbitRel G X)
local notation "ΩF" => {o : Ω // Quotient.map' F hF o = o}
local notation "T" => (fun x : X => {g : G // g • F x = x})

/-- The twisted fixed-point incidence set is a copy of `G` over each
orbit fixed by `F`. No finiteness assumption is needed for this bijection. -/
def twistedBurnsideEquiv : (Σ g : G, {x : X // g • F x = x}) ≃ ΩF × G := by
  let fixedOrbit (s : Σ x : X, T x) : ΩF := ⟨mkOrbit s.1, by
    change mkOrbit (F s.1) = mkOrbit s.1
    calc
      mkOrbit (F s.1) = mkOrbit (s.2.1 • F s.1) :=
        orbitRel.Quotient.quotient_smul_eq.symm
      _ = mkOrbit s.1 := congrArg mkOrbit s.2.2⟩
  have hmem (o : ΩF) (x : X) : x ∈ orbit G o.1.out ↔ mkOrbit x = o.1 := by
    rw [← orbitRel.Quotient.orbit_eq_orbit_out o.1 Quotient.out_eq']
    exact orbitRel.Quotient.mem_orbit
  let fiberEquiv (o : ΩF) :
      {s // fixedOrbit s = o} ≃ Σ x : orbit G o.1.out, T x.1 :=
    { toFun := fun ⟨s, hs⟩ => ⟨⟨s.1, (hmem o s.1).mpr (congrArg Subtype.val hs)⟩, s.2⟩
      invFun := fun ⟨x, g⟩ => ⟨⟨x.1, g⟩, Subtype.ext ((hmem o x.1).mp x.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let transporterEquiv (o : ΩF) (x : orbit G o.1.out) :
      T x.1 ≃ stabilizer G o.1.out := by
    have hFx : mkOrbit (F x.1) = o.1 :=
      (congrArg (Quotient.map' F hF) ((hmem o x.1).mp x.2)).trans o.2
    let k := (mem_orbit_iff.mp x.2).choose
    have hk : k • o.1.out = x.1 := (mem_orbit_iff.mp x.2).choose_spec
    let b := (mem_orbit_iff.mp ((hmem o (F x.1)).mpr hFx)).choose
    have hb : b • o.1.out = F x.1 :=
      (mem_orbit_iff.mp ((hmem o (F x.1)).mpr hFx)).choose_spec
    refine ((Equiv.mulLeft k⁻¹).trans (Equiv.mulRight b)).subtypeEquiv ?_
    intro g
    change g • F x.1 = x.1 ↔ (k⁻¹ * g * b) • o.1.out = o.1.out
    simp only [mul_assoc, mul_smul, inv_smul_eq_iff, hb, hk]
  calc
    (Σ g : G, {x : X // g • F x = x}) ≃ {gx : G × X // gx.1 • F gx.2 = gx.2} :=
      (Equiv.subtypeProdEquivSigmaSubtype (fun (g : G) (x : X) => g • F x = x)).symm
    _ ≃ {xg : X × G // xg.2 • F xg.1 = xg.1} := (Equiv.prodComm G X).subtypeEquiv fun _ => Iff.rfl
    _ ≃ Σ x : X, T x := Equiv.subtypeProdEquivSigmaSubtype (fun (x : X) (g : G) => g • F x = x)
    _ ≃ Σ o : ΩF, {s // fixedOrbit s = o} := (Equiv.sigmaFiberEquiv fixedOrbit).symm
    _ ≃ Σ o : ΩF, Σ x : orbit G o.1.out, T x.1 := Equiv.sigmaCongrRight fiberEquiv
    _ ≃ Σ o : ΩF, Σ _ : orbit G o.1.out, stabilizer G o.1.out :=
      Equiv.sigmaCongrRight fun o => Equiv.sigmaCongrRight (transporterEquiv o)
    _ ≃ Σ o : ΩF, orbit G o.1.out × stabilizer G o.1.out :=
      Equiv.sigmaCongrRight fun o => Equiv.sigmaEquivProd (orbit G o.1.out) (stabilizer G o.1.out)
    _ ≃ Σ _ : ΩF, G := Equiv.sigmaCongrRight fun o => orbitProdStabilizerEquivGroup G o.1.out
    _ ≃ ΩF × G := Equiv.sigmaEquivProd ΩF G

/-- Count the incidence bijection in extended naturals. -/
theorem twistedBurnside.{uG, uX} : TwistedBurnsideStatement.{uG, uX} := by
  intro G _ _ X _ F hF
  rw [← enatCardSigma, ENat.card_congr (twistedBurnsideEquiv F hF), ENat.card_prod,
    ENat.card_eq_coe_fintype_card (α := G), mul_comm]

end Langlands
