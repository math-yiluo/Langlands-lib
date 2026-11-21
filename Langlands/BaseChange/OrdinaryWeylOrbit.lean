import Langlands.BaseChange.RegularCentralizer
import Langlands.BaseChange.WeylTorusFinite

/-! # Fibers of ordinary Weyl conjugation -/

namespace Langlands.BaseChange.WeylTorus

open Langlands.JacquetLanglands Langlands.QuotientIntegration Langlands.TraceFormula

universe u

variable {F : Type u} [Field F] {n : ℕ}

private theorem mem_glCentralizer_iff_commute (x γ : GeneralLinear n F) :
    x ∈ glCentralizer γ ↔ Commute x γ := by
  rw [glCentralizer_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
  rfl

private theorem glCentralizer_map_conj (γ x : GeneralLinear n F) :
    (glCentralizer γ).map (MulAut.conj x).toMonoidHom = glCentralizer (x * γ * x⁻¹) := by
  ext z
  rw [Subgroup.mem_map_equiv, mem_glCentralizer_iff_commute, mem_glCentralizer_iff_commute]
  have h := Commute.conj_iff (a := (MulAut.conj x).symm z) (b := γ) x
  change Commute ((MulAut.conj x) ((MulAut.conj x).symm z)) (x * γ * x⁻¹) ↔ _ at h
  simpa only [MulEquiv.apply_symm_apply] using h.symm

private theorem isRegularSemisimple_conj {γ : GeneralLinear n F} (x : GeneralLinear n F)
    (hγ : IsRegularSemisimple γ) : IsRegularSemisimple (x * γ * x⁻¹) := by
  change (x.val * γ.val * (x⁻¹).val).charpoly.Separable
  rw [Matrix.coe_units_inv, Matrix.charpoly_units_conj]
  exact hγ

private theorem glCentralizer_le_of_mem {δ γ : GeneralLinear n F}
    (hγ : IsRegularSemisimple γ) (hδ : δ ∈ glCentralizer γ) :
    glCentralizer γ ≤ glCentralizer δ := by
  intro x hx
  apply (mem_glCentralizer_iff_commute x δ).mpr
  exact congrArg Subtype.val (glCentralizer_mul_comm hγ ⟨x, hx⟩ ⟨δ, hδ⟩)

/-- Every regular element of a rational maximal torus has that torus as its centralizer. -/
theorem glCentralizer_eq_of_regularPoint (T : WeylTorus F n) (t : T.regularPoints) :
    glCentralizer t.val.val = T.val := by
  obtain ⟨γ, hγ, hT⟩ := T.property
  have ht : t.val.val ∈ glCentralizer γ := hT.symm ▸ t.val.property
  have hγt := (mem_glCentralizer_iff_commute γ t.val.val).mpr
    ((mem_glCentralizer_iff_commute t.val.val γ).mp ht).symm
  exact (le_antisymm (glCentralizer_le_of_mem t.property hγt)
    (glCentralizer_le_of_mem hγ ht)).trans hT

private theorem mem_iff_commute (T : WeylTorus F n) (t : T.regularPoints)
    (x : GeneralLinear n F) : x ∈ T.val ↔ Commute x t.val.val :=
  (congrArg (fun H : Subgroup (GeneralLinear n F) => x ∈ H)
    (T.glCentralizer_eq_of_regularPoint t).symm).to_iff.trans
      (mem_glCentralizer_iff_commute x t.val.val)

/-- Conjugation on the quotient by a rational torus and its regular point set. -/
def ordinaryOrbitMap (T : WeylTorus F n) :
    LeftQuotient T.val × T.regularPoints → GeneralLinear n F :=
  fun (q, t) => descend T.val (fun x => x⁻¹ * t.val.val * x) (fun h x => by
    let c : glCentralizer t.val.val := ⟨h.val, (mem_glCentralizer_iff_commute _ _).mpr
      ((T.mem_iff_commute t h.val).mp h.property)⟩
    exact twistedConj_left_mul (MonoidHom.id _) t.val.val c x) q

@[simp] theorem ordinaryOrbitMap_mk (T : WeylTorus F n) (x : GeneralLinear n F)
    (t : T.regularPoints) :
    T.ordinaryOrbitMap (leftQuotientMap T.val x, t) = x⁻¹ * t.val.val * x := rfl

theorem isRegularSemisimple_ordinaryOrbitMap (T : WeylTorus F n)
    (p : LeftQuotient T.val × T.regularPoints) : IsRegularSemisimple (T.ordinaryOrbitMap p) := by
  obtain ⟨q, t⟩ := p
  induction q using Quotient.inductionOn with
  | h x =>
    change IsRegularSemisimple (x⁻¹ * t.val.val * x)
    simpa only [inv_inv] using isRegularSemisimple_conj x⁻¹ t.property

/-- The centralizer of a regular element determines which tori contribute to its fiber. -/
theorem mem_range_ordinaryOrbitMap_iff (T : WeylTorus F n)
    {γ : GeneralLinear n F} (hγ : IsRegularSemisimple γ) :
    γ ∈ Set.range T.ordinaryOrbitMap ↔ IsConjugate ⟨glCentralizer γ, γ, hγ, rfl⟩ T := by
  constructor
  · rintro ⟨⟨q, t⟩, rfl⟩
    induction q using Quotient.inductionOn with
    | h x =>
      refine ⟨x, ?_⟩
      change (glCentralizer (x⁻¹ * t.val.val * x)).map (MulAut.conj x).toMonoidHom = T.val
      rw [glCentralizer_map_conj, show x * (x⁻¹ * t.val.val * x) * x⁻¹ = t.val.val by group]
      exact T.glCentralizer_eq_of_regularPoint t
  · rintro ⟨x, hx⟩
    change (glCentralizer γ).map (MulAut.conj x).toMonoidHom = T.val at hx
    rw [glCentralizer_map_conj] at hx
    have hmem : x * γ * x⁻¹ ∈ T.val :=
      hx ▸ (mem_glCentralizer_iff_commute _ _).mpr (Commute.refl _)
    use (leftQuotientMap T.val x, ⟨⟨_, hmem⟩, isRegularSemisimple_conj x hγ⟩)
    rw [ordinaryOrbitMap_mk]
    group

private theorem ordinaryOrbitMap_fiber_fst_injective (T : WeylTorus F n)
    (g : GeneralLinear n F) :
    Function.Injective (fun p : {p // T.ordinaryOrbitMap p = g} => p.val.1) := by
  intro p q heq
  change p.val.1 = q.val.1 at heq
  let x := p.val.1.out
  have hx : leftQuotientMap T.val x = p.val.1 := Quotient.out_eq _
  have hpq : T.ordinaryOrbitMap (leftQuotientMap T.val x, p.val.2) =
      T.ordinaryOrbitMap (leftQuotientMap T.val x, q.val.2) := by
    calc
      T.ordinaryOrbitMap (leftQuotientMap T.val x, p.val.2) = g := by
        rw [hx]
        exact p.property
      _ = T.ordinaryOrbitMap (leftQuotientMap T.val x, q.val.2) := by
        rw [hx, heq]
        exact q.property.symm
  simp only [ordinaryOrbitMap_mk] at hpq
  apply Subtype.ext
  refine Prod.ext heq (Subtype.ext (Subtype.ext ?_))
  exact mul_left_cancel (mul_right_cancel hpq)

/-- Every nonempty fiber of ordinary Weyl conjugation is in bijection with the
rational Weyl group. The bijection uses the indicated point of the fiber. -/
noncomputable def ordinaryOrbitFiberEquiv (T : WeylTorus F n)
    (γ : T.regularPoints) (x : GeneralLinear n F) :
    T.RationalWeylGroup ≃ {p // T.ordinaryOrbitMap p = x⁻¹ * γ.val.val * x} := by
  let N := Subgroup.normalizer (T.val : Set (GeneralLinear n F))
  let Fiber := {p // T.ordinaryOrbitMap p = x⁻¹ * γ.val.val * x}
  let point (k : N) : Fiber := by
    have hmem := (Subgroup.mem_normalizer_iff''.mp k.property γ.val.val).mp γ.val.property
    have hreg : IsRegularSemisimple (k.val⁻¹ * γ.val.val * k.val) := by
      simpa only [inv_inv] using isRegularSemisimple_conj k.val⁻¹ γ.property
    refine ⟨(leftQuotientMap T.val (k.val⁻¹ * x), ⟨⟨_, hmem⟩, hreg⟩), ?_⟩
    rw [ordinaryOrbitMap_mk]
    group
  let f : T.RationalWeylGroup → Fiber := Quotient.lift point (by
    intro k m h
    apply T.ordinaryOrbitMap_fiber_fst_injective
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    change (m.val⁻¹ * x) * (k.val⁻¹ * x)⁻¹ ∈ T.val
    have hkm : k.val⁻¹ * m.val ∈ T.val := by
      change k⁻¹ * m ∈ T.val.subgroupOf N
      exact QuotientGroup.leftRel_apply.mp h
    simpa only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] using T.val.inv_mem hkm)
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro a b
    induction a using Quotient.inductionOn with
    | h k =>
      induction b using Quotient.inductionOn with
      | h m =>
        intro heq
        have h := congrArg (fun p : Fiber => p.val.1) heq
        change leftQuotientMap T.val (k.val⁻¹ * x) =
          leftQuotientMap T.val (m.val⁻¹ * x) at h
        have hkm := QuotientGroup.rightRel_apply.mp (Quotient.exact h)
        change (m.val⁻¹ * x) * (k.val⁻¹ * x)⁻¹ ∈ T.val at hkm
        apply Quotient.sound
        apply QuotientGroup.leftRel_apply.mpr
        change k.val⁻¹ * m.val ∈ T.val
        simpa only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] using T.val.inv_mem hkm
  · intro p
    let y := p.val.1.out
    have hy : leftQuotientMap T.val y = p.val.1 := Quotient.out_eq _
    have hp : y⁻¹ * p.val.2.val.val * y = x⁻¹ * γ.val.val * x := by
      rw [← ordinaryOrbitMap_mk, hy]
      exact p.property
    let k := x * y⁻¹
    have hkt : k⁻¹ * γ.val.val * k = p.val.2.val.val := by
      have h := congrArg (fun z => y * z * y⁻¹) hp.symm
      simpa only [k, mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left, mul_inv_cancel,
        mul_one] using h
    have hk : k ∈ N := by
      apply Subgroup.mem_normalizer_iff''.mpr
      intro z
      rw [T.mem_iff_commute γ z, T.mem_iff_commute p.val.2 _, ← hkt]
      simpa only [inv_inv] using (Commute.conj_iff (a := z) (b := γ.val.val) k⁻¹).symm
    refine ⟨Quotient.mk _ ⟨k, hk⟩, T.ordinaryOrbitMap_fiber_fst_injective _ ?_⟩
    change leftQuotientMap T.val (k⁻¹ * x) = p.val.1
    simpa only [k, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one] using hy

/-- The multiplicity of the ordinary Weyl map is the order of the rational Weyl group. -/
theorem natCard_ordinaryOrbitFiber (T : WeylTorus F n) {g : GeneralLinear n F}
    (hg : g ∈ Set.range T.ordinaryOrbitMap) :
    Nat.card {p // T.ordinaryOrbitMap p = g} = Nat.card T.RationalWeylGroup := by
  obtain ⟨⟨q, γ⟩, rfl⟩ := hg
  induction q using Quotient.inductionOn with
  | h x =>
    change Nat.card {p // T.ordinaryOrbitMap p = x⁻¹ * γ.val.val * x} = _
    exact Nat.card_congr (T.ordinaryOrbitFiberEquiv γ x).symm

end Langlands.BaseChange.WeylTorus

namespace Langlands.BaseChange

open Langlands.JacquetLanglands

universe u

/-- The ordinary Weyl maps partition the regular locus by representative tori and
have the indicated finite multiplicity on each image. -/
def OrdinaryWeylOrbitDecompositionStatement : Prop :=
  ∀ (F : Type u) [Field F] (n : ℕ) (S : Set (WeylTorus F n)),
    WeylTorus.IsRepresentativeSet S →
      (∀ γ : GeneralLinear n F, IsRegularSemisimple γ ↔
        ∃! T : WeylTorus F n, T ∈ S ∧ γ ∈ Set.range T.ordinaryOrbitMap) ∧
      (∀ (T : WeylTorus F n) (γ : GeneralLinear n F),
        γ ∈ Set.range T.ordinaryOrbitMap →
          Finite T.RationalWeylGroup ∧
            Nat.card {p // T.ordinaryOrbitMap p = γ} = Nat.card T.RationalWeylGroup ∧
            0 < Nat.card T.RationalWeylGroup)

theorem ordinaryWeylOrbitDecomposition : OrdinaryWeylOrbitDecompositionStatement.{u} := by
  intro F _ n S hS
  refine ⟨?_, fun T γ hγ => ⟨T.finite_rationalWeylGroup,
    T.natCard_ordinaryOrbitFiber hγ, T.natCard_rationalWeylGroup_pos⟩⟩
  intro γ
  constructor
  · intro hγ
    simpa only [WeylTorus.mem_range_ordinaryOrbitMap_iff _ hγ] using
      hS ⟨glCentralizer γ, γ, hγ, rfl⟩
  · rintro ⟨T, ⟨_, p, rfl⟩, _⟩
    exact T.isRegularSemisimple_ordinaryOrbitMap p

end Langlands.BaseChange
