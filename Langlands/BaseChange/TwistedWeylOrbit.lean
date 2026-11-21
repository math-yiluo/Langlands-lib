import Langlands.BaseChange.CyclicNormLemma
import Langlands.BaseChange.ExactNormCentralizer
import Langlands.BaseChange.OrdinaryWeylOrbit
import Langlands.BaseChange.WeylTorusNormImage

/-! # Fibers of cyclically twisted Weyl conjugation -/

namespace Langlands.BaseChange.WeylTorus

open Langlands.JacquetLanglands Langlands.QuotientIntegration Langlands.TraceFormula
open Set

universe u v

private theorem leftQuotientMap_eq_of_twistedConj_eq
    {G M : Type*} [Group G] [FunLike M G G] [MonoidHomClass M G G]
    (θ : M) (d x y : G) (heq : x⁻¹ * d * θ x = y⁻¹ * d * θ y) :
    leftQuotientMap (twistedCentralizer θ d) x =
      leftQuotientMap (twistedCentralizer θ d) y := by
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  apply (mem_twistedCentralizer θ d _).mpr
  calc
    (y * x⁻¹)⁻¹ * d * θ (y * x⁻¹) =
        x * (y⁻¹ * d * θ y) * (θ x)⁻¹ := by
      rw [map_mul, map_inv, mul_inv_rev, inv_inv]
      group
    _ = d := by rw [← heq]; group

variable {F : Type u} [Field F] {n : ℕ}

private theorem ordinaryOrbitMap_left_injective (T : WeylTorus F n) (t : T.regularPoints) :
    Function.Injective (fun q => T.ordinaryOrbitMap (q, t)) := by
  intro q r h
  induction q using Quotient.inductionOn with
  | h x =>
    induction r using Quotient.inductionOn with
    | h y =>
      change x⁻¹ * t.val.val * x = y⁻¹ * t.val.val * y at h
      change leftQuotientMap T.val x = leftQuotientMap T.val y
      rw [← T.glCentralizer_eq_of_regularPoint t]
      exact leftQuotientMap_eq_of_twistedConj_eq (MonoidHom.id _) t.val.val x y h

variable {E : Type v} [CommRing E] [Algebra F E] {σ : E ≃ₐ[F] E} {l : ℕ}

/-- The regular points of a rational torus in its cyclic norm image. -/
abbrev regularNormPoints (T : WeylTorus F n) (σ : E ≃ₐ[F] E) (l : ℕ) :=
  T.regularPoints ∩ T.normImage σ l

private abbrev AssociatedRegularPoints (T : WeylTorus F n) (d : GeneralLinear n E)
    (σ : E ≃ₐ[F] E) (l : ℕ) :=
  {t : T.regularPoints // IsNormAssociated σ l d t.val.val}

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology F E]

variable (T : WeylTorus F n) (hσ : IsCyclicAlgebra σ l)
  (lift : T.regularNormPoints σ l → T.points E)
  (hlift : ∀ t, cyclicNorm σ l (lift t).val = baseChange F E n t.val.val)

include hσ hlift in
private theorem sigmaCentralizer_lift (t : T.regularNormPoints σ l) :
    sigmaCentralizer σ n (lift t).val = T.val.map (baseChange F E n) := by
  rw [sigmaCentralizer_eq_map_glCentralizer_of_cyclicNorm_eq hσ t.property.1 (hlift t),
    T.glCentralizer_eq_of_regularPoint ⟨t.val, t.property.1⟩]

/-- The twisted Weyl map on the fixed rational-torus quotient and the regular
norm-image points. An exact lift of each torus parameter specifies the map. -/
def twistedOrbitMap :
    LeftQuotient (T.val.map (baseChange F E n)) × T.regularNormPoints σ l → GeneralLinear n E :=
  fun (q, t) => descend (T.val.map (baseChange F E n))
    (fun x => x⁻¹ * (lift t).val * entrywiseAut σ n x) (fun h x => by
      have hc : h.val ∈ sigmaCentralizer σ n (lift t).val := by
        rw [T.sigmaCentralizer_lift hσ lift hlift t]
        exact h.property
      exact twistedConj_left_mul (entrywiseAut σ n) (lift t).val ⟨h.val, hc⟩ x) q

@[simp] theorem twistedOrbitMap_mk (x : GeneralLinear n E) (t : T.regularNormPoints σ l) :
    T.twistedOrbitMap hσ lift hlift (leftQuotientMap (T.val.map (baseChange F E n)) x, t) =
      x⁻¹ * (lift t).val * entrywiseAut σ n x := rfl

private theorem twistedOrbitMap_assoc
    (p : LeftQuotient (T.val.map (baseChange F E n)) × T.regularNormPoints σ l) :
    IsNormAssociated σ l (T.twistedOrbitMap hσ lift hlift p) p.2.val.val := by
  obtain ⟨q, t⟩ := p
  induction q using Quotient.inductionOn with
  | h x =>
    change IsNormAssociated σ l (x⁻¹ * (lift t).val * entrywiseAut σ n x) t.val.val
    refine ⟨x⁻¹, ?_⟩
    rw [cyclicNorm_twistedConj, hσ.pow_eq_one, entrywiseAut_one_apply, hlift t]
    group

theorem isSigmaRegular_twistedOrbitMap
    (p : LeftQuotient (T.val.map (baseChange F E n)) × T.regularNormPoints σ l) :
    IsSigmaRegular σ l (T.twistedOrbitMap hσ lift hlift p) :=
  ⟨p.2.val.val, T.twistedOrbitMap_assoc hσ lift hlift p, p.2.property.1⟩

private theorem twistedOrbitMap_left_injective (t : T.regularNormPoints σ l) :
    Function.Injective (fun q => T.twistedOrbitMap hσ lift hlift (q, t)) := by
  intro q r h
  induction q using Quotient.inductionOn with
  | h x =>
    induction r using Quotient.inductionOn with
    | h y =>
      change x⁻¹ * (lift t).val * entrywiseAut σ n x =
        y⁻¹ * (lift t).val * entrywiseAut σ n y at h
      change leftQuotientMap (T.val.map (baseChange F E n)) x =
        leftQuotientMap (T.val.map (baseChange F E n)) y
      rw [← T.sigmaCentralizer_lift hσ lift hlift t]
      exact leftQuotientMap_eq_of_twistedConj_eq (entrywiseAut σ n) (lift t).val x y h

private theorem exists_twistedOrbitMap_eq (t : T.regularNormPoints σ l)
    {d : GeneralLinear n E} (hd : IsNormAssociated σ l d t.val.val) :
    ∃ q, T.twistedOrbitMap hσ lift hlift (q, t) = d := by
  obtain ⟨x, hx⟩ := hd
  have hc : ∃ g : GeneralLinear n E,
      g⁻¹ * cyclicNorm σ l (lift t).val * g = cyclicNorm σ l d := by
    refine ⟨x⁻¹, ?_⟩
    rw [hlift t, ← hx]
    group
  obtain ⟨y, hy⟩ := (cyclicNormLemma F E σ l n hσ).2.2 (lift t).val d hc
  exact ⟨leftQuotientMap _ y, hy⟩

private noncomputable def twistedOrbitFiberEquivAssociated (d : GeneralLinear n E) :
    {p // T.twistedOrbitMap hσ lift hlift p = d} ≃ AssociatedRegularPoints T d σ l := by
  let e (p : {p // T.twistedOrbitMap hσ lift hlift p = d}) :
      AssociatedRegularPoints T d σ l :=
    ⟨⟨p.val.2.val, p.val.2.property.1⟩,
      (congrArg (fun x => IsNormAssociated σ l x p.val.2.val.val) p.property).mp
        (T.twistedOrbitMap_assoc hσ lift hlift p.val)⟩
  refine Equiv.ofBijective e ⟨?_, ?_⟩
  · rintro ⟨⟨q, t⟩, hq⟩ ⟨⟨r, s⟩, hr⟩ he
    have hs : t = s := Subtype.ext
      (congrArg (fun a : AssociatedRegularPoints T d σ l => a.val.val) he)
    subst s
    exact Subtype.ext (Prod.ext
      (T.twistedOrbitMap_left_injective hσ lift hlift t (hq.trans hr.symm)) rfl)
  · intro t
    let t' : T.regularNormPoints σ l :=
      ⟨t.val.val, t.val.property,
        (T.mem_normImage_iff_isNorm hσ t.val.property).mpr ⟨d, t.property⟩⟩
    obtain ⟨q, hq⟩ := T.exists_twistedOrbitMap_eq hσ lift hlift t' t.property
    exact ⟨⟨(q, t'), hq⟩, Subtype.ext (Subtype.ext rfl)⟩

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology F E] in
include hσ in
private theorem assoc_of_ordinaryOrbitMap_eq {d : GeneralLinear n E} {g : GeneralLinear n F}
    (hd : IsNormAssociated σ l d g)
    (p : LeftQuotient T.val × T.regularPoints) (hp : T.ordinaryOrbitMap p = g) :
    IsNormAssociated σ l d p.2.val.val := by
  obtain ⟨q, t⟩ := p
  induction q using Quotient.inductionOn with
  | h x =>
    change x⁻¹ * t.val.val * x = g at hp
    have ht : x * g * x⁻¹ = t.val.val := by rw [← hp]; group
    simpa only [inv_one, one_mul, map_one, mul_one, inv_inv, ht] using
      hd.twistedConj hσ.pow_eq_one 1 x⁻¹

private noncomputable def ordinaryOrbitFiberEquivAssociated
    {d : GeneralLinear n E} {g : GeneralLinear n F} (hd : IsNormAssociated σ l d g) :
    {p // T.ordinaryOrbitMap p = g} ≃ AssociatedRegularPoints T d σ l := by
  let e (p : {p // T.ordinaryOrbitMap p = g}) : AssociatedRegularPoints T d σ l :=
    ⟨p.val.2, T.assoc_of_ordinaryOrbitMap_eq hσ hd p.val p.property⟩
  refine Equiv.ofBijective e ⟨?_, ?_⟩
  · rintro ⟨⟨q, t⟩, hq⟩ ⟨⟨r, s⟩, hr⟩ he
    have hs : t = s := congrArg Subtype.val he
    subst s
    exact Subtype.ext (Prod.ext
      (T.ordinaryOrbitMap_left_injective t (hq.trans hr.symm)) rfl)
  · intro t
    obtain ⟨x, hx⟩ := (cyclicNormLemma F E σ l n hσ).2.1 d t.val.val g t.property hd
    exact ⟨⟨(leftQuotientMap T.val x, t.val), hx⟩, Subtype.ext rfl⟩

/-- The twisted Weyl fiber over an element associated with `g` has the same
torus parameters as the ordinary Weyl fiber over `g`. -/
noncomputable def twistedOrbitFiberEquivOrdinary {d : GeneralLinear n E} {g : GeneralLinear n F}
    (hd : IsNormAssociated σ l d g) :
    {p // T.twistedOrbitMap hσ lift hlift p = d} ≃ {p // T.ordinaryOrbitMap p = g} :=
  (T.twistedOrbitFiberEquivAssociated hσ lift hlift d).trans
    (T.ordinaryOrbitFiberEquivAssociated hσ hd).symm

/-- On associated elements, the twisted and ordinary Weyl images match. -/
theorem mem_range_twistedOrbitMap_iff_ordinary {d : GeneralLinear n E} {g : GeneralLinear n F}
    (hd : IsNormAssociated σ l d g) :
    d ∈ range (T.twistedOrbitMap hσ lift hlift) ↔ g ∈ range T.ordinaryOrbitMap := by
  let e := T.twistedOrbitFiberEquivOrdinary hσ lift hlift hd
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨(e ⟨p, hp⟩).val, (e ⟨p, hp⟩).property⟩
  · rintro ⟨p, hp⟩
    exact ⟨(e.symm ⟨p, hp⟩).val, (e.symm ⟨p, hp⟩).property⟩

/-- Each nonempty twisted Weyl fiber has the rational Weyl multiplicity. -/
theorem natCard_twistedOrbitFiber {d : GeneralLinear n E}
    (hd : d ∈ range (T.twistedOrbitMap hσ lift hlift)) :
    Nat.card {p // T.twistedOrbitMap hσ lift hlift p = d} =
      Nat.card T.RationalWeylGroup := by
  obtain ⟨g, hg⟩ := (cyclicNormLemma F E σ l n hσ).1 d
  exact (Nat.card_congr (T.twistedOrbitFiberEquivOrdinary hσ lift hlift hg)).trans
    (T.natCard_ordinaryOrbitFiber
      ((T.mem_range_twistedOrbitMap_iff_ordinary hσ lift hlift hg).mp hd))

end Langlands.BaseChange.WeylTorus

namespace Langlands.BaseChange

open Set

/-- The representative twisted Weyl images partition the σ-regular locus and
their fibers have the corresponding rational Weyl orders. -/
def TwistedWeylOrbitDecompositionStatement.{u, v} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (E : Type v) [CommRing E] [Algebra F E]
    [TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology F E]
    (σ : E ≃ₐ[F] E) (l n : ℕ) (hσ : IsCyclicAlgebra σ l)
    (S : Set (WeylTorus F n)), WeylTorus.IsRepresentativeSet S →
    ∀ (lift : ∀ T : S, T.val.regularNormPoints σ l → T.val.points E)
      (hlift : ∀ (T : S) (t : T.val.regularNormPoints σ l),
        cyclicNorm σ l (lift T t).val = baseChange F E n t.val.val),
      (∀ d : GeneralLinear n E, IsSigmaRegular σ l d ↔
        ∃! T : S, d ∈ range (T.val.twistedOrbitMap hσ (lift T) (hlift T))) ∧
      (∀ (T : S) (d : GeneralLinear n E), d ∈ range (T.val.twistedOrbitMap hσ (lift T) (hlift T)) →
        Nat.card {p // T.val.twistedOrbitMap hσ (lift T) (hlift T) p = d} =
          Nat.card T.val.RationalWeylGroup)

theorem twistedWeylOrbitDecomposition : TwistedWeylOrbitDecompositionStatement.{u, v} := by
  intro F _ _ _ _ E _ _ _ _ _ σ l n hσ S hS lift hlift
  refine ⟨?_, fun T _ hd => T.val.natCard_twistedOrbitFiber hσ (lift T) (hlift T) hd⟩
  intro d
  constructor
  · rintro ⟨g, hd, hg⟩
    have hpart := (ordinaryWeylOrbitDecomposition F n S hS).1 g
    obtain ⟨T, ⟨hT, ht⟩, huniq⟩ := hpart.mp hg
    let U : S := ⟨T, hT⟩
    refine ⟨U, (U.val.mem_range_twistedOrbitMap_iff_ordinary hσ (lift U) (hlift U) hd).mpr ht, ?_⟩
    intro V hv
    exact Subtype.ext (huniq V.val ⟨V.property,
      (V.val.mem_range_twistedOrbitMap_iff_ordinary hσ (lift V) (hlift V) hd).mp hv⟩)
  · rintro ⟨T, ⟨p, rfl⟩, _⟩
    exact T.val.isSigmaRegular_twistedOrbitMap hσ (lift T) (hlift T) p

end Langlands.BaseChange
