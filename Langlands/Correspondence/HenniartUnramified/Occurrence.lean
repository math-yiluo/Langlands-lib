import Langlands.Correspondence.HenniartUnramified.Period

/-! # Occurrence of inertia types in local Weil representations -/

noncomputable section

namespace Langlands.Henniart.Numerical

open Correspondence FiniteRepresentation FiniteRepresentation.SplitDegree Weil.Local
open VirtualRepresentation VirtualRepresentation.LocalWeil.Ramification

universe uF uW

section General

variable {G : Type*} [Group G] {V W U : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W] [AddCommGroup U] [Module ℂ U]

theorem comp_equiv_ne_zero {ρ : Representation ℂ G V} {ρ' : Representation ℂ G W}
    {σ : Representation ℂ G U} (P : Representation.IntertwiningMap ρ σ)
    (e : Representation.Equiv ρ' ρ) (hP : P ≠ 0) : P.comp e.toIntertwiningMap ≠ 0 := by
  intro h0
  apply hP
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  have h1 := congrArg (fun F : Representation.IntertwiningMap ρ' σ => F (e.symm v)) h0
  simp only [Representation.IntertwiningMap.comp_apply] at h1
  change P (e.toIntertwiningMap (e.symm v)) = 0 at h1
  rw [Representation.Equiv.coe_toIntertwiningMap] at h1
  simpa using h1

theorem equiv_comp_ne_zero {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    {σ' : Representation ℂ G U} (P : Representation.IntertwiningMap ρ σ)
    (e : Representation.Equiv σ σ') (hP : P ≠ 0) : e.toIntertwiningMap.comp P ≠ 0 := by
  intro h0
  apply hP
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  have h1 := congrArg (fun F : Representation.IntertwiningMap ρ σ' => F v) h0
  simp only [Representation.IntertwiningMap.comp_apply] at h1
  change e.toIntertwiningMap (P v) = 0 at h1
  rw [Representation.Equiv.coe_toIntertwiningMap] at h1
  change P v = 0
  have h2 := congrArg e.symm h1
  simpa using h2

theorem equiv_toIntertwiningMap_ne_zero [Nontrivial V] {ρ : Representation ℂ G V}
    {σ : Representation ℂ G W} (e : Representation.Equiv ρ σ) : e.toIntertwiningMap ≠ 0 := by
  intro h0
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  apply hv
  have h1 := congrArg (fun F : Representation.IntertwiningMap ρ σ => F v) h0
  change e.toIntertwiningMap v = 0 at h1
  rw [Representation.Equiv.coe_toIntertwiningMap] at h1
  have h2 := congrArg e.symm h1
  simpa using h2

end General

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (φ : localWeilGroup F)
  (hφ : localDegree F φ = Multiplicative.ofAdd (1 : ℤ))

/-- Inertia types of the local Weil group. -/
abbrev WType : Type _ :=
  {B : FiniteRepresentation.{0, uF, uW} ℂ (weilSplit F φ hφ).inertia //
    (weilSplit F φ hφ).IsType B}

/-- The type `B` occurs in (is a quotient of) the inertia restriction of `ρ`. -/
def Occurs {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (localWeilGroup F) V)
    (B : WType.{uF, uW} F φ hφ) : Prop :=
  ∃ P : Representation.IntertwiningMap (ρ.comp (weilSplit F φ hφ).inertia.subtype)
    B.1.representation, P ≠ 0

variable {F φ hφ}

/-- Unramified twists do not change the inertia restriction. -/
theorem twist_comp_inertia {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (localWeilGroup F) V) (z : ℂˣ) :
    (Langlands.twist (unramifiedCharacter (localDegree F) z).toMonoidHom ρ).comp
        (weilSplit F φ hφ).inertia.subtype =
      ρ.comp (weilSplit F φ hφ).inertia.subtype := by
  ext n : 1
  change ((unramifiedCharacter (localDegree F) z n : ℂˣ) : ℂ) • ρ n = ρ n
  rw [unramifiedCharacter_on_kernel (localDegree F) z n.2, Units.val_one, one_smul]

/-- An equivalence with a twist restricts to an equivalence on inertia. -/
def restrictEquiv {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (localWeilGroup F) V} {ρ' : Representation ℂ (localWeilGroup F) W}
    {z : ℂˣ}
    (e : Representation.Equiv
      (Langlands.twist (unramifiedCharacter (localDegree F) z).toMonoidHom ρ) ρ') :
    Representation.Equiv (ρ.comp (weilSplit F φ hφ).inertia.subtype)
      (ρ'.comp (weilSplit F φ hφ).inertia.subtype) :=
  twist_comp_inertia (φ := φ) (hφ := hφ) ρ z ▸ equivComp e (weilSplit F φ hφ).inertia.subtype

theorem occurs_of_equiv {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ (localWeilGroup F) V}
    {ρ' : Representation ℂ (localWeilGroup F) W} (e : Representation.Equiv ρ ρ')
    {B : WType.{uF, uW} F φ hφ} (h : Occurs F φ hφ ρ B) : Occurs F φ hφ ρ' B := by
  obtain ⟨P, hP⟩ := h
  let e' := equivComp e.symm (weilSplit F φ hφ).inertia.subtype
  exact ⟨P.comp e'.toIntertwiningMap, comp_equiv_ne_zero P e' hP⟩

theorem occurs_twist_iff {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (localWeilGroup F) V} (z : ℂˣ) {B : WType.{uF, uW} F φ hφ} :
    Occurs F φ hφ (Langlands.twist (unramifiedCharacter (localDegree F) z).toMonoidHom ρ) B ↔
      Occurs F φ hφ ρ B := by
  unfold Occurs
  rw [twist_comp_inertia]

theorem occurs_congr {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (localWeilGroup F) V} {B B' : WType.{uF, uW} F φ hφ}
    (e : Representation.Equiv B.1.representation B'.1.representation) (h : Occurs F φ hφ ρ B) :
    Occurs F φ hφ ρ B' := by
  obtain ⟨P, hP⟩ := h
  exact ⟨e.toIntertwiningMap.comp P, equiv_comp_ne_zero P e hP⟩

theorem occurs_of_class_eq {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (localWeilGroup F) V} {B B' : WType.{uF, uW} F φ hφ}
    (h : (weilSplit F φ hφ).toClass B = (weilSplit F φ hφ).toClass B')
    (hB : Occurs F φ hφ ρ B) : Occurs F φ hφ ρ B' :=
  occurs_congr ((toClass_eq_iff _ B B').mp h).some hB

/-- The types occurring in a coinduction are exactly the conjugates of its type. -/
theorem occurs_typeCoind_iff {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {E : SplitDegree H} {m : ℕ} (S : Stage (weilSplit F φ hφ) E (m + 1))
    (B : WType.{uF, uW} F φ hφ)
    (hp : Function.minimalPeriod ((weilSplit F φ hφ).conjType 1)
      ((weilSplit F φ hφ).toClass B) = m + 1) (B' : WType.{uF, uW} F φ hφ) :
    Occurs F φ hφ (S.typeCoind B hp) B' ↔
      ∃ j : Fin (m + 1), (weilSplit F φ hφ).toClass B' =
        (weilSplit F φ hφ).conjType j ((weilSplit F φ hφ).toClass B) := by
  constructor
  · rintro ⟨Q, hQ⟩
    exact S.occurs_typeCoind B hp B' Q hQ
  · rintro ⟨j, hj⟩
    rw [conjType_mk] at hj
    have e := ((toClass_eq_iff _ _ _).mp hj.symm).some
    exact occurs_congr e ⟨S.projType B hp j, S.projType_ne_zero B hp j⟩

/-- In an irreducible representation containing a type of period `m + 1`, the occurring types
are exactly its conjugates. -/
theorem occurs_iff_of_occurs (A : WeilObj.{uF, uW} F) (B : WType.{uF, uW} F φ hφ)
    (hB : Occurs F φ hφ A.1.representation B) {m : ℕ}
    (hp : Function.minimalPeriod ((weilSplit F φ hφ).conjType 1)
      ((weilSplit F φ hφ).toClass B) = m + 1) (B' : WType.{uF, uW} F φ hφ) :
    Occurs F φ hφ A.1.representation B' ↔
      ∃ j : Fin (m + 1), (weilSplit F φ hφ).toClass B' =
        (weilSplit F φ hφ).conjType j ((weilSplit F φ hφ).toClass B) := by
  obtain ⟨P, hP⟩ := hB
  obtain ⟨u, ⟨e⟩⟩ :=
    (weilStage F φ hφ m).twist_equiv_typeCoind B hp A.1.representation A.2.2 P hP
  rw [← occurs_typeCoind_iff (weilStage F φ hφ m) B hp B', ← occurs_twist_iff u]
  exact ⟨occurs_of_equiv e, occurs_of_equiv e.symm⟩

/-- Two irreducible representations containing a common type of finite period differ by an
unramified twist. -/
theorem exists_twist_of_occurs (A A' : WeilObj.{uF, uW} F) (B : WType.{uF, uW} F φ hφ)
    (hB : Occurs F φ hφ A.1.representation B) (hB' : Occurs F φ hφ A'.1.representation B)
    {m : ℕ}
    (hp : Function.minimalPeriod ((weilSplit F φ hφ).conjType 1)
      ((weilSplit F φ hφ).toClass B) = m + 1) :
    ∃ z : ℂˣ, Nonempty (Representation.Equiv
      (Langlands.twist (unramifiedCharacter (localDegree F) z).toMonoidHom A'.1.representation)
      A.1.representation) := by
  obtain ⟨P, hP⟩ := hB
  obtain ⟨P', hP'⟩ := hB'
  obtain ⟨u, ⟨e⟩⟩ :=
    (weilStage F φ hφ m).twist_equiv_typeCoind B hp A.1.representation A.2.2 P hP
  obtain ⟨u', ⟨e'⟩⟩ :=
    (weilStage F φ hφ m).twist_equiv_typeCoind B hp A'.1.representation A'.2.2 P' hP'
  let E := (restrictEquiv (φ := φ) (hφ := hφ) e').trans (restrictEquiv (φ := φ) (hφ := hφ) e).symm
  have : Nontrivial A'.1 := nontrivial_of_isIrreducible _ A'.2.2
  exact twist_equiv_of_inertia_ne_zero (weilSplit F φ hφ) A'.1.representation A.1.representation
    A'.2.2 A.2.2 E.toIntertwiningMap (equiv_toIntertwiningMap_ne_zero E)

/-- Torsion number one forces an irreducible inertia restriction. -/
theorem inertia_irreducible_of_torsion_one {k : ℕ} (A : WeilObj.{uF, uW} F) (h : A.1.rank = k + 1)
    (ht : weilTorsionNumber F (weilClassOf F A h) = 1) :
    Representation.IsIrreducible
      (A.1.representation.comp (weilSplit F φ hφ).inertia.subtype) := by
  have : Nontrivial A.1 := nontrivial_of_isIrreducible _ A.2.2
  obtain ⟨B, ⟨P, hP⟩, hpos⟩ := exists_occurring_type (D := weilSplit F φ hφ) A.1.representation
    A.2.1 (Ramification.HerbrandBridge.continuousWeilFiniteInertiaImage F A.1 A.2.1)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  have hT := weilTorsionNumber_eq_period F φ hφ A h B P hP hm
  rw [ht] at hT
  have hm0 : m = 0 := by omega
  subst hm0
  obtain ⟨u, ⟨e⟩⟩ :=
    (weilStage F φ hφ 0).twist_equiv_typeCoind B hm A.1.representation A.2.2 P hP
  let e1 := restrictEquiv (φ := φ) (hφ := hφ) e
  let Q := (weilStage F φ hφ 0).projType B hm 0
  let e2 : Representation.Equiv
      (((weilStage F φ hφ 0).typeCoind B hm).comp (weilSplit F φ hφ).inertia.subtype)
      ((weilSplit F φ hφ).conjObj 0 B).1.representation :=
    Representation.Equiv.mk (LinearEquiv.funUnique (Fin 1) ℂ B.1) fun n => by
      have h1 := Q.isIntertwining' n
      exact h1
  rw [Weil.IsomorphismInvariance.irreducible_iff (e1.trans e2)]
  exact ((weilSplit F φ hφ).conjObj 0 B).2.2

end Langlands.Henniart.Numerical
