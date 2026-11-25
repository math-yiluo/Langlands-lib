import Langlands.Geometry.FormalGroup.SpecialResidueTangent
import Langlands.Geometry.FormalGroup.SubfieldResidueCyclicLift
import Langlands.Geometry.FormalGroup.DiagonalKernelEquations
import Langlands.Geometry.FormalGroup.RationalHeightIso
import Langlands.Geometry.FormalGroup.FieldRationalDegree

/-! # Heights of integral maps of special formal modules over fields -/

noncomputable section

set_option autoImplicit false

universe u v s

namespace Langlands.FormalGroup.LocalDivision

open ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {k : Type (max u v)} [Field k] [Algebra 𝒪[K] k] [Algebra 𝓀[K] k]
  [IsScalarTower 𝒪[K] 𝓀[K] k]

local notation "C" => SubfieldIntegerRing K D ι
local notation "kC" => IsLocalRing.ResidueField C
local notation "d" => CentralSimple.reducedDegree K D
set_option quotPrecheck false in
local notation "q" => Nat.card 𝓀[K]
local notation "m" => Nat.card kC - 1

private local instance : IsLocalHom (algebraMap 𝒪[K] C) := subfieldIntegerAlgebra_isLocalHom ι

section Coordinates

variable {σ : Type} [Finite σ] {M : ModuleLaw 𝒪[K] k σ}
  {E : ModuleLaw.OrderAction (IntegerRing K D) M}

local notation "TangentDecomposition" =>
  ModuleLaw.OrderAction.TangentCharacterDecomposition E
    (AlgHom.toRingHom (subfieldIntegerInclusion K D ι)) d (RingHom.id k)
variable (e : Fin (CentralSimple.reducedDegree K D) ≃
    (IsLocalRing.ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]] k))
  (r : ResidueCyclicLift (SubfieldIntegerRing K D ι))

private def weight (i : Fin d) : k := e i (IsLocalRing.residue C r.value)

omit [Algebra 𝒪[K] k] [IsScalarTower 𝒪[K] 𝓀[K] k] in
private theorem weight_order (i : Fin d) : orderOf (weight e r i) = m :=
  (orderOf_injective (e i).toMonoidHom (e i).injective _).trans r.residueOrder

omit [Algebra 𝒪[K] k] [IsScalarTower 𝒪[K] 𝓀[K] k] in
private theorem weight_pow (i : Fin d) : weight e r i ^ m = 1 := by
  rw [← weight_order e r i, pow_orderOf_eq_one]

private theorem residueOrder_pos (hL : IsUnramifiedSubfieldOfReducedDegree K D ι) : 0 < m := by
  let : Module.Finite 𝒪[K] C := hL.2.1
  let : Finite kC := IsLocalRing.ResidueField.finite_of_finite
    (R := 𝒪[K]) (S := C) inferInstance
  exact Nat.sub_pos_of_lt Finite.one_lt_card

omit [Algebra 𝒪[K] k] [IsScalarTower 𝒪[K] 𝓀[K] k] in
private theorem weight_ne_zero (hm : 0 < m) (i : Fin d) : weight e r i ≠ 0 := by
  intro hz
  have h := weight_pow e r i
  rw [hz, zero_pow hm.ne'] at h
  exact zero_ne_one h

omit [Algebra 𝒪[K] k] [IsScalarTower 𝒪[K] 𝓀[K] k] in
private theorem residueOrder_cast_ne_zero (hL : IsUnramifiedSubfieldOfReducedDegree K D ι)
    (j : kC →ₐ[𝓀[K]] k) : ((m : ℕ) : k) ≠ 0 := by
  let : Module.Finite 𝒪[K] C := hL.2.1
  let : Finite kC := IsLocalRing.ResidueField.finite_of_finite
    (R := 𝒪[K]) (S := C) inferInstance
  let : Fintype kC := Fintype.ofFinite _
  have hcard : 1 < Nat.card kC := Finite.one_lt_card
  have hq₀ : (Nat.card kC : kC) = 0 := by
    simpa only [Nat.card_eq_fintype_card] using FiniteField.cast_card_eq_zero kC
  have hm : ((m : ℕ) : kC) ≠ 0 := by
    rw [Nat.cast_sub hcard.le, hq₀, Nat.cast_one, zero_sub]
    exact neg_ne_zero.mpr one_ne_zero
  rw [← map_natCast j]
  exact fun h => hm (j.injective (h.trans (map_zero j).symm))

private def residueGeneratorAction (E : ModuleLaw.OrderAction (IntegerRing K D) M) : Hom M M :=
  E.action (subfieldIntegerInclusion K D ι r.value)

omit [Algebra 𝓀[K] k] [IsScalarTower 𝒪[K] 𝓀[K] k] in
private theorem residueGeneratorAction_pow (E : ModuleLaw.OrderAction (IntegerRing K D) M) :
    residueGeneratorAction r E ^ m = 1 := by
  rw [residueGeneratorAction, ← map_pow, ← map_pow, r.pow_eq_one, map_one, map_one]

private def tangentCoordinatesBy (t : TangentDecomposition)
    (hL : IsUnramifiedSubfieldOfReducedDegree K D ι) : (σ → k) ≃ₗ[k] (Fin d → k) :=
  t.coordinates.trans (LinearEquiv.piCongrLeft' k (fun _ : Fin d => k)
    (e.trans (tangentResidueCharacters t hL).symm).symm)

private theorem tangentCoordinatesBy_diagonalizes (t : TangentDecomposition)
    (hL : IsUnramifiedSubfieldOfReducedDegree K D ι) (x : σ → k) (i : Fin d) :
    tangentCoordinatesBy e t hL ((residueGeneratorAction r E).toHom.toCoordinateMap.linearPart x) i =
      weight e r i * tangentCoordinatesBy e t hL x i := by
  let j := (tangentResidueCharacters t hL).symm (e i)
  have h := t.diagonalizes r.value x j
  change t.coordinates (((residueGeneratorAction r E).toHom.toCoordinateMap.map
    (RingHom.id k)).linearPart x) j = t.characters j r.value * t.coordinates x j at h
  rw [CoordinateMap.map_ringHom_id, ← tangentResidueCharacters_residue t hL] at h
  have he : tangentResidueCharacters t hL j = e i := Equiv.apply_symm_apply _ _
  rw [he] at h
  exact h

/-- Actual formal coordinates in which the lifted residue generator is diagonal according to
one common ordering of the residue embeddings. -/
def specialCyclicCoordinateIso (t : TangentDecomposition)
    (hL : IsUnramifiedSubfieldOfReducedDegree K D ι) :=
  cyclicCoordinateIso (residueGeneratorAction r E) (tangentCoordinatesBy e t hL) (weight e r) m
    (residueOrder_cast_ne_zero hL (e ⟨0, CentralSimple.reducedDegree_pos K D⟩))
    (weight_ne_zero e r (residueOrder_pos hL)) (tangentCoordinatesBy_diagonalizes e r t hL)

private theorem specialCyclicCoordinateIso_conjugate (t : TangentDecomposition)
    (hL : IsUnramifiedSubfieldOfReducedDegree K D ι) :
    let a := specialCyclicCoordinateIso e r t hL
    (Hom.isoTransport a a (residueGeneratorAction r E)).toHom.toCoordinateMap =
      CoordinateMap.ofLinearMap (CoordinateMap.diagonalLinear (weight e r)) :=
  cyclicCoordinateIso_conjugate _ _ _ _ _ _ _ (residueOrder_pos hL).ne'
    (weight_pow e r) (residueGeneratorAction_pow r E)

end Coordinates

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra 𝓀[K] k] [IsScalarTower 𝒪[K] 𝓀[K] k] in
private theorem isoTransport_comp {σ τ υ σ' τ' υ' : Type}
    [Finite σ] [Finite τ] [Finite υ] [Finite σ'] [Finite τ'] [Finite υ']
    {M : ModuleLaw 𝒪[K] k σ} {N : ModuleLaw 𝒪[K] k τ} {P : ModuleLaw 𝒪[K] k υ}
    {M' : ModuleLaw 𝒪[K] k σ'} {N' : ModuleLaw 𝒪[K] k τ'} {P' : ModuleLaw 𝒪[K] k υ'}
    (a : Iso M M') (b : Iso N N') (c : Iso P P') (f : Hom M N) (g : Hom N P) :
    (Hom.isoTransport b c g).comp (Hom.isoTransport a b f) = Hom.isoTransport a c (g.comp f) := by
  simp only [Hom.isoTransport_apply, Hom.comp_assoc]
  rw [← Hom.comp_assoc b.inv b.hom, b.inv_hom, Hom.id_comp]

private theorem dvd_exponent_of_pow_modEq {q₀ d₀ h : ℕ} (hq : 1 < q₀) (hd : 0 < d₀)
    (hh : q₀ ^ h ≡ 1 [MOD q₀ ^ d₀ - 1]) : d₀ ∣ h := by
  have hpow (n : ℕ) : 1 ≤ q₀ ^ n := Nat.one_le_pow _ _ (by omega)
  have hq₁ : q₀ ^ d₀ ≡ 1 [MOD q₀ ^ d₀ - 1] :=
    ((Nat.modEq_iff_dvd' (hpow d₀)).mpr (dvd_refl _)).symm
  have hr : q₀ ^ h ≡ q₀ ^ (h % d₀) [MOD q₀ ^ d₀ - 1] := by
    calc
      q₀ ^ h = q₀ ^ (h % d₀) * (q₀ ^ d₀) ^ (h / d₀) := by
        rw [← pow_mul, ← pow_add, Nat.mod_add_div]
      _ ≡ q₀ ^ (h % d₀) [MOD q₀ ^ d₀ - 1] := by
        simpa only [one_pow, mul_one] using (Nat.ModEq.refl (q₀ ^ (h % d₀))).mul (hq₁.pow (h / d₀))
  have hdiv := (hr.symm.trans hh).symm.dvd'
  apply Nat.dvd_of_mod_eq_zero
  by_contra hn
  have hl : 1 < q₀ ^ (h % d₀) := one_lt_pow₀ hq hn
  have hu := Nat.pow_lt_pow_right hq (Nat.mod_lt h hd)
  have hle := Nat.le_of_dvd (Nat.sub_pos_of_lt hl) hdiv
  omega

namespace SpecialModule

variable [IsAlgClosed k] {X Y : SpecialModule K D ι k}

/-- An actual order-linear isogeny between special formal modules over a geometric
residue field has integral height divisible by the reduced division degree. -/
theorem dvd_integralHeight (f : ModuleLaw.OrderAction.Hom X.order Y.order) {h : ℕ}
    (hf : f.val.HasHeight q h) : d ∣ h := by
  let tX := (X.tangent k (RingHom.id k)).some
  let tY := (Y.tangent k (RingHom.id k)).some
  let e := tangentResidueCharacters tX X.unramified
  let r := subfieldResidueCyclicLift ι X.unramified
  let a := specialCyclicCoordinateIso e r tX X.unramified
  let b := specialCyclicCoordinateIso e r tY Y.unramified
  let A := Hom.isoTransport a a (residueGeneratorAction r X.order)
  let B := Hom.isoTransport b b (residueGeneratorAction r Y.order)
  let F := Hom.isoTransport a b f.val
  have hF : F.HasHeight q h := hf.isoTransport a b
  have hcomm : F.comp A = B.comp F := by
    dsimp only [F, A, B]
    rw [isoTransport_comp (K := K) a a b, isoTransport_comp (K := K) a b b]
    exact congrArg (Hom.isoTransport a b) (f.commutes (subfieldIntegerInclusion K D ι r.value))
  let : Fintype 𝓀[K] := Fintype.ofFinite _
  obtain ⟨p, hpκ, _, hp, _⟩ := FiniteField.card' 𝓀[K]
  let : CharP 𝓀[K] p := hpκ
  let : CharP k p := charP_of_injective_ringHom (algebraMap 𝓀[K] k).injective p
  let : ExpChar k p := ExpChar.prime hp
  have ha := specialCyclicCoordinateIso_conjugate e r tX X.unramified
  have hb := specialCyclicCoordinateIso_conjugate e r tY Y.unramified
  let P := Classical.choice hF.1.2
  have hh := RationalHeightRankCongruence.finrank_modEq_of_diagonal_formal_kernel (p := p)
    (weight e r) (residueOrder_cast_ne_zero X.unramified (e ⟨0, CentralSimple.reducedDegree_pos K D⟩))
    (weight_order e r) (weight_ne_zero e r (residueOrder_pos X.unramified)) hp.two_le F A B ha hb hcomm P
  change hF.1.fieldDegree ≡ 1 [MOD m] at hh
  rw [hF.1.fieldDegree_eq_of_rank hF.2, subfieldResidue_card ι X.unramified] at hh
  exact dvd_exponent_of_pow_modEq Finite.one_lt_card (CentralSimple.reducedDegree_pos K D) hh

end SpecialModule
end Langlands.FormalGroup.LocalDivision
