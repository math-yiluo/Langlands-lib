import Langlands.GaloisCohomology.Global.Abelianization.SIdeleClassGroup
import Langlands.GaloisCohomology.Global.Units.Divisor

/-!
# A presentation of the `S`-idèle class group

For a number field `K` and a finite set `S` of finite places, every class of the `S`-idèle class
group `SIdeleClassGroup S = I_K / K^× U^S` is represented by an idèle with arbitrary components at
the places of `S`, a power of a fixed uniformizer at the other finite places, and `1` at the
archimedean places. This gives a surjective homomorphism

`sPresentation S : (∏_{w ∈ S} K_wˣ) × Div_S → SIdeleClassGroup S`

from the local groups at `S` and the group `SDivisor S` of divisors prime to `S` (of the module
`Langlands.GaloisCohomology.Global.Units.Divisor`) (`sPresentation_surjective`), whose kernel is
the image of `Kˣ` under `x ↦ ((x)_{w ∈ S}, div_S(x))` (`principalPresentation`,
`ker_sPresentation`).
So `SIdeleClassGroup S` is the quotient of `(∏_{w ∈ S} K_wˣ) × Div_S` by `Kˣ`; the image of
`∏_{w ∈ S} K_wˣ` has quotient the `S`-class group.

The uniformizers are the images `localUniformizer v` of fixed elements `globalUniformizer v` of
`K` of valuation `exp (-1)` at `v`; the order of an idèle at a finite place is `ideleOrd`.

## References

Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Chapter VIII, §3, p. 454 (the
`S`-idèle class group) and Proposition (8.3.5), p. 455 (the sequence
`0 → C_{K,S} → C_S(K) → Cl_S(K) → 0`, whose proof computes the cokernel of the local groups at
`S` as the divisors prime to `S` modulo principal divisors).
-/

noncomputable section

universe u

namespace Langlands.GaloisCohomology

open Langlands.Global IsDedekindDomain
open scoped NumberField

variable {K : Type u} [Field K] [NumberField K]

section Uniformizer

/-- The valuation of the image of an element of `K` in `K_v` is its valuation at `v`. -/
private theorem valued_algebraMap (v : FinitePlace K) (x : K) :
    Valued.v (algebraMap K (FiniteCompletion K v) x) = v.valuation K x := by
  simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
    Algebra.algebraMap_self, RingHom.id_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

/-- An element of `K` of valuation `exp (-1)` at the finite place `v` (a choice). -/
def globalUniformizer (v : FinitePlace K) : Kˣ :=
  Units.mk0 (v.valuation_exists_uniformizer K).choose fun h => by
    have h' := (v.valuation_exists_uniformizer K).choose_spec
    rw [h, map_zero] at h'
    exact WithZero.exp_ne_zero h'.symm

/-- `globalUniformizer v` has valuation `exp (-1)` at `v`. -/
theorem valuation_globalUniformizer (v : FinitePlace K) :
    v.valuation K (globalUniformizer v : K) = WithZero.exp (-1 : ℤ) :=
  (v.valuation_exists_uniformizer K).choose_spec

/-- `globalUniformizer v` has order `1` at `v`. -/
theorem ordAt_globalUniformizer (v : FinitePlace K) : ordAt v (globalUniformizer v) = 1 := by
  have h := valuation_eq_exp_neg_ordAt v (globalUniformizer v)
  rw [valuation_globalUniformizer, WithZero.exp_inj] at h
  omega

/-- The image of `globalUniformizer v` in `K_v`: a uniformizer of `K_v`. -/
def localUniformizer (v : FinitePlace K) : (FiniteCompletion K v)ˣ :=
  Units.map (algebraMap K (FiniteCompletion K v) : K →* FiniteCompletion K v) (globalUniformizer v)

/-- `localUniformizer v` is a uniformizer of `K_v`. -/
theorem valued_localUniformizer (v : FinitePlace K) :
    Valued.v (localUniformizer v : FiniteCompletion K v) = WithZero.exp (-1 : ℤ) := by
  change Valued.v (algebraMap K (FiniteCompletion K v) (globalUniformizer v : K)) = _
  rw [valued_algebraMap, valuation_globalUniformizer]

/-- The valuation of a power of `localUniformizer v`. -/
theorem valued_localUniformizer_zpow (v : FinitePlace K) (k : ℤ) :
    Valued.v ((localUniformizer v ^ k : (FiniteCompletion K v)ˣ) : FiniteCompletion K v) =
      WithZero.exp (-k) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, valued_localUniformizer, ← WithZero.exp_zsmul,
    smul_neg, zsmul_one, Int.cast_id]

end Uniformizer

section Order

/-- The order of an idèle at a finite place: minus the logarithm of the valuation of its
component. -/
def ideleOrd (v : FinitePlace K) (x : Ideles K) : ℤ :=
  -WithZero.log (Valued.v (finiteIdeleProjection K v x : FiniteCompletion K v))

/-- The valuation of a component of an idèle in terms of `ideleOrd`. -/
theorem valued_finiteIdeleProjection (v : FinitePlace K) (x : Ideles K) :
    Valued.v (finiteIdeleProjection K v x : FiniteCompletion K v) =
      WithZero.exp (-ideleOrd v x) := by
  rw [ideleOrd, neg_neg, WithZero.exp_log]
  simp

/-- An idèle has order `0` at all but finitely many finite places. -/
theorem finite_setOf_ideleOrd_ne_zero (x : Ideles K) :
    {v : FinitePlace K | ideleOrd v x ≠ 0}.Finite := by
  have h := (NumberField.AdeleRing.isUnit_iff.1 x.isUnit).2.2
  refine (Filter.eventually_cofinite.1 h).subset fun v hv => ?_
  intro h1
  apply hv
  change -WithZero.log (Valued.v ((x : Adeles K).2 v)) = 0
  rw [h1, WithZero.log_one, neg_zero]

/-- The order of a principal idèle is the order of the element. -/
theorem ideleOrd_diagonalUnits (v : FinitePlace K) (a : Kˣ) :
    ideleOrd v (diagonalUnits K a) = ordAt v a := by
  have h := valued_finiteIdeleProjection v (diagonalUnits K a)
  change Valued.v (algebraMap K (FiniteCompletion K v) (a : K)) = _ at h
  rw [valued_algebraMap, valuation_eq_exp_neg_ordAt, WithZero.exp_inj, neg_inj] at h
  exact h.symm

end Order

section Presentation

variable (S : Set (HeightOneSpectrum (𝓞 K)))

open Classical in
/-- The coefficient at a finite place `v` of a divisor prime to `S`, extended by `0` on `S`. -/
def sDivisorExponent (D : SDivisor S) (v : FinitePlace K) : ℤ :=
  if h : v ∈ S then 0 else D ⟨v, h⟩

variable {S}

omit [NumberField K] in
/-- The coefficient at a place outside `S`. -/
theorem sDivisorExponent_of_notMem (D : SDivisor S) {v : FinitePlace K} (h : v ∉ S) :
    sDivisorExponent S D v = D ⟨v, h⟩ :=
  dite_eq_right h

omit [NumberField K] in
/-- The coefficient at a place of `S` is `0`. -/
theorem sDivisorExponent_of_mem (D : SDivisor S) {v : FinitePlace K} (h : v ∈ S) :
    sDivisorExponent S D v = 0 :=
  dite_eq_left h

omit [NumberField K] in
/-- `sDivisorExponent` is additive. -/
theorem sDivisorExponent_add (D₁ D₂ : SDivisor S) (v : FinitePlace K) :
    sDivisorExponent S (D₁ + D₂) v = sDivisorExponent S D₁ v + sDivisorExponent S D₂ v := by
  by_cases h : v ∈ S
  · simp [sDivisorExponent_of_mem _ h]
  · simp [sDivisorExponent_of_notMem _ h]

variable (S)

/-- The idèle of a divisor `D` prime to `S`: the power `localUniformizer v ^ D v` at each finite
place `v ∉ S`, and `1` at the places of `S` and at the archimedean places. -/
def sDivisorIdele : SDivisor S →+ Additive (Ideles K) :=
  Finsupp.liftAddHom fun v =>
    zmultiplesHom _ (Additive.ofMul (finiteIdeleInclusion K v.1 (localUniformizer v.1)))

/-- The idèle of a multiple of one place. -/
theorem sDivisorIdele_single (v : {v : FinitePlace K // v ∉ S}) (k : ℤ) :
    (sDivisorIdele S (Finsupp.single v k)).toMul =
      finiteIdeleInclusion K v.1 (localUniformizer v.1) ^ k := by
  simp [sDivisorIdele]

/-- The finite components of the idèle of a divisor. -/
theorem finiteIdeleProjection_sDivisorIdele (D : SDivisor S) (v : FinitePlace K) :
    finiteIdeleProjection K v (sDivisorIdele S D).toMul =
      localUniformizer v ^ sDivisorExponent S D v := by
  classical
  induction D using Finsupp.induction_linear with
  | zero => simp [sDivisorExponent]
  | add D₁ D₂ h₁ h₂ => rw [map_add, toMul_add, map_mul, h₁, h₂, sDivisorExponent_add, zpow_add]
  | single w k =>
    rw [sDivisorIdele_single, map_zpow]
    by_cases h : v = w.1
    · subst h
      rw [finiteIdeleProjection_inclusion, sDivisorExponent_of_notMem _ w.2]
      simp
    · rw [finiteIdeleProjection_finiteIdeleInclusion_of_ne h, one_zpow]
      by_cases hS : v ∈ S
      · rw [sDivisorExponent_of_mem _ hS, zpow_zero]
      · rw [sDivisorExponent_of_notMem _ hS, Finsupp.single_apply, ite_eq_right, zpow_zero]
        intro e
        exact h (congrArg Subtype.val e).symm

/-- The idèle with prescribed components at the places of the finite set `S`, and `1` at the
other places. -/
def sPlacesIdele [Finite S] : (∀ w : S, (FiniteCompletion K w)ˣ) →* Ideles K :=
  letI := Fintype.ofFinite S
  { toFun := fun a => ∏ w : S, finiteIdeleInclusion K w.1 (a w)
    map_one' := by simp
    map_mul' := fun a b => by
      simp only [Pi.mul_apply, map_mul]
      exact Finset.prod_mul_distrib }

open Classical in
/-- The finite components of `sPlacesIdele S a`. -/
theorem finiteIdeleProjection_sPlacesIdele [Finite S] (a : ∀ w : S, (FiniteCompletion K w)ˣ)
    (v : FinitePlace K) :
    finiteIdeleProjection K v (sPlacesIdele S a) = if h : v ∈ S then a ⟨v, h⟩ else 1 := by
  let := Fintype.ofFinite S
  change finiteIdeleProjection K v (∏ w : S, finiteIdeleInclusion K w.1 (a w)) = _
  rw [map_prod]
  split_ifs with h
  · rw [Finset.prod_eq_single ⟨v, h⟩
      (fun w _ hw => finiteIdeleProjection_finiteIdeleInclusion_of_ne
        (fun e => hw (Subtype.ext e.symm)) _)
      (fun h' => absurd (Finset.mem_univ _) h'), finiteIdeleProjection_inclusion]
  · refine Finset.prod_eq_one fun w _ => finiteIdeleProjection_finiteIdeleInclusion_of_ne ?_ _
    intro e
    rw [e] at h
    exact h w.2

/-- A presentation of the `S`-idèle class group for finite `S`: a family of local units at the
places of `S` and a divisor `D` prime to `S` go to the class of the idèle with these components at
`S` and `localUniformizer v ^ D v` at `v ∉ S`. It is surjective (`sPresentation_surjective`) and
its kernel is the image of `Kˣ` under `principalPresentation` (`ker_sPresentation`). -/
def sPresentation [Finite S] :
    (∀ w : S, (FiniteCompletion K w)ˣ) × Multiplicative (SDivisor S) →* SIdeleClassGroup S :=
  (SIdeleClassGroup.mk S).comp
    ((sPlacesIdele S).coprod (AddMonoidHom.toMultiplicativeLeft (sDivisorIdele S)))

/-- The value of the presentation. -/
theorem sPresentation_apply [Finite S] (a : ∀ w : S, (FiniteCompletion K w)ˣ)
    (D : Multiplicative (SDivisor S)) :
    sPresentation S (a, D) =
      SIdeleClassGroup.mk S (sPlacesIdele S a * (sDivisorIdele S D.toAdd).toMul) :=
  rfl

/-- The presentation on the local groups at `S`. -/
theorem sPresentation_apply_one_right [Finite S] (a : ∀ w : S, (FiniteCompletion K w)ˣ) :
    sPresentation S (a, 1) = SIdeleClassGroup.mk S (sPlacesIdele S a) := by
  rw [sPresentation_apply, toAdd_one, map_zero, toMul_zero, mul_one]

/-- The presentation on a multiple of one place outside `S`. -/
theorem sPresentation_one_single [Finite S] (v : {v : FinitePlace K // v ∉ S}) (k : ℤ) :
    sPresentation S (1, Multiplicative.ofAdd (Finsupp.single v k)) =
      SIdeleClassGroup.mk S (finiteIdeleInclusion K v.1 (localUniformizer v.1 ^ k)) := by
  rw [sPresentation_apply, map_one, one_mul, toAdd_ofAdd, sDivisorIdele_single, map_zpow, map_zpow,
    map_zpow]

/-- A unit `x` of `K` goes to its components at the places of `S` and its divisor prime to `S`. -/
def principalPresentation :
    Kˣ →* (∀ w : S, (FiniteCompletion K w)ˣ) × Multiplicative (SDivisor S) :=
  (MonoidHom.pi fun w : S =>
      (finiteIdeleProjection K w.1 : Ideles K →* _).comp (diagonalUnits K)).prod
    (AddMonoidHom.toMultiplicativeRight (sDivisorOf S))

/-- The value of `principalPresentation S`. -/
theorem principalPresentation_apply (x : Kˣ) :
    principalPresentation S x =
      (fun w : S => finiteIdeleProjection K w.1 (diagonalUnits K x),
        Multiplicative.ofAdd (sDivisorOf S (Additive.ofMul x))) :=
  rfl

/-- The presentation is surjective. -/
theorem sPresentation_surjective [Finite S] : Function.Surjective (sPresentation S) := by
  intro c
  obtain ⟨x, rfl⟩ := SIdeleClassGroup.mk_surjective S c
  let D : SDivisor S := Finsupp.ofSupportFinite (fun v => ideleOrd v.1 x) (by
    refine ((finite_setOf_ideleOrd_ne_zero x).preimage Subtype.val_injective.injOn).subset ?_
    intro v hv
    exact hv)
  have hD : ∀ v : {v : FinitePlace K // v ∉ S}, D v = ideleOrd v.1 x := fun v => rfl
  refine ⟨(fun w => finiteIdeleProjection K w.1 x, Multiplicative.ofAdd D), ?_⟩
  rw [sPresentation_apply]
  apply (QuotientGroup.eq (s := sIdeleClassSubgroup S)).2
  refine Subgroup.mem_sup_right
    (mem_unitIdelesOutside_iff_valued.2 ⟨fun v hv => ?_, fun v hv => ?_⟩)
  · rw [map_mul, map_inv, map_mul, finiteIdeleProjection_sPlacesIdele, dite_eq_left hv, toAdd_ofAdd,
      finiteIdeleProjection_sDivisorIdele, sDivisorExponent_of_mem _ hv, zpow_zero, mul_one,
      inv_mul_cancel]
  · rw [map_mul, map_inv, map_mul, finiteIdeleProjection_sPlacesIdele, dite_eq_right hv,
      toAdd_ofAdd,
      finiteIdeleProjection_sDivisorIdele, sDivisorExponent_of_notMem _ hv, hD, one_mul,
      Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, valued_localUniformizer_zpow,
      valued_finiteIdeleProjection]
    exact inv_mul_cancel₀ WithZero.exp_ne_zero

/-- The kernel of the presentation is the image of `Kˣ`. -/
theorem ker_sPresentation [Finite S] :
    (sPresentation S).ker = (principalPresentation S).range := by
  ext ⟨a, D⟩
  rw [MonoidHom.mem_ker, sPresentation_apply, MonoidHom.mem_range]
  constructor
  · intro h
    have hmem := (QuotientGroup.eq_one_iff (N := sIdeleClassSubgroup S) _).1 h
    obtain ⟨_, ⟨x, rfl⟩, u, hu, hxu⟩ := Subgroup.mem_sup.1 hmem
    obtain ⟨hS, hout⟩ := mem_unitIdelesOutside_iff_valued.1 hu
    refine ⟨x, Prod.ext (funext fun w => ?_) ?_⟩
    · have e := congrArg (finiteIdeleProjection K w.1) hxu
      rw [map_mul, hS w.1 w.2, mul_one, map_mul, finiteIdeleProjection_sPlacesIdele,
        dite_eq_left w.2,
        finiteIdeleProjection_sDivisorIdele, sDivisorExponent_of_mem _ w.2, zpow_zero,
        mul_one] at e
      exact e
    · apply Multiplicative.toAdd.injective
      ext v
      have e := congrArg (fun y => Valued.v ((finiteIdeleProjection K v.1 y :
        (FiniteCompletion K v.1)ˣ) : FiniteCompletion K v.1)) hxu
      simp only [map_mul, Units.val_mul, finiteIdeleProjection_sPlacesIdele, dite_eq_right v.2,
        one_mul, finiteIdeleProjection_sDivisorIdele, sDivisorExponent_of_notMem _ v.2,
        valued_localUniformizer_zpow, valued_finiteIdeleProjection, ideleOrd_diagonalUnits] at e
      have hu0 : ideleOrd v.1 u = 0 := by
        have h1 := hout v.1 v.2
        rw [valued_finiteIdeleProjection, ← WithZero.exp_zero, WithZero.exp_inj] at h1
        omega
      rw [hu0, neg_zero, WithZero.exp_zero, mul_one, WithZero.exp_inj, neg_inj] at e
      change sDivisorOf S (Additive.ofMul x) v = D.toAdd v
      rw [sDivisorOf_apply, toMul_ofMul, e]
  · rintro ⟨x, hx⟩
    have h1 := congrArg Prod.fst hx
    have h2 := congrArg Prod.snd hx
    rw [principalPresentation_apply] at h1 h2
    subst h1
    subst h2
    apply (QuotientGroup.eq_one_iff (N := sIdeleClassSubgroup S) _).2
    have hu : (diagonalUnits K x)⁻¹ * (sPlacesIdele S (fun w => finiteIdeleProjection K w.1
        (diagonalUnits K x)) * (sDivisorIdele S (sDivisorOf S (Additive.ofMul x))).toMul) ∈
          unitIdelesOutside S := by
      refine mem_unitIdelesOutside_iff_valued.2 ⟨fun v hv => ?_, fun v hv => ?_⟩
      · rw [map_mul, map_mul, map_inv, finiteIdeleProjection_sPlacesIdele, dite_eq_left hv,
          finiteIdeleProjection_sDivisorIdele, sDivisorExponent_of_mem _ hv, zpow_zero, mul_one,
          inv_mul_cancel]
      · rw [map_mul, map_mul, map_inv, finiteIdeleProjection_sPlacesIdele, dite_eq_right hv,
          one_mul,
          finiteIdeleProjection_sDivisorIdele, sDivisorExponent_of_notMem _ hv, Units.val_mul,
          map_mul, Units.val_inv_eq_inv_val, map_inv₀, valued_finiteIdeleProjection,
          valued_localUniformizer_zpow, sDivisorOf_apply, toMul_ofMul, ideleOrd_diagonalUnits]
        exact inv_mul_cancel₀ WithZero.exp_ne_zero
    have : sPlacesIdele S (fun w => finiteIdeleProjection K w.1 (diagonalUnits K x)) *
        (sDivisorIdele S (sDivisorOf S (Additive.ofMul x))).toMul =
        diagonalUnits K x * ((diagonalUnits K x)⁻¹ * (sPlacesIdele S (fun w =>
          finiteIdeleProjection K w.1 (diagonalUnits K x)) *
            (sDivisorIdele S (sDivisorOf S (Additive.ofMul x))).toMul)) := by group
    rw [toAdd_ofAdd, this]
    exact Subgroup.mul_mem_sup ⟨x, rfl⟩ hu

end Presentation

end Langlands.GaloisCohomology
