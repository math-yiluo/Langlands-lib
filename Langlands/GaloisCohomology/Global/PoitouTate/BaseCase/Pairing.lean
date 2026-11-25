import Langlands.GaloisCohomology.Global.PoitouTate.BaseCase.Reciprocity
import Langlands.GaloisCohomology.Global.Abelianization.ArtinFrobenius
import Langlands.GaloisCohomology.Global.PoitouTate.BaseCase.Main
import Langlands.Global.IdeleClosedSubgroupDensity
import Mathlib.Algebra.Module.CharacterModule

/-!
# The pairing of `H_c²(G_S, μ_n)` with the characters of `G_S`

For a number field `K`, a finite set `S` of finite places containing the places above `n` (`n` a
prime power, `n` odd or `K` totally complex), this file proves that the pairing

  `H_c²(G_S, μ_n) × H¹(G_S, ℤ/n) → ℤ/n`, `(y, χ) ↦ finiteTrace (y ∪ χ)`

has trivial kernels on both sides (`rootsOfUnityPairingStatement`), by comparing it with the
reciprocity isomorphism `continuousCharEquivSIdeleClass` between the characters of `G_S` and those
of the `S`-idèle class group `C_S`.

## Main statements

* `classPairing_eq_neg`: for a character `z` of `G_S` with values in `ℤ/n` (a `1`-cocycle) and a
  class `c ∈ C_S`, the pairing `classPairing z c` of the Kummer class with compact support of `c`
  with `z` is `-ψ_z(c)`, `ψ_z = continuousCharEquivSIdeleClass χ_z`, `χ_z = cocycleCharacter z`.
* `toAdd_continuousCharEquivSIdeleClass_sPresentation_mulSingle`: at a place `v ∈ S`, `ψ_z` takes at
  the class of the idèle `a ∈ K_vˣ` at `v` the value `-z(σ)`, `σ` an arithmetic Artin lift of `a`.
* `eq_zero_of_forall_finiteTrace_compactCupRes_eq_zero_left`,
  `eq_zero_of_forall_finiteTrace_compactCupRes_eq_zero_right`: the two kernels are trivial.
* `rootsOfUnityPairingStatement`: `RootsOfUnityPairingStatement`.

## Proofs

The Kummer classes with compact support of the data `(t, a)` exhaust `H_c²(G_S, μ_n)`
(`surjective_kummerCompactδ`, `unitsData_surjective`) and depend only on the `S`-idèle class of the
datum (`unitsData_eq_zero_of_unitsClass_eq_zero`); so the pairing with `z` is a homomorphism
`classPairing z : C_S → ℤ/n`. The sum `classPairing z + ψ_z`, read on the idèles, has a kernel that
contains the `n`-th powers and the units outside `S` positive at the real places (so it is open,
`isOpen_of_pow_mem_of_positiveUnitIdelesOutside_le`, hence closed), the principal idèles, and the
local groups at the places `v ∉ S`: at the uniformizer of `v`, the pairing is the cup symbol
`inv_v (δχ_v ∪ π_v)` (`finiteTrace_kummerCompactδ_unitsData` for a datum `(t, 1)` with
`div(t) = -v`), which is `χ_z(σ)` for an arithmetic Artin lift `σ` of `π_v`
(`Local.invariant_characterClass_cup`), and `ψ_z` takes the value `χ_z(σ)⁻¹` there
(`continuousCharEquivSIdeleClass_sPresentation_one_single_of_isArithmeticArtinLift`). By the
density of the principal idèles with the local groups outside `S`
(`Langlands.Global.IdeleDensity.eq_top_of_isClosed`) the kernel is everything.

For the kernels: a character `z` with `classPairing z = 0` has `ψ_z = 1`, so `χ_z = 1` and the
class of `z` is zero (`eq_zero_of_cocycleCharacter_eq_one`). A class `y = δ_c(e(d))` pairing
trivially with all characters has `f(cls d) = 1` for every homomorphism `f : C_S → ℤ/n`
(`continuousCharEquivSIdeleClass` is onto and every continuous character comes from a cocycle,
`cocycleOfCharacter`), so `cls d` is an `n`-th power (`exists_eq_pow_of_forall_monoidHom_eq_one`, by
the characters of `C_S / C_S^n` with values in `ℚ/ℤ`), and `y` is `n` times a class of
`H_c²(G_S, μ_n)`, which is killed by `n`.

## References

See the page beside this file.
-/

noncomputable section

namespace Langlands.GaloisCohomology.PoitouTate.Internal

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain

universe u

section Character

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ}

/-- The continuous character `G → ℤ/n` of a `1`-cocycle with values in `ℤ/n`. -/
def cocycleCharacter (z : cocycles (zmodRep.{u} G n) 1) :
    ContinuousMonoidHom G (Multiplicative (ZMod n)) where
  toFun g := Multiplicative.ofAdd (zmodCocycleHom z g)
  map_one' := by rw [zmodCocycleHom_one, ofAdd_zero]
  map_mul' g h := by rw [zmodCocycleHom_mul, ofAdd_add]
  continuous_toFun := ((isLocallyConstant_zmodCocycleHom z).comp Multiplicative.ofAdd).continuous

theorem cocycleCharacter_apply (z : cocycles (zmodRep.{u} G n) 1) (g : G) :
    cocycleCharacter z g = Multiplicative.ofAdd (zmodCocycleHom z g) :=
  rfl

/-- The `1`-cocycle of a continuous character `G → ℤ/n`. -/
def cocycleOfCharacter (χ : ContinuousMonoidHom G (Multiplicative (ZMod n))) :
    cocycles (zmodRep.{u} G n) 1 :=
  cocyclesOneOfHom (zmodRep.{u} G n) (fun g a => (rfl : (zmodRep.{u} G n).ρ g a = a))
    (fun g => (ULift.up (χ g).toAdd : zmodRep.{u} G n))
    ((IsLocallyConstant.of_discrete fun c : Multiplicative (ZMod n) =>
      (ULift.up c.toAdd : zmodRep.{u} G n)).comp_continuous χ.continuous)
    (fun g h => by rw [map_mul, toAdd_mul]; rfl)

theorem cocycleCharacter_cocycleOfCharacter (χ : ContinuousMonoidHom G (Multiplicative (ZMod n))) :
    cocycleCharacter (cocycleOfCharacter χ) = χ := by
  ext g
  have h := cochainOf_cocyclesOneOfHom (zmodRep.{u} G n)
    (fun g a => (rfl : (zmodRep.{u} G n).ρ g a = a))
    (fun g => (ULift.up (χ g).toAdd : zmodRep.{u} G n))
    ((IsLocallyConstant.of_discrete fun c : Multiplicative (ZMod n) =>
      (ULift.up c.toAdd : zmodRep.{u} G n)).comp_continuous χ.continuous)
    (fun g h => by rw [map_mul, toAdd_mul]; rfl) ![g]
  exact congrArg (fun a : zmodRep.{u} G n => Multiplicative.ofAdd a.down) h

/-- A cocycle with trivial character is zero. -/
theorem eq_zero_of_cocycleCharacter_eq_one (z : cocycles (zmodRep.{u} G n) 1)
    (h : cocycleCharacter z = 1) : z = 0 := by
  apply cocycles_ext
  funext v
  have hv : v = ![v 0] := by
    funext i
    fin_cases i
    rfl
  rw [map_zero, cochainOf_zero, Pi.zero_apply, hv]
  apply ULift.ext
  have e := congrArg Multiplicative.toAdd (DFunLike.congr_fun h (v 0))
  exact e

end Character

section Idele

open Langlands.Global

variable {K : Type u} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}

/-- A subgroup of the idèles containing `positiveUnitIdelesOutside S` and the uniformizer
`localUniformizer v` at a place `v ∉ S` contains the whole local group at `v`. -/
theorem finiteIdeleInclusion_mem_of_localUniformizer_mem {H : Subgroup (Ideles K)}
    (hU : positiveUnitIdelesOutside S ≤ H) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S)
    (hπ : finiteIdeleInclusion K v (localUniformizer v) ∈ H) (a : (FiniteCompletion K v)ˣ) :
    finiteIdeleInclusion K v a ∈ H := by
  have ha0 : Valued.v (a : FiniteCompletion K v) ≠ 0 := (_root_.map_ne_zero _).2 a.ne_zero
  set k := -WithZero.log (Valued.v (a : FiniteCompletion K v)) with hk
  have hak : Valued.v (a : FiniteCompletion K v) = WithZero.exp (-k) := by
    rw [hk, neg_neg, WithZero.exp_log ha0]
  set u := (localUniformizer v ^ k)⁻¹ * a with hu
  have hu1 : Valued.v (u : FiniteCompletion K v) = 1 := by
    rw [hu, Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀,
      valued_localUniformizer_zpow, hak, inv_mul_cancel₀ WithZero.exp_ne_zero]
  have hau : a = localUniformizer v ^ k * u := by rw [hu, mul_inv_cancel_left]
  rw [hau, map_mul, map_zpow]
  exact H.mul_mem (H.zpow_mem hπ k)
    (hU (finiteIdeleInclusion_mem_positiveUnitIdelesOutside hv
      ((mem_units_iff_valued_eq_one u).2 hu1)))

end Idele

section Dual

/-- In a commutative group, an element on which every homomorphism to `ℤ/n` is trivial is an
`n`-th power. -/
theorem exists_eq_pow_of_forall_monoidHom_eq_one {C : Type*} [CommGroup C] {n : ℕ} [NeZero n]
    (c : C) (h : ∀ f : C →* Multiplicative (ZMod n), f c = 1) : ∃ c' : C, c = c' ^ n := by
  classical
  by_contra hne'
  have hne : ∀ c' : C, c ≠ c' ^ n := fun c' hc' => hne' ⟨c', hc'⟩
  set N := (powMonoidHom n : C →* C).range with hN
  have ha : (Additive.ofMul (QuotientGroup.mk c : C ⧸ N) : Additive (C ⧸ N)) ≠ 0 := by
    intro h0
    obtain ⟨c', hc'⟩ := (QuotientGroup.eq_one_iff c).1 h0
    exact hne c' hc'.symm
  obtain ⟨φ, hφ⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero ha
  have hφn : ∀ x : Additive (C ⧸ N),
      n • (QZ.toAddCircle.symm.toAddMonoidHom.comp φ) x = 0 := by
    intro x
    rw [← map_nsmul]
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    have hx : n • x = 0 := by
      rw [← ofMul_toMul x, ← hy, ← ofMul_pow, ← QuotientGroup.mk_pow,
        (QuotientGroup.eq_one_iff (y ^ n)).2 (MonoidHom.mem_range.2 ⟨y, rfl⟩), ofMul_one]
    rw [hx, map_zero]
  set ψ : Additive (C ⧸ N) →+ ZMod n := zmodOfQZ _ hφn
  have h1 := h ((AddMonoidHom.toMultiplicativeRight ψ).comp (QuotientGroup.mk' N))
  have h2 : ψ (Additive.ofMul (QuotientGroup.mk c : C ⧸ N)) = 0 :=
    Multiplicative.ofAdd.injective (h1.trans ofAdd_zero.symm)
  have h3 := zmodToQZ_zmodOfQZ _ hφn (Additive.ofMul (QuotientGroup.mk c : C ⧸ N))
  rw [h2, map_zero] at h3
  exact hφ ((AddEquiv.map_eq_zero_iff QZ.toAddCircle.symm).1 h3.symm)

end Dual

section Pairing

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (ι : PlaceEmbeddings K Ω) (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] {n : ℕ} [NeZero n]
  (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((n : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
  (hK : Odd n ∨ IsTotallyComplex K)

/-- The pairing of the data with a character `z`: the trace of the cup product of the Kummer class
with compact support of a datum with `z`. -/
def unitsPairing (z : cocycles (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) 1) :
    UnitsDatum Ω S →+ ZMod n where
  toFun d := finiteTrace ι S n hK (compactCupRes (localFamily ι S)
    (zmodMulPairingRight n (dualizingModule K Ω S n) (nsmul_dualizingModule S n))
    (show 2 + 1 = 3 from rfl) ((kummerCompactδ ι n hS).hom (unitsData S ι d)) (cohomologyπ _ 1 z))
  map_zero' := by rw [map_zero, map_zero, map_zero, LinearMap.zero_apply, map_zero]
  map_add' d d' := by rw [map_add, map_add, map_add, LinearMap.add_apply, map_add]

theorem unitsPairing_apply (z : cocycles (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) 1)
    (d : UnitsDatum Ω S) :
    unitsPairing ι S hS hK z d = finiteTrace ι S n hK (compactCupRes (localFamily ι S)
      (zmodMulPairingRight n (dualizingModule K Ω S n) (nsmul_dualizingModule S n))
      (show 2 + 1 = 3 from rfl) ((kummerCompactδ ι n hS).hom (unitsData S ι d))
      (cohomologyπ _ 1 z)) :=
  rfl

theorem unitsPairing_eq_zero_of_unitsClass_eq_zero
    (z : cocycles (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) 1) (d : UnitsDatum Ω S)
    (h : unitsClass Ω S d = 0) : unitsPairing ι S hS hK z d = 0 := by
  rw [unitsPairing_apply, unitsData_eq_zero_of_unitsClass_eq_zero S ι d h, map_zero, map_zero,
    LinearMap.zero_apply, map_zero]

/-- The pairing of the `S`-idèle classes with a character `z`: the pairing of any datum with the
given class (`classPairing_unitsClass`). -/
def classPairing (z : cocycles (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) 1) :
    Additive (SIdeleClassGroup S) →+ ZMod n where
  toFun c := unitsPairing ι S hS hK z (Function.surjInv (unitsClass_surjective Ω S) c)
  map_zero' := unitsPairing_eq_zero_of_unitsClass_eq_zero ι S hS hK z _
    (Function.surjInv_eq (unitsClass_surjective Ω S) 0)
  map_add' c c' := by
    have h := unitsPairing_eq_zero_of_unitsClass_eq_zero ι S hS hK z
      (Function.surjInv (unitsClass_surjective Ω S) (c + c') -
        (Function.surjInv (unitsClass_surjective Ω S) c +
          Function.surjInv (unitsClass_surjective Ω S) c')) (by
      rw [map_sub, map_add, Function.surjInv_eq (unitsClass_surjective Ω S),
        Function.surjInv_eq (unitsClass_surjective Ω S),
        Function.surjInv_eq (unitsClass_surjective Ω S)]
      exact sub_self (c + c'))
    rw [map_sub, sub_eq_zero, map_add] at h
    exact h

theorem classPairing_unitsClass
    (z : cocycles (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) 1)
    (d : UnitsDatum Ω S) :
    classPairing ι S hS hK z (unitsClass Ω S d) = unitsPairing ι S hS hK z d := by
  have h := unitsPairing_eq_zero_of_unitsClass_eq_zero ι S hS hK z
    (Function.surjInv (unitsClass_surjective Ω S) (unitsClass Ω S d) - d) (by
      rw [map_sub, Function.surjInv_eq (unitsClass_surjective Ω S)]
      exact sub_self (unitsClass Ω S d))
  rw [map_sub, sub_eq_zero] at h
  exact h

omit [Finite S] [NeZero n] in
/-- The cup symbol of the unit `1` is zero. -/
theorem cupSymbol_one (z : cocycles (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) 1)
    (v : HeightOneSpectrum (𝓞 K)) : cupSymbol ι S z v 1 = 0 := by
  have h := Local.characterCup_mul_right (v.adicCompletion K)
    (AlgebraicClosure (v.adicCompletion K))
    (localCharacter ι S z v) (isOpen_ker_localCharacter ι S z v) 1 1
  rw [mul_one, left_eq_add] at h
  rw [cupSymbol, h, map_zero]

omit [Finite S] [NeZero n] in
/-- **The cup symbol is the value of the local character at an Artin lift.** -/
theorem cupSymbol_eq_of_isArithmeticArtinLift
    (z : cocycles (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) 1)
    (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ)
    (σ : Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K))
    (hσ : letI := Langlands.Global.FiniteCompletion.valuativeRel v
      letI := Langlands.Global.FiniteCompletion.isNonarchimedeanLocalField v
      ClassFieldTheory.Local.Artin.IsArithmeticArtinLift (v.adicCompletion K)
        (AlgebraicClosure (v.adicCompletion K)) a σ) :
    cupSymbol ι S z v a =
      QZ.toRationalModIntegers (zmodToQZ n (zmodCocycleHom z (localizationHom ι S v σ))) := by
  let _ := Langlands.Global.FiniteCompletion.valuativeRel v
  have := Langlands.Global.FiniteCompletion.isNonarchimedeanLocalField v
  exact Local.invariant_characterClass_cup (v.adicCompletion K)
    (AlgebraicClosure (v.adicCompletion K))
    _ _ a σ hσ

/-- The pairing of a datum `(t, 1)` with `div(t) = -v`, `v ∉ S`, is the value of `z` at the
localization of an Artin lift of `localUniformizer v`. -/
theorem unitsPairing_of_divAbove_eq_neg_single (hn : IsPrimePow n)
    (z : cocycles (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) 1)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) (t : Additive (sInvariantSubgroup Ω S))
    (ht : divAbove S t = -Finsupp.single ⟨v, hv⟩ 1)
    (σ : Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K))
    (hσ : letI := Langlands.Global.FiniteCompletion.valuativeRel v
      letI := Langlands.Global.FiniteCompletion.isNonarchimedeanLocalField v
      ClassFieldTheory.Local.Artin.IsArithmeticArtinLift (v.adicCompletion K)
        (AlgebraicClosure (v.adicCompletion K)) (localUniformizer v) σ) :
    unitsPairing ι S hS hK z (t, 0) = zmodCocycleHom z (localizationHom ι S v σ) := by
  apply zmodToQZ_injective (n := n)
  apply QZ.toRationalModIntegers.injective
  refine (finiteTrace_kummerCompactδ_unitsData ι S hn hS hK (t, 0) z).trans ?_
  simp only [Pi.zero_apply, toMul_zero, cupSymbol_one, Finset.sum_const_zero, zero_sub, ht]
  rw [← Finsupp.single_neg, Finsupp.sum_single_index (by rw [zero_smul]), neg_smul, one_smul,
    neg_neg]
  exact cupSymbol_eq_of_isArithmeticArtinLift ι S z v _ σ hσ

/-- **The pairing is minus the character of class field theory.** For a character `z` of `G_S`, the
pairing `classPairing z` of the `S`-idèle classes with `z` is minus the character
`continuousCharEquivSIdeleClass χ_z` of the `S`-idèle class group. -/
theorem classPairing_eq_neg (hn : IsPrimePow n)
    (z : cocycles (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) 1)
    (c : Additive (SIdeleClassGroup S)) :
    classPairing ι S hS hK z c = -(continuousCharEquivSIdeleClass Ω (Set.toFinite S) hK
      (cocycleCharacter z) (Additive.toMul c)).toAdd := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have : IsGalois K Ω := IsSepClosure.isGalois
  set ψ := continuousCharEquivSIdeleClass Ω (Set.toFinite S) hK (cocycleCharacter z) with hψ
  set T : Additive (SIdeleClassGroup S) →+ ZMod n :=
    classPairing ι S hS hK z + MonoidHom.toAdditiveLeft ψ with hT
  have hgen : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S), T (Additive.ofMul
      (sPresentation S (1, Multiplicative.ofAdd (Finsupp.single ⟨v, hv⟩ 1)))) = 0 := by
    intro v hv
    obtain ⟨t, ht⟩ := divAbove_surjective (Ω := Ω) S (-Finsupp.single ⟨v, hv⟩ 1)
    obtain ⟨σ, hσ⟩ : ∃ σ : Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K),
        letI := Langlands.Global.FiniteCompletion.valuativeRel v
        letI := Langlands.Global.FiniteCompletion.isNonarchimedeanLocalField v
        ClassFieldTheory.Local.Artin.IsArithmeticArtinLift (v.adicCompletion K)
          (AlgebraicClosure (v.adicCompletion K)) (localUniformizer v) σ := by
      let _ := Langlands.Global.FiniteCompletion.valuativeRel v
      have := Langlands.Global.FiniteCompletion.isNonarchimedeanLocalField v
      exact ClassFieldTheory.Local.Artin.exists_isArithmeticArtinLift _ _ _
    have hcls : unitsClass Ω S (t, 0) = Additive.ofMul
        (sPresentation S (1, Multiplicative.ofAdd (Finsupp.single ⟨v, hv⟩ 1))) := by
      rw [unitsClass_apply, ht, neg_neg]
      rfl
    rw [← hcls]
    change classPairing ι S hS hK z (unitsClass Ω S (t, 0)) +
      (ψ (Additive.toMul (unitsClass Ω S (t, 0)))).toAdd = 0
    rw [classPairing_unitsClass, unitsPairing_of_divAbove_eq_neg_single ι S hS hK hn z hv t ht σ hσ,
      hcls, toMul_ofMul, hψ,
      continuousCharEquivSIdeleClass_sPresentation_one_single_of_isArithmeticArtinLift ι S hK _ hv σ
        hσ, cocycleCharacter_apply, toAdd_inv, toAdd_ofAdd, add_neg_cancel]
  set Θ : Langlands.Global.Ideles K →* Multiplicative (ZMod n) :=
    (AddMonoidHom.toMultiplicativeRight T).comp (SIdeleClassGroup.mk S) with hΘ
  have hU : positiveUnitIdelesOutside S ≤ Θ.ker := fun x hx => by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, SIdeleClassGroup.mk_eq_one_of_mem
      (positiveUnitIdelesOutside_le_unitIdelesOutside S hx), map_one]
  have hker : Θ.ker = ⊤ := by
    refine Langlands.Global.IdeleDensity.eq_top_of_isClosed Θ.ker (Set.toFinite S).toFinset ?_ ?_ ?_
    · exact Subgroup.isClosed_of_isOpen _ (isOpen_of_pow_mem_of_positiveUnitIdelesOutside_le
        (Set.toFinite S) (NeZero.ne n) Θ.ker (fun x => by
          rw [MonoidHom.mem_ker, map_pow]
          exact zmod_pow_eq_one _) hU)
    · intro a
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, SIdeleClassGroup.mk_diagonalUnits, map_one]
    · intro v hv a
      have hv' : v ∉ S := fun h => hv ((Set.toFinite S).mem_toFinset.2 h)
      refine finiteIdeleInclusion_mem_of_localUniformizer_mem hU hv' ?_ a
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← zpow_one (localUniformizer v),
        ← sPresentation_one_single S ⟨v, hv'⟩ 1]
      change Multiplicative.ofAdd (T (Additive.ofMul _)) = 1
      rw [hgen v hv', ofAdd_zero]
  have hTc : T c = 0 := by
    obtain ⟨x, hx⟩ := SIdeleClassGroup.mk_surjective S (Additive.toMul c)
    have h1 : Θ x = 1 := (MonoidHom.mem_ker).1 (hker ▸ Subgroup.mem_top x)
    rw [hΘ, MonoidHom.comp_apply, hx] at h1
    exact Multiplicative.ofAdd.injective (h1.trans ofAdd_zero.symm)
  exact eq_neg_of_add_eq_zero_left hTc

include hS in
open Classical in
/-- **The reciprocity character at the places of `S`.** For `v ∈ S`, `a ∈ K_vˣ` and an arithmetic
Artin lift `σ` of `a` (local class field theory), the character `ψ_z` of the `S`-idèle class group
attached to `z` takes at the class of the idèle `a` at `v` the value `-z(σ)`, `σ` read in `G_S`
through `localizationHom ι S v`: the character `continuousCharEquivSIdeleClass` is the geometric
normalization of reciprocity at every place. -/
theorem toAdd_continuousCharEquivSIdeleClass_sPresentation_mulSingle (hn : IsPrimePow n)
    (z : cocycles (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) 1) (v : S)
    (a : (v.1.adicCompletion K)ˣ)
    (σ : Gal(AlgebraicClosure (v.1.adicCompletion K)/v.1.adicCompletion K))
    (hσ : letI := Langlands.Global.FiniteCompletion.valuativeRel v.1
      letI := Langlands.Global.FiniteCompletion.isNonarchimedeanLocalField v.1
      ClassFieldTheory.Local.Artin.IsArithmeticArtinLift (v.1.adicCompletion K)
        (AlgebraicClosure (v.1.adicCompletion K)) a σ) :
    (continuousCharEquivSIdeleClass Ω (Set.toFinite S) hK (cocycleCharacter z)
        (sPresentation S (Pi.mulSingle v a, 1))).toAdd =
      -zmodCocycleHom z (localizationHom ι S v.1 σ) := by
  classical
  let _ : Fintype S := Fintype.ofFinite S
  set d : UnitsDatum Ω S := (0, Pi.single v (Additive.ofMul a)) with hd
  have hcls : unitsClass Ω S d = Additive.ofMul (sPresentation S (Pi.mulSingle v a, 1)) := by
    rw [unitsClass_apply, hd, map_zero, neg_zero, ofAdd_zero]
    dsimp only
    congr 3
  have hpair : unitsPairing ι S hS hK z d = zmodCocycleHom z (localizationHom ι S v.1 σ) := by
    apply zmodToQZ_injective (n := n)
    apply QZ.toRationalModIntegers.injective
    refine (finiteTrace_kummerCompactδ_unitsData ι S hn hS hK d z).trans ?_
    rw [hd, map_zero, Finsupp.sum_zero_index, sub_zero]
    dsimp only
    rw [Finset.sum_eq_single v (fun w _ hw => by
        rw [Pi.single_eq_of_ne hw, toMul_zero, cupSymbol_one])
      (fun h => absurd (Finset.mem_univ v) h),
      Pi.single_eq_same, toMul_ofMul]
    exact cupSymbol_eq_of_isArithmeticArtinLift ι S z v.1 a σ hσ
  have h := classPairing_eq_neg ι S hS hK hn z (unitsClass Ω S d)
  rw [classPairing_unitsClass, hpair, hcls, toMul_ofMul] at h
  rw [h, neg_neg]

include hS in
/-- **Trivial left kernel.** A character of `G_S` with values in `ℤ/n` pairing trivially with
`H_c²(G_S, μ_n)` is zero. -/
theorem eq_zero_of_forall_finiteTrace_compactCupRes_eq_zero_left (hn : IsPrimePow n)
    (x : cohomology (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) 1)
    (hx : ∀ y : compactSupportCohomologyRes (localFamily ι S) (dualizingModule K Ω S n) 2,
      finiteTrace ι S n hK (compactCupRes (localFamily ι S)
        (zmodMulPairingRight n (dualizingModule K Ω S n) (nsmul_dualizingModule S n))
        (show 2 + 1 = 3 from rfl) y x) = 0) : x = 0 := by
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective _ 1 x
  have hψ : continuousCharEquivSIdeleClass Ω (Set.toFinite S) hK (cocycleCharacter z) = 1 := by
    refine MonoidHom.ext fun c => ?_
    obtain ⟨d, hd⟩ := unitsClass_surjective Ω S (Additive.ofMul c)
    have h1 := classPairing_eq_neg ι S hS hK hn z (unitsClass Ω S d)
    rw [classPairing_unitsClass, unitsPairing_apply, hx, hd, toMul_ofMul, eq_comm,
      neg_eq_zero] at h1
    exact Multiplicative.toAdd.injective h1
  have hχ : cocycleCharacter z = 1 :=
    (continuousCharEquivSIdeleClass Ω (Set.toFinite S) hK).injective (hψ.trans (map_one _).symm)
  rw [eq_zero_of_cocycleCharacter_eq_one z hχ, map_zero]

include hS in
/-- **Trivial right kernel.** A class of `H_c²(G_S, μ_n)` pairing trivially with all characters of
`G_S` with values in `ℤ/n` is zero. -/
theorem eq_zero_of_forall_finiteTrace_compactCupRes_eq_zero_right (hn : IsPrimePow n)
    (y : compactSupportCohomologyRes (localFamily ι S) (dualizingModule K Ω S n) 2)
    (hy : ∀ x : cohomology (zmodRep.{u} (GaloisGroupUnramifiedOutside K Ω S) n) 1,
      finiteTrace ι S n hK (compactCupRes (localFamily ι S)
        (zmodMulPairingRight n (dualizingModule K Ω S n) (nsmul_dualizingModule S n))
        (show 2 + 1 = 3 from rfl) y x) = 0) : y = 0 := by
  obtain ⟨e, rfl⟩ := surjective_kummerCompactδ ι hn hS hK y
  obtain ⟨d, rfl⟩ := unitsData_surjective S ι e
  have hf : ∀ f : SIdeleClassGroup S →* Multiplicative (ZMod n),
      f (Additive.toMul (unitsClass Ω S d)) = 1 := by
    intro f
    obtain ⟨χ, rfl⟩ := (continuousCharEquivSIdeleClass Ω (Set.toFinite S) hK).surjective f
    have h1 := classPairing_eq_neg ι S hS hK hn (cocycleOfCharacter χ) (unitsClass Ω S d)
    rw [classPairing_unitsClass, unitsPairing_apply, hy, eq_comm, neg_eq_zero,
      cocycleCharacter_cocycleOfCharacter] at h1
    exact Multiplicative.toAdd.injective h1
  obtain ⟨c', hc'⟩ := exists_eq_pow_of_forall_monoidHom_eq_one (C := SIdeleClassGroup S) _
    (fun f => hf f)
  obtain ⟨d', hd'⟩ := unitsClass_surjective Ω S (Additive.ofMul c')
  have h0 : unitsClass Ω S (d - n • d') = 0 := by
    rw [map_sub, map_nsmul, hd']
    have e : unitsClass Ω S d = n • Additive.ofMul c' := by
      rw [← ofMul_pow, ← hc', ofMul_toMul]
    rw [e]
    exact sub_self (n • Additive.ofMul c')
  have h := unitsData_eq_zero_of_unitsClass_eq_zero S ι _ h0
  rw [map_sub, map_nsmul, sub_eq_zero] at h
  rw [h, map_nsmul]
  exact nsmul_compactSupportCohomologyRes_eq_zero (localFamily ι S) (nsmul_dualizingModule S n) 2 _

end Pairing

end Langlands.GaloisCohomology.PoitouTate.Internal

namespace Langlands.GaloisCohomology.PoitouTate

open NumberField IsDedekindDomain Internal

universe u

/-- **The pairing `H_c²(G_S, μ_n) × H¹(G_S, ℤ/n) → ℤ/n` is perfect.** -/
theorem rootsOfUnityPairingStatement : RootsOfUnityPairingStatement.{u} := by
  intro K _ _ Ω _ _ _ S _ ι n _ hn hS hK _
  exact ⟨fun x hx => eq_zero_of_forall_finiteTrace_compactCupRes_eq_zero_left ι S hS hK hn x hx,
    fun y hy => eq_zero_of_forall_finiteTrace_compactCupRes_eq_zero_right ι S hS hK hn y hy⟩

end Langlands.GaloisCohomology.PoitouTate
