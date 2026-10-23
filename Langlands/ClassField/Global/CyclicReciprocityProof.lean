import Langlands.ClassField.Global.CyclicReciprocityParts
import Langlands.ClassField.Global.UnramifiedCyclotomicStatement

/-! # The reciprocity law for cyclic subextensions of cyclotomic extensions -/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Polynomial
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local

namespace Langlands.ClassField.Global

universe u

namespace CyclicReciprocity

open Reciprocity LocalSymbolIdentity UnramifiedCyclotomic FundamentalClass CompletionTower

section Residue

variable {F : Type*} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

/-- The residue field of a finite place has at least two elements. -/
theorem one_lt_card_residue : 1 < Nat.card (𝓞 F ⧸ v.asIdeal) := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  rcases Nat.lt_or_ge 1 (Ideal.absNorm v.asIdeal) with h | h
  · exact h
  · exfalso
    interval_cases hh : Ideal.absNorm v.asIdeal
    · exact v.ne_bot (Ideal.absNorm_eq_zero_iff.1 hh)
    · exact v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 hh)

/-- `q ^ n - 1` is a unit at `v` for `q = |𝓞 F / v|` and `n > 0`. -/
theorem natCast_card_pow_sub_one_not_mem {n : ℕ} (hn : 0 < n) :
    (((Nat.card (𝓞 F ⧸ v.asIdeal)) ^ n - 1 : ℕ) : 𝓞 F) ∉ v.asIdeal := by
  intro h
  have hq : ((Nat.card (𝓞 F ⧸ v.asIdeal) : ℕ) : 𝓞 F) ∈ v.asIdeal := by
    have := Ideal.absNorm_mem v.asIdeal
    rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at this
  have h1 : 1 ≤ Nat.card (𝓞 F ⧸ v.asIdeal) ^ n :=
    Nat.one_le_pow _ _ (by have := one_lt_card_residue v; omega)
  rw [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one] at h
  have h2 := v.asIdeal.sub_mem (v.asIdeal.pow_mem_of_mem hq n hn) h
  rw [sub_sub_cancel] at h2
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h2)

end Residue

/-- The order of `q` modulo `q ^ n - 1` is `n`. -/
theorem orderOf_natCast_pow_sub_one {q n : ℕ} (hq : 1 < q) (hn : 0 < n) :
    orderOf ((q : ℕ) : ZMod (q ^ n - 1)) = n := by
  rw [orderOf_eq_iff hn]
  constructor
  · rw [← Nat.cast_pow]
    have : q ^ n = (q ^ n - 1) + 1 := (Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))).symm
    rw [this, Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]
  · intro k hk hk0 h
    rw [← Nat.cast_pow] at h
    have h1 : q ^ k = (q ^ k - 1) + 1 := (Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))).symm
    rw [h1, Nat.cast_add, Nat.cast_one, add_eq_right, ZMod.natCast_eq_zero_iff] at h
    have h2 : q ^ k < q ^ n := Nat.pow_lt_pow_right hq hk
    have h3 : q ≤ q ^ k := Nat.le_self_pow (by omega) q
    have h4 := Nat.le_of_dvd (by omega) h
    omega

section LocalIdentity

variable {F E L : Type u} [Field F] [Field E] [Field L] [NumberField F] [NumberField E]
  [NumberField L] [Algebra F E] [Algebra E L] [Algebra F L] [IsScalarTower F E L]
  [IsGalois F E] [IsGalois F L]
  {M : ℕ} [NeZero M] {ζ : L} (hζ : IsPrimitiveRoot ζ M) (hinj : Function.Injective (hζ.autToPow F))
  (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]

/-- **The local identity at a finite place.** Given the unramified data at `v` for a modulus
`N ∣ M` prime to `v` with `n` the order of `q` modulo `N`, the local invariant at `w | v` of the
global carry class of `a` for a character `χ` of `Gal(E/F)` into `ℤ/n` is `χ(Art_v(a)|_E) / n`. -/
theorem finiteLocalInvariant_cyclicClass_of_modulus (hU : UnramifiedCyclotomicFrobenius.{u})
    (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
    (hI : (I (residuePrime v)).RelativeClassFormation ∧
      (I (residuePrime v)).ArithmeticNormalization)
    (N : ℕ) [NeZero N] (hN : N ∣ M) (hNv : ((N : ℕ) : 𝓞 F) ∉ v.asIdeal)
    {n : ℕ} [NeZero n] (hn : n = orderOf ((Nat.card (𝓞 F ⧸ v.asIdeal) : ℕ) : ZMod N))
    (χ : (E ≃ₐ[F] E) →* Multiplicative (ZMod n)) (a : Fˣ) :
    finiteLocalInvariant v w I (cyclicClass F E χ a) =
      zmodClass n (χ ((artinSymbol hζ hinj v
        (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)).restrictNormal E)).toAdd := by
  have hcomm : ∀ σ τ : L ≃ₐ[F] L, σ * τ = τ * σ := fun σ τ =>
    hinj (by rw [map_mul, map_mul, mul_comm])
  have hH : (rootStabilizer (F := F) (ζ := ζ) (M / N)).Normal := normal_of_comm hcomm _
  set u := (placeAbove L w).1
  have : u.asIdeal.LiesOver w.asIdeal := (placeAbove L w).2
  have : u.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.trans u.asIdeal w.asIdeal v.asIdeal
  obtain ⟨e, he, hen, χU, hχU, hfrob⟩ := hU F L M ζ hζ hinj v u N hN hNv hH
  obtain rfl : e = n := hen.trans hn.symm
  have := isGalois_adicCompletion v w
  have := FiniteExtension.local_finite v w
  have := isGalois_adicCompletion v u
  have := FiniteExtension.local_finite v u
  have := FiniteExtension.local_finite w u
  obtain ⟨⟨_, _, hInf, _⟩, _⟩ := id hI
  change (I (residuePrime v)).relative (padicField v) (w.adicCompletion E)
      ((unitsLocalMap v w 2).hom (cyclicClass F E χ a)) = _
  rw [unitsLocalMap_cyclicClass,
    ← hInf (padicField v) (w.adicCompletion E) (u.adicCompletion L),
    CyclicClassAlgebra.relativeInflation_cyclicClass]
  have hchar : (χ.comp (decompositionHom v w)).comp
      (AlgEquiv.restrictNormalHom (F := v.adicCompletion F) (K₁ := u.adicCompletion L)
        (w.adicCompletion E)) =
      (χ.comp (AlgEquiv.restrictNormalHom E)).comp (decompositionHom v u) := by
    ext σ
    exact congrArg (fun g => (χ g).toAdd) (decompositionHom_restrictNormal v w u σ).symm
  rw [hchar, relative_cyclicClass hcomm hζ hinj v u (I (residuePrime v)) hI
    (rootStabilizer (F := F) (ζ := ζ) (M / N)) χU hχU hfrob]
  rfl

end LocalIdentity

section CyclotomicIdentity

variable {F E L : Type u} [Field F] [Field E] [Field L] [NumberField F] [NumberField E]
  [NumberField L] [Algebra F E] [Algebra E L] [Algebra F L] [IsScalarTower F E L]
  [IsGalois F E] [IsGalois F L]
  {m : ℕ} [NeZero m] [IsCyclotomicExtension {m} F L] {ζ : L} (hζ : IsPrimitiveRoot ζ m)
  (hinj : Function.Injective (hζ.autToPow F))
  (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]

/-- **The local identity at every finite place.** For `E ⊆ L = F(μ_m)`, the local invariant at
`w | v` of the global carry class of `a` for a character `χ` of `Gal(E/F)` into `ℤ/n` is
`χ(Art_v(a)|_E) / n`. The proof enlarges `m` to `(q ^ n - 1) m` with `q = |𝓞_F / v|`. -/
theorem finiteLocalInvariant_cyclicClass (hU : UnramifiedCyclotomicFrobenius.{u})
    (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
    (hI : ∀ (p : ℕ) [Fact p.Prime],
      (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization)
    {n : ℕ} [NeZero n] (χ : (E ≃ₐ[F] E) →* Multiplicative (ZMod n)) (a : Fˣ) :
    finiteLocalInvariant v w I (cyclicClass F E χ a) =
      zmodClass n (χ ((artinSymbol hζ hinj v
        (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)).restrictNormal E)).toAdd := by
  set q := Nat.card (𝓞 F ⧸ v.asIdeal)
  have hq : 1 < q := one_lt_card_residue v
  have hn : 0 < n := NeZero.pos n
  set N := q ^ n - 1
  have : NeZero N := ⟨by have := Nat.le_self_pow hn.ne' q; omega⟩
  let L' := CyclotomicField (N * m) F
  have : IsGalois F L' := IsCyclotomicExtension.isGalois {N * m} F L'
  have hζ' : IsPrimitiveRoot (IsCyclotomicExtension.zeta (N * m) F L') (N * m) :=
    IsCyclotomicExtension.zeta_spec (N * m) F L'
  have hinj' : Function.Injective (hζ'.autToPow F) := hζ'.autToPow_injective F
  have hζm : IsPrimitiveRoot (IsCyclotomicExtension.zeta (N * m) F L' ^ N) m :=
    hζ'.pow (NeZero.pos _) rfl
  have hsplit : Splits ((X ^ m - 1 : F[X]).map (algebraMap F L')) := by
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one, ← C_1]
    exact X_pow_sub_one_splits hζm
  have := IsCyclotomicExtension.isSplittingField_X_pow_sub_one m F L
  let j : L →ₐ[F] L' := IsSplittingField.lift L (X ^ m - 1) hsplit
  let : Algebra L L' := j.toRingHom.toAlgebra
  have : IsScalarTower F L L' := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  let : Algebra E L' := ((algebraMap L L').comp (algebraMap E L)).toAlgebra
  have : IsScalarTower E L L' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower F E L' := IsScalarTower.of_algebraMap_eq fun x => by
    change _ = j (algebraMap E L (algebraMap F E x))
    rw [← IsScalarTower.algebraMap_apply, j.commutes]
  obtain ⟨i, -, hi⟩ := hζm.eq_pow_of_pow_eq_one (ξ := algebraMap L L' ζ)
    (by rw [← map_pow, hζ.pow_eq_one, map_one])
  have hζζ : algebraMap L L' ζ = IsCyclotomicExtension.zeta (N * m) F L' ^ (N * i) := by
    rw [← hi, pow_mul]
  rw [finiteLocalInvariant_cyclicClass_of_modulus hζ' hinj' v w hU I (hI _) N
    (dvd_mul_right N m) (natCast_card_pow_sub_one_not_mem v hn)
    (orderOf_natCast_pow_sub_one hq hn).symm χ a,
    ← artinSymbol_restrictNormal (dvd_mul_left m N) hζ hζ' hζζ hinj hinj' v]
  congr 3
  exact IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply E L _

end CyclotomicIdentity

section Sum

open Langlands.Global.CyclotomicSymbol

variable {F E L : Type u} [Field F] [Field E] [Field L] [NumberField F] [NumberField E]
  [NumberField L] [Algebra F E] [Algebra E L] [Algebra F L] [IsScalarTower F E L]
  [IsGalois F E] [IsGalois F L]
  {m : ℕ} [NeZero m] {ζ : L} (hζ : IsPrimitiveRoot ζ m)
  (hinj : Function.Injective (hζ.autToPow F))

/-- `-1` lies in the Galois image of `L / F` when `F` has a real place: a complex conjugation
acts on `ζ` as `ζ ↦ ζ⁻¹`. -/
theorem neg_one_mem_galoisImage (v : InfinitePlace F) (hv : v.IsReal) :
    (-1 : (ZMod m)ˣ) ∈ galoisImage F hζ := by
  obtain ⟨τ, ⟨ψ, hτ⟩, -⟩ := exists_isConj_restrict (F := F) (E := F) (L := L) v hv
  exact ⟨τ, autToPow_eq_neg_one hζ (apply_eq_inv_of_isConj hτ hζ)⟩

/-- A character `χ` of `Gal(E/F)` read on the Galois image `galoisImage F hζ ≅ Gal(L/F)` and
measured in `ℚ/ℤ`: `s ↦ χ(σ_s|_E) / n` for the automorphism `σ_s` acting on `ζ` by `s`. -/
def imageCharacter {n : ℕ} [NeZero n] (χ : (E ≃ₐ[F] E) →* Multiplicative (ZMod n)) :
    Additive (galoisImage F hζ) →+ RationalModIntegers :=
  (zmodClass n).comp (MonoidHom.toAdditiveLeft
    ((χ.comp (AlgEquiv.restrictNormalHom E)).comp (MonoidHom.ofInjective hinj).symm.toMonoidHom))

omit [NumberField F] [NumberField E] [NumberField L] [IsGalois F L] in
theorem imageCharacter_apply {n : ℕ} [NeZero n] (χ : (E ≃ₐ[F] E) →* Multiplicative (ZMod n))
    (s : galoisImage F hζ) :
    imageCharacter hζ hinj χ (Additive.ofMul s) =
      zmodClass n (χ (((MonoidHom.ofInjective hinj).symm s).restrictNormal E)).toAdd :=
  rfl

open Classical in
/-- The sign element of `a` at an infinite place `v` of `F`: `-1` if `v` is real and `a` is
negative at `v`, and `1` otherwise. -/
def signElement (a : Fˣ) (v : InfinitePlace F) : galoisImage F hζ :=
  if h : v.IsReal ∧ (v.embedding (a : F)).re < 0 then ⟨-1, neg_one_mem_galoisImage hζ v h.1⟩
  else 1

open Classical in
theorem coe_signElement (a : Fˣ) (v : InfinitePlace F) :
    (signElement hζ a v : (ZMod m)ˣ) =
      if v.IsReal ∧ (v.embedding (a : F)).re < 0 then -1 else 1 := by
  unfold signElement
  split_ifs <;> rfl

/-- The archimedean invariant of a carry class at a place `w | v`, through the sign element. -/
theorem archimedeanInvariant_eq_imageCharacter {n : ℕ} [NeZero n]
    (χ : (E ≃ₐ[F] E) →* Multiplicative (ZMod n)) (hχ : Function.Injective χ) (a : Fˣ)
    (v : InfinitePlace F) (w : InfinitePlace E) [w.LiesOver v] :
    archimedeanInvariant w (cyclicClass F E χ a) =
      imageCharacter hζ hinj χ (Additive.ofMul (signElement hζ a v)) := by
  have hcomap := InfinitePlace.LiesOver.comap_eq w v
  by_cases hv : v.IsReal
  · obtain ⟨τ, ⟨ψ, hτ⟩, hc⟩ := exists_isConj_restrict (L := L) w (hcomap ▸ hv)
    have hτ1 : (MonoidHom.ofInjective hinj).symm ⟨-1, neg_one_mem_galoisImage hζ v hv⟩ = τ := by
      apply (MonoidHom.ofInjective hinj).injective
      rw [MulEquiv.apply_symm_apply]
      apply Subtype.ext
      exact (autToPow_eq_neg_one hζ (apply_eq_inv_of_isConj hτ hζ)).symm
    rw [archimedeanInvariant_cyclicClass_of_isConj χ hχ a w _ hc, re_embedding_algebraMap w v]
    unfold signElement
    split_ifs with h1 h2 h2
    · rw [imageCharacter_apply]
      exact congrArg (fun σ : L ≃ₐ[F] L => zmodClass n (χ (σ.restrictNormal E)).toAdd) hτ1.symm
    · exact absurd ⟨hv, h1⟩ h2
    · exact absurd h2.2 h1
    · rw [ofMul_one, map_zero]
  · rw [archimedeanInvariant_eq_zero_of_isComplex w
      (by rw [hcomap]; exact InfinitePlace.not_isReal_iff_isComplex.1 hv)]
    unfold signElement
    split_ifs with h1
    · exact absurd h1.1 hv
    · rw [ofMul_one, map_zero]

variable [IsCyclotomicExtension {m} F L]

/-- The finite local invariant of a carry class at a place `w | v`, through the cyclotomic norm
symbol of `a` at `v`. -/
theorem finiteLocalInvariant_eq_imageCharacter (hU : UnramifiedCyclotomicFrobenius.{u})
    (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
    (hI : ∀ (p : ℕ) [Fact p.Prime],
      (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization)
    {n : ℕ} [NeZero n] (χ : (E ≃ₐ[F] E) →* Multiplicative (ZMod n)) (a : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal] :
    finiteLocalInvariant v w I (cyclicClass F E χ a) =
      imageCharacter hζ hinj χ (Additive.ofMul ⟨_, normSymbolAt_mem_galoisImage m hζ
        (rationalPlace v) (placeAboveRational v)
        (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)⟩) := by
  rw [finiteLocalInvariant_cyclicClass hζ hinj v w hU I hI χ a]
  rfl

include hinj in
/-- **The reciprocity law for carry classes.** For `E ⊆ L = F(μ_m)` and an injective character
`χ : Gal(E/F) → ℤ/n`, the carry class of every `a ∈ Fˣ` satisfies the reciprocity law: the sum
of its local invariants is the image under `imageCharacter` of the product of the local norm
symbols and the signs of `a`, which is `1` by the product formula for `N_{F/ℚ}(a)`. -/
theorem sumOfInvariantsVanishes_cyclicClass (hU : UnramifiedCyclotomicFrobenius.{u})
    (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
    (hI : ∀ (p : ℕ) [Fact p.Prime],
      (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization)
    {n : ℕ} [NeZero n] (χ : (E ≃ₐ[F] E) →* Multiplicative (ZMod n)) (hχ : Function.Injective χ)
    (a : Fˣ) : SumOfInvariantsVanishes I (cyclicClass F E χ a) := by
  intro wf wi
  let s : HeightOneSpectrum (𝓞 F) → galoisImage F hζ := fun v =>
    ⟨_, normSymbolAt_mem_galoisImage m hζ (rationalPlace v) (placeAboveRational v)
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)⟩
  have hfin : ∀ v, (haveI := (wf v).2; finiteLocalInvariant v (wf v).1 I (cyclicClass F E χ a)) =
      imageCharacter hζ hinj χ (Additive.ofMul (s v)) := fun v => by
    have := (wf v).2
    exact finiteLocalInvariant_eq_imageCharacter hζ hinj hU I hI χ a v (wf v).1
  have harch : ∀ v, archimedeanInvariant (wi v).1 (cyclicClass F E χ a) =
      imageCharacter hζ hinj χ (Additive.ofMul (signElement hζ a v)) := fun v => by
    have := (wi v).2
    exact archimedeanInvariant_eq_imageCharacter hζ hinj χ hχ a v (wi v).1
  have hS := mulSupport_normSymbolAt_finite (F := F) m a
  have hsupp : (Function.support fun v => haveI := (wf v).2;
      finiteLocalInvariant v (wf v).1 I (cyclicClass F E χ a)) ⊆ hS.toFinset := by
    intro v hv
    rw [Set.Finite.coe_toFinset]
    intro h1
    apply hv
    have : s v = 1 := Subtype.ext h1
    exact (hfin v).trans (by rw [this, ofMul_one, map_zero])
  refine ⟨hS.subset (by simpa using hsupp), ?_⟩
  have hprod : (∏ v ∈ hS.toFinset, s v) * ∏ v, signElement hζ a v = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, SubmonoidClass.coe_finsetProd, SubmonoidClass.coe_finsetProd,
      OneMemClass.coe_one]
    have h1 : ∏ v ∈ hS.toFinset, ((s v : galoisImage F hζ) : (ZMod m)ˣ) =
        symbolProduct m (Units.map (Algebra.norm ℚ : F →* ℚ) a) := by
      rw [← finprod_normSymbolAt m a]
      exact (finprod_eq_prod_of_mulSupport_subset _ fun v hv => by
        rw [Set.Finite.coe_toFinset]; exact hv).symm
    have h2 : ∏ v, ((signElement hζ a v : galoisImage F hζ) : (ZMod m)ˣ) =
        signUnit m (Units.map (Algebra.norm ℚ : F →* ℚ) a) := by
      rw [signUnit_norm]
      exact Finset.prod_congr rfl fun v _ => coe_signElement hζ a v
    rw [h1, h2, mul_comm, product_formula]
  have key : (∑ v ∈ hS.toFinset, imageCharacter hζ hinj χ (Additive.ofMul (s v))) +
      ∑ v, imageCharacter hζ hinj χ (Additive.ofMul (signElement hζ a v)) =
      imageCharacter hζ hinj χ
        (Additive.ofMul ((∏ v ∈ hS.toFinset, s v) * ∏ v, signElement hζ a v)) := by
    rw [ofMul_mul, ofMul_prod, ofMul_prod, map_add, map_sum, map_sum]
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  simp only [hfin, harch]
  rw [key, hprod, ofMul_one, map_zero]

end Sum

/-- **Reciprocity for cyclic subextensions of cyclotomic extensions**, given the unramified
cyclotomic Frobenius data: every class of `H²(Gal(E/F), Eˣ)` is a carry class `cyclicClass χ a`
for a coordinate `χ : Gal(E/F) ≅ ℤ/n`, and `E` embeds into `L = F(μ_m)`. -/
theorem cyclicCyclotomicReciprocity_of (hU : UnramifiedCyclotomicFrobenius.{u}) :
    CyclicCyclotomicReciprocity.{u} := by
  rintro I hI F _ _ E _ _ _ _ hcyc ⟨m, hm, ⟨ι⟩⟩ x
  have : NeZero m := ⟨hm.ne'⟩
  let L := CyclotomicField m F
  have : IsGalois F L := IsCyclotomicExtension.isGalois {m} F L
  let : Algebra E L := ι.toRingHom.toAlgebra
  have : IsScalarTower F E L := IsScalarTower.of_algebraMap_eq fun y => (ι.commutes y).symm
  have hζ := IsCyclotomicExtension.zeta_spec m F L
  have hinj := hζ.autToPow_injective F
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : NeZero (Nat.card (E ≃ₐ[F] E)) := ⟨Nat.card_pos.ne'⟩
  let χ := (zmodCyclicMulEquiv hcyc).symm
  obtain ⟨a, rfl⟩ := CyclicClassAlgebra.exists_cyclicClass_eq χ x
  exact sumOfInvariantsVanishes_cyclicClass hζ hinj hU I hI χ.toMonoidHom χ.injective a

end CyclicReciprocity

end Langlands.ClassField.Global
