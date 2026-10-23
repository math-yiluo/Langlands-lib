import Langlands.ClassField.Global.ReciprocityStatement
import Langlands.ClassField.Global.LocalSymbolIdentity

/-! # Parts of the cyclic cyclotomic reciprocity law: archimedean invariants of carry classes -/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField
open Langlands.ClassFieldTheory.Local

namespace Langlands.Global.CyclotomicSymbol

/-- Reduction of the cyclotomic symbol from modulus `m'` to a divisor `m`. -/
theorem localSymbol_cast {m m' : ℕ} [NeZero m] [NeZero m'] (h : m ∣ m') (p : ℕ) [Fact p.Prime]
    (x : ℚ_[p]ˣ) :
    Units.map (ZMod.castHom h (ZMod m)).toMonoidHom (localSymbol m' p x) = localSymbol m p x := by
  apply eq_of_reduction m
  intro q hq
  have hle : m.factorization q ≤ m'.factorization q :=
    (Nat.factorization_le_iff_dvd (NeZero.ne m) (NeZero.ne m')).2 h q
  have hpow : q ^ m.factorization q ∣ q ^ m'.factorization q := pow_dvd_pow q hle
  have hred : reduction m q (Units.map (ZMod.castHom h (ZMod m)).toMonoidHom (localSymbol m' p x)) =
      Units.map (ZMod.castHom hpow (ZMod (q ^ m.factorization q))).toMonoidHom
        (reduction m' q (localSymbol m' p x)) := by
    apply Units.ext
    change (ZMod.castHom (Nat.ordProj_dvd m q) _).comp (ZMod.castHom h (ZMod m)) _ =
      (ZMod.castHom hpow _).comp (ZMod.castHom (Nat.ordProj_dvd m' q) _) _
    rw [RingHom.ext_zmod ((ZMod.castHom (Nat.ordProj_dvd m q) _).comp (ZMod.castHom h (ZMod m)))
      ((ZMod.castHom hpow _).comp (ZMod.castHom (Nat.ordProj_dvd m' q) _))]
  rw [hred]
  by_cases hqp : q = p
  · subst hqp
    rw [reduction_localSymbol_self, reduction_localSymbol_self, map_inv]
    congr 1
    apply Units.ext
    change ZMod.castHom hpow _ (PadicInt.toZModPow _ _) = PadicInt.toZModPow _ _
    rw [ZMod.castHom_apply, PadicInt.cast_toZModPow _ _ hle]
  · rw [reduction_localSymbol_of_ne m' p hq hqp, reduction_localSymbol_of_ne m p hq hqp, map_zpow]
    congr 1
    apply Units.ext
    simp

end Langlands.Global.CyclotomicSymbol

namespace Langlands.Global.CyclotomicSymbol

open Langlands.Global.AdelicFunctoriality
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension

/-- The symbol of the local norm of a unit at a place not dividing `m` is trivial. -/
theorem normSymbolAt_eq_one_of_valued {K : Type*} [Field K] [NumberField K] (m : ℕ) [NeZero m]
    (p₀ : HeightOneSpectrum (𝓞 ℚ)) (w : HeightOneSpectrum (𝓞 K)) [w.asIdeal.LiesOver p₀.asIdeal]
    (hpm : ¬ ((Rat.HeightOneSpectrum.primesEquiv p₀ : ℕ) ∣ m)) (b : (w.adicCompletion K)ˣ)
    (hb : Valued.v (b : w.adicCompletion K) = 1) : normSymbolAt m p₀ w b = 1 := by
  rw [normSymbolAt_apply, localSymbol_of_not_dvd m _ hpm]
  set x := (Units.map ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv p₀).toRingEquiv.toMonoidHom.comp
    (FiniteExtension.localNorm p₀ w)) b)
  have hint : ∀ y : (w.adicCompletion K)ˣ, Valued.v (y : w.adicCompletion K) = 1 →
      ‖((Units.map ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv p₀).toRingEquiv.toMonoidHom.comp
        (FiniteExtension.localNorm p₀ w)) y : _ˣ) : ℚ_[(Rat.HeightOneSpectrum.primesEquiv p₀ : ℕ)])‖ ≤ 1 := by
    intro y hy
    have h1 : (y : w.adicCompletion K) ∈ w.adicCompletionIntegers K := by
      rw [mem_adicCompletionIntegers, hy]
    have h2 := FiniteExtension.localNorm_integral p₀ w h1
    exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn p₀).mapsTo h2
  have h1 := hint b hb
  have h2 := hint b⁻¹ (by rw [Units.val_inv_eq_inv_val, map_inv₀, hb, inv_one])
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at h2
  have hpos : 0 < ‖((x : _ˣ) : ℚ_[(Rat.HeightOneSpectrum.primesEquiv p₀ : ℕ)])‖ :=
    norm_pos_iff.2 x.ne_zero
  have hn1 : ‖((x : _ˣ) : ℚ_[(Rat.HeightOneSpectrum.primesEquiv p₀ : ℕ)])‖ = 1 := by
    have := (inv_le_one₀ hpos).1 h2
    linarith
  have hv : ((x : _ˣ) : ℚ_[(Rat.HeightOneSpectrum.primesEquiv p₀ : ℕ)]).valuation = 0 := by
    have h3 := Padic.norm_eq_zpow_neg_valuation x.ne_zero
    rw [hn1] at h3
    have hp1 : (1 : ℝ) < (Rat.HeightOneSpectrum.primesEquiv p₀ : ℕ) := by
      exact_mod_cast (Rat.HeightOneSpectrum.primesEquiv p₀).2.one_lt
    have h4 : ((Rat.HeightOneSpectrum.primesEquiv p₀ : ℕ) : ℝ) ^
        (-((x : _ˣ) : ℚ_[(Rat.HeightOneSpectrum.primesEquiv p₀ : ℕ)]).valuation) =
        ((Rat.HeightOneSpectrum.primesEquiv p₀ : ℕ) : ℝ) ^ (0 : ℤ) := by
      rw [← h3, zpow_zero]
    have h5 := (zpow_right_inj₀ (by positivity) hp1.ne').1 h4
    linarith
  change _ ^ ((x : _ˣ) : ℚ_[(Rat.HeightOneSpectrum.primesEquiv p₀ : ℕ)]).valuation = 1
  rw [hv, zpow_zero]

end Langlands.Global.CyclotomicSymbol

namespace Langlands.ClassField.Global

universe u

namespace CyclicReciprocity

open Reciprocity LocalSymbolIdentity

section Carry

/-- An element of order two in `ℤ/n` has carry `1` with itself and class `1/2`. -/
theorem carry_of_two_torsion {n : ℕ} [NeZero n] (x : ZMod n) (hx : x ≠ 0) (h2 : x + x = 0) :
    cyclicCarry x x = 1 ∧ 2 * x.val = n := by
  have hspec := cyclicCarry_spec x x
  rw [h2, ZMod.val_zero, add_zero] at hspec
  have hpos : 0 < x.val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero x).2 hx)
  have hlt := ZMod.val_lt x
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hc : cyclicCarry x x = 1 := by
    rcases Nat.lt_or_ge (cyclicCarry x x) 1 with h | h
    · have : cyclicCarry x x = 0 := by omega
      rw [this, mul_zero] at hspec
      omega
    · rcases Nat.lt_or_ge (cyclicCarry x x) 2 with h' | h'
      · omega
      · have : n * 2 ≤ n * cyclicCarry x x := Nat.mul_le_mul_left n h'
        omega
  refine ⟨hc, ?_⟩
  rw [hc, mul_one] at hspec
  omega

end Carry

section Archimedean

variable {F E : Type u} [Field F] [Field E] [Algebra F E] (w : InfinitePlace E)

theorem eq_of_isConj {c d : E ≃ₐ[F] E} (hc : ComplexEmbedding.IsConj w.embedding c)
    (hd : ComplexEmbedding.IsConj w.embedding d) : c = d := by
  apply AlgEquiv.ext
  intro x
  apply w.embedding.injective
  rw [hc.eq, hd.eq]

/-- The archimedean invariant of a carry class at a place `w` with a nontrivial stabilizer
element `c`: `χ(c) / n` if `a` is negative at `w`, and `0` otherwise. -/
theorem archimedeanInvariant_cyclicClass {n : ℕ} [NeZero n]
    (χ : (E ≃ₐ[F] E) →* Multiplicative (ZMod n)) (hχ : Function.Injective χ) (a : Fˣ)
    (c : E ≃ₐ[F] E) (hc : c ∈ MulAction.stabilizer (E ≃ₐ[F] E) w) (hc1 : c ≠ 1) :
    archimedeanInvariant w (cyclicClass F E χ a) =
      if (w.embedding (algebraMap F E a)).re < 0 then zmodClass n (χ c).toAdd else 0 := by
  classical
  have hex : ∃ c : E ≃ₐ[F] E, c ∈ MulAction.stabilizer (E ≃ₐ[F] E) w ∧ c ≠ 1 := ⟨c, hc, hc1⟩
  have hconj := isConj_of_mem_stabilizer w hc hc1
  have hchoose : hex.choose = c :=
    eq_of_isConj w (isConj_of_mem_stabilizer w hex.choose_spec.1 hex.choose_spec.2) hconj
  have hcc := conjugation_mul_self w hconj
  -- the coordinate of `c` has order two
  have hx0 : (χ c).toAdd ≠ 0 := by
    intro h
    apply hc1
    apply hχ
    rw [map_one, ← ofAdd_toAdd (χ c), h, ofAdd_zero]
  have hx2 : (χ c).toAdd + (χ c).toAdd = 0 := by
    rw [← toAdd_mul, ← map_mul, hcc, map_one, toAdd_one]
  obtain ⟨hcarry, hval⟩ := carry_of_two_torsion _ hx0 hx2
  -- evaluate the cocycle
  unfold archimedeanInvariant
  rw [cyclicClass, H2Lift_H2π]
  change (if h : ∃ c : E ≃ₐ[F] E, c ∈ MulAction.stabilizer (E ≃ₐ[F] E) w ∧ c ≠ 1 then
      signClass (w.embedding (conjugationValue h.choose (cyclicUnitCocycle F E χ a) : E))
    else 0) = _
  rw [dite_eq_left hex, hchoose]
  have hcv : (conjugationValue c (cyclicUnitCocycle F E χ a) : E) = algebraMap F E a := by
    unfold conjugationValue
    rw [CyclicClassAlgebra.cyclicUnitCocycle_apply, CyclicClassAlgebra.cyclicUnitCocycle_apply,
      hcarry, map_one, toAdd_one]
    have h00 : cyclicCarry (0 : ZMod n) 0 = 0 := by simp [cyclicCarry]
    rw [h00, one_nsmul, zero_nsmul, add_zero]
    rfl
  rw [hcv]
  unfold signClass
  split_ifs with h
  · rw [zmodClass_apply]
    congr 1
    have hn : (n : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne n
    field_simp
    exact_mod_cast hval.symm
  · rfl

/-- With trivial stabilizer, the archimedean invariant vanishes. -/
theorem archimedeanInvariant_eq_zero_of_stabilizer
    (h : ∀ c ∈ MulAction.stabilizer (E ≃ₐ[F] E) w, c = 1) (x : relativeCohomology F E 2) :
    archimedeanInvariant w x = 0 := by
  classical
  obtain ⟨y, rfl⟩ := H2π_surjective x
  unfold archimedeanInvariant
  rw [H2Lift_H2π]
  change (if h : ∃ c : E ≃ₐ[F] E, c ∈ MulAction.stabilizer (E ≃ₐ[F] E) w ∧ c ≠ 1 then
      signClass (w.embedding (conjugationValue h.choose y : E)) else 0) = 0
  rw [dite_eq_right fun ⟨c, hc, hc1⟩ => hc1 (h c hc)]

end Archimedean

section ArtinRestriction

open Langlands.Global.CyclotomicSymbol

variable {F L L' : Type u} [Field F] [Field L] [Field L'] [Algebra F L] [Algebra F L']
  [Algebra L L'] [IsScalarTower F L L'] [Normal F L]
  {m m' : ℕ} [NeZero m] [NeZero m'] (hmm : m ∣ m') {ζ : L} {ζ' : L'}
  (hζ : IsPrimitiveRoot ζ m) (hζ' : IsPrimitiveRoot ζ' m') {k : ℕ}
  (hζζ : algebraMap L L' ζ = ζ' ^ k)

include hζζ in
/-- `autToPow` is compatible with restriction to a cyclotomic subfield. -/
theorem autToPow_restrictNormal (σ : L' ≃ₐ[F] L') :
    hζ.autToPow F (σ.restrictNormal L) =
      Units.map (ZMod.castHom hmm (ZMod m)).toMonoidHom (hζ'.autToPow F σ) := by
  apply Units.ext
  set c' := ((hζ'.autToPow F σ : (ZMod m')ˣ) : ZMod m')
  set c := ((hζ.autToPow F (σ.restrictNormal L) : (ZMod m)ˣ) : ZMod m)
  have h1 : algebraMap L L' (ζ ^ c.val) = algebraMap L L' (ζ ^ c'.val) := by
    rw [hζ.autToPow_spec F (σ.restrictNormal L), AlgEquiv.restrictNormal_commutes, map_pow, hζζ,
      map_pow, ← hζ'.autToPow_spec F σ, ← pow_mul, ← pow_mul, mul_comm]
  have h2 : ζ ^ c.val = ζ ^ c'.val := (algebraMap L L').injective h1
  rw [← pow_mod_orderOf, ← pow_mod_orderOf (n := c'.val), ← hζ.eq_orderOf] at h2
  have h3 := hζ.pow_inj (Nat.mod_lt _ (NeZero.pos m)) (Nat.mod_lt _ (NeZero.pos m)) h2
  rw [Nat.mod_eq_of_lt (ZMod.val_lt c)] at h3
  change c = ZMod.castHom hmm (ZMod m) c'
  rw [← ZMod.natCast_zmod_val c, ← ZMod.natCast_zmod_val c', map_natCast, h3, ZMod.natCast_mod]

include hmm hζζ in
/-- The local Artin symbol is compatible with restriction to a cyclotomic subfield. -/
theorem artinSymbol_restrictNormal [NumberField F] [NumberField L] [NumberField L']
    [IsGalois F L] [IsGalois F L'] (hinj : Function.Injective (hζ.autToPow F))
    (hinj' : Function.Injective (hζ'.autToPow F)) (v : HeightOneSpectrum (𝓞 F))
    (b : (v.adicCompletion F)ˣ) :
    (artinSymbol hζ' hinj' v b).restrictNormal L = artinSymbol hζ hinj v b := by
  apply hinj
  rw [autToPow_restrictNormal hmm hζ hζ' hζζ, autToPow_artinSymbol, autToPow_artinSymbol,
    normSymbolAt_apply, normSymbolAt_apply, localSymbol_cast hmm]

end ArtinRestriction

section FiniteProduct

open Langlands.Global.CyclotomicSymbol Langlands.Global.AdelicFunctoriality
open Langlands.Global.CompletionPadic

variable {F : Type u} [Field F] [NumberField F]

/-- A finite place lying over a rational place has it as its rational place. -/
theorem rationalPlace_eq_of_liesOver (p₀ : HeightOneSpectrum (𝓞 ℚ)) (v : HeightOneSpectrum (𝓞 F))
    [v.asIdeal.LiesOver p₀.asIdeal] : rationalPlace v = p₀ :=
  HeightOneSpectrum.ext (Ideal.over_def v.asIdeal p₀.asIdeal).symm

/-- The symbol at a place does not depend on how its rational place is named. -/
theorem normSymbolAt_congr (m : ℕ) [NeZero m] {K : Type*} [Field K] [NumberField K]
    {p₀ p₁ : HeightOneSpectrum (𝓞 ℚ)} (h : p₀ = p₁) (w : HeightOneSpectrum (𝓞 K))
    [w.asIdeal.LiesOver p₀.asIdeal] [w.asIdeal.LiesOver p₁.asIdeal] :
    normSymbolAt m p₀ w = normSymbolAt m p₁ w := by
  subst h
  rfl

/-- Regrouping a finite product over the finite places of `F` by the rational places below. -/
theorem finprod_eq_finprod_placesAbove {G : Type*} [CommMonoid G]
    (g : HeightOneSpectrum (𝓞 F) → G) (hg : (Function.mulSupport g).Finite) :
    ∏ᶠ v, g v = ∏ᶠ p₀ : HeightOneSpectrum (𝓞 ℚ), ∏ w : FinitePlacesAbove F p₀, g w.1 := by
  classical
  set S := hg.toFinset
  set T := S.image rationalPlace
  have h1 : ∏ᶠ v, g v = ∏ v ∈ S, g v :=
    finprod_eq_prod_of_mulSupport_subset g (by simp [S])
  have hfib : ∀ p₀ : HeightOneSpectrum (𝓞 ℚ),
      ∏ w : FinitePlacesAbove F p₀, g w.1 = ∏ v ∈ S with rationalPlace v = p₀, g v := by
    intro p₀
    symm
    refine Finset.prod_bij_ne_one
      (fun v hv _ => (⟨v, ⟨(congrArg HeightOneSpectrum.asIdeal
        (Finset.mem_filter.1 hv).2).symm⟩⟩ : FinitePlacesAbove F p₀))
      (fun _ _ _ => Finset.mem_univ _) (fun _ _ _ _ _ _ h => congrArg Subtype.val h) ?_
      (fun _ _ _ => rfl)
    intro w _ hw
    refine ⟨w.1, Finset.mem_filter.2 ⟨?_, rationalPlace_eq_of_liesOver p₀ w.1⟩, hw, rfl⟩
    simpa [S] using hw
  have h2 : ∏ᶠ p₀ : HeightOneSpectrum (𝓞 ℚ), ∏ w : FinitePlacesAbove F p₀, g w.1 =
      ∏ p₀ ∈ T, ∏ w : FinitePlacesAbove F p₀, g w.1 := by
    apply finprod_eq_prod_of_mulSupport_subset
    intro p₀ hp
    rw [Function.mem_mulSupport, hfib] at hp
    obtain ⟨v, hv, -⟩ := Finset.exists_ne_one_of_prod_ne_one hp
    rw [Finset.mem_filter] at hv
    rw [Finset.mem_coe, Finset.mem_image]
    exact ⟨v, hv.1, hv.2⟩
  rw [h1, h2, Finset.prod_congr rfl fun p₀ _ => hfib p₀]
  exact (Finset.prod_fiberwise_of_maps_to (fun v hv => Finset.mem_image_of_mem _ hv) g).symm

/-- A rational prime dividing `M` makes `M` lie in every place above it. -/
theorem natCast_mem_of_dvd (v : HeightOneSpectrum (𝓞 F)) {M : ℕ} (h : residuePrime v ∣ M) :
    ((M : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  have h1 := (Rat.HeightOneSpectrum.natGenerator_dvd_iff (rationalPlace v)).1 h
  have h2 : ((M : ℕ) : 𝓞 ℚ) ∈ (rationalPlace v).asIdeal := by
    rw [Ideal.mem_map_of_equiv] at h1
    obtain ⟨x, hx, hxe⟩ := h1
    have : x = (M : 𝓞 ℚ) :=
      (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).injective (by rw [hxe, map_natCast])
    rwa [← this]
  rw [Ideal.over_def v.asIdeal (rationalPlace v).asIdeal, Ideal.mem_comap, map_natCast] at h2
  exact h2

variable (m : ℕ) [NeZero m]

/-- The symbol of a global unit is trivial at a place prime to `m` where it is a unit. -/
theorem normSymbolAt_algebraMap_eq_one (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ)
    (ha : v.valuation F (a : F) = 1) (hm : ((m : ℕ) : 𝓞 F) ∉ v.asIdeal) :
    normSymbolAt m (rationalPlace v) v (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a) =
      1 := by
  refine normSymbolAt_eq_one_of_valued m (rationalPlace v) v
    (fun h => hm (natCast_mem_of_dvd v h)) _ ?_
  exact (valuedAdicCompletion_eq_valuation' (v := v) (a : F)).trans ha

/-- The symbols of a global unit are trivial at almost all places. -/
theorem mulSupport_normSymbolAt_finite (a : Fˣ) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => normSymbolAt m (rationalPlace v) v
      (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)).Finite := by
  refine (((HeightOneSpectrum.Support.finite (𝓞 F) (a : F)).union
    (HeightOneSpectrum.Support.finite (𝓞 F) ((a : F)⁻¹))).union
    (HeightOneSpectrum.Support.finite (𝓞 F) (((m : ℕ) : F)⁻¹))).subset ?_
  intro v hv
  by_contra hS
  simp only [Set.mem_union, not_or, HeightOneSpectrum.Support, Set.mem_ofPred_eq, not_lt] at hS
  obtain ⟨⟨h1, h2⟩, h3⟩ := hS
  apply hv
  apply normSymbolAt_algebraMap_eq_one
  · rw [map_inv₀] at h2
    have h0 : (0 : WithZero (Multiplicative ℤ)) < v.valuation F (a : F) := by
      rw [zero_lt_iff, Valuation.ne_zero_iff]
      exact a.ne_zero
    exact le_antisymm h1 ((inv_le_one₀ h0).1 h2)
  · intro hmem
    have h4' := (valuation_lt_one_iff_mem (K := F) v ((m : ℕ) : 𝓞 F)).2 hmem
    have h4 : v.valuation F ((m : ℕ) : F) < 1 := by exact_mod_cast h4'
    rw [map_inv₀] at h3
    have h0 : (0 : WithZero (Multiplicative ℤ)) < v.valuation F ((m : ℕ) : F) := by
      rw [zero_lt_iff, Valuation.ne_zero_iff]
      exact_mod_cast NeZero.ne m
    exact absurd ((inv_le_one₀ h0).1 h3) (not_le.2 h4)

/-- **The finite product formula for local symbols.** The product over all finite places of `F`
of the local symbols of a global unit `a` is the product of the rational cyclotomic symbols of
`N_{F/ℚ}(a)` at all primes. -/
theorem finprod_normSymbolAt (a : Fˣ) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), normSymbolAt m (rationalPlace v) v
        (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a) =
      symbolProduct m (Units.map (Algebra.norm ℚ : F →* ℚ) a) := by
  rw [finprod_eq_finprod_placesAbove (F := F) _ (mulSupport_normSymbolAt_finite m a),
    symbolProduct_apply,
    ← finprod_comp_equiv (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ))]
  refine finprod_congr fun p₀ => ?_
  rw [show primeSymbol m (Rat.HeightOneSpectrum.primesEquiv p₀) =
    ratLocalSymbol m (Rat.HeightOneSpectrum.primesEquiv p₀) from rfl, ratLocalSymbol_norm_eq_prod]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [normSymbolAt_congr m (rationalPlace_eq_of_liesOver p₀ w.1) w.1]

end FiniteProduct

section Sign

open Langlands.Global.CyclotomicSymbol

variable (m : ℕ) [NeZero m]

/-- The sign symbol on nonzero real numbers, `x ↦ ±1 ∈ (ℤ/m)ˣ`. -/
def realSignUnit : ℝˣ →* (ZMod m)ˣ where
  toFun x := if (x : ℝ) < 0 then -1 else 1
  map_one' := by simp
  map_mul' a b := by
    have ha := a.ne_zero
    have hb := b.ne_zero
    rcases ha.lt_or_gt with ha' | ha' <;> rcases hb.lt_or_gt with hb' | hb'
    · simp [Units.val_mul, ha', hb', not_lt.2 (mul_pos_of_neg_of_neg ha' hb').le]
    · simp [Units.val_mul, ha', not_lt.2 hb'.le, mul_neg_of_neg_of_pos ha' hb']
    · simp [Units.val_mul, not_lt.2 ha'.le, hb', mul_neg_of_pos_of_neg ha' hb']
    · simp [Units.val_mul, not_lt.2 ha'.le, not_lt.2 hb'.le, not_lt.2 (mul_pos ha' hb').le]

omit [NeZero m] in
theorem realSignUnit_apply (x : ℝˣ) :
    realSignUnit m x = if (x : ℝ) < 0 then -1 else 1 := rfl

omit [NeZero m] in
theorem signUnit_eq_realSignUnit (α : ℚˣ) :
    signUnit m α = realSignUnit m (Units.map (Rat.castHom ℝ).toMonoidHom α) := by
  change (if (α : ℚ) < 0 then -1 else 1) = (if ((α : ℚ) : ℝ) < 0 then -1 else 1)
  simp only [Rat.cast_lt_zero]

variable {F : Type*} [Field F] [NumberField F]

open Classical in
/-- The real number attached to an element at an infinite place: its image under the real
embedding at a real place, the square of its absolute value at a complex place. -/
def placeFactor (w : InfinitePlace F) (x : F) : ℝ :=
  if w.IsReal then (w.embedding x).re else ‖w.embedding x‖ ^ 2

open Classical in
/-- The product of the complex embeddings defining an infinite place. -/
theorem prod_filter_mk_eq (w : InfinitePlace F) (x : F) :
    ∏ φ ∈ Finset.univ.filter (fun φ : F →+* ℂ => InfinitePlace.mk φ = w), φ x =
      (placeFactor w x : ℂ) := by
  classical
  have hfilter : Finset.univ.filter (fun φ : F →+* ℂ => InfinitePlace.mk φ = w) =
      {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
    ext φ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    conv_lhs => rw [← InfinitePlace.mk_embedding w, InfinitePlace.mk_eq_iff]
    refine or_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
    · rw [← h]
      exact (star_star φ).symm
    · rw [h]
      exact star_star _
  rw [hfilter]
  unfold placeFactor
  split_ifs with hw
  · have hc : ComplexEmbedding.conjugate w.embedding = w.embedding :=
      ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp hw)
    rw [hc, Finset.pair_eq_singleton, Finset.prod_singleton,
      ← InfinitePlace.embedding_of_isReal_apply hw, Complex.ofReal_re]
  · have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
      intro h
      exact hw (InfinitePlace.isReal_iff.mpr (ComplexEmbedding.isReal_iff.mpr h.symm))
    rw [Finset.prod_pair hne, ComplexEmbedding.conjugate_coe_eq, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]

/-- The norm to `ℚ` as the product of the place factors. -/
theorem algebraMap_norm_eq_prod (x : F) :
    ((Algebra.norm ℚ x : ℚ) : ℝ) = ∏ w : InfinitePlace F, placeFactor w x := by
  classical
  apply Complex.ofReal_injective
  rw [Complex.ofReal_prod, Complex.ofReal_ratCast]
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  rw [eq_ratCast] at h
  rw [h, ← Fintype.prod_equiv (RingHom.equivRatAlgHom F ℂ) (fun f => f x) (fun φ => φ x)
    fun _ => by simp [RingHom.equivRatAlgHom_apply],
    ← Finset.prod_fiberwise Finset.univ InfinitePlace.mk (fun φ => φ x)]
  exact Finset.prod_congr rfl fun w _ => prod_filter_mk_eq w x

theorem placeFactor_ne_zero (w : InfinitePlace F) {x : F} (hx : x ≠ 0) : placeFactor w x ≠ 0 := by
  have h := prod_filter_mk_eq w x
  intro h0
  rw [h0, Complex.ofReal_zero, Finset.prod_eq_zero_iff] at h
  obtain ⟨φ, -, hφ⟩ := h
  exact hx (φ.injective (by rw [hφ, map_zero]))

omit [NeZero m] in
open Classical in
/-- **The sign of a norm.** The sign symbol of `N_{F/ℚ}(a)` is the product over the real places
of `F` at which `a` is negative of `-1`. -/
theorem signUnit_norm (a : Fˣ) :
    signUnit m (Units.map (Algebra.norm ℚ : F →* ℚ) a) =
      ∏ w : InfinitePlace F, if w.IsReal ∧ (w.embedding (a : F)).re < 0 then -1 else 1 := by
  rw [signUnit_eq_realSignUnit]
  have hunit : Units.map (Rat.castHom ℝ).toMonoidHom (Units.map (Algebra.norm ℚ : F →* ℚ) a) =
      ∏ w : InfinitePlace F, Units.mk0 (placeFactor w a) (placeFactor_ne_zero w a.ne_zero) := by
    apply Units.ext
    rw [Units.coe_prod]
    simp only [Units.coe_map, Units.val_mk0]
    exact algebraMap_norm_eq_prod (a : F)
  rw [hunit, map_prod]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [realSignUnit_apply, Units.val_mk0]
  unfold placeFactor
  by_cases hw : w.IsReal
  · simp only [hw, ↓reduceIte, true_and]
  · simp only [hw, ↓reduceIte, false_and]
    rw [ite_eq_right_iff]
    intro h
    exact absurd h (not_lt.2 (sq_nonneg _))

end Sign

section Conjugation

/-- An automorphism acting as complex conjugation inverts roots of unity. -/
theorem apply_eq_inv_of_isConj {F L : Type*} [Field F] [Field L] [Algebra F L] {ψ : L →+* ℂ}
    {τ : L ≃ₐ[F] L} (hτ : ComplexEmbedding.IsConj ψ τ) {m : ℕ} [NeZero m] {ζ : L}
    (hζ : IsPrimitiveRoot ζ m) : τ ζ = ζ⁻¹ := by
  apply ψ.injective
  rw [hτ.eq, map_inv₀]
  have h1 : ‖ψ ζ‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hζ.pow_eq_one, map_one]) (NeZero.ne m)
  rw [Complex.inv_eq_conj h1, starRingEnd_apply]

/-- `autToPow` of an automorphism inverting `ζ` is `-1`. -/
theorem autToPow_eq_neg_one {F L : Type*} [Field F] [Field L] [Algebra F L] {m : ℕ} [NeZero m]
    {ζ : L} (hζ : IsPrimitiveRoot ζ m) {τ : L ≃ₐ[F] L} (h : τ ζ = ζ⁻¹) :
    hζ.autToPow F τ = -1 := by
  apply Units.ext
  have hspec := hζ.autToPow_spec F τ
  set c := ((hζ.autToPow F τ : (ZMod m)ˣ) : ZMod m)
  have h1 : ζ ^ (c.val + 1) = 1 := by
    rw [pow_succ, hspec, h, inv_mul_cancel₀ (hζ.ne_zero (NeZero.ne m))]
  have h3 := (ZMod.natCast_eq_zero_iff _ _).2 ((hζ.pow_eq_one_iff_dvd _).1 h1)
  push_cast at h3
  rw [ZMod.natCast_zmod_val] at h3
  rw [Units.val_neg, Units.val_one]
  linear_combination h3

variable {F E L : Type u} [Field F] [Field E] [Field L] [NumberField F] [NumberField E]
  [NumberField L] [Algebra F E] [Algebra E L] [Algebra F L] [IsScalarTower F E L] [IsGalois F L]
  [Normal F E]

omit [NumberField F] in
/-- Over a real place of `F`, a complex conjugation of `L / F` attached to an extension of the
embedding of a place `w` of `E` restricts to a conjugation at `w`. -/
theorem exists_isConj_restrict (w : InfinitePlace E) (hv : (w.comap (algebraMap F E)).IsReal) :
    ∃ τ : L ≃ₐ[F] L, (∃ ψ : L →+* ℂ, ComplexEmbedding.IsConj ψ τ) ∧
      ComplexEmbedding.IsConj w.embedding (τ.restrictNormal E) := by
  set ψ := ComplexEmbedding.lift L w.embedding
  have hψ : ψ.comp (algebraMap E L) = w.embedding :=
    ComplexEmbedding.lift_comp_algebraMap L w.embedding
  rw [← InfinitePlace.mk_embedding w, InfinitePlace.comap_mk, InfinitePlace.isReal_mk_iff] at hv
  have hreal := RingHom.congr_fun (ComplexEmbedding.isReal_iff.mp hv)
  have hcomp : ψ.comp (algebraMap F L) = (ComplexEmbedding.conjugate ψ).comp (algebraMap F L) := by
    ext x
    simp only [RingHom.comp_apply, ComplexEmbedding.conjugate_coe_eq,
      IsScalarTower.algebraMap_apply F E L x]
    have h1 := RingHom.congr_fun hψ (algebraMap F E x)
    simp only [RingHom.comp_apply] at h1
    rw [h1]
    have h2 := hreal x
    simp only [RingHom.comp_apply, ComplexEmbedding.conjugate_coe_eq] at h2
    exact h2.symm
  obtain ⟨σ, hσ⟩ :=
    ComplexEmbedding.exists_comp_symm_eq_of_comp_eq ψ (ComplexEmbedding.conjugate ψ) hcomp
  have hconj : ComplexEmbedding.IsConj ψ σ.symm := hσ.symm
  refine ⟨σ.symm, ⟨ψ, hconj⟩, ?_⟩
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply]
  rw [← hψ, RingHom.comp_apply, RingHom.comp_apply]
  change _ = ψ (algebraMap E L ((σ.symm.restrictNormal E) x))
  rw [AlgEquiv.restrictNormal_commutes, hconj.eq]
  rfl

end Conjugation

section ArchimedeanPlaces

variable {F E : Type u} [Field F] [Field E] [Algebra F E]

/-- The real part of the image of `x ∈ F` under the embedding of a place above `v`. -/
theorem re_embedding_algebraMap (w : InfinitePlace E) (v : InfinitePlace F) [w.LiesOver v]
    (x : F) : (w.embedding (algebraMap F E x)).re = (v.embedding x).re := by
  rcases InfinitePlace.LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq w v with h | h
  · rw [← h]
    rfl
  · rw [← h, RingHom.comp_apply, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]

/-- Archimedean invariants vanish at places above complex places. -/
theorem archimedeanInvariant_eq_zero_of_isComplex (w : InfinitePlace E)
    (hv : (w.comap (algebraMap F E)).IsComplex) (x : relativeCohomology F E 2) :
    archimedeanInvariant w x = 0 := by
  apply archimedeanInvariant_eq_zero_of_stabilizer
  intro d hd
  by_contra hd1
  have h := (isConj_of_mem_stabilizer w hd hd1).isReal_comp
  rw [← InfinitePlace.mk_embedding w, InfinitePlace.comap_mk, InfinitePlace.isComplex_mk_iff] at hv
  exact hv h

/-- The archimedean invariant of a carry class at a place `w` with conjugation `c`
(`c = 1` when `w` is real). -/
theorem archimedeanInvariant_cyclicClass_of_isConj {n : ℕ} [NeZero n]
    (χ : (E ≃ₐ[F] E) →* Multiplicative (ZMod n)) (hχ : Function.Injective χ) (a : Fˣ)
    (w : InfinitePlace E) (c : E ≃ₐ[F] E) (hc : ComplexEmbedding.IsConj w.embedding c) :
    archimedeanInvariant w (cyclicClass F E χ a) =
      if (w.embedding (algebraMap F E a)).re < 0 then zmodClass n (χ c).toAdd else 0 := by
  by_cases hc1 : c = 1
  · subst hc1
    rw [map_one, toAdd_one, map_zero, ite_self]
    apply archimedeanInvariant_eq_zero_of_stabilizer
    intro d hd
    by_contra hd1
    exact hd1 (eq_of_isConj w (isConj_of_mem_stabilizer w hd hd1) hc)
  · have hmem : c ∈ MulAction.stabilizer (E ≃ₐ[F] E) w := by
      rw [← InfinitePlace.mk_embedding w, InfinitePlace.mem_stabilizer_mk_iff]
      exact Or.inr hc
    exact archimedeanInvariant_cyclicClass w χ hχ a c hmem hc1

end ArchimedeanPlaces

end CyclicReciprocity

end Langlands.ClassField.Global
