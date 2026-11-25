# Local duality at the real places

`Langlands/GaloisCohomology/Global/RealPlaces/LocalDuality.lean`, namespace `Langlands.GaloisCohomology`.

## Statements

**Order two.** Let `L/K` be an extension of fields (`K L : Type u`) whose Galois group, discrete
and finite, is `{1, c}` with `c ≠ 1` (hypotheses `hG : ∀ g, g = 1 ∨ g = c` and `hc : c ≠ 1`). Let
`inv : H²(Gal(L/K), Lˣ) →+ ℚ/ℤ` be a homomorphism, and suppose

* (`hinv`) for every `t ∈ Lˣ` fixed by `c` with `t² = 1` and `t ≠ 1`, `inv` of the class of the
  `2`-cocycle `cocycleTwo t` (supported at `(c, c)`, with value `t`) is `1/2`;
* (`hconj`) `c` acts on every root of unity of `L` by inversion;
* (`hroots`) `μ_k(L) ≅ ℤ/k` for every `k > 0`.

For a finite smooth module `M` over `ULift ℤ` with Cartier dual `M' = Hom(M, Lˣ)` (`cartierDual`),
`orderTwoDualityPairing inv M h : Hʳ(M) →+ Hˢ(M') →+ ℚ/ℤ` (`h : r + s = 2`) is the cup product with
the Cartier pairing followed by `inv`. It vanishes on norm classes in degree `0`
(`orderTwoDualityPairing_two_zero_eq_zero`, `orderTwoDualityPairing_zero_two_eq_zero`) and so
defines `orderTwoDualityPairingZeroTwo : Ĥ⁰(M) →+ H²(M') →+ ℚ/ℤ` and
`orderTwoDualityPairingTwoZero : H²(M) →+ Ĥ⁰(M') →+ ℚ/ℤ`, where `Ĥ⁰ = H⁰/N` is Tate's group
(`cohomologyTateZero`).

**Theorem** (`orderTwoLocalDuality`). The pairings `Ĥ⁰(M) × H²(M') → ℚ/ℤ`, `H¹(M) × H¹(M') → ℚ/ℤ`
and `H²(M) × Ĥ⁰(M') → ℚ/ℤ` are perfect: each pairing and its flip are bijective onto the groups of
homomorphisms to `ℚ/ℤ`.

**Real places.** Let `K` be a number field, `w` an infinite place, `K̄_w` the algebraic closure of
the completion `K_w`, `closureConj w hw` the complex conjugation of `K̄_w` at a real place
(`hw : w.IsReal`), and `realInvariantQZ w : H²(Gal(K̄_w/K_w), K̄_wˣ) →+ ℚ/ℤ` the real invariant of the
local Brauer group (`realInvariantHom` of `Langlands.GaloisCohomology.Global.BrauerSequence.Existence`,
read in `QZ`). The three conditions hold: `realInvariantQZ_cocycleTwo` (the class of `cocycleTwo (−1)`
is not zero because `−1` is not a norm `m · c(m)`, by `exists_mul_closureConj_iff`),
`closureConj_unitsModule_of_torsion` (a root of unity `ζ` has `|ζ| = 1` in `ℂ`, so its conjugate is
`ζ⁻¹`; `closureConj_apply_of_pow_eq_one`) and `nonempty_rootsOfUnityModule_addEquiv_zmod` (`μ_k(K̄_w)`
is cyclic of order `k`).

**Theorem** (`realLocalDuality`). For a real place `w`, a `Fintype` structure on `Gal(K̄_w/K_w)` and
a finite smooth module `M` of `Gal(K̄_w/K_w)` over `ULift ℤ`, the three pairings
`Ĥ⁰(M) × H²(M') → ℚ/ℤ`, `H¹(M) × H¹(M') → ℚ/ℤ`, `H²(M) × Ĥ⁰(M') → ℚ/ℤ` (cup product and the real
invariant) are perfect, with their flips.

This is the duality theorem for `Gal(ℂ/ℝ)` of NSW (7.2.17) for finite modules and in the degrees
`0, 1, 2` (with `Ĥ⁰` in degree `0`; the other degrees of Tate cohomology are periodic and are not
stated here).

## Proof

For a group of order two `{1, c}` the cohomology is computed by explicit cocycles
(`Langlands.GaloisCohomology.CompactSupport.TateModified.OrderTwo`): `H¹(M) ≅ ker(1 + c)/im(1 − c)`
(`OrderTwo.h1EquivOfOrderTwo`), `H²(M) ≅ M^c/im(1 + c)` (`OrderTwo.h2EquivOfOrderTwo`) and
`Ĥ⁰(M) ≅ M^c/im(1 + c)` (`OrderTwo.cohomZeroEquivContinuous`), the groups `tateQuot σ` of
`σ = −c` and `σ = c`. For `M` killed by `n = #M` and an isomorphism `μ_n(L) ≅ ℤ/n` the Cartier dual
is `Hom(M, ℚ/ℤ)` (`cartierDualEquivQZ`, through `cartierDualIsoHomRootsOfUnityOfNsmul`), and because
`c` inverts roots of unity, the action of `c` on `M'` becomes the dual involution
`f ↦ −f ∘ c` (`cartierDualToQZ_act`). The cup product of the explicit cocycles is again the cocycle
supported at `(c, c)` whose value is the evaluation of the two arguments: `cupPairing_cocycleOne`
(degrees `1 + 1`), `cupPairing_cocycleTwo_zero` (`2 + 0`) and `cupPairing_zero_cocycleTwo`
(`0 + 2`), from the cochain formula of the cup product (`cochainOf_cupCartier`) and the normalized
form of `2`-cocycles (`OrderTwo.exists_eq_cocycleTwo_of_normalized`). The value of that evaluation
has order at most two, and `inv` of its class is the corresponding element of `ℚ/ℤ`
(`inv_cocycleTwo_eq`, `inv_cocycleTwo_eq_cartierDualToQZ`; an element of order two of `ℚ/ℤ` is `1/2`,
`QZ.eq_mk_half_of_two_nsmul`). Hence each pairing is carried to `Involution.tatePair` of `σ` and its
dual involution (`orderTwoDualityPairingTwoZero_eq_tatePair`,
`orderTwoDualityPairingZeroTwo_eq_tatePair`, `orderTwoDualityPairing_one_eq_tatePair`), which is
perfect for a finite group (`Involution.tatePair_bijective`, `Involution.tatePair_flip_bijective`),
and bijectivity transfers along the isomorphisms (`bijective_of_pairing_eq_addEquiv`,
`bijective_flip_of_pairing_eq_addEquiv` of `Langlands.Cohomology.Profinite.TorsionDual`, with the
identity of `ℚ/ℤ`).

## Declarations, in order

`Involution.dualInv_neg`, `cartierDualRoots`, `rootsOfUnityToUnits_cartierDualRoots`,
`cartierDualToQZ`, `cartierDualToQZ_apply`, `cartierDualToQZ_apply_eq_zero_iff`,
`cartierDualToQZ_injective`, `cartierDualToQZ_surjective`, `cartierDualEquivQZ`,
`cartierDualToQZ_act`, `QZ.eq_mk_half_of_two_nsmul`, `cohomologyπ_cocycleTwo_congr`,
`cochainOf_cupCartier`, `cupPairing_cocycleOne`,
`cupPairing_cocycleTwo_zero`, `cupPairing_zero_cocycleTwo`, `orderTwoDualityPairing`,
`orderTwoDualityPairing_apply`, `inv_cocycleTwo_eq`, `inv_cocycleTwo_eq_cartierDualToQZ`,
`orderTwoDualityPairing_two_zero_eq_zero`, `orderTwoDualityPairing_zero_two_eq_zero`,
`orderTwoDualityPairingTwoZero`, `orderTwoDualityPairingTwoZero_mk`,
`orderTwoDualityPairingZeroTwo`, `orderTwoDualityPairingZeroTwo_mk`,
`orderTwoDualityPairingTwoZero_eq_tatePair`, `orderTwoDualityPairingZeroTwo_eq_tatePair`,
`orderTwoDualityPairing_one_eq_tatePair`, `orderTwoLocalDuality`, `realInvariantQZ`,
`closureConj_apply_of_pow_eq_one`, `closureConj_unitsModule_of_torsion`,
`nonempty_rootsOfUnityModule_addEquiv_zmod`, `realInvariantQZ_cocycleTwo`, `realLocalDuality`.

## Complete types

```lean
@Langlands.GaloisCohomology.Involution.dualInv_neg : ∀ {M : Type u_1} [inst : AddCommGroup M] (σ : M →+ M)
  (f : M →+ Langlands.ProfiniteCohomology.QZ),
  (Langlands.GaloisCohomology.Involution.dualInv (-σ)) f = -(Langlands.GaloisCohomology.Involution.dualInv σ) f
@Langlands.GaloisCohomology.cartierDualRoots : {K L : Type u_1} →
  [inst : Field K] →
    [inst_1 : Field L] →
      [inst_2 : Algebra K L] →
        (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) Gal(L/K)) →
          {n : ℕ} →
            (∀ (m : ↑M), n • m = 0) →
              ↑(Langlands.GaloisCohomology.cartierDual K L M) →+
                ↑M →+ ↑(Langlands.GaloisCohomology.rootsOfUnityModule K L n)
@Langlands.GaloisCohomology.rootsOfUnityToUnits_cartierDualRoots : ∀ {K L : Type u_1} [inst : Field K]
  [inst_1 : Field L] [inst_2 : Algebra K L] (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) Gal(L/K)) {n : ℕ}
  (hMn : ∀ (m : ↑M), n • m = 0) (φ : ↑(Langlands.GaloisCohomology.cartierDual K L M)) (m : ↑M),
  (Rep.Hom.hom (Langlands.GaloisCohomology.rootsOfUnityToUnits K L n))
      (((Langlands.GaloisCohomology.cartierDualRoots M hMn) φ) m) =
    φ m
@Langlands.GaloisCohomology.cartierDualToQZ : {K L : Type u_1} →
  [inst : Field K] →
    [inst_1 : Field L] →
      [inst_2 : Algebra K L] →
        (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) Gal(L/K)) →
          {n : ℕ} →
            (∀ (m : ↑M), n • m = 0) →
              ↑(Langlands.GaloisCohomology.rootsOfUnityModule K L n) ≃+ ZMod n →
                ↑(Langlands.GaloisCohomology.cartierDual K L M) →+ ↑M →+ Langlands.ProfiniteCohomology.QZ
@Langlands.GaloisCohomology.cartierDualToQZ_apply : ∀ {K L : Type u_1} [inst : Field K] [inst_1 : Field L]
  [inst_2 : Algebra K L] (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) Gal(L/K)) {n : ℕ} (hMn : ∀ (m : ↑M), n • m = 0)
  (e : ↑(Langlands.GaloisCohomology.rootsOfUnityModule K L n) ≃+ ZMod n)
  (φ : ↑(Langlands.GaloisCohomology.cartierDual K L M)) (m : ↑M),
  ((Langlands.GaloisCohomology.cartierDualToQZ M hMn e) φ) m =
    (Langlands.ProfiniteCohomology.zmodToQZ n) (e (((Langlands.GaloisCohomology.cartierDualRoots M hMn) φ) m))
@Langlands.GaloisCohomology.cartierDualToQZ_apply_eq_zero_iff : ∀ {K L : Type u_1} [inst : Field K] [inst_1 : Field L]
  [inst_2 : Algebra K L] (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) Gal(L/K)) {n : ℕ} [NeZero n]
  (hMn : ∀ (m : ↑M), n • m = 0) (e : ↑(Langlands.GaloisCohomology.rootsOfUnityModule K L n) ≃+ ZMod n)
  (φ : ↑(Langlands.GaloisCohomology.cartierDual K L M)) (m : ↑M),
  ((Langlands.GaloisCohomology.cartierDualToQZ M hMn e) φ) m = 0 ↔ φ m = 0
@Langlands.GaloisCohomology.cartierDualToQZ_injective : ∀ {K L : Type u_1} [inst : Field K] [inst_1 : Field L]
  [inst_2 : Algebra K L] (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) Gal(L/K)) {n : ℕ} [NeZero n]
  (hMn : ∀ (m : ↑M), n • m = 0) (e : ↑(Langlands.GaloisCohomology.rootsOfUnityModule K L n) ≃+ ZMod n),
  Function.Injective ⇑(Langlands.GaloisCohomology.cartierDualToQZ M hMn e)
@Langlands.GaloisCohomology.cartierDualToQZ_surjective : ∀ {K L : Type u_1} [inst : Field K] [inst_1 : Field L]
  [inst_2 : Algebra K L] (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) Gal(L/K)) {n : ℕ} [NeZero n]
  (hMn : ∀ (m : ↑M), n • m = 0) (e : ↑(Langlands.GaloisCohomology.rootsOfUnityModule K L n) ≃+ ZMod n),
  Function.Surjective ⇑(Langlands.GaloisCohomology.cartierDualToQZ M hMn e)
@Langlands.GaloisCohomology.cartierDualEquivQZ : {K L : Type u_1} →
  [inst : Field K] →
    [inst_1 : Field L] →
      [inst_2 : Algebra K L] →
        (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) Gal(L/K)) →
          {n : ℕ} →
            [NeZero n] →
              (∀ (m : ↑M), n • m = 0) →
                ↑(Langlands.GaloisCohomology.rootsOfUnityModule K L n) ≃+ ZMod n →
                  ↑(Langlands.GaloisCohomology.cartierDual K L M) ≃+ (↑M →+ Langlands.ProfiniteCohomology.QZ)
@Langlands.GaloisCohomology.cartierDualToQZ_act : ∀ {K L : Type u_1} [inst : Field K] [inst_1 : Field L]
  [inst_2 : Algebra K L] (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) Gal(L/K)) {n : ℕ} (hMn : ∀ (m : ↑M), n • m = 0)
  (e : ↑(Langlands.GaloisCohomology.rootsOfUnityModule K L n) ≃+ ZMod n) {c : Gal(L/K)},
  c⁻¹ = c →
    (∀ (ζ : ↑(Langlands.GaloisCohomology.unitsModule K L)),
        n • ζ = 0 → ((Langlands.GaloisCohomology.unitsModule K L).ρ c) ζ = -ζ) →
      ∀ (φ : ↑(Langlands.GaloisCohomology.cartierDual K L M)),
        (Langlands.GaloisCohomology.cartierDualToQZ M hMn e) (((Langlands.GaloisCohomology.cartierDual K L M).ρ c) φ) =
          (Langlands.GaloisCohomology.Involution.dualInv (Langlands.GaloisCohomology.OrderTwo.act M c))
            ((Langlands.GaloisCohomology.cartierDualToQZ M hMn e) φ)
@Langlands.GaloisCohomology.QZ.eq_mk_half_of_two_nsmul : ∀ {q : Langlands.ProfiniteCohomology.QZ},
  2 • q = 0 → q ≠ 0 → q = Langlands.ProfiniteCohomology.QZ.mk (1 / 2)
@Langlands.GaloisCohomology.cohomologyπ_cocycleTwo_congr : ∀ {k G : Type u_1} [inst : CommRing k] [inst_1 : Group G]
  [inst_2 : TopologicalSpace G] [inst_3 : IsTopologicalGroup G] [inst_4 : DiscreteTopology G] {c : G}
  (hG : ∀ (g : G), g = 1 ∨ g = c) (hc : c ≠ 1) (A : Rep.{u_1, u_1, u_1} k G) [inst_5 : Langlands.IsSmoothRep A]
  {a b : ↑A} (ha : (A.ρ c) a = a) (hb : (A.ρ c) b = b),
  a = b →
    (CategoryTheory.ConcreteCategory.hom (Langlands.ProfiniteCohomology.cohomologyπ A 2))
        (Langlands.GaloisCohomology.OrderTwo.cocycleTwo A hG hc a ha) =
      (CategoryTheory.ConcreteCategory.hom (Langlands.ProfiniteCohomology.cohomologyπ A 2))
        (Langlands.GaloisCohomology.OrderTwo.cocycleTwo A hG hc b hb)
@Langlands.GaloisCohomology.cochainOf_cupCartier : ∀ {K L : Type u_1} [inst : Field K] [inst_1 : Field L]
  [inst_2 : Algebra K L] [inst_3 : DiscreteTopology Gal(L/K)] (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) Gal(L/K))
  [inst_4 : Langlands.IsSmoothRep M] [inst_5 : Finite ↑M] {p q : ℕ} (h : p + q = 2)
  (x : ↑(Langlands.ProfiniteCohomology.cocycles M p))
  (y : ↑(Langlands.ProfiniteCohomology.cocycles (Langlands.GaloisCohomology.cartierDual K L M) q))
  (s : Fin 2 → Gal(L/K)),
  Langlands.ProfiniteCohomology.cochainOf (Langlands.GaloisCohomology.unitsModule K L)
      ((Langlands.ProfiniteCohomology.cocycleι (Langlands.GaloisCohomology.unitsModule K L) 2)
        ((CategoryTheory.ConcreteCategory.hom
            (HomologicalComplex.cyclesMap
              (Langlands.ProfiniteCohomology.coeffCochainsMap (Langlands.GaloisCohomology.cartierPairing K L M)) 2))
          (((Langlands.ProfiniteCohomology.cupCocycles h) x) y)))
      s =
    (((Langlands.GaloisCohomology.cartierDual K L M).ρ (Fin.partialProd s ⟨p, ⋯⟩))
        (Langlands.ProfiniteCohomology.cochainOf (Langlands.GaloisCohomology.cartierDual K L M)
          ((Langlands.ProfiniteCohomology.cocycleι (Langlands.GaloisCohomology.cartierDual K L M) q) y)
          fun (j : Fin q) => s ⟨p + ↑j, ⋯⟩))
      (Langlands.ProfiniteCohomology.cochainOf M ((Langlands.ProfiniteCohomology.cocycleι M p) x) fun (i : Fin p) =>
        s ⟨↑i, ⋯⟩)
@Langlands.GaloisCohomology.cupPairing_cocycleOne : ∀ {K L : Type u_1} [inst : Field K] [inst_1 : Field L]
  [inst_2 : Algebra K L] [inst_3 : DiscreteTopology Gal(L/K)] (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) Gal(L/K))
  [inst_4 : Langlands.IsSmoothRep M] [inst_5 : Finite ↑M] {c : Gal(L/K)} (hG : ∀ (g : Gal(L/K)), g = 1 ∨ g = c)
  (hc : c ≠ 1) (α : ↑M) (hα : α + (M.ρ c) α = 0) (β : ↑(Langlands.GaloisCohomology.cartierDual K L M))
  (hβ : β + ((Langlands.GaloisCohomology.cartierDual K L M).ρ c) β = 0),
  ∃ (ht :
    ((Langlands.GaloisCohomology.unitsModule K L).ρ c) ((((Langlands.GaloisCohomology.cartierDual K L M).ρ c) β) α) =
      (((Langlands.GaloisCohomology.cartierDual K L M).ρ c) β) α),
    ((Langlands.ProfiniteCohomology.cupPairing (Langlands.GaloisCohomology.cartierPairing K L M) ⋯)
          ((CategoryTheory.ConcreteCategory.hom (Langlands.ProfiniteCohomology.cohomologyπ M 1))
            (Langlands.GaloisCohomology.OrderTwo.cocycleOne M hG hc α hα)))
        ((CategoryTheory.ConcreteCategory.hom
            (Langlands.ProfiniteCohomology.cohomologyπ (Langlands.GaloisCohomology.cartierDual K L M) 1))
          (Langlands.GaloisCohomology.OrderTwo.cocycleOne (Langlands.GaloisCohomology.cartierDual K L M) hG hc β hβ)) =
      (CategoryTheory.ConcreteCategory.hom
          (Langlands.ProfiniteCohomology.cohomologyπ (Langlands.GaloisCohomology.unitsModule K L) 2))
        (Langlands.GaloisCohomology.OrderTwo.cocycleTwo (Langlands.GaloisCohomology.unitsModule K L) hG hc
          ((((Langlands.GaloisCohomology.cartierDual K L M).ρ c) β) α) ht)
@Langlands.GaloisCohomology.cupPairing_cocycleTwo_zero : ∀ {K L : Type u_1} [inst : Field K] [inst_1 : Field L]
  [inst_2 : Algebra K L] [inst_3 : DiscreteTopology Gal(L/K)] (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) Gal(L/K))
  [inst_4 : Langlands.IsSmoothRep M] [inst_5 : Finite ↑M] {c : Gal(L/K)} (hG : ∀ (g : Gal(L/K)), g = 1 ∨ g = c)
  (hc : c ≠ 1) (a : ↑M) (ha : (M.ρ c) a = a) (φ : ↥(Langlands.GaloisCohomology.cartierDual K L M).ρ.invariants),
  ∃ (ht : ((Langlands.GaloisCohomology.unitsModule K L).ρ c) (↑φ a) = ↑φ a),
    ((Langlands.ProfiniteCohomology.cupPairing (Langlands.GaloisCohomology.cartierPairing K L M) ⋯)
          ((CategoryTheory.ConcreteCategory.hom (Langlands.ProfiniteCohomology.cohomologyπ M 2))
            (Langlands.GaloisCohomology.OrderTwo.cocycleTwo M hG hc a ha)))
        ((ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.zeroIso (Langlands.GaloisCohomology.cartierDual K L M)).inv)
          φ) =
      (CategoryTheory.ConcreteCategory.hom
          (Langlands.ProfiniteCohomology.cohomologyπ (Langlands.GaloisCohomology.unitsModule K L) 2))
        (Langlands.GaloisCohomology.OrderTwo.cocycleTwo (Langlands.GaloisCohomology.unitsModule K L) hG hc (↑φ a) ht)
@Langlands.GaloisCohomology.cupPairing_zero_cocycleTwo : ∀ {K L : Type u_1} [inst : Field K] [inst_1 : Field L]
  [inst_2 : Algebra K L] [inst_3 : DiscreteTopology Gal(L/K)] (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) Gal(L/K))
  [inst_4 : Langlands.IsSmoothRep M] [inst_5 : Finite ↑M] {c : Gal(L/K)} (hG : ∀ (g : Gal(L/K)), g = 1 ∨ g = c)
  (hc : c ≠ 1) (a : ↥M.ρ.invariants) (φ : ↑(Langlands.GaloisCohomology.cartierDual K L M))
  (hφ : ((Langlands.GaloisCohomology.cartierDual K L M).ρ c) φ = φ),
  ∃ (ht : ((Langlands.GaloisCohomology.unitsModule K L).ρ c) (φ ↑a) = φ ↑a),
    ((Langlands.ProfiniteCohomology.cupPairing (Langlands.GaloisCohomology.cartierPairing K L M) ⋯)
          ((ModuleCat.Hom.hom (Langlands.ProfiniteCohomology.zeroIso M).inv) a))
        ((CategoryTheory.ConcreteCategory.hom
            (Langlands.ProfiniteCohomology.cohomologyπ (Langlands.GaloisCohomology.cartierDual K L M) 2))
          (Langlands.GaloisCohomology.OrderTwo.cocycleTwo (Langlands.GaloisCohomology.cartierDual K L M) hG hc φ hφ)) =
      (CategoryTheory.ConcreteCategory.hom
          (Langlands.ProfiniteCohomology.cohomologyπ (Langlands.GaloisCohomology.unitsModule K L) 2))
        (Langlands.GaloisCohomology.OrderTwo.cocycleTwo (Langlands.GaloisCohomology.unitsModule K L) hG hc (φ ↑a) ht)
@Langlands.GaloisCohomology.orderTwoDualityPairing : {K L : Type u_1} →
  [inst : Field K] →
    [inst_1 : Field L] →
      [inst_2 : Algebra K L] →
        [inst_3 : DiscreteTopology Gal(L/K)] →
          (↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K L) 2) →+
              Langlands.ProfiniteCohomology.QZ) →
            (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) Gal(L/K)) →
              [inst_4 : Langlands.IsSmoothRep M] →
                [inst_5 : Finite ↑M] →
                  {r s : ℕ} →
                    r + s = 2 →
                      ↑(Langlands.ProfiniteCohomology.cohomology M r) →+
                        ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.cartierDual K L M) s) →+
                          Langlands.ProfiniteCohomology.QZ
@Langlands.GaloisCohomology.orderTwoDualityPairing_apply : ∀ {K L : Type u_1} [inst : Field K] [inst_1 : Field L]
  [inst_2 : Algebra K L] [inst_3 : DiscreteTopology Gal(L/K)]
  (inv :
    ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K L) 2) →+
      Langlands.ProfiniteCohomology.QZ)
  (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) Gal(L/K)) [inst_4 : Langlands.IsSmoothRep M] [inst_5 : Finite ↑M]
  {r s : ℕ} (h : r + s = 2) (x : ↑(Langlands.ProfiniteCohomology.cohomology M r))
  (y : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.cartierDual K L M) s)),
  ((Langlands.GaloisCohomology.orderTwoDualityPairing inv M h) x) y =
    inv (((Langlands.ProfiniteCohomology.cupPairing (Langlands.GaloisCohomology.cartierPairing K L M) h) x) y)
@Langlands.GaloisCohomology.inv_cocycleTwo_eq : ∀ {K L : Type u_1} [inst : Field K] [inst_1 : Field L]
  [inst_2 : Algebra K L] [inst_3 : DiscreteTopology Gal(L/K)] {c : Gal(L/K)} (hG : ∀ (g : Gal(L/K)), g = 1 ∨ g = c)
  (hc : c ≠ 1)
  (inv :
    ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K L) 2) →+
      Langlands.ProfiniteCohomology.QZ),
  (∀ (t : ↑(Langlands.GaloisCohomology.unitsModule K L))
      (ht : ((Langlands.GaloisCohomology.unitsModule K L).ρ c) t = t),
      2 • t = 0 →
        t ≠ 0 →
          inv
              ((CategoryTheory.ConcreteCategory.hom
                  (Langlands.ProfiniteCohomology.cohomologyπ (Langlands.GaloisCohomology.unitsModule K L) 2))
                (Langlands.GaloisCohomology.OrderTwo.cocycleTwo (Langlands.GaloisCohomology.unitsModule K L) hG hc t
                  ht)) =
            Langlands.ProfiniteCohomology.QZ.mk (1 / 2)) →
    ∀ (t : ↑(Langlands.GaloisCohomology.unitsModule K L))
      (ht : ((Langlands.GaloisCohomology.unitsModule K L).ρ c) t = t),
      2 • t = 0 →
        ∀ (q : Langlands.ProfiniteCohomology.QZ),
          2 • q = 0 →
            (q = 0 ↔ t = 0) →
              inv
                  ((CategoryTheory.ConcreteCategory.hom
                      (Langlands.ProfiniteCohomology.cohomologyπ (Langlands.GaloisCohomology.unitsModule K L) 2))
                    (Langlands.GaloisCohomology.OrderTwo.cocycleTwo (Langlands.GaloisCohomology.unitsModule K L) hG hc t
                      ht)) =
                q
@Langlands.GaloisCohomology.inv_cocycleTwo_eq_cartierDualToQZ : ∀ {K L : Type u_1} [inst : Field K] [inst_1 : Field L]
  [inst_2 : Algebra K L] [inst_3 : DiscreteTopology Gal(L/K)] {c : Gal(L/K)} (hG : ∀ (g : Gal(L/K)), g = 1 ∨ g = c)
  (hc : c ≠ 1)
  (inv :
    ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K L) 2) →+
      Langlands.ProfiniteCohomology.QZ),
  (∀ (t : ↑(Langlands.GaloisCohomology.unitsModule K L))
      (ht : ((Langlands.GaloisCohomology.unitsModule K L).ρ c) t = t),
      2 • t = 0 →
        t ≠ 0 →
          inv
              ((CategoryTheory.ConcreteCategory.hom
                  (Langlands.ProfiniteCohomology.cohomologyπ (Langlands.GaloisCohomology.unitsModule K L) 2))
                (Langlands.GaloisCohomology.OrderTwo.cocycleTwo (Langlands.GaloisCohomology.unitsModule K L) hG hc t
                  ht)) =
            Langlands.ProfiniteCohomology.QZ.mk (1 / 2)) →
    ∀ (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) Gal(L/K)) {n : ℕ} [NeZero n] (hMn : ∀ (m : ↑M), n • m = 0)
      (e : ↑(Langlands.GaloisCohomology.rootsOfUnityModule K L n) ≃+ ZMod n)
      (φ : ↑(Langlands.GaloisCohomology.cartierDual K L M)) (m : ↑M),
      2 • ((Langlands.GaloisCohomology.cartierDualToQZ M hMn e) φ) m = 0 →
        ∀ (t : ↑(Langlands.GaloisCohomology.unitsModule K L)),
          t = φ m ∨ t = -φ m →
            ∀ (ht : ((Langlands.GaloisCohomology.unitsModule K L).ρ c) t = t),
              inv
                  ((CategoryTheory.ConcreteCategory.hom
                      (Langlands.ProfiniteCohomology.cohomologyπ (Langlands.GaloisCohomology.unitsModule K L) 2))
                    (Langlands.GaloisCohomology.OrderTwo.cocycleTwo (Langlands.GaloisCohomology.unitsModule K L) hG hc t
                      ht)) =
                ((Langlands.GaloisCohomology.cartierDualToQZ M hMn e) φ) m
@Langlands.GaloisCohomology.orderTwoDualityPairing_two_zero_eq_zero : ∀ {K L : Type u_1} [inst : Field K]
  [inst_1 : Field L] [inst_2 : Algebra K L] [inst_3 : DiscreteTopology Gal(L/K)] [inst_4 : Fintype Gal(L/K)]
  (inv :
    ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K L) 2) →+
      Langlands.ProfiniteCohomology.QZ)
  {c : Gal(L/K)},
  (∀ (g : Gal(L/K)), g = 1 ∨ g = c) →
    c ≠ 1 →
      ∀ (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) Gal(L/K)) [inst_5 : Langlands.IsSmoothRep M] [inst_6 : Finite ↑M]
        (x : ↑(Langlands.ProfiniteCohomology.cohomology M 2)),
        ∀ y ∈ Langlands.GaloisCohomology.normClasses (Langlands.GaloisCohomology.cartierDual K L M),
          ((Langlands.GaloisCohomology.orderTwoDualityPairing inv M ⋯) x) y = 0
@Langlands.GaloisCohomology.orderTwoDualityPairing_zero_two_eq_zero : ∀ {K L : Type u_1} [inst : Field K]
  [inst_1 : Field L] [inst_2 : Algebra K L] [inst_3 : DiscreteTopology Gal(L/K)] [inst_4 : Fintype Gal(L/K)]
  (inv :
    ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K L) 2) →+
      Langlands.ProfiniteCohomology.QZ)
  {c : Gal(L/K)},
  (∀ (g : Gal(L/K)), g = 1 ∨ g = c) →
    c ≠ 1 →
      ∀ (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) Gal(L/K)) [inst_5 : Langlands.IsSmoothRep M] [inst_6 : Finite ↑M],
        ∀ x ∈ Langlands.GaloisCohomology.normClasses M,
          ∀ (y : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.cartierDual K L M) 2)),
            ((Langlands.GaloisCohomology.orderTwoDualityPairing inv M ⋯) x) y = 0
@Langlands.GaloisCohomology.orderTwoDualityPairingTwoZero : {K L : Type u_1} →
  [inst : Field K] →
    [inst_1 : Field L] →
      [inst_2 : Algebra K L] →
        [inst_3 : DiscreteTopology Gal(L/K)] →
          [inst_4 : Fintype Gal(L/K)] →
            (↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K L) 2) →+
                Langlands.ProfiniteCohomology.QZ) →
              {c : Gal(L/K)} →
                (∀ (g : Gal(L/K)), g = 1 ∨ g = c) →
                  c ≠ 1 →
                    (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) Gal(L/K)) →
                      [inst_5 : Langlands.IsSmoothRep M] →
                        [inst_6 : Finite ↑M] →
                          ↑(Langlands.ProfiniteCohomology.cohomology M 2) →+
                            Langlands.GaloisCohomology.cohomologyTateZero
                                (Langlands.GaloisCohomology.cartierDual K L M) →+
                              Langlands.ProfiniteCohomology.QZ
@Langlands.GaloisCohomology.orderTwoDualityPairingTwoZero_mk : ∀ {K L : Type u_1} [inst : Field K] [inst_1 : Field L]
  [inst_2 : Algebra K L] [inst_3 : DiscreteTopology Gal(L/K)] [inst_4 : Fintype Gal(L/K)]
  (inv :
    ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K L) 2) →+
      Langlands.ProfiniteCohomology.QZ)
  {c : Gal(L/K)} (hG : ∀ (g : Gal(L/K)), g = 1 ∨ g = c) (hc : c ≠ 1)
  (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) Gal(L/K)) [inst_5 : Langlands.IsSmoothRep M] [inst_6 : Finite ↑M]
  (x : ↑(Langlands.ProfiniteCohomology.cohomology M 2))
  (y : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.cartierDual K L M) 0)),
  ((Langlands.GaloisCohomology.orderTwoDualityPairingTwoZero inv hG hc M) x) (Submodule.Quotient.mk y) =
    ((Langlands.GaloisCohomology.orderTwoDualityPairing inv M ⋯) x) y
@Langlands.GaloisCohomology.orderTwoDualityPairingZeroTwo : {K L : Type u_1} →
  [inst : Field K] →
    [inst_1 : Field L] →
      [inst_2 : Algebra K L] →
        [inst_3 : DiscreteTopology Gal(L/K)] →
          [inst_4 : Fintype Gal(L/K)] →
            (↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K L) 2) →+
                Langlands.ProfiniteCohomology.QZ) →
              {c : Gal(L/K)} →
                (∀ (g : Gal(L/K)), g = 1 ∨ g = c) →
                  c ≠ 1 →
                    (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) Gal(L/K)) →
                      [inst_5 : Langlands.IsSmoothRep M] →
                        [inst_6 : Finite ↑M] →
                          Langlands.GaloisCohomology.cohomologyTateZero M →+
                            ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.cartierDual K L M)
                                  2) →+
                              Langlands.ProfiniteCohomology.QZ
@Langlands.GaloisCohomology.orderTwoDualityPairingZeroTwo_mk : ∀ {K L : Type u_1} [inst : Field K] [inst_1 : Field L]
  [inst_2 : Algebra K L] [inst_3 : DiscreteTopology Gal(L/K)] [inst_4 : Fintype Gal(L/K)]
  (inv :
    ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K L) 2) →+
      Langlands.ProfiniteCohomology.QZ)
  {c : Gal(L/K)} (hG : ∀ (g : Gal(L/K)), g = 1 ∨ g = c) (hc : c ≠ 1)
  (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) Gal(L/K)) [inst_5 : Langlands.IsSmoothRep M] [inst_6 : Finite ↑M]
  (x : ↑(Langlands.ProfiniteCohomology.cohomology M 0))
  (y : ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.cartierDual K L M) 2)),
  ((Langlands.GaloisCohomology.orderTwoDualityPairingZeroTwo inv hG hc M) (Submodule.Quotient.mk x)) y =
    ((Langlands.GaloisCohomology.orderTwoDualityPairing inv M ⋯) x) y
@Langlands.GaloisCohomology.orderTwoDualityPairingTwoZero_eq_tatePair : ∀ {K L : Type u_1} [inst : Field K]
  [inst_1 : Field L] [inst_2 : Algebra K L] [inst_3 : DiscreteTopology Gal(L/K)] [inst_4 : Fintype Gal(L/K)]
  (inv :
    ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K L) 2) →+
      Langlands.ProfiniteCohomology.QZ)
  {c : Gal(L/K)} (hG : ∀ (g : Gal(L/K)), g = 1 ∨ g = c) (hc : c ≠ 1),
  (∀ (t : ↑(Langlands.GaloisCohomology.unitsModule K L))
      (ht : ((Langlands.GaloisCohomology.unitsModule K L).ρ c) t = t),
      2 • t = 0 →
        t ≠ 0 →
          inv
              ((CategoryTheory.ConcreteCategory.hom
                  (Langlands.ProfiniteCohomology.cohomologyπ (Langlands.GaloisCohomology.unitsModule K L) 2))
                (Langlands.GaloisCohomology.OrderTwo.cocycleTwo (Langlands.GaloisCohomology.unitsModule K L) hG hc t
                  ht)) =
            Langlands.ProfiniteCohomology.QZ.mk (1 / 2)) →
    (∀ (ζ : ↑(Langlands.GaloisCohomology.unitsModule K L)),
        (∃ (k : ℕ), 0 < k ∧ k • ζ = 0) → ((Langlands.GaloisCohomology.unitsModule K L).ρ c) ζ = -ζ) →
      (∀ (k : ℕ), 0 < k → Nonempty (↑(Langlands.GaloisCohomology.rootsOfUnityModule K L k) ≃+ ZMod k)) →
        ∀ (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) Gal(L/K)) [inst_5 : Langlands.IsSmoothRep M] [inst_6 : Finite ↑M],
          ∃ (e :
            Langlands.GaloisCohomology.Involution.tateQuot (Langlands.GaloisCohomology.OrderTwo.act M c) ≃+
              ↑(Langlands.ProfiniteCohomology.cohomology M 2))
            (e' :
            Langlands.GaloisCohomology.Involution.tateQuot
                (Langlands.GaloisCohomology.Involution.dualInv (Langlands.GaloisCohomology.OrderTwo.act M c)) ≃+
              Langlands.GaloisCohomology.cohomologyTateZero (Langlands.GaloisCohomology.cartierDual K L M)),
            ∀ (x : Langlands.GaloisCohomology.Involution.tateQuot (Langlands.GaloisCohomology.OrderTwo.act M c))
              (y :
                Langlands.GaloisCohomology.Involution.tateQuot
                  (Langlands.GaloisCohomology.Involution.dualInv (Langlands.GaloisCohomology.OrderTwo.act M c))),
              ((Langlands.GaloisCohomology.orderTwoDualityPairingTwoZero inv hG hc M) (e x)) (e' y) =
                ((Langlands.GaloisCohomology.Involution.tatePair (Langlands.GaloisCohomology.OrderTwo.act M c)) x) y
@Langlands.GaloisCohomology.orderTwoDualityPairingZeroTwo_eq_tatePair : ∀ {K L : Type u_1} [inst : Field K]
  [inst_1 : Field L] [inst_2 : Algebra K L] [inst_3 : DiscreteTopology Gal(L/K)] [inst_4 : Fintype Gal(L/K)]
  (inv :
    ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K L) 2) →+
      Langlands.ProfiniteCohomology.QZ)
  {c : Gal(L/K)} (hG : ∀ (g : Gal(L/K)), g = 1 ∨ g = c) (hc : c ≠ 1),
  (∀ (t : ↑(Langlands.GaloisCohomology.unitsModule K L))
      (ht : ((Langlands.GaloisCohomology.unitsModule K L).ρ c) t = t),
      2 • t = 0 →
        t ≠ 0 →
          inv
              ((CategoryTheory.ConcreteCategory.hom
                  (Langlands.ProfiniteCohomology.cohomologyπ (Langlands.GaloisCohomology.unitsModule K L) 2))
                (Langlands.GaloisCohomology.OrderTwo.cocycleTwo (Langlands.GaloisCohomology.unitsModule K L) hG hc t
                  ht)) =
            Langlands.ProfiniteCohomology.QZ.mk (1 / 2)) →
    (∀ (ζ : ↑(Langlands.GaloisCohomology.unitsModule K L)),
        (∃ (k : ℕ), 0 < k ∧ k • ζ = 0) → ((Langlands.GaloisCohomology.unitsModule K L).ρ c) ζ = -ζ) →
      (∀ (k : ℕ), 0 < k → Nonempty (↑(Langlands.GaloisCohomology.rootsOfUnityModule K L k) ≃+ ZMod k)) →
        ∀ (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) Gal(L/K)) [inst_5 : Langlands.IsSmoothRep M] [inst_6 : Finite ↑M],
          ∃ (e :
            Langlands.GaloisCohomology.Involution.tateQuot (Langlands.GaloisCohomology.OrderTwo.act M c) ≃+
              Langlands.GaloisCohomology.cohomologyTateZero M)
            (e' :
            Langlands.GaloisCohomology.Involution.tateQuot
                (Langlands.GaloisCohomology.Involution.dualInv (Langlands.GaloisCohomology.OrderTwo.act M c)) ≃+
              ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.cartierDual K L M) 2)),
            ∀ (x : Langlands.GaloisCohomology.Involution.tateQuot (Langlands.GaloisCohomology.OrderTwo.act M c))
              (y :
                Langlands.GaloisCohomology.Involution.tateQuot
                  (Langlands.GaloisCohomology.Involution.dualInv (Langlands.GaloisCohomology.OrderTwo.act M c))),
              ((Langlands.GaloisCohomology.orderTwoDualityPairingZeroTwo inv hG hc M) (e x)) (e' y) =
                ((Langlands.GaloisCohomology.Involution.tatePair (Langlands.GaloisCohomology.OrderTwo.act M c)) x) y
@Langlands.GaloisCohomology.orderTwoDualityPairing_one_eq_tatePair : ∀ {K L : Type u_1} [inst : Field K]
  [inst_1 : Field L] [inst_2 : Algebra K L] [inst_3 : DiscreteTopology Gal(L/K)]
  (inv :
    ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K L) 2) →+
      Langlands.ProfiniteCohomology.QZ)
  {c : Gal(L/K)} (hG : ∀ (g : Gal(L/K)), g = 1 ∨ g = c) (hc : c ≠ 1),
  (∀ (t : ↑(Langlands.GaloisCohomology.unitsModule K L))
      (ht : ((Langlands.GaloisCohomology.unitsModule K L).ρ c) t = t),
      2 • t = 0 →
        t ≠ 0 →
          inv
              ((CategoryTheory.ConcreteCategory.hom
                  (Langlands.ProfiniteCohomology.cohomologyπ (Langlands.GaloisCohomology.unitsModule K L) 2))
                (Langlands.GaloisCohomology.OrderTwo.cocycleTwo (Langlands.GaloisCohomology.unitsModule K L) hG hc t
                  ht)) =
            Langlands.ProfiniteCohomology.QZ.mk (1 / 2)) →
    (∀ (ζ : ↑(Langlands.GaloisCohomology.unitsModule K L)),
        (∃ (k : ℕ), 0 < k ∧ k • ζ = 0) → ((Langlands.GaloisCohomology.unitsModule K L).ρ c) ζ = -ζ) →
      (∀ (k : ℕ), 0 < k → Nonempty (↑(Langlands.GaloisCohomology.rootsOfUnityModule K L k) ≃+ ZMod k)) →
        ∀ (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) Gal(L/K)) [inst_4 : Langlands.IsSmoothRep M] [inst_5 : Finite ↑M],
          ∃ (e :
            Langlands.GaloisCohomology.Involution.tateQuot (-Langlands.GaloisCohomology.OrderTwo.act M c) ≃+
              ↑(Langlands.ProfiniteCohomology.cohomology M 1))
            (e' :
            Langlands.GaloisCohomology.Involution.tateQuot
                (Langlands.GaloisCohomology.Involution.dualInv (-Langlands.GaloisCohomology.OrderTwo.act M c)) ≃+
              ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.cartierDual K L M) 1)),
            ∀ (x : Langlands.GaloisCohomology.Involution.tateQuot (-Langlands.GaloisCohomology.OrderTwo.act M c))
              (y :
                Langlands.GaloisCohomology.Involution.tateQuot
                  (Langlands.GaloisCohomology.Involution.dualInv (-Langlands.GaloisCohomology.OrderTwo.act M c))),
              ((Langlands.GaloisCohomology.orderTwoDualityPairing inv M ⋯) (e x)) (e' y) =
                ((Langlands.GaloisCohomology.Involution.tatePair (-Langlands.GaloisCohomology.OrderTwo.act M c)) x) y
@Langlands.GaloisCohomology.orderTwoLocalDuality : ∀ {K L : Type u_1} [inst : Field K] [inst_1 : Field L]
  [inst_2 : Algebra K L] [inst_3 : DiscreteTopology Gal(L/K)] [inst_4 : Fintype Gal(L/K)]
  (inv :
    ↑(Langlands.ProfiniteCohomology.cohomology (Langlands.GaloisCohomology.unitsModule K L) 2) →+
      Langlands.ProfiniteCohomology.QZ)
  {c : Gal(L/K)} (hG : ∀ (g : Gal(L/K)), g = 1 ∨ g = c) (hc : c ≠ 1),
  (∀ (t : ↑(Langlands.GaloisCohomology.unitsModule K L))
      (ht : ((Langlands.GaloisCohomology.unitsModule K L).ρ c) t = t),
      2 • t = 0 →
        t ≠ 0 →
          inv
              ((CategoryTheory.ConcreteCategory.hom
                  (Langlands.ProfiniteCohomology.cohomologyπ (Langlands.GaloisCohomology.unitsModule K L) 2))
                (Langlands.GaloisCohomology.OrderTwo.cocycleTwo (Langlands.GaloisCohomology.unitsModule K L) hG hc t
                  ht)) =
            Langlands.ProfiniteCohomology.QZ.mk (1 / 2)) →
    (∀ (ζ : ↑(Langlands.GaloisCohomology.unitsModule K L)),
        (∃ (k : ℕ), 0 < k ∧ k • ζ = 0) → ((Langlands.GaloisCohomology.unitsModule K L).ρ c) ζ = -ζ) →
      (∀ (k : ℕ), 0 < k → Nonempty (↑(Langlands.GaloisCohomology.rootsOfUnityModule K L k) ≃+ ZMod k)) →
        ∀ (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) Gal(L/K)) [inst_5 : Langlands.IsSmoothRep M] [inst_6 : Finite ↑M],
          (Function.Bijective ⇑(Langlands.GaloisCohomology.orderTwoDualityPairingZeroTwo inv hG hc M) ∧
              Function.Bijective ⇑(Langlands.GaloisCohomology.orderTwoDualityPairingZeroTwo inv hG hc M).flip) ∧
            (Function.Bijective ⇑(Langlands.GaloisCohomology.orderTwoDualityPairing inv M ⋯) ∧
                Function.Bijective ⇑(Langlands.GaloisCohomology.orderTwoDualityPairing inv M ⋯).flip) ∧
              Function.Bijective ⇑(Langlands.GaloisCohomology.orderTwoDualityPairingTwoZero inv hG hc M) ∧
                Function.Bijective ⇑(Langlands.GaloisCohomology.orderTwoDualityPairingTwoZero inv hG hc M).flip
@Langlands.GaloisCohomology.realInvariantQZ : {K : Type u_1} →
  [inst : Field K] →
    [NumberField K] →
      (w : NumberField.InfinitePlace K) →
        Langlands.GaloisCohomology.RealBrauerGroup w →+ Langlands.ProfiniteCohomology.QZ
@Langlands.GaloisCohomology.closureConj_apply_of_pow_eq_one : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  (w : NumberField.InfinitePlace K) (hw : w.IsReal) (ζ : (AlgebraicClosure w.Completion)ˣ) {k : ℕ},
  0 < k → ζ ^ k = 1 → (Langlands.GaloisCohomology.closureConj w hw) ↑ζ = ↑ζ⁻¹
@Langlands.GaloisCohomology.closureConj_unitsModule_of_torsion : ∀ {K : Type u_1} [inst : Field K]
  [inst_1 : NumberField K] (w : NumberField.InfinitePlace K) (hw : w.IsReal)
  (ζ : ↑(Langlands.GaloisCohomology.unitsModule w.Completion (AlgebraicClosure w.Completion))),
  (∃ (k : ℕ), 0 < k ∧ k • ζ = 0) →
    ((Langlands.GaloisCohomology.unitsModule w.Completion (AlgebraicClosure w.Completion)).ρ
          (Langlands.GaloisCohomology.closureConj w hw))
        ζ =
      -ζ
@Langlands.GaloisCohomology.nonempty_rootsOfUnityModule_addEquiv_zmod : ∀ {K : Type u_1} [inst : Field K]
  [NumberField K] (w : NumberField.InfinitePlace K) (k : ℕ),
  0 < k →
    Nonempty (↑(Langlands.GaloisCohomology.rootsOfUnityModule w.Completion (AlgebraicClosure w.Completion) k) ≃+ ZMod k)
@Langlands.GaloisCohomology.realInvariantQZ_cocycleTwo : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  (w : NumberField.InfinitePlace K) (hw : w.IsReal)
  (t : ↑(Langlands.GaloisCohomology.unitsModule w.Completion (AlgebraicClosure w.Completion)))
  (ht :
    ((Langlands.GaloisCohomology.unitsModule w.Completion (AlgebraicClosure w.Completion)).ρ
          (Langlands.GaloisCohomology.closureConj w hw))
        t =
      t),
  2 • t = 0 →
    t ≠ 0 →
      (Langlands.GaloisCohomology.realInvariantQZ w)
          ((CategoryTheory.ConcreteCategory.hom
              (Langlands.ProfiniteCohomology.cohomologyπ
                (Langlands.GaloisCohomology.unitsModule w.Completion (AlgebraicClosure w.Completion)) 2))
            (Langlands.GaloisCohomology.OrderTwo.cocycleTwo
              (Langlands.GaloisCohomology.unitsModule w.Completion (AlgebraicClosure w.Completion)) ⋯ ⋯ t ht)) =
        Langlands.ProfiniteCohomology.QZ.mk (1 / 2)
@Langlands.GaloisCohomology.realLocalDuality : ∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
  (w : NumberField.InfinitePlace K) [inst_2 : Fintype Gal(AlgebraicClosure w.Completion/w.Completion)] (hw : w.IsReal)
  (M : Rep.{u_1, u_1, u_1} (ULift.{u_1, 0} ℤ) Gal(AlgebraicClosure w.Completion/w.Completion))
  [inst_3 : Langlands.IsSmoothRep M] [inst_4 : Finite ↑M],
  (Function.Bijective
        ⇑(Langlands.GaloisCohomology.orderTwoDualityPairingZeroTwo (Langlands.GaloisCohomology.realInvariantQZ w) ⋯ ⋯
            M) ∧
      Function.Bijective
        ⇑(Langlands.GaloisCohomology.orderTwoDualityPairingZeroTwo (Langlands.GaloisCohomology.realInvariantQZ w) ⋯ ⋯
              M).flip) ∧
    (Function.Bijective
          ⇑(Langlands.GaloisCohomology.orderTwoDualityPairing (Langlands.GaloisCohomology.realInvariantQZ w) M ⋯) ∧
        Function.Bijective
          ⇑(Langlands.GaloisCohomology.orderTwoDualityPairing (Langlands.GaloisCohomology.realInvariantQZ w) M
                ⋯).flip) ∧
      Function.Bijective
          ⇑(Langlands.GaloisCohomology.orderTwoDualityPairingTwoZero (Langlands.GaloisCohomology.realInvariantQZ w) ⋯ ⋯
              M) ∧
        Function.Bijective
          ⇑(Langlands.GaloisCohomology.orderTwoDualityPairingTwoZero (Langlands.GaloisCohomology.realInvariantQZ w) ⋯ ⋯
                M).flip
```

## Source and licence

Ported from the repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>), commit `f1f6d65`, files
`src/GroundTheory/ProfiniteCohomology/RealPlaces/LocalDualityCup.lean` (lines 15–290),
`RealPlaces/LocalDuality.lean` (lines 13–312 and 329–358) and `RealPlaces/LocalDualityDefs.lean`
(lines 54–63). The repository has no licence file; its text is used with attribution (`licenses/RiemannHypothesis/SOURCE.md`). Changes: the source works in `Type`
with the real invariant `realInv` built from the quadratic invariant of its local class field theory
and two hypotheses on norms; here the invariant is a parameter `inv` with the property `hinv`, the
universe is arbitrary, and the source's declarations `realInv*`, `realDualityPairing*` become
`inv_cocycleTwo_eq*`, `orderTwoDualityPairing*`; `cupPairing_cocycleTwo_H0` and
`cupPairing_H0_cocycleTwo` become `cupPairing_cocycleTwo_zero` and `cupPairing_zero_cocycleTwo`;
`real_local_duality_of_orderTwo` becomes `orderTwoLocalDuality`. The Library's names replace the
source's (`unitsModule`, `rootsOfUnityModule`, `IsSmoothRep`, `zeroIso`, `coeffCochainsMap` for
`galUnits`, `galRootsOfUnity`, `IsDiscreteRep`, `H0Iso`, `cochainsMap`). The section on a real place
(`realInvariantQZ` to `realLocalDuality`) is new: it uses the Library's real invariant and complex
conjugation of `Langlands.GaloisCohomology.Global.BrauerSequence` in place of the source's
`LocalDualityPlace.lean`.

## References

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd edition (Springer 2008;
  corrected printing 2013), chapter VII, §2, Theorem (7.2.17), p. 390 (for `G = G(ℂ|ℝ)` and a
  finitely generated module `A` with `A' = Hom(A, ℂˣ)`, `H²(G, ℂˣ) ≅ ½ℤ/ℤ` and the cup product
  `Ĥⁱ(G, A') × Ĥ²⁻ⁱ(G, A) → H²(G, ℂˣ)` is perfect for all `i`; the proof there is by dévissage from
  `ℤ/2`, `ℤ`, `ℤ(1)`, the proof here by explicit cocycles).
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd edition (BookSurge 2006), chapter I, §4, p. 55
  (at an archimedean place `Hʳ(K_v, M)` means Tate's group, `H⁰(ℝ, M) = M^{Gal(ℂ/ℝ)}/N_{ℂ/ℝ}M`).
