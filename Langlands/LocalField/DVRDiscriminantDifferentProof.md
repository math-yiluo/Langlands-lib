# The discriminant of an extension of DVRs is the norm of its different: proof

This module proves `Langlands.LocalField.DVRDiscriminantDifferent` (`DVRDiscriminantDifferentStatement`):

```lean
theorem dvrDiscriminantDifferent : DVRDiscriminantDifferent.{uA, uB, uK, uL, uι}
```

(name space `Langlands.LocalField`), with the level parameters of the statement in its order.

## Proof outline

1. **Monogenicity.** `B = A[x]` for some `x` (`Ramification.exists_adjoin_singleton_eq_top_of_isSeparable_residueField`,
   `LocalFactor/Ramification/Monogenic`, Serre III §6 Proposition 12). Let `pb` be the power basis
   `1, x, …, x^{n-1}` (Mathlib's `PowerBasis.ofAdjoinEqTop'`) and `f` the minimal polynomial of `x`.
2. **Discriminant of the power basis.** Localizing at `A⁰` turns `pb` into a power basis of `L` over
   `K` with generator `x` (`localizedPowerBasis`), whose discriminant is the image of `disc_A(pb)`
   (Mathlib's `Algebra.discr_localizationLocalization`). Over the fields,
   `disc = (−1)^{n(n−1)/2} N_{L/K}(f'(x))` (Mathlib's `Algebra.discr_powerBasis_eq_norm`); the
   minimal polynomial over `K` is the image of `f` (`minpoly.isIntegrallyClosed_eq_field_fractions`)
   and the norm over `K` is the image of the norm over `A` (`Algebra.norm_localization`). By
   injectivity of `A → K`, `disc_A(pb) = ± N_{B/A}(f'(x))` (`discr_powerBasis_eq_norm_of_isFractionRing`).
3. **Different of a monogenic extension.** Mathlib's `conductor_mul_differentIdeal` gives
   `𝔠 · 𝔇 = (f'(x))` with `𝔠` the conductor of `A[x]` in `B`, which is `B` here
   (`conductor_eq_top_of_adjoin_eq_top`); so `𝔇 = (f'(x))` (`differentIdeal_eq_span_aeval`; Serre III §6,
   Corollary 2 of Proposition 11).
4. **Norm.** `N(f'(x))` generates the norm of the principal ideal `(f'(x))` (Mathlib's
   `Ideal.spanNorm_singleton`, `Algebra.intNorm_eq_norm`), and `±1` is a unit; so
   `(disc_A(pb)) = N(𝔇)`.
5. **Any basis.** For two bases `e`, `b` indexed by `ι`, `b = e · P` with `P = e.toMatrix b`, and
   `disc(b) = det(P)² disc(e)` (Mathlib's `Algebra.discr_of_matrix_vecMul`) with `det P` a unit
   (`Module.Basis.isUnit_det`) (`span_discr_eq_of_basis`). The power basis is reindexed along
   `Module.Basis.indexEquiv` (`Algebra.discr_reindex`).
6. **Valuation.** If `𝔇 = m_B^d`, then `N(𝔇) = N(m_B)^d = m_A^{f d}` (the norm is multiplicative;
   Mathlib's `Ideal.relNorm_eq_pow_of_isMaximal`, which needs separability of the fraction fields in the
   form `FractionRing A → FractionRing B`, transported from `K → L` as in Mathlib's `Different`;
   `isSeparable_fractionRing`).

## Declarations, in order

Name space `Langlands.LocalField.DiscriminantDifferent` unless stated.

- `span_discr_eq_of_basis {ι} [Fintype ι] [DecidableEq ι] (e b : Module.Basis ι A B) :
  Ideal.span {Algebra.discr A b} = Ideal.span {Algebra.discr A e}` (any commutative rings).
- `localizedPowerBasis (K L) (pb : PowerBasis A B) : PowerBasis K L`.
- `discr_powerBasis_eq_norm_of_isFractionRing (K L) (pb : PowerBasis A B) :
  Algebra.discr A pb.basis = (-1) ^ (Module.finrank K L * (Module.finrank K L - 1) / 2) *
    Algebra.norm A (aeval pb.gen (derivative (minpoly A pb.gen)))`.
- `differentIdeal_eq_span_aeval (K L) (x : B) (hx : Algebra.adjoin A {x} = ⊤)
  (hxL : Algebra.adjoin K {algebraMap B L x} = ⊤) :
  differentIdeal A B = Ideal.span {aeval x (derivative (minpoly A x))}`.
- `span_discr_eq_spanNorm (K L) {ι} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι A B) :
  Ideal.span {Algebra.discr A b} = Ideal.spanNorm A (differentIdeal A B)`.
- `isSeparable_fractionRing (K L) : Algebra.IsSeparable (FractionRing A) (FractionRing B)`.
- `span_discr_eq_maximalIdeal_pow (K L) {ι} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι A B)
  (d : ℕ) (hd : differentIdeal A B = maximalIdeal B ^ d) :
  Ideal.span {Algebra.discr A b} = maximalIdeal A ^ ((maximalIdeal B).inertiaDeg A * d)`.
- `Langlands.LocalField.dvrDiscriminantDifferent : DVRDiscriminantDifferent`.

The hypotheses of the lemmas are those of the statement (DVRs, fraction fields, separability,
integral closure, finiteness, separable residue extension), with `Module.IsTorsionFree A B` and
`Module.Free A B` as instance arguments.

## Literature

Serre, *Local Fields*, GTM 67, 1979, Chapter III: §3 Proposition 6, printed p. 50
(`𝔡_{B/A} = N_{L/K}(𝔇_{B/A})`, proved there through the module index `χ_A(B*/B)`; the Library's proof
goes through a power basis instead); §6 Proposition 11 and its Corollaries 1 and 2, printed
pp. 55–57 (`(f'(x)) = 𝔠 · 𝔇`, and `𝔇 = (f'(x))` when `B = A[x]`; Serre's Lemma 2 computes the
sign `(−1)^{n(n−1)/2}`); Proposition 12, printed p. 57 (monogenicity). PDF page = printed page + 7.
