# Parts of the reciprocity law for cyclic cyclotomic extensions

This module collects the auxiliary results for the proof of the reciprocity law for cyclic
subextensions of cyclotomic extensions (reciprocity proof, task fb66219f). The proof itself
is in `Langlands.ClassField.Global.CyclicReciprocityProof`. The results fall into four
groups:

- archimedean invariants of carry classes;
- compatibility of the local Artin symbol with restriction to a cyclotomic subfield;
- the product over all finite places of the local cyclotomic symbols of a global unit;
- the sign of a norm, and complex conjugations in cyclotomic extensions.

The module defines two auxiliary functions, `realSignUnit` and `placeFactor`; everything
else is a theorem.

## Cyclotomic symbols (namespace `Langlands.Global.CyclotomicSymbol`)

- `localSymbol_cast`: for `m ∣ m'`, reducing the rational cyclotomic symbol
  `localSymbol m' p x ∈ (ℤ/m')ˣ` modulo `m` gives `localSymbol m p x`. The proof compares
  the reductions at every prime `q` (`eq_of_reduction`). At `q = p` both sides are inverse
  reductions of the same `p`-adic unit (`PadicInt.cast_toZModPow`). At `q ≠ p` both sides
  are powers of `p`.
- `normSymbolAt_eq_one_of_valued`: let `w` be a place of a number field `K` above a rational
  prime `p` with `p ∤ m`, and let `b` be a unit of `K_w` with `|b|_w = 1`. Then
  `normSymbolAt m p w b = 1`. The local norm of `b` is a `p`-adic unit (`localNorm_integral`
  applied to `b` and `b⁻¹`), and for `p ∤ m` the symbol of `x` is `p^{v_p(x)}`.

## Carry classes at infinite places (namespace `Langlands.ClassField.Global.CyclicReciprocity`)

Here `χ : Gal(E/F) → ℤ/n` is an injective character, `a ∈ Fˣ`, and `cyclicClass F E χ a` is
the Library's carry class of `a` and `χ` in `H²(Gal(E/F), Eˣ)`. `archimedeanInvariant w` is
the archimedean invariant of `Langlands.ClassField.Global.ReciprocityStatement`: for a
cocycle `f` and a nontrivial element `c` of the stabilizer of `w`, it is `1/2` if the real
part of `w(f(c, c) f(1, 1))` is negative and `0` otherwise; with trivial stabilizer it is `0`.

- `carry_of_two_torsion`: if `x ∈ ℤ/n` is nonzero with `x + x = 0`, then the carry of
  `(x, x)` is `1` and `2 x.val = n`.
- `eq_of_isConj`: two automorphisms of `E / F` that act as complex conjugation on the
  embedding of `w` are equal.
- `archimedeanInvariant_cyclicClass`: if `c ≠ 1` stabilizes `w`, then
  `archimedeanInvariant w (cyclicClass F E χ a)` is `χ(c).val / n` if `w(a) < 0`, and `0`
  otherwise. The element `c` is the complex conjugation at `w`, so `χ(c)` has order two and
  `χ(c).val / n = 1/2`. The carry cocycle takes the value `a` at `(c, c)` and `1` at
  `(1, 1)`.
- `archimedeanInvariant_eq_zero_of_stabilizer`: with trivial stabilizer the archimedean
  invariant of every class is `0`.
- `re_embedding_algebraMap`: for `w` above `v`, the real parts of `w(x)` and `v(x)` agree for
  `x ∈ F`.
- `archimedeanInvariant_eq_zero_of_isComplex`: archimedean invariants vanish at places
  above complex places of `F`.
- `archimedeanInvariant_cyclicClass_of_isConj`: if `c` acts as complex conjugation at `w`
  (`c = 1` when `w` is real), then `archimedeanInvariant w (cyclicClass F E χ a)` is
  `χ(c).val / n` if `w(a) < 0`, and `0` otherwise.

## The Artin symbol and restriction

Let `ζ ∈ L` be a primitive `m`-th root of unity, `ζ' ∈ L'` a primitive `m'`-th root of unity,
`m ∣ m'`, and `L → L'` a map over `F` sending `ζ` to a power `ζ'^k`.

- `autToPow_restrictNormal`: for `σ ∈ Gal(L'/F)`, the exponent by which `σ|_L` acts on `ζ` is
  the reduction modulo `m` of the exponent by which `σ` acts on `ζ'`.
- `artinSymbol_restrictNormal`: the local Artin symbol `artinSymbol` of
  `Langlands.ClassField.Global.LocalSymbolIdentity` for `L'` restricts on `L` to the one for
  `L`. This combines the previous result with `localSymbol_cast`.

## The finite product formula

- `rationalPlace_eq_of_liesOver`, `normSymbolAt_congr`: bookkeeping for the rational place
  below a finite place.
- `finprod_eq_finprod_placesAbove`: a finite product over the finite places of `F` equals the
  product over the rational primes `p` of the products over the places of `F` above `p`.
- `natCast_mem_of_dvd`: if the residue characteristic of `v` divides `M`, then `M ∈ v`.
- `normSymbolAt_algebraMap_eq_one`: if `a ∈ Fˣ` is a unit at `v` and `m ∉ v`, the symbol of `a`
  at `v` is `1`.
- `mulSupport_normSymbolAt_finite`: the symbol of `a` at `v` is `1` for all but finitely many
  `v`.
- `finprod_normSymbolAt` (finite product formula): for `a ∈ Fˣ`,

  `∏_v normSymbolAt m (rationalPlace v) v a = symbolProduct m (N_{F/ℚ} a)`,

  the product over all finite places `v` of `F` on the left, and the product over all primes
  `p` of the rational symbols of `N_{F/ℚ}(a)` on the right. It follows from the regrouping
  above and the Library's `ratLocalSymbol_norm_eq_prod`: the global norm is the product of
  the local norms at the places above `p`.

## The sign of a norm

- `realSignUnit m : ℝˣ →* (ℤ/m)ˣ` sends `x` to `-1` if `x < 0` and to `1` otherwise.
  `signUnit_eq_realSignUnit`: the Library's `signUnit m` on `ℚˣ` is its restriction.
- `placeFactor w x` is `w(x)`, a real number, at a real place `w`, and `|w(x)|²` at a complex
  place.
- `prod_filter_mk_eq`: the product of `φ(x)` over the complex embeddings `φ` defining `w` is
  `placeFactor w x`.
- `algebraMap_norm_eq_prod`: `N_{F/ℚ}(x) = ∏_w placeFactor w x` over the infinite places of
  `F`, from `Algebra.norm_eq_prod_embeddings`.
- `placeFactor_ne_zero`: `placeFactor w x ≠ 0` for `x ≠ 0`.
- `signUnit_norm`: `signUnit m (N_{F/ℚ} a)` is the product over the infinite places `w` of
  `-1` if `w` is real and `w(a) < 0`, and of `1` otherwise.

## Complex conjugations

- `apply_eq_inv_of_isConj`: an automorphism acting as complex conjugation for some complex
  embedding sends every root of unity `ζ` to `ζ⁻¹`, since `|ψ(ζ)| = 1`.
- `autToPow_eq_neg_one`: an automorphism with `τ(ζ) = ζ⁻¹` has `autToPow τ = -1`.
- `exists_isConj_restrict`: let `L / F` be Galois, `E ⊆ L` normal over `F`, and `w` a place
  of `E` above a real place of `F`. There is `τ ∈ Gal(L/F)` acting as complex conjugation
  for some complex embedding of `L` and whose restriction to `E` acts as complex conjugation
  on the embedding of `w`. Take `τ` from an extension `ψ` of the embedding of `w` to `L`
  (`ComplexEmbedding.exists_comp_symm_eq_of_comp_eq`, comparing `ψ` with its conjugate).

## Provenance

These are the ingredients of the reciprocity law for cyclic cyclotomic extensions, Case 1 of
the proof of Theorem 6 in Artin–Tate, Chapter VII §3, printed p.45 (PDF p.54). There the
local invariants of a class `κ(a) ∪ δχ` are `χ` of the local norm residue symbols of `a`,
and their sum vanishes because the product of the symbols of a global element is `1`.
The archimedean computation follows the description of `H²(ℂ/ℝ, ℂˣ)` in Milne,
*Class Field Theory*, Chapter IV §4, "The real numbers", printed p.139 (PDF p.148).

Artin–Tate prove Case 1 only over `ℚ`, and reduce a general base field to `ℚ` by inflation
and transfer. This project works over `F` directly. The finite product formula and the sign
formula reduce the product of the symbols over the places of `F` to the product over the
places of `ℚ` through the norm `N_{F/ℚ}`. This route, and the formulations through
`normSymbolAt`, `artinSymbol`, `archimedeanInvariant` and `placeFactor`, are internal to
this project.
