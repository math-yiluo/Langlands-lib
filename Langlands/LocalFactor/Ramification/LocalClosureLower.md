# Lower ramification groups of finite levels through the valuation of a separable closure

The module `Langlands.LocalFactor.Ramification.LocalClosureLower` compares, for a
nonarchimedean local field \(K\) of either characteristic, a separable closure \(\Omega\) of
\(K\) and a finite Galois subextension \(L\) of \(\Omega\) (a
`FiniteGaloisIntermediateField K Ω`), the Library's finite-level structure
`localTopologicalData K L` with the valuation `closureValuation K Ω` of \(\Omega\)
(`Langlands/Galois/Local/AbsoluteDefinitions.lean`, the spectral valuation extending the
valuation of \(K\)). It reads the Library's lower ramification groups
`lowerRamificationGroup (localTopologicalData K L) K i` off `closureValuation K Ω`. This is
Serre, *Local Fields*, IV §1, Lemma 1 b) (p. 61): \(s\in G_i\) exactly when
\(v_L(s(a)-a)\ge i+1\) for every integer \(a\) of \(L\), written multiplicatively with an element
\(\pi\) of \(L\) of maximal valuation \(<1\) in place of the normalized valuation \(v_L\).

## Compatible valuations (section `Generic`)

For a field \(L\) with a valuative relation and a valuation \(w\) compatible with it
(`Valuation.Compatible`), with values in any linearly ordered commutative group with zero:

- `compatible_le_iff`, `compatible_mem_integer_iff`, `compatible_mem_maximalIdeal_iff`:
  \(w\) compares elements as the canonical valuation `valuation L` does, the canonical integers
  `𝒪[L]` are the elements with \(w\le 1\) and their maximal ideal is cut out by \(w<1\);
- `compatible_irreducible_lt_one`, `compatible_irreducible_pos`: an irreducible element
  \(\varpi\) of `𝒪[L]` has \(0<w(\varpi)<1\).

If `𝒪[L]` is a discrete valuation ring and \(\varpi\) is irreducible in it:

- `compatible_mem_maximalIdeal_pow_iff`: \(y\in\mathfrak m^n\) exactly when
  \(w(y)\le w(\varpi)^n\) (as \(\mathfrak m^n=(\varpi^n)\), and divisibility in a valuation ring
  is comparison of valuations, `Valuation.Integers.dvd_iff_le`);
- `compatible_le_of_lt_one`: \(w(y)<1\) implies \(w(y)\le w(\varpi)\);
- `compatible_exists_eq_pow`: every nonzero \(y\) with \(w(y)\le 1\) has
  \(w(y)=w(\varpi)^n\) for some \(n\) (`IsDiscreteValuationRing.eq_unit_mul_pow_irreducible`).

## Automorphisms moving products (section `Moves`)

For a valuation \(v\) with values in \(\mathbb R_{\ge 0}\) on a commutative ring and a ring
endomorphism \(f\) preserving \(v\):

- `map_sub_mul_le`: if \(v(f(a)-a)\le c\,v(a)\) and \(v(f(b)-b)\le c\,v(b)\), then
  \(v(f(ab)-ab)\le c\,v(ab)\), from \(f(ab)-ab=f(a)(f(b)-b)+(f(a)-a)b\);
- `map_sub_pow_le`: the same bound for the powers of \(a\).

## Integer indexing (section `IntegerIndex`)

- `mem_lowerRamificationGroupInt_iff`: for the Library's integer-indexed lower groups
  `lowerRamificationGroupInt T K i`, \(g\) lies in it exactly when \(i<0\) or \(g\) lies in
  `lowerRamificationGroup T K i.toNat`; this unfolds `lowerGroupInt`, which is the whole group
  below \(0\).

## Finite levels (section `Closure`)

Here \(v\) is `closureValuation K Ω`.

- `levelValuation K Ω L` is the restriction of \(v\) to \(L\);
  `levelValuation_eq_spectralValuation` identifies it with the spectral valuation of \(L\) over
  \(K\) (`spectralNorm.eq_of_tower`), and `levelValuation_compatible` states that it is
  compatible with the valuative relation of `localTopologicalData K L`, which is
  `LocalField.canonicalValuativeRel K L`, the relation of that spectral valuation.
- `mem_localIntegers_iff`: the integers `(localTopologicalData K L).Integers` are the elements
  of \(L\) with \(v\le 1\).
- `exists_levelUniformizer`: there is \(\pi\in L\) with \(0<v(\pi)<1\) and
  \(v(y)\le v(\pi)\) for every \(y\in L\) with \(v(y)<1\): an irreducible element of the
  integer ring, a discrete valuation ring since \(L\) is a nonarchimedean local field.
- `exists_irreducible_eq_of_isMax`: conversely, every \(\pi\in L\) with \(v(\pi)<1\) and that
  maximality property has the valuation of an irreducible element of the integer ring.
- `exists_closureValuation_eq_pow`: for such \(\pi\), every nonzero integral \(y\in L\) has
  \(v(y)=v(\pi)^n\) for some \(n\).
- `le_pow_succ_of_lt_pow`: for such \(\pi\) with \(v(\pi)>0\), \(v(y)<v(\pi)^n\) implies
  \(v(y)\le v(\pi)^{n+1}\) for \(y\in L\) (apply the maximality to \(y/\pi^n\)).
- `mem_lowerRamificationGroup_iff_closureValuation`: for such \(\pi\), an automorphism \(g\)
  of \(L\) over \(K\) lies in `lowerRamificationGroup (localTopologicalData K L) K i` exactly
  when \(v(g(x)-x)\le v(\pi)^{i+1}\) for every \(x\in L\) with \(v(x)\le 1\). The Library
  defines the group by \(g(x)-x\in\mathfrak m^{i+1}\) for all integers \(x\)
  (`mem_lowerRamificationGroup`); `compatible_mem_maximalIdeal_pow_iff` with an irreducible
  element of the valuation of \(\pi\) translates the condition.

Every declaration of the module depends only on `propext`, `Classical.choice` and
`Quot.sound`.
