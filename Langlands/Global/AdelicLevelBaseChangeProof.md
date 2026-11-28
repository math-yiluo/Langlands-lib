# Proof of scalar extension of adelic level rings

The theorem `adelicLevelBaseChange` proves `AdelicLevelBaseChangeStatement`
as the pair of `AdelicLevelBaseChange.numberFieldAdelicLevelBaseChange`
(number fields, every finite \(S\subseteq T\) of finite places) and
`AdelicLevelBaseChange.curvePlaceAdelicLevelBaseChange` (global function
fields over a finite constant field, every nonempty finite \(S\subseteq T\)
of places). For \(\mathcal O_{F,S}\subseteq\mathcal O_{F,T}\) and
\(\mathbb A_{F,S}\subseteq\mathbb A_{F,T}\) the isomorphism
\[
\mathcal O_{F,T}\otimes_{\mathcal O_{F,S}}\mathbb A_{F,S}\simeq\mathbb A_{F,T},
\qquad b\otimes a\mapsto b\cdot a,
\]
is linear over \(\mathcal O_{F,T}\). This is the identity stated in the
paragraph after Remark 3.5 on p. 6 of Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (2011). The Lean proof follows
the argument below, which shows that both inclusions are localizations
away from one element.

## A denominator with prescribed support

The proof first finds a nonzero \(d\) in the global field \(F\) whose
valuation is \(<1\) at each place of \(T\setminus S\) and \(=1\) at each
place outside \(T\).

- The private lemma `exists_generator_with_support` takes a Dedekind
  domain \(R\) with finite class group and a finite set \(E\) of
  height-one primes. It multiplies the elements of
  `exists_primePowerGenerator` (module
  `Langlands.Global.FiniteConstantChartPrimeGenerator`) over \(E\). The
  product is nonzero and lies in exactly the primes of \(E\).
- For a number field, `numberField_exists_level_denominator` applies it to
  the ring of integers, whose class group is finite by Mathlib's
  `NumberField.RingOfIntegers.instFintypeClassGroup`, with
  \(E=T\setminus S\). Mathlib's `valuation_lt_one_iff_mem` and
  `valuation_eq_one_iff_notMem` turn prime membership into the valuation
  conditions.
- For a function field, `curvePlace_exists_level_denominator` picks
  \(v_0\in S\). It takes \(s\in F\) with its only pole at \(v_0\), from
  `exists_curvePlace_singlePole` (module
  `Langlands.Global.CurvePlaceSinglePoleProof`). The element \(s\) is
  transcendental over \(k\), so \(F\) is finite over \(k(s)\). The
  normalized chart `CurveModel.chartRing k {s}`, the integral closure of
  \(k[s]\) in \(F\), has a finite class group by
  `finite_classGroup_normalizedCurveChart`. Each place \(w\notin S\) has
  \(s\) in its valuation ring. So \(w\) is the place of the height-one
  prime `CurveModel.primeOfValuationSubring` of the chart, by
  `FiniteConstantCurveChart.ofHeightOneSpectrum_center`. Then
  `exists_generator_with_support` with \(E\) the centres of the places in
  \(T\setminus S\) gives \(d\). Its valuation is \(\le 1\) at every place
  outside \(S\), since the chart lies in those valuation rings. It is
  \(<1\) at exactly the centres in \(E\).

This is the only use of \(S\ne\varnothing\).

## Both inclusions are away localizations

- `exists_level_exponent` is the finiteness step. Let \(\delta\) be the
  family of valuations of \(d\) and let \(\alpha\) be a family of values
  that is \(\le 1\) outside \(T\). Then one exponent \(n\) gives
  \(\delta_v^n\alpha_v\le 1\) for every \(v\notin S\). The exponent is the
  sum of local exponents over the finite set \(T\setminus S\). Each local
  exponent comes from Mathlib's `MulArchimedean.arch` for the value
  monoid `WithZero (Multiplicative ℤ)`. Outside \(T\) the valuation of
  \(d\) is \(1\), so the bound there is the hypothesis on \(\alpha\).
- `isLocalizationAway_subringInclusion` shows the following. If
  \(A\le B\) are subrings of a commutative ring, \(d\in A\) is a unit in
  \(B\), and a power of \(d\) brings each element of \(B\) into \(A\),
  then the inclusion makes \(B\) the localization of \(A\) away from
  \(d\).

The element \(d\) lies in \(\mathcal O_{F,S}\) and \(d^{-1}\) lies in
\(\mathcal O_{F,T}\). Applying `exists_level_exponent` to the
valuations of an element of \(\mathcal O_{F,T}\) gives the localization
\(\mathcal O_{F,T}=\mathcal O_{F,S}[1/d]\).

For the level rings the same lemma is applied to the valuations of the
completed coordinates at the places outside \(S\). For number fields
these come from `finiteProjection`, and `valued_finiteProjection_diagonal`
identifies the coordinate valuation of the diagonal of \(d\) with
\(v(d)\). For function fields `curvePlace_completed_valuation` does the
same through `RestrictedProduct.evalRingHom`. The archimedean factors of
a number field and the factors at places of \(S\) carry no integrality
condition. So \(\mathbb A_{F,T}\) is the localization of
\(\mathbb A_{F,S}\) away from the image of \(d\).

## The pushout

`exists_pushout_equiv` takes a commutative square of rings in which
\(R\to B\) is the localization away from \(d\) and \(A\to C\) is the
localization away from the image of \(d\). Mathlib's
`Algebra.isLocalization_iff_isPushout`, with
`Algebra.algebraMapSubmonoid_powers`, makes the square a pushout, and
`Algebra.IsPushout.comm` swaps its sides. Then
`Algebra.IsPushout.equiv` gives the \(B\)-algebra isomorphism
\(B\otimes_R A\simeq C\), and `Algebra.IsPushout.equiv_tmul` evaluates
it on simple tensors as \(b\otimes a\mapsto b\cdot a\).

Each base-change theorem applies `exists_pushout_equiv` with
\(R=\mathcal O_{F,S}\), \(B=\mathcal O_{F,T}\), \(A=\mathbb A_{F,S}\) and
\(C=\mathbb A_{F,T}\). The algebra structures are those of the
statement: `numberFieldSIntegersMap`, `numberFieldAdeleLevelMap` and
`numberFieldAdeleLevelDiagonal`, or their `curvePlace` counterparts. So
the isomorphism and its value on \(b\otimes a\) are those asserted.
