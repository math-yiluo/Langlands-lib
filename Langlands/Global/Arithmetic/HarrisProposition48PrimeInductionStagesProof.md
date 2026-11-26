# Weak monomial induction in stages for the identity Mackey constituent

Module `Langlands.Global.Arithmetic.HarrisProposition48PrimeInductionStagesProof`.

`Langlands.Global.Harris.proposition48PrimeInductionStages` proves exactly
`Langlands.Global.Harris.Proposition48PrimeInductionStagesStatement` at arbitrary
independent universes `uF` (local field) and `uV` (spectral carrier), with no
added premise. Let `Q` be a problem with `E ⊆ E' ⊆ L`, Hecke character `ξ` of `E'`,
and `D` an intermediate field with `D ≤ Q.conjugateField 1` (that is,
`D ⊆ E'` inside `L`). If a cuspidal class `c` over `E` is a weak induction
(`IsoClass.IsWeakInductionOf`) of a cuspidal class `d` over `D`, and `d` is a
Mackey constituent of the identity double coset (a weak automorphic induction
of `Q.mackeyCharacter D 1`), then `c` is a weak automorphic induction of `ξ`.

## Source

- Michael Harris, *The local Langlands conjecture for GL(n) over a p-adic field,
  n < p*, Invent. Math. 134 (1998), 177–210 (registered source
  `harris-1998-local-langlands`), proof of Proposition 4.8, printed p.203
  (`math_9611226v1.tex`, lines 1655–1664): `Π = AI_{E_{t-1}/E} Π(e,t-1)`, and
  "It is thus clear that `Π` is a weak automorphic induction of **χ**", where
  the bold **χ** (macro `\bc`) is the Hecke character written `ξ` in the
  Library.
- J. Arthur and L. Clozel, *Simple algebras, base change, and the advanced
  theory of the trace formula* (1989), Chapter III: induction of unramified
  data is a relation between local components at almost all places, and it is
  transitive in towers.

The Lean proof follows this route: it composes the two unramified induction
relations at almost every place, through the tower of finite places.

## Declarations

General lemmas, independent of Proposition 4.8:

- `Langlands.Automorphic.Unramified.WeakInduction.finitePlacesAboveTower`: for
  number fields `K ⊆ E ⊆ M` with `IsScalarTower K E M` and a finite place `v` of
  `K`, the equivalence between pairs `(w, u)` with `w` a finite place of `E`
  above `v` and `u` a finite place of `M` above `w`, and the finite places of
  `M` above `v`. It sends `(w, u)` to `u` and `u` to `(u ∩ E, u)`.
- `Langlands.Automorphic.Unramified.WeakInduction.eventually_forall_finitePlacesAbove`:
  a property of almost all finite places of `E` holds, for almost all finite
  places `v` of `K`, at every place of `E` above `v`.
- `Langlands.Automorphic.Unramified.WeakInduction.isWeakInductionOf_of_isArithmeticWeakInductionOf`
  (weak induction in stages for spectral systems): if `s` over `K` is an
  arithmetic weak induction (`SpectralSystem.IsArithmeticWeakInductionOf`) of
  `t` over `E`, and `t` is a weak induction (`SpectralSystem.IsWeakInductionOf`)
  of a Hecke character `χ` of `M`, then `s` is a weak induction of `χ` for
  `M/K`.
- `Langlands.Automorphic.CuspidalOperatorRealization.IsoClass.HasSpectralSystem.sameEulerPolynomials`:
  two spectral systems attached to one cuspidal class, through presentations
  with carriers in possibly different universes, have the same Euler
  polynomials at almost all places.
- `Langlands.Automorphic.CuspidalOperatorRealization.IsoClass.IsWeakInductionOf.isWeakAutomorphicInductionOf`
  (weak automorphic induction in stages): for `K ⊆ E ⊆ M`, if `c` over `K` is a
  weak induction of `d` over `E` and `d` is a weak automorphic induction of `χ`,
  then `c` is a weak automorphic induction of `χ`. The two spectral systems of
  `d` supplied by the hypotheses may come from different presentations.

## Implemented proof

1. **Rank.** The arithmetic weak induction gives `n = m · [E : K]` and the weak
   induction of `χ` gives `m = [M : E]`. The tower law
   `Module.finrank_mul_finrank` gives `n = [M : K]`.
2. **Cofinite sets.** The weak induction of `χ` holds at all finite places `w` of
   `E` outside a finite set. Its image under `HeightOneSpectrum.under` is
   finite, so by `SpectralSystem.eventually_avoidsAbove` the property holds at
   every place above `v` for almost all `v`
   (`eventually_forall_finitePlacesAbove`). This is intersected with the
   cofinite set of the arithmetic weak induction.
3. **Unramifiedness.** Fix such a `v` and a place `u` of `M` above `v`, and let
   `w = u ∩ E`. Then `e(w|v) = 1` by the arithmetic weak induction, and
   `e(u|w) = 1` and `χ` is unramified at `u` by the weak induction of `χ` at `w`.
   `Ideal.ramificationIdx_tower` gives `e(u|v) = e(w|v) · e(u|w) = 1`.
4. **Euler factors.** Fix a family `ϖ` of uniformizers at the places of `M`
   above `v`. Its restriction to the places above `w` is a family of
   uniformizers above `w`, since the completion at `u` does not depend on the
   base. Then
   `L_v(s) = ∏_{w|v} L_w(t)(X^{f(w|v)})` (arithmetic weak induction) and
   `L_w(t) = ∏_{u|w} (1 - χ_u(ϖ_u) X^{f(u|w)})` (weak induction of `χ`). By
   `Polynomial.prod_comp`, each factor becomes `1 - χ_u(ϖ_u) X^{f(w|v) f(u|w)}`,
   and `Ideal.inertiaDeg_tower` gives `f(u|v) = f(w|v) · f(u|w)`. The double
   product is the product over the places `u` of `M` above `v`, by
   `Fintype.prod_equiv` along `finitePlacesAboveTower` and
   `Fintype.prod_sigma`.
5. **Aligning the systems of `d`.** The weak induction `c → d` supplies a system
   `t` of `d`, and the Mackey constituent supplies a possibly different system
   `t'` of `d`. Both come from presentations of realizations of `d`;
   `IsoClass.hasSpectralSystem_iff` moves them to one realization, and
   `CuspidalSpectralPresentation.spectralSystem_sameEulerPolynomials` gives
   `t.SameEulerPolynomials t'`. Then
   `SpectralSystem.IsArithmeticWeakInductionOf.of_sameEulerPolynomials` makes
   `s` an arithmetic weak induction of `t'`, and step 4 applies
   (`IsWeakInductionOf.isWeakAutomorphicInductionOf`).
6. **The identity double coset.** With `M = Q.mackeyField D 1` and the inclusion
   algebra `D → M` used by `IsMackeyConstituent`, the tower `E ⊆ D ⊆ M` is a
   scalar tower by definition. Step 5 gives that `c` is a weak automorphic
   induction of `Q.mackeyCharacter D 1` over `E`. The `E`-algebra isomorphism
   `Q.identityMackeyEquiv D hD : E' ≃ₐ[E] M` (which uses `D ≤ E'`) and
   `IsoClass.IsWeakAutomorphicInductionOf.arithmeticComap`, applied with the
   identity of `E` and this isomorphism, give that
   `arithmeticComap (RingEquiv.refl E) c = c` (`IsoClass.arithmeticComap_refl`)
   is a weak automorphic induction of the pullback of the Mackey character,
   which is `ξ` by `Proposition48Problem.identityMackeyEquiv_comap`.

No spectral rigidity or strong multiplicity one is used: the comparison of
the two systems of `d` uses only that two presentations of one cuspidal
realization have the same spherical spectra wherever both systems are defined
(`CuspidalSpectralPresentation.spectralSystem_eigenvalues_eq`).
