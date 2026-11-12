# Harris (1999), Theorem 5.9(i): a pure compatible family attached to `Π`

Author: Worker 34. This module states part (i) of Harris's Theorem 5.9 over
the Library's actual cuspidal classes and genuine `λ`-adic Galois
representations. The statement is a `Prop` definition; nothing here proves
it.

## Source

M. Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), 299-318. Registered original
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

- §1, printed p.301: `E` is a totally real number field and `𝒦` a totally
  imaginary quadratic extension of `E`, `c` the nontrivial element of
  `Gal(𝒦/E)`; `n > 1`.
- §4, printed p.308: "We return to the framework of [H1, H2] ... Thus `𝒦` is
  assumed to contain an imaginary quadratic field `𝒦₀`."
- §5, printed p.313, equation (5.6) and the paragraph before it: a `λ`-adic
  representation is *pure of weight `m`* if its Frobenius eigenvalues at almost
  all unramified places are algebraic numbers `β` with `|β| = Nw^{m/2}` for
  every complex absolute value; the normalized local Artin `L`-function is
  `L_w(s, σ) = ∏_β (1 - (β/|β|) Nw^{-s})^{-1}`, `β` running over the
  eigenvalues of a geometric Frobenius.
- §5, printed p.314, the paragraph before Theorem 5.9: `Π` is a cuspidal
  automorphic representation of `GL(n, 𝒦)` of cohomological type, that is
  `Π_∞` has `(𝔤, K_∞)`-cohomology with coefficients in some
  finite-dimensional representation of `GL(n, 𝒦_∞)`.
- Theorem 5.9, printed pp.314-315: "Assume the Galois conjugate `Π^c` of `Π`
  is isomorphic to the contragredient `Π̌`. Let `v` be a finite place of `𝒦`,
  split over `K`, and suppose the local component `Π_v` at `v` is
  supercuspidal. (i) (Clozel, Kottwitz) There is a number field `C` and a
  compatible family of `λ`-adic representations `σ_λ(Π)` of `Gal(𝒦̄/𝒦)`, pure
  of some weight `m`, where `λ` runs over finite places of `C`, such that, for
  almost all finite places `w` of `𝒦` at which `σ(Π)` and `Π_w` are
  unramified, we have equality of local Euler factors
  `L_w(s, σ_λ(Π)) = L_w(s, Π_w)`. Here the left-hand side is the normalized
  local Artin `L`-function and the right-hand side is the standard
  `L`-function of the unramified representation `Π_w`."

The proof (p.315) cites Clozel 1991 under a parity hypothesis, removed in
Clozel 1993; those inputs are separate statements of this task.

## Library objects used

- `CuspidalOperatorRealization.IsoClass 𝒦 r` (published): irreducible
  cuspidal classes of `GL_{r+1}(𝔸_𝒦)`.
- `IsRegularAlgebraic` (published `Langlands/Automorphic/RegularAlgebraic`):
  Clozel's regular algebraic infinitesimal character, used for cohomological
  type as in the published Harris Proposition 4.8 statement.
- `IsConjugateSelfDual` (published
  `Langlands/Automorphic/ConjugateContragredient`): `π^∨ ≅ π ∘ c` for the CM
  conjugation `IsCMField.complexConj 𝒦`, which is the nontrivial element of
  `Gal(𝒦/𝒦⁺)`.
- `Harris.conjPlace 𝒦 v` (published `Langlands/Global/Arithmetic/HarrisSetup`):
  the complex-conjugate place `c(v)`.
- `HasSupercuspidalComponent` (published
  `Langlands/Automorphic/SupercuspidalComponent`): some actual spectral
  presentation of a representative has a supercuspidal local component at
  `v`.
- `Collection`, `IsPureCompatible`, `HasRank` (published
  `Langlands/Galois/CompatibleFamily`), and
  `CuspidalOperatorRealization.IsoClass.IsWeaklyAssociated` (published
  `Langlands/Galois/WeakAssociation`, introduced with the Harris 1998
  Theorem 1.2 statement).

## Statement

`Langlands.GaloisRepresentation.Harris1999Theorem59iStatement` quantifies over

- a number field `𝒦 : Type u𝒦` with instances `IsCMField 𝒦` and
  `CompactSpace (AdeleQuotient 𝒦)`. A CM field is a totally imaginary
  quadratic extension of its maximal totally real subfield `𝒦⁺`, which is
  Harris's `E`. The compactness instance is required by the published cuspidal
  classes and proved by the published `compactSpace_adeleQuotient`;
- an intermediate field `𝒦₀` of `𝒦/ℚ` of degree 2 that is totally complex (an
  imaginary quadratic subfield, the framework of §4);
- `r` with `1 ≤ r`, so `n = r + 1 > 1` as in §1;
- a cuspidal class `c` of `GL_{r+1}(𝔸_𝒦)` and a finite place `v` of `𝒦`.

Hypotheses: `c` is regular algebraic (cohomological type); `c` is conjugate
self-dual (`Π^c ≅ Π̌`); `Harris.conjPlace 𝒦 v ≠ v` (`v` is split over `𝒦⁺`);
and `c` has a supercuspidal component at `v`.

Conclusion (i): there are a number field `L : Type uL` (Harris's `C`), an
embedding `ι : L → ℂ`, a collection `R : Collection 𝒦 L ∅` of genuine `λ`-adic
representations of `Gal(𝒦̄/𝒦)` for every finite place `λ` of `L` (no place is
excluded), with carriers in universe `uV`, and an integer `m`, such that

- `R` is compatible and pure of weight `m` (`IsPureCompatible ∅ R m`);
- every `R λ` has rank `r + 1`;
- `R` is weakly associated to `c` (`IsWeaklyAssociated c ι ∅ R`): some
  spectral system `s` of an actual presentation of `c` (local factor carriers
  in universe `uW`) and common Euler polynomials `P_w ∈ L[X]` of `R` satisfy,
  at all but finitely many places `w`, that the unitary normalization at `ι`
  of `P_w` is the Euler polynomial of `s` at `w`. This is the equality of the
  normalized local Artin factor (5.6) with the standard local factor.

## Conventions and scope

- **"Split over `K`".** The printed hypothesis reads "a finite place of `𝒦`,
  split over `K`"; no field `K` is defined in §1 or §5 of the paper. The
  statement reads it as: the place of `E = 𝒦⁺` below `v` splits in `𝒦`, which
  is `c(v) ≠ v`. This is the reading used in the proof on p.315 (a totally
  real quadratic `E'/E` "in which `v` splits", with `Π'` supercuspidal at the
  two places of `𝒦'` dividing `v`), in Corollary 5.10 ("a place of `E` that
  splits in `𝒦`"), and in Clozel's hypotheses (a place of `F` split in
  `F_c`).
- **Contextual hypotheses.** `n > 1` (§1) and `𝒦 ⊇ 𝒦₀` imaginary quadratic
  (§4) are retained. Without an imaginary quadratic subfield, Clozel's method
  gives representations of the Galois group of a reflex field that can be
  larger than `𝒦` (Clozel 1991, Théorème 5.3 and Définition 5.2). The §4
  assumptions that a chosen prime `p` splits in `𝒦₀` and that `v` divides `p`
  belong to the `p`-adic uniformization of Theorem 5.7. Theorem 5.9 concerns
  varieties that need not admit that uniformization (p.314), and its
  hypotheses on `v` are only the ones stated above, so these assumptions are
  not imposed.
- **Cohomological type.** As in the Harris 1998 Theorem 1.2 statement,
  cohomological type is encoded by `IsRegularAlgebraic`. The equivalence with
  nonvanishing `(𝔤, K)`-cohomology for cuspidal representations is a theorem
  of Clozel that the Library does not prove.
- **Coefficient places.** Harris's `λ` runs over the finite places of `C`, so
  the excluded set is empty. A conclusion with a nonempty excluded set would be
  weaker.
- **Rank.** The rank `r + 1` is not printed in (i). It follows from the
  matching at one place, since the Euler polynomial of a representation of
  rank `d` has degree `d`, and is stated explicitly.
- **Weights.** The weight `m` is existential, as printed. The unitary
  normalization makes the matching independent of `m`; Frobenius is
  geometric.
- **Embedding.** One embedding `ι` of the coefficient field is existential.
  Clozel's coefficient field is a subfield of `ℂ` (1991, Théorème 5.3(i)).
  Purity makes the radii `|β|` in (5.6) independent of the complex absolute
  value, but the normalized Euler polynomial can depend on the embedding (see
  `Langlands/Galois/WeakAssociation`), so the matching is asserted for the
  chosen `ι`.
- **Unramified matching only.** No ramified local compatibility is asserted.
  Part (ii), the identification of the restriction to a decomposition group at
  `v` with `σ(Π_v)`, belongs to the parent task and is not stated here.
