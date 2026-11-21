# Equivalent irreducible cuspidal `L²` summands of `GL_n` have equivalent realizations

Module `Langlands.Automorphic.GeneralLinearCuspidalSummandEquivalenceStatement`, namespace
`Langlands.Automorphic.GroupSchemeFunctions`. It states one proposition,
`GeneralLinearCuspidalSummandEquivalenceStatement`, and contains no proof.

The module uses the vocabulary of the published
`Langlands.Automorphic.GeneralLinearCuspidalSummandRealizationStatement`, which it imports. The
`L²` model is the full almost-everywhere cuspidal subspace `S = fullAEL2CuspidalSubmodule` of
`L²` of the positive-central rational quotient of `GL_{r+1}`, with its right regular action
`πc = fullAEL2CuspidalBoundedRightAction`. The model by forms is
`CuspidalOperatorRealization F r`. The predicate `IsGeneralLinearFormClass F r T i φ f` says that
the `L²` class `φ` is the class of the function that the form `f` induces on the quotient. The
Markdown of that module explains both models and their correspondence with Getz–Hahn.

The two local instances supply `IsAffine` and `Smooth` for the general linear group scheme from
the published `isAffine_groupScheme` and `smoothStatement`, as in the imported module. Their
names are new, so the module can be imported together with the modules that define the other
copies.

## The statement

Throughout, `GLG = GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)`.

The data are those of `GeneralLinearCuspidalSummandRealizationStatement`:

* a number field `F : Type u` whose adele quotient is compact (an instance argument, which
  `CuspidalOperatorRealization` requires; the published `compactSpace_adeleQuotient` supplies
  it for every number field), and `r : ℕ`;
* `hPD : ParabolicDynamicStatement`, the standing structural hypothesis of the Library's
  cuspidal `L²` spaces;
* a commutative group scheme `T` with a central morphism `i : T → GLG` (`IsCentral i`), an
  isomorphism `e` of `T` with a split torus on a finite type `I`, and injective character
  restriction `characterRestrict i` with finite-index image (an instance argument);
* right invariance of Haar measure on the norm-one subgroup `GLG(𝔸)¹` (an instance argument).

Let `S` and `πc` be as above, with `hG` the published
`GroupScheme.isConnectedReductive_generalLinear F (Fin (r + 1))`. The statement says: let `P` and
`Q` be submodules of `S`, each nonzero, closed, invariant under `πc a` for every
`a ∈ GLG(𝔸)`, and minimal (every closed invariant submodule is `0` or the whole). Let
`U : P ≃ₗᵢ[ℂ] Q` be a complex-linear isometric equivalence with `U (πc a x) = πc a (U x)` for
all `a` and all `x ∈ P`. (The invariance proof `hPi` only forms the element `πc a x` of `P`.)
Let `R, R' : CuspidalOperatorRealization F r` and let `Φ : R.Space → S` and
`Φ' : R'.Space → S` be complex-linear maps such that

* `IsGeneralLinearFormClass F r T i (Φ f) (R.realization.toContinuous f)` for every vector `f`
  of `R`, and the closure of the image of `Φ` is `P`;
* `IsGeneralLinearFormClass F r T i (Φ' f) (R'.realization.toContinuous f)` for every vector
  `f` of `R'`, and the closure of the image of `Φ'` is `Q`.

Then `Nonempty (R.Equivalence R')`: there is a linear isomorphism `R.Space ≃ R'.Space` that
commutes with the finite adelic translations, the translations by the standard maximal compact
subgroup at the archimedean places, and the action of the enveloping algebra
(`OperatorRealization.Equivalence`, a `Representation.Equiv` for the whole automorphic operator
algebra).

The hypotheses on `P`, `Q`, `U` are copied from `GeneralLinearCuspidalMultiplicityOneStatement`,
and those on `R`, `Φ` (and `R'`, `Φ'`) are the conclusion of
`GeneralLinearCuspidalSummandRealizationStatement` for `P` (and `Q`). The minimality of `Q` and
the isometry property of `U` are not needed for the mathematics (they follow from, or can be
replaced by, the minimality of `P` and the continuity of `U`), but they are kept so that the
statement applies verbatim to the data of the multiplicity-one statement.

## Provenance

This is a derived statement. Getz–Hahn do not state it in this form; it is the comparison, in
the Library's two models of the cuspidal spectrum, of their Theorem 6.6.4 ("two discrete
automorphic representations are unitarily equivalent if and only if the associated automorphic
representations are equivalent", the direction "only if") with Theorem 9.7.3 (the `K`-finite
vectors of a discrete cuspidal automorphic representation are cusp forms). Its role is to carry
the hypothesis `P ≅ Q` of multiplicity one from the `L²` model to the model by forms, where
multiplicity one is the published `CuspidalOperatorMultiplicityOneStatement`.

### Why the statement holds

The following argument is a sketch, not a formal proof. The notation `V_fin` for the `K`-finite
vectors of a unitary representation `V`, with `K = K_∞ K^∞`, is Getz–Hahn's (6.24). As explained
in the Markdown of `GeneralLinearCuspidalSummandRealizationStatement`, `P` and `Q` are discrete
cuspidal automorphic representations in Getz–Hahn's sense (p. 169), the forms of `R` and `R'`
are cusp forms in their sense, and the quotient carrying `S` is `[GL_{r+1}]` up to a positive
constant in the measure.

1. *`Φ` is an injective intertwining map onto a submodule of `P_fin`.* By hypothesis the image
   of `Φ` lies in its closure `P`. A form of `R` is `K_∞`-finite for the standard maximal
   compact subgroup and of finite level, hence `K`-finite, and `Φ` commutes with right
   translations; so `Φ` maps into `P_fin`. `Φ` is injective because an `L²` class has at most
   one continuous representative (the quotient measure charges every nonempty open set). It
   intertwines the finite and compact translations of `R` with `πc`, and the enveloping-algebra
   action of `R` with the derived action on smooth vectors: for `X` in the real Lie algebra, the
   `L²` difference quotients of the class of a form `h` converge to the class of `X h`, by
   dominated convergence, since `X h` is again a cusp form and hence bounded (Theorem 9.7.1).
   The same holds for `Φ'`, `R'` and `Q`.
2. *`Φ(R) = P_fin` and `Φ'(R') = Q_fin`.* `P` is an irreducible unitary representation, so
   `P_fin` is an irreducible `(𝔤, K_∞) × G(𝔸_F^∞)`-module (Theorem 6.6.2). `Φ(R)` is a nonzero
   submodule of it, so it is all of `P_fin`. Likewise `Φ'(R') = Q_fin`. (This is also (9.40) of
   Theorem 9.7.3.)
3. *`U` restricts to an isomorphism `P_fin ≅ Q_fin`.* `U` and `U⁻¹` commute with `πc`, so they
   preserve `K`-finite vectors, and `U(P_fin) = Q_fin`. For `φ ∈ P_fin` and `X` in the real Lie
   algebra, `U` maps the difference quotients of `φ` to those of `U φ`. By step 1 the former
   converge to `X φ` and the latter, `U φ` being the class of a form of `R'`, converge to
   `X (U φ)`; by continuity of `U`, `U (X φ) = X (U φ)`. So `U` commutes with the enveloping
   algebra on `P_fin`. This is the "only if" direction of Theorem 6.6.4.
4. *Conclusion.* `Φ'⁻¹ ∘ U ∘ Φ : R.Space → R'.Space` is a linear bijection that commutes with
   the finite translations, the compact translations and the enveloping algebra, which is an
   element of `R.Equivalence R'` (the Library's `OperatorRealization.Equivalence.ofGenerators`
   builds one from these three conditions).

## Sources

1. J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations*, Graduate Texts in
   Mathematics 300, Springer, 2024 (registered literature source
   `getz-hahn-2024-automorphic-representations`). The PDF page is the printed page + 14 in
   Chapter 6 and the printed page + 12 in Chapter 9.

   * (6.24) and Theorem 6.6.2, pp. 170–171 (PDF pp. 184–185): for an irreducible unitary
     representation `(π, V)` of `G(𝔸_F)`, the space `V_fin` of `K`-finite vectors is an
     admissible and irreducible `(𝔤, K_∞) × G(𝔸_F^∞)`-module.
   * Theorem 6.6.4 and its proof, p. 172 (PDF p. 186): the `K`-finite vectors of a discrete
     automorphic representation form an automorphic representation, and two discrete automorphic
     representations are unitarily equivalent if and only if the associated automorphic
     representations are equivalent.
   * Theorem 9.7.1, p. 264 (PDF p. 276): elements of `A_cusp^{A_G}` are rapidly decreasing in the
     number field case.
   * Theorem 9.7.3, p. 265 (PDF p. 277), and the proof of (9.40) on p. 266 (PDF p. 278): for a
     discrete cuspidal automorphic representation `(π, V)`, `V_fin` is a cuspidal automorphic
     representation and `A_cusp^{A_G}(π) = L²_cusp(π)_fin`.

2. J. R. Getz and H. Hahn, *Errata for An Introduction to Automorphic Representations*, October
   2026 (registered literature source `getz-hahn-2024-errata-2026-10`), p. 2, Chapter 6, §6.6:
   in the display at the top of p. 171, `(π_∞, V_fin)` should read `(π, V_fin)`, and the proof of
   Theorem 6.6.2 should cite Theorem 4.4.9 instead of Lemma 4.4.9. Neither correction affects the
   use made here. The errata have no entry for §9.7.

## Use

`Langlands.Automorphic.GeneralLinearCuspidalMultiplicityOneReduction` derives
`GeneralLinearCuspidalMultiplicityOneStatement` from this statement together with
`GeneralLinearCuspidalSummandRealizationStatement` and `CuspidalOperatorMultiplicityOneStatement`.
