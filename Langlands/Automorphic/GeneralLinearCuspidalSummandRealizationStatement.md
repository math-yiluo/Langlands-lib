# Irreducible cuspidal `L²` summands of `GL_n` and cuspidal operator realizations

Module `Langlands.Automorphic.GeneralLinearCuspidalSummandRealizationStatement`, namespace
`Langlands.Automorphic.GroupSchemeFunctions`. It defines one auxiliary proposition and states
two propositions. It contains no proof.

The module connects two existing Library models of the cuspidal spectrum of `GL_{r+1}` over a
number field `F`:

* the `L²` model: the full almost-everywhere cuspidal subspace
  `S = fullAEL2CuspidalSubmodule` of `L²` of the positive-central rational quotient of the
  group scheme `GL_{r+1}`, with its right regular action
  `πc = fullAEL2CuspidalBoundedRightAction` (modules `GroupSchemeFullAEL2` and
  `GroupSchemeFullAEL2Integrated`), as in `GeneralLinearCuspidalMultiplicityOneStatement`;
* the model by forms: `CuspidalOperatorRealization F r` (module `CuspidalOperatorRealization`),
  an irreducible cuspidal subspace of automorphic forms on `GL_{r+1}(𝔸_F)` in the matrix model.

The two local instances supply `IsAffine` and `Smooth` for the general linear group scheme from
the published `isAffine_groupScheme` and `smoothStatement`, as in
`GeneralLinearCuspidalMultiplicityOneStatement`. Their names are new, so the module can be
imported together with that module.

## The statements

Throughout, `GLG = GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)`,
`Q = PositiveRationalQuotient F GLG T i` and `μQ = positiveRationalQuotientHaarMeasure F GLG T i`.

### `IsGeneralLinearFormClass F r T i φ f`

For an `L²` class `φ : Lp ℂ 2 μQ` and a continuous function
`f : Langlands.Automorphic.ContinuousRationalFunctions F (r + 1)` on `GL_{r+1}(𝔸_F)` in the
matrix model, `IsGeneralLinearFormClass F r T i φ f` holds when there is a continuous function
`h : C(Q, ℂ)` such that

* the pullback of `h` to the adelic points of `GLG` (`positiveQuotientContinuousPullback`),
  transported to the matrix model by `continuousGeneralLinearEquiv F (r + 1)`, equals `f`; and
* `φ` agrees with `h` `μQ`-almost everywhere.

So `f` is invariant under the positive image of `T`, it descends to the continuous function `h`
on `Q`, and `φ` is the `L²` class of `h`. In particular `h` is square integrable.

### `GeneralLinearCuspidalSummandRealizationStatement` (from `L²` summands to realizations)

The data are a number field `F : Type u` whose adele quotient is compact (an instance argument,
which `CuspidalOperatorRealization` requires), `r : ℕ`, and the hypotheses of
`GeneralLinearCuspidalMultiplicityOneStatement` for `GL_{r+1}`:

* `hPD : ParabolicDynamicStatement`, the standing structural hypothesis of the Library's
  cuspidal `L²` spaces;
* a commutative group scheme `T` with a central morphism `i : T → GLG` (`IsCentral i`), an
  isomorphism `e` of `T` with a split torus on a finite type `I`, and injective character
  restriction `characterRestrict i` with finite-index image (an instance argument). The centre
  `G_m` of `GLG` satisfies these conditions;
* right invariance of Haar measure on the norm-one subgroup `GLG(𝔸)¹` (an instance argument).

Connected reductivity of `GLG` is supplied by the published
`GroupScheme.isConnectedReductive_generalLinear`. Let `S` and `πc` be as above. The statement
says: let `P` be a submodule of `S` that is nonzero, closed, invariant under `πc a` for every
`a ∈ GLG(𝔸)`, and minimal (every closed invariant submodule of `P` is `0` or `P`). Then there
are `R : CuspidalOperatorRealization F r` and a complex-linear map `Φ : R.Space → S` such that

* for every vector `f` of `R`, `IsGeneralLinearFormClass F r T i (Φ f) (R.realization.toContinuous f)`:
  `Φ f` is the `L²` class of the function on `Q` induced by the form `f`; and
* the closure of the image of `Φ` in `S` is `P`.

The first condition determines `Φ`. The second gives both `Φ f ∈ P` for every `f` and density of
the image in `P`.

### `GeneralLinearCuspidalRealizationSummandStatement` (from realizations to `L²` summands)

The data are the same. Let `R : CuspidalOperatorRealization F r`, and suppose that every vector
`f` of `R` descends to `Q`: there is `h : C(Q, ℂ)` whose pullback, transported to the matrix
model, is `R.realization.toContinuous f`. Then there are a submodule `P` of `S` that is nonzero,
closed, invariant and minimal in the sense above, and a complex-linear map `Φ : R.Space → S`,
such that `IsGeneralLinearFormClass F r T i (Φ f) (R.realization.toContinuous f)` for every `f`
and the closure of the image of `Φ` is `P`.

The descent hypothesis is needed. A realization is a space of functions on
`GL_{r+1}(F) \ GL_{r+1}(𝔸_F)` whose central character is not fixed. Its forms define functions on
`Q` only if they are invariant under the positive image of `T`. For the centre `T = G_m` that
image is `A_G`, the positive scalars at the archimedean places.

## Sources

1. J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations*, Graduate Texts
   in Mathematics 300, Springer, 2024 (registered literature source
   `getz-hahn-2024-automorphic-representations`). The PDF page is the printed page + 14 in
   Chapter 6 and the printed page + 12 in Chapter 9, as checked against the running heads.

   * (6.1), p. 158 (PDF p. 172): `C^∞(G(𝔸_F)) := C^∞(G(F_∞)) ⊗ C^∞(G(𝔸_F^∞))`, with an
     algebraic tensor product. See *Conventions* below.
   * Definition 6.3.1, p. 161 (PDF p. 175): `φ` has moderate growth if `|φ(g)| ≤ c‖g‖^r` for all
     `g ∈ G(𝔸_F)`, with the adelic norm (6.7)–(6.8) and one pair `(c, r)` for all adelic points.
   * Definition 6.3.3, p. 163 (PDF p. 177): an automorphic form is a smooth function of moderate
     growth on `G(𝔸_F)` that is left `G(F)`-invariant, `K`-finite and `Z(𝔤)`-finite.
   * Definition 6.5.1, p. 167 (PDF p. 181): a cusp form is an automorphic form whose constant
     terms (6.18) along every proper parabolic subgroup vanish at every point.
   * §6.5, pp. 168–169 (PDF pp. 182–183). Definition 6.5.2: a cuspidal automorphic representation
     is an automorphic representation equivalent to a subquotient of `A_cusp`. The cuspidal
     subspace `L²_cusp([G])` (6.20) consists of the `φ ∈ L²([G])` whose constant terms (6.21)
     along every proper parabolic vanish almost everywhere. On p. 169: an irreducible
     subrepresentation of `L²_cusp([G])` is called a *discrete cuspidal automorphic
     representation*. `A_cusp^{A_G}` is the space of `A_G`-invariant cusp forms, and
     `A_cusp^{A_G}(π)` is its `π`-isotypic component, the algebraic sum of the irreducible
     `(𝔤, K_∞) × G(𝔸_F^∞)`-submodules of `A_cusp^{A_G}` equivalent to `π`. Theorem 6.5.3 on the
     same page is restated as Theorem 9.7.3.
   * Proposition 6.7.2, p. 177 (PDF p. 191): cusp forms on `GL_2(𝔸_ℚ)` attached to cuspidal
     modular forms. Theorem 6.8.1, p. 179 (PDF p. 193): `Δ` spans the cusp forms of weight 12 and
     level 1.
   * Corollary 9.1.3, p. 241 (PDF p. 253): `L²_cusp([G])` is a Hilbert direct sum of irreducible
     representations, each occurring with finite multiplicity.
   * Theorem 9.7.1, p. 264 (PDF p. 276): an element of `A_cusp^{A_G}` is rapidly decreasing in the
     number field case (citing Mœglin–Waldspurger, I.2.12).
   * Lemma 9.7.2, p. 264 (PDF p. 276): for an irreducible unitary representation `(π, V)` of
     `A_G \ G(𝔸_F)`, the `K`-finite vectors `V_fin` are dense in `V`, and every `φ ∈ V_fin` is
     `π(f)φ` for some `f ∈ C_c^∞(A_G \ G(𝔸_F))`.
   * Theorem 9.7.3, p. 265 (PDF p. 277), with its proof on pp. 265–267 (PDF pp. 277–279):
     `A_cusp^{A_G}` is a dense subspace of `L²_cusp([G])`. If `(π, V)` is a discrete cuspidal
     automorphic representation, then `V_fin` is a cuspidal automorphic representation, and
     `A_cusp^{A_G}(π) = L²_cusp(π)_fin` (9.40). The association of `(π, V_fin)` to `(π, V)` is a
     bijection between isomorphism classes of discrete cuspidal automorphic representations and
     of cuspidal automorphic representations. The proof (p. 265) begins by noting that elements
     of `A_cusp^{A_G}` are bounded by Theorem 9.7.1, hence square integrable on `[G]`, which has
     finite measure. On pp. 265–266 it shows that a cuspidal automorphic representation `π`
     realized as a subspace `W ≤ A_cusp^{A_G}` lies in `L²_cusp(π)`, so that
     `A_cusp^{A_G}(π) = A_cusp^{A_G} ∩ L²_cusp(π)` (9.42). It then proves (9.40) on p. 266:
     `L²_cusp(π)` is a finite direct sum of irreducible representations, all isomorphic to
     `(π, V)`. The rest of the proof, pp. 266–267, concerns (9.41).

2. A. Borel and H. Jacquet, *Automorphic forms and automorphic representations*, in *Automorphic
   Forms, Representations and L-Functions*, Proc. Sympos. Pure Math. 33, part 1, 1979,
   pp. 189–202 (registered literature source `borel-jacquet-1979-automorphic`). In this article
   the PDF page is the printed page − 5.

   * §4.1, p. 194 (PDF p. 189): a function on `G(𝔸) = G_∞ × G(𝔸_f)` is *smooth* if it is
     continuous, `C^∞` in `x ∈ G_∞` for fixed `y ∈ G(𝔸_f)`, and locally constant in `y` for fixed
     `x`.
   * §4.2, pp. 194–195 (PDF pp. 189–190): a `K_∞`-automorphic form is a smooth function that is
     (a) left `G(F)`-invariant, (b) fixed under convolution with a simple idempotent `ξ_∞ ⊗ ξ_L`
     (so `K_∞`-finite and right invariant under a compact open subgroup `L`), (c) annihilated by
     an ideal of finite codimension of `Z(𝔤_∞)`, and (d) for each `y ∈ G(𝔸_f)`, the function
     `x ↦ f(x y)` on `G_∞` is slowly increasing.
   * §4.3, p. 195 (PDF p. 190), last paragraph after (iv): slowly increasing functions on `G(𝔸)`
     can be defined directly with an adelic norm (4), and for continuous functions satisfying
     4.2(a) and (b) this is equivalent to 4.2(d).
   * §4.4, p. 196 (PDF p. 191): for a cuspidal function satisfying 4.2(a)–(c) and having a
     central character, being slowly increasing, being bounded, and being square integrable
     modulo `Z(𝔸) G(F)` are equivalent.

## Conventions: smoothness and growth

The Library's automorphic forms on `GL_{r+1}(𝔸_F)` (module `Forms`) follow Borel–Jacquet §4. The
published `isAutomorphicForm_iff_source_conditions` (`Langlands/Automorphic/Forms.lean`) unfolds
`IsAutomorphicForm` into: finite level, finiteness under the standard maximal compact subgroup at
the archimedean places, annihilation of every archimedean slice by one ideal of finite
codimension of the centre of the enveloping algebra, and, for each finite adele `b`, a polynomial
bound `‖f(a, b)‖ ≤ C ‖a‖^d` in the archimedean variable `a`, with `C` and `d` depending on `b`.
The underlying functions are continuous, smooth in the archimedean variable and locally constant
in the finite one. These are Borel–Jacquet §4.1 and §4.2(a)–(d).

This departs from Getz–Hahn in two places.

* **Smoothness.** Read literally, (6.1) allows only finite sums `Σ φ_∞ ⊗ φ^∞`. That class
  contains no nonzero cusp form on `GL_2` over `ℚ`. For such a sum `f`, the finite-adelic factors
  may be taken linearly independent. They then span a finite-dimensional space stable under left
  translation by `GL_2(ℚ)`, because `f` is left `GL_2(ℚ)`-invariant. Local constancy at finitely
  many points shows that a congruence subgroup of the rational upper unipotent group acts
  trivially on this space. The kernel of the action is normal in `GL_2(ℚ)`, so conjugation by
  rational diagonal matrices puts the whole rational upper unipotent group `N(ℚ)` in it. By
  density of `N(ℚ)` in `N(𝔸_f)` and in `N(ℝ)`, and continuity, `f` is left invariant under
  `N(𝔸_ℚ)`. Its constant term along the upper Borel subgroup is then a positive multiple of `f`,
  so a cusp form of this kind vanishes. But Proposition 6.7.2, p. 177 (PDF p. 191), together
  with Theorem 6.8.1, p. 179 (PDF p. 193), gives a nonzero cusp form on `GL_2(𝔸_ℚ)` attached to
  Ramanujan's `Δ`. We therefore read Getz–Hahn's smoothness in the usual sense of Borel–Jacquet
  §4.1, together with a finite level. This is the class the Library uses. Getz–Hahn's Chapter 9
  results are used below only in this sense.
* **Growth.** Getz–Hahn Definition 6.3.1 asks for one bound `c ‖g‖^r` on all of `G(𝔸_F)`, while
  the Library, like Borel–Jacquet 4.2(d), asks for a bound on each finite slice. For continuous
  functions that are left `G(F)`-invariant and of finite level, the two conditions are
  equivalent by Borel–Jacquet §4.3, p. 195, last paragraph. The Library has not formalized this
  equivalence. Its comparison `isAdelicAutomorphicForm_iff_generalLinear_and_adelicGrowth`
  (`Langlands/Automorphic/GeneralLinearAdelicForms.lean`) keeps the adelic growth condition as a
  separate conjunct.

Under these conventions the Library's automorphic forms are Getz–Hahn's automorphic forms with
respect to `K = K_∞ K^∞`, where `K_∞` is the standard maximal compact subgroup at the archimedean
places. Finite level and `K^∞`-finiteness agree for these functions. Finite level under a compact
open `L` gives `K^∞`-finiteness: the translates `x ↦ f(x k)` with `k ∈ K^∞` depend only on `k`
modulo the open normal core of `L ∩ K^∞` in `K^∞`. Conversely, a `K^∞`-finite function that is
locally constant in the finite variable is fixed by an open subgroup of `K^∞`, because the
translate `x ↦ f(x k)` is determined by its values at finitely many points.

## Correspondence with the sources

* **The `L²` side.** As explained in `GeneralLinearCuspidalMultiplicityOneStatement.md`, `S` is
  Getz–Hahn's `L²_cusp([GL_{r+1}])` (6.20), and for the centre `T = G_m` the quotient `Q` is
  `[GL_{r+1}] = A_G GL_{r+1}(F) \ GL_{r+1}(𝔸_F)`. For every admissible `T`, `Q` is homeomorphic to
  `GL_{r+1}(F) \ GL_{r+1}(𝔸)¹`. `μQ` is the transport of Haar measure on that quotient. Rescaling
  the measure by a positive constant changes neither the almost-everywhere classes nor the
  closed invariant subspaces. A nonzero minimal closed invariant subspace `P` of `S` is a
  discrete cuspidal automorphic representation in Getz–Hahn's sense (p. 169).
* **The side of forms.** `CuspidalOperatorRealization F r` is a subspace of the Library's stable
  automorphic functions on `GL_{r+1}(𝔸_F)` (module `OperatorCore`). It is invariant under finite
  adelic translations, translations by the standard maximal compact subgroup at the archimedean
  places, and the enveloping-algebra action. It is irreducible under the algebra these operators
  generate, which is irreducibility as a `(𝔤, K_∞) × G(𝔸_F^∞)`-module. Its forms are cuspidal.
  `StableAutomorphicFunctions` is the largest subspace of the Library's automorphic forms
  invariant under these operators, so every invariant space of automorphic forms lies in it.
  The forms are automorphic forms in Getz–Hahn's sense under the conventions above. Their
  cuspidality is Getz–Hahn's (6.18): the Library's matrix predicate `IsCuspidal` is equivalent
  to vanishing of the constant terms along all proper rational parabolic subgroups by the
  published `mem_normalizedGeneralLinearParabolicCuspidal_iff`
  (`Langlands/Automorphic/GeneralLinearParabolicCuspidalEquivalence.lean`). A realization is
  jointly admissible by the published `CuspidalOperatorRealization.isJointlyAdmissible`
  (`Langlands/Automorphic/CuspidalJointAdmissibility.lean`), so it is a cuspidal automorphic
  representation in the sense of Definition 6.5.2, realized as a subspace rather than a
  subquotient. A form `f` of `R` with `IsGeneralLinearFormClass F r T i φ f` is invariant under
  the positive image of `T` (for the centre, `A_G`), so it lies in `A_cusp^{A_G}`.
* **From `P` to `R`.** By Theorem 9.7.3, the `K`-finite vectors `P_fin` of `P` form a cuspidal
  automorphic representation and lie in `L²_cusp(π)_fin = A_cusp^{A_G}(π)` (9.40). So they are
  classes of `A_G`-invariant cusp forms. Each class has exactly one continuous representative,
  since `μQ` charges every nonempty open set. By Lemma 9.7.2, `P_fin` is dense in `P`. The space
  of continuous representatives, pulled back to `GL_{r+1}(𝔸_F)` and transported to the matrix
  model, consists of Library automorphic forms: adelic moderate growth gives the bound on each
  slice. This space is the realization `R`, and `Φ` sends a form to its class. The
  `(𝔤, K_∞) × G(𝔸_F^∞)`-action of `P_fin` agrees with the operators of `R`. The group actions are
  right translations in both models. For the Lie algebra, `X h` is again an `A_G`-invariant cusp
  form, hence bounded, and then the `L²` difference quotients of `h` converge to `X h` on the
  finite measure space `Q` by dominated convergence.
* **From `R` to `P`.** The forms of `R` lie in `A_cusp^{A_G}` (see *The side of forms*). By
  Theorem 9.7.1 and the first step of the proof of Theorem 9.7.3, they are bounded, so their
  classes lie in `L²(Q)`. Borel–Jacquet §4.4 gives the same boundedness directly: `R` has a
  central character (published `OperatorRealization.existsUnique_hasCentralCharacter`), which is
  trivial on the positive image of `T` and therefore unitary. Their constant terms vanish
  everywhere, so the classes lie in `S`. Let `Φ : R → S` send a form to its class. It is
  injective by uniqueness of continuous representatives, and, as in the previous item, it
  intertwines the operators of `R` with the `(𝔤, K_∞) × G(𝔸_F^∞)`-action on smooth vectors.
  Write `W` for its image. By the argument for (9.42) on pp. 265–266,
  `W ≤ L²_cusp(π)` for the discrete cuspidal automorphic representation `(π, V)` with
  `V_fin ≅ R`, and `W` lies in `L²_cusp(π)_fin`. The next step is derived here; Getz–Hahn do not
  state it. By Corollary 9.1.3 and the proof of (9.40), `L²_cusp(π)` is an orthogonal sum
  `V_1 ⊕ ⋯ ⊕ V_m` of closed irreducible subspaces with unitary isomorphisms `U_j : V → V_j` of
  `G(𝔸_F)`-representations. Each `U_j` restricts to an isomorphism `ι_j : V_fin → (V_j)_fin`, and
  `L²_cusp(π)_fin = ⊕_j (V_j)_fin`. Fix an isomorphism `α : V_fin → W` of
  `(𝔤, K_∞) × G(𝔸_F^∞)`-modules, and let `p_j` be the orthogonal projection onto `V_j`. It
  commutes with `G(𝔸_F)`, so it preserves `K`-finite vectors and commutes with the Lie algebra
  action. Then `ι_j⁻¹ ∘ p_j ∘ α` is an endomorphism of the irreducible admissible module
  `V_fin`. It preserves a nonzero finite-dimensional space `V_fin(σ)^{K'}` for some `K_∞`-type
  `σ` and some compact open `K'`. So it has an eigenvalue `c_j` there, and its `c_j`-eigenspace
  is a nonzero submodule, hence all of `V_fin`. Therefore `α(v) = Σ_j c_j U_j v` for
  `v ∈ V_fin`. The map `U = Σ_j c_j U_j : V → L²_cusp(π)` is `G(𝔸_F)`-equivariant and satisfies
  `‖U v‖² = (Σ_j |c_j|²) ‖v‖²`, with `Σ_j |c_j|² > 0` because `W ≠ 0`. So its image `P = U(V)`
  is closed, invariant and isomorphic to `V`, hence nonzero and minimal. Since `V_fin` is dense
  in `V` (Lemma 9.7.2) and `U` is continuous, `W = U(V_fin)` is dense in `P`. This gives the
  closure statement, including the invariance of the closure under all of `G(𝔸_F)`, not only
  under the operators of `R`.
* **What the Lean statements keep.** They keep the function-level identification
  (`IsGeneralLinearFormClass`) and density. In both directions the image of `Φ` is exactly the
  space `P_fin` of `K`-finite vectors of `P`. From `P` to `R` this is (9.40). From `R` to `P`
  it holds because `U` is an isomorphism of `V` onto `P`, so `P_fin = U(V_fin) = W`. The Lean
  statements do not formalize `P_fin`. They assert no uniqueness of `R` and no multiplicity
  statement. Multiplicity one is `GeneralLinearCuspidalMultiplicityOneStatement`.

## Use

This module links the trace-formula work on irreducible summands of `S` (for example Task 7701,
`Langlands.TraceFormula.GroupSchemeCuspidalLocalTraceFactorizationStatement`) to the local
components and `L`-functions that the Library defines for cuspidal operator realizations.
