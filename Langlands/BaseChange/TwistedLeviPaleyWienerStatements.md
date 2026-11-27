# Inputs of the twisted trace Paley–Wiener theorem on Levi products

The module `Langlands.BaseChange.TwistedLeviPaleyWienerStatements` states six
propositions about the Levi products `M_B = ∏ᵢ GL_{Bᵢ}(E)` of `GL_n(E)`. They
are the results that the proof of Rogawski's twisted trace Paley–Wiener
theorem (Rogawski 1988, Proposition 11.2, following Bernstein–Deligne–Kazhdan
1986, §4.3) quotes, in the distribution language of
`Langlands.BaseChange.TwistedPaleyWiener`.
`Langlands.BaseChange.TwistedPaleyWienerReduction` proves that together they
imply `TwistedTracePaleyWienerStatement`. This module states them and does not
prove them.

## Common setting

Every proposition quantifies, as `TwistedTracePaleyWienerStatement` does, over
a nonarchimedean local field `F : Type u` of characteristic zero, a field
`E : Type v` that is a topological `F`-algebra with its module topology, an
automorphism `σ : E ≃ₐ[F] E` and `l n : ℕ` with `IsCyclicAlgebra σ l`. Every
Levi product `C.Levi E` (for `C : BlockShape n`) receives its Borel σ-algebra
and the Hausdorff, locally compact and totally disconnected instances
`levi_t2Space_of_finite`, `levi_locallyCompactSpace_of_finite` and
`levi_totallyDisconnectedSpace_of_finite`, which reduce to the factor
statements `generalLinear_*_of_finite` through the product instances. The
measures are arbitrary Haar measures. Representations have carriers in
`Type z`. `ProperRefinement E B` is the type of block shapes `C` with
`C.parabolic E ≤ B.parabolic E` and `B.length < C.length`. Since `E` is a
field, these are the block shapes refining `B` into more blocks (see the
Markdown of `Langlands.BaseChange.TwistedLeviParabolic`), and their Levi
products are the proper standard Levi subgroups of `M_B`. "Good" below means
`IsCompactlyDominatedFunctional (leviAut σ B) μ Φ` and
`IsLeviSigmaInducedRegularFunctional σ B μ Φ`.

## The six propositions

1. `TwistedLeviInductionTransferStatement` (induction on test functions).
   For `C` refining `B` and Haar measures `μ` on `M_B` and `ν` on `M_C`, some
   linear map `CT` satisfies `IsLeviInductionTransfer σ B μ C ν CT`. Source:
   the descent formula of Henniart–Lemaire (2011), II.4.5, formula (2),
   printed p. 86, with the twisting operator of Rogawski (1988), §3, and
   Henniart–Lemaire (2011), II.4.4. The source states it for `GL_n(E)`,
   normalized induction, tensor products of σ-pairs and Haar measures
   normalized by maximal compact subgroups; the Markdown of
   `Langlands.BaseChange.TwistedLeviPaleyWiener` explains the derived form for
   a general admissible pair on `M_C`, unnormalized induction inside `M_B` and
   arbitrary Haar measures.
2. `TwistedLeviJacquetDescentStatement` (Jacquet lifts and the combinatorial
   lemma). For a family of Haar measures `μs` and test maps `CT C` realizing
   induction from every proper refinement `C` of `B`, there are linear maps
   `L C : SchwartzBruhat (M_C) → SchwartzBruhat (M_B)` and finitely supported
   coefficients `c` such that `θ ∘ L C` lies in the span of the irreducible
   twisted characters of `M_C` for every irreducible twisted character `θ` of
   `M_B`, and `x = ∑_C c C • (x ∘ L C ∘ CT C)` for every `x` in
   `leviProperInducedSpan σ B (μs B)`. With `L C` a Jacquet lift (Rogawski,
   Proposition 7.1: `tr π(L C f) = tr r_C(π)(f)`), the first property is finite
   length of Jacquet modules, the operator `x ↦ x ∘ L C ∘ CT C` is
   `i_C ∘ r_C`, and the identity is Rogawski's Lemma 8.2 and Proposition 9.1
   (Bernstein–Deligne–Kazhdan, §3.3) applied to properly induced elements. The
   unnormalized functors give the same composite `i_C ∘ r_C` as the normalized
   ones, because the half moduli cancel.
3. `TwistedLeviDiscretePaleyWienerStatement` (the discrete case). A good
   functional on `M_B` that vanishes on `leviProperInducedSpan σ B μ` is a
   twisted trace functional. In Rogawski's proof of Proposition 11.2 these
   are the discrete good forms `F ∈ F_disc(G)` (printed p. 229, first
   paragraph): within one stable component, Proposition 10.1 (finiteness of
   the discrete supports up to σ-invariant unramified twist) and the argument
   of Bernstein–Deligne–Kazhdan, §4 (Proposition 4.2), give a trace form that
   agrees with `F` on the span `R(Θ_disc)` of the representations with a
   discrete infinitesimal character, and Propositions 9.1 and 7.1 then show that `F`
   minus that trace form is a trace form. The abstract lemma
   `PaleyWienerAssembly.exists_eq_eval_of_discrete`, with its parameter
   `Good` taken to be the discrete good forms, derives the statement from the
   descent identity of item 2 and a subspace of discrete-support characters
   satisfying its hypotheses `hA1`, `hA2`, `hA4` and `hA9`; there `hA4` is the
   interpolation for discrete good forms only.
4. `TwistedLeviGoodRestrictionStatement` (restriction of good forms). If `CT`
   realizes induction from `M_C` to `M_B`, then `Φ ∘ CT^t` is good on `M_C`
   whenever `Φ` is good on `M_B`. Source: Rogawski, Lemma 11.1(b);
   Bernstein–Deligne–Kazhdan, Proposition 3.2(i); for compact domination,
   Henniart–Lemaire (2011), II.5.7, Remarque (1).
5. `TwistedLeviInducedSpanStatement` (finite length of induction). The
   induction of an irreducible admissible σ-pair from `M_C` to `M_B` is
   admissible and its twisted character lies in the span of the irreducible
   twisted characters of `M_B`. Source: finite length of parabolic induction
   (Henniart–Lemaire 2011, II.5.5) and the dévissage of twisted characters
   along σ-stable composition series (Rogawski 1988, §2; Henniart–Lemaire
   2011, II.5.2–II.5.4).
6. `TwistedLeviTraceGoodStatement` (trace forms are good). Subtracting the
   evaluation at a test function from a good functional gives a good
   functional. Source: Bernstein–Deligne–Kazhdan, §1.2, and Rogawski,
   Lemma 11.1(a); good forms form a subspace.

`TwistedLeviPaleyWienerInputsStatement` is their conjunction.

## Comparison with the sources

The sources work with linear forms on a Grothendieck group of twisted
representations; here the forms are linear functionals on
`Distribution (M_B)`, evaluated on twisted characters. The twisted character
`(Π, A) ↦ Θ^A_Π` of a σ-representation of finite length is additive along
short exact sequences, vanishes on the classes whose summands are permuted
cyclically with a nontrivial orbit (Rogawski's `Irr(M*)°` of §2, Lemma 2.1,
printed pp. 216–217, whose twisted characters vanish by §5, printed p. 218;
they generate Henniart–Lemaire's `G^{>0}` of II.5.4, printed p. 103), and is
homogeneous in the intertwiner: `Θ^{λA}_Π = λ Θ^A_Π` for `λ ∈ ℂˣ`
(Henniart–Lemaire 2011, II.5.4, Remarque). In particular it vanishes on the
sums `∑_{i<t} (Π, μ^i A)` for a primitive `t`-th root of unity `μ` with
`t > 1`, and it satisfies Rogawski's relations `π^c = c π` for the `r`-th roots
of unity `c` (§2, printed p. 216). Composing it with a linear functional on
distributions therefore gives a form on the Grothendieck group that satisfies
the relations of the source quotients and also Henniart–Lemaire's separate
homogeneity condition `Φ(Π, λA) = λ Φ(Π, A)` of II.5.7, printed p. 105.
Homogeneity for all `λ ∈ ℂˣ` is a linear relation among twisted characters
that is not part of the quotient of II.5.4, whose root-of-unity sums keep the
modulus of the scalar fixed: for the trivial representation and the trivial
twist, the intertwiners `2 · id` and `id` have characters in the ratio `2`.
So the forms obtained from linear functionals on distributions are
homogeneous, as the forms of II.5.7 are. In Rogawski's setting `ε` has
order `r` and `π(ε)^r = 1`, and an element of `R(M*)′` (a form vanishing on
`Irr(M*)°`) is determined by its values on the chosen extensions of the
`π ∈ Irr(M)^ε`; it extends homogeneously to all intertwiners.

The carriers of the twisted characters in `twistedSpectrum` and of the
inducing pairs are complex vector spaces in `Type z`. Smooth induction of a
carrier in `Type z` has its function model in `Type (max v z)`; item 1 and
`leviProperInducedSpan` take the twisted distribution of that model directly.
Item 5 requires the irreducible constituents of the induced representation to
be represented in `Type z`, which is possible because they have countable
dimension. In item 2 no universe change occurs: the Jacquet module of a
carrier in `Type z` is a quotient of that carrier, so it and its subquotients
stay in `Type z`. Item 2 is stated for every
admissible choice of the test maps `CT`, since its two identities only involve
the values of `CT` on twisted characters, which item 1 determines. All six
propositions hold for every Levi product, including the one-block shape,
whose Levi product is `GL_n(E)` up to the block-diagonal isomorphism.

## Sources

- J. D. Rogawski, *Trace Paley–Wiener theorem in the twisted case*, Trans.
  Amer. Math. Soc. 309 (1988), 215–229: §§2–3 (printed pp. 216–218), §5
  (p. 218), Proposition 7.1 (p. 219), Lemma 8.2 (p. 222), Proposition 9.1
  (p. 223), Proposition 10.1 (p. 224), Lemma 11.1 and Proposition 11.2
  (p. 228). Literature ID `rogawski-1988-twisted-trace-paley-wiener`.
- J. Bernstein, P. Deligne and D. Kazhdan, *Trace Paley–Wiener theorem for
  reductive p-adic groups*, J. Analyse Math. 47 (1986), 180–192: §1.2,
  §§3.1–3.3, Proposition 4.2 and §4.3 (printed pp. 180–185). Literature ID
  `bernstein-deligne-kazhdan-1986-trace-paley-wiener`.
- G. Henniart and B. Lemaire, *Changement de base et induction automorphe pour
  GL_n en caractéristique non nulle*, Mém. SMF 124 (2011), II.4.4 (p. 85),
  II.4.5, formula (2) (p. 86), II.5.2–II.5.5 (pp. 100–104) and II.5.7
  (p. 105). Literature ID
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`.
