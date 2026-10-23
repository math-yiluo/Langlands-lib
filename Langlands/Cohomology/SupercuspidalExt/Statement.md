# Supercuspidal Ext vanishing

Author: Worker 3.

This module defines two functors, one predicate and three propositions, with
their conjunction `Langlands.Cohomology.SupercuspidalExt.SupercuspidalExtStatements`.
The propositions are the representation-theoretic inputs of the degeneration
step in Harris 1997, p.96, and Harris 1999, p.312: higher `Ext` groups into
a supercuspidal coefficient representation vanish. They are theorem-statement
definitions, not proofs. Reciprocity, injectivity, projectivity and vanishing
are conclusions; none is supplied as data or as a hypothesis of another
component.

## Objects

`Ext` is Worker 13's `Langlands.Cohomology.SmoothExt.ext R G V n`, the
`n`-th right derived functor of equivariant `Hom(V, -)` on the abelian
category `Langlands.SmoothRep R G` of smooth representations. It takes values
in `R`-modules. It is computed with injective resolutions; the category has
enough injectives (`Langlands.SmoothRep.enoughInjectives`). The coefficient
ring `R`, the group `G` and the representation carriers all lie in one
universe `u`, as `SmoothExt` requires. `G` is a topological group, and a
subgroup carries the subspace topology.

The module declares, in the namespace `Langlands.Cohomology.SupercuspidalExt`:

- `restriction R G H`, the functor from smooth representations of `G` to
  smooth representations of a subgroup `H`. It lifts Mathlib's
  `Rep.resFunctor H.subtype` to the smooth subcategory. The lift uses the
  published `Langlands.isSmooth_comp`: a vector fixed by an open subgroup `K`
  of `G` is fixed by the preimage of `K` in `H`, which is open because the
  inclusion is continuous.
- `compactInduction R G H`, the published compact induction
  `Langlands.Induction.compactInductionFunctor H` applied to the underlying
  representation of a smooth representation of `H`. Its values are compactly
  supported functions modulo `H` with right translation, as defined in
  `Langlands.Representation.Induction.Definitions`.
- `HasCompactCoefficients ρ`, for a smooth complex representation `ρ`:
  every matrix coefficient `g ↦ ℓ(ρ(g) v)`, with `ℓ` a smooth vector of the
  algebraic dual, has compact support. This is the hypothesis of the
  published `Langlands.CompactCoefficientSplittingStatement`, written for a
  bundled smooth representation.

## The three propositions

| Declaration | Hypotheses | Conclusion |
| --- | --- | --- |
| `CompactInductionExtReciprocityStatement R G` | `R` a commutative ring, `G` a topological group, `H` an open subgroup, `V` a smooth representation of `H`. | For every `n`, the functors `Ext^n_G(c-Ind_H^G V, -)` and `restriction ⋙ Ext^n_H(V, -)`, from smooth representations of `G` to `R`-modules, are naturally isomorphic. |
| `CompactCoefficientInjectiveProjectiveStatement G μ` | `G : Type` is Hausdorff, locally compact, totally disconnected and σ-compact, with a regular left Haar measure `μ` that is also right invariant. `ρ` is an irreducible smooth complex representation with `HasCompactCoefficients ρ`. | `ρ` is an injective object and a projective object of the category of smooth complex representations of `G`. |
| `CompactInductionSupercuspidalExtVanishingStatement G μ` | `G` and `μ` as above. `G₀` is an open subgroup. `π` is a smooth complex representation of `G`. Its restriction to `G₀` is isomorphic to the biproduct of a finite family `σ` of irreducible smooth representations of `G₀` with `HasCompactCoefficients`. `V` is a smooth representation of `G₀`. | `Ext^{n+1}_G(c-Ind_{G₀}^G V, π) = 0` for every `n`. |

`SupercuspidalExtStatements G μ` is the conjunction of the three, with the
first taken over `R = ℂ`, in this order.

In the second and third components the carriers are in `Type`, because the
coefficient field `ℂ` is in `Type` and `SmoothExt` uses one universe. The
finite biproduct in the third component exists because the smooth category is
abelian; the file enables Mathlib's `Abelian.hasFiniteBiproducts` locally for
this statement.

The third component follows from the first two. By the first, with `R = ℂ`
and `H = G₀`, the group in question is `Ext^{n+1}_{G₀}(V, π|_{G₀})`. That is
the finite sum of the `Ext^{n+1}_{G₀}(V, σ_i)`. Each `σ_i` is injective by the
second component applied to `G₀`, so these groups vanish by Worker 13's
`isZero_ext_succ_of_injective`. The open subgroup `G₀` satisfies the
hypotheses of the second component: it is closed, hence σ-compact, and the
restriction of `μ` is a two-sided Haar measure on it. The third component is
stated separately because it is the form in which Harris uses the argument.

## Original-source correspondence

Harris, *Supercuspidal representations in the cohomology of Drinfel'd upper
half spaces; elaboration of Carayol's program*, Invent. Math. 129 (1997),
75-119, printed p.96 (PDF p.22). For the spectral sequence (10), Harris
argues as follows. A supercuspidal `π_v` is "both injective and projective in
the category of smooth representations with central character" (citing
Casselman 5.4.1 and [BZ, Theorem 2.44]). The cohomology groups have no
central character, so he uses the stabilizer `GJ^0` of a connected component
`R_N^1` of `M_N`. Then `H^j_c(M_N) ≅ c-Ind_{GJ^0}^{GJ} H^j_c(R_N)`, and
"Frobenius reciprocity [BZ, Prop. 2.29] thus yields an isomorphism of
functors" `Hom_{GJ}(H^j_c(M_N), -) ≅ Hom_{GJ^0}(H^j_c(R_N), -)`, "hence
isomorphisms" `Ext^i_{GJ}(H^j_c(M_N), -) ≅ Ext^i_{GJ^0}(H^j_c(R_N), -)` for
all `i` and `j`. "Now `GJ^0` has compact center. Hence `π_v`, viewed as a
representation of `GJ^0`, is still supercuspidal (i.e., its matrix
coefficients are compactly supported). Thus, as in [BZ, Theorem 2.44], [it]
is injective and projective in the category of smooth representations."
He concludes that (10) collapses to the isomorphisms (11).

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), 299-318, printed p.312 (PDF p.14), below
(5.1): "This also follows from Theorem 1 of [H1] and Proposition 4.10: since
`π_v` is supercuspidal, the higher Ext's vanish and the spectral sequence
(4.10.1) degenerates". Here [H1] is Harris 1997.

Bernstein and Zelevinsky, *Representations of the group GL(n,F) where F is a
non-Archimedean local field*, Russian Math. Surveys 31:3 (1976):

- 2.28-2.29, pp.23-24 (PDF pp.23-24): Frobenius duality. Proposition 2.29
  gives `Hom_G(ind(G, H, ρ), π̃) ≅ Hom_H((Δ_H/Δ_G) ρ, (π|_H)~)` for a closed
  subgroup `H`, with contragredients and a ratio of modulus characters.
- 2.40-2.44, pp.26-28: a representation is finite (2.40) when its matrix
  coefficients `g ↦ ⟨ξ̃, π(g⁻¹)ξ⟩`, with `ξ̃` smooth in the dual, are
  compactly supported. Precomposition with inversion preserves compact
  support, so this is `HasCompactCoefficients`. For a unimodular `l`-group
  countable at infinity (2.42), Theorem 2.44(a) splits off every finite
  irreducible representation.
- 3.26, p.36: the restriction of an irreducible representation of `GL_n(F)`
  to `G°` is a finite direct sum of irreducible representations; 3.28 applies
  2.44(a) to each of them.

| Source | Statement | Lean component |
| --- | --- | --- |
| Harris 1997 p.96; BZ 2.29 | Frobenius reciprocity for compact induction from `GJ^0` gives isomorphisms of `Ext` groups. | `CompactInductionExtReciprocityStatement` |
| Harris 1997 p.96; BZ 2.44(a); Casselman 5.4.1 as cited by Harris | A representation with compactly supported matrix coefficients is injective and projective among smooth representations. | `CompactCoefficientInjectiveProjectiveStatement` |
| Harris 1997 p.96; Harris 1999 p.312; BZ 3.26 and 3.28 | The higher `Ext` from the compactly induced cohomology into the supercuspidal coefficient representation vanish. | `CompactInductionSupercuspidalExtVanishingStatement` |

Derivations and choices:

- Reciprocity. For an open subgroup the modulus ratio in BZ 2.29 is trivial.
  The component uses the direct form: compact induction from an open
  subgroup is left adjoint to restriction. For complex coefficients this
  adjunction is the published, unproved clause
  `Langlands.Induction.OpenSubgroupAdjunctionClause` in
  `Langlands.Representation.Induction.StructuralStatement`. Both functors
  are exact, and restriction, a right adjoint of an exact functor, preserves
  injectives. So applying `Hom_G(c-Ind V, -) ≅ Hom_H(V, -) ∘ restriction` to
  an injective resolution gives the `Ext` isomorphism for every `n`. The
  statement is made over an arbitrary commutative ring, since none of these
  steps uses the coefficients.
- Injectivity and projectivity. The published, unproved
  `Langlands.CompactCoefficientSplittingStatement` states, after BZ 2.44(a),
  that every embedding of such `ρ` into a smooth representation, and every
  surjection onto it, splits. With enough injectives, the first gives injectivity: `ρ`
  is a retract of an injective object containing it. The second gives
  projectivity in any abelian category: pull an epimorphism back along a map
  from `ρ` and split the pulled-back epimorphism. The component records this
  categorical form, which is the one Harris states.
- Restriction to `GJ^0`. Harris says that `π_v` restricted to `GJ^0` "is
  still supercuspidal". That restriction need not be irreducible. By BZ 3.26
  it is a finite direct sum of irreducible representations. Harris's
  statement is that these have compactly supported matrix coefficients on
  `GJ^0`, which has compact center. The third component takes this decomposition as its hypothesis,
  because the published splitting statement is for irreducible
  representations.

## Scope

- The coefficients of the second and third components are complex. Harris
  1997 works with `Q̄_ℓ` and says that one may choose an isomorphism
  `Q̄_ℓ ≅ ℂ` (p.95). Harris 1999, printed p.306 (PDF p.8), final
  paragraph, defines `L_v = L ⊗_ℚ ℚ_v` for a place `v` of `ℚ`, with `L`
  the number field over which the coefficient representation is rational.
  At a finite prime `ℓ`, the usual decomposition into completions gives
  `L_ℓ ≅ ∏_{λ | ℓ} L_λ`. Thus Harris's `L_ℓ` is a finite-product
  coefficient algebra, not necessarily a field: there may be just one
  factor. A chosen completion `L_λ` at a finite place `λ` of `L` above `ℓ`
  is a field, but Harris's notation denotes the whole tensor-product
  algebra. In (4.10.1), printed p.311 (PDF p.13), his `Ext` is taken in
  smooth `L_ℓ[GJ]`-modules. This module's second and third components do
  not cover those coefficients. The companion
  `Langlands.Cohomology.SupercuspidalExtCharZero.Statement` states the
  corresponding goals for `[Field k] [CharZero k]`, hence for each
  individual factor `L_λ`. Neither of these two modules formalizes the
  decomposition of smooth representations and their `Ext` groups along
  the factors, so these field-level goals do not supply a product-algebra
  `Ext` vanishing theorem.
- No central-character category is introduced. As in Harris 1997, the
  passage to `GJ^0`, which has compact center, replaces it.
- The geometric input `H^j_c(M_N) ≅ c-Ind_{GJ^0}^{GJ} H^j_c(R_N)` (Harris
  1997, appendix (A.8)) is not stated here. It concerns the Drinfeld tower.
- The decomposition of `π|_{GJ^0}` and the compactness of its matrix
  coefficients are hypotheses of the third component, not conclusions.
- With these components, the hyperext degeneration statement
  `Langlands.Cohomology.HyperextDegenerationStatement` of this framework gives
  the collapse of (10) to (11); that combination is not restated, and this
  module does not import it.

## Registered sources

- `harris-1997-drinfeld-cohomology`, PDF SHA-256
  `aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`:
  printed pp.95-96 (PDF pp.21-22), read in the text layer. Casselman's
  Theorem 5.4.1, which Harris also cites, was not read.
- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, PDF SHA-256
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`:
  printed pp.306, 311 and 312 (PDF pp.8, 13 and 14), read visually from
  the page scans.
- `bernstein-zelevinsky-1976-representations-gln`, PDF SHA-256
  `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`:
  2.28-2.29, pp.23-24; 2.40-2.44, pp.26-28; 3.26-3.28, p.36; read in the
  text layer.

## Formal dependencies and checks

Project imports, byte-identical to Library commits
`ef274d37c255e4b25a990dd377d10e2da436807d` and
`09d04036c57ae8751aadc1beefbcd76b482a8a7d`:

| Module | Author | Lean SHA-256 | Markdown SHA-256 |
| --- | --- | --- | --- |
| `Langlands.Cohomology.SmoothExt` | Worker 13 | `7dc67a2e1e0e9244dfd73c8d056c8a308e1cd04fc3bbce696f574dfd34391d9f` | `3541f8f564938d5c659a76a723501307a9f36649d7a27f7f4acbd5c347521d51` |
| `Langlands.Representation.Induction.Definitions` | Worker 15 | `c4d24368c009c903ea7450a8fc08f3dbeb5dbdb31fc3aabdc394b89b731880cf` | `7e3f0697431e4814007ac100da702a56037c1fd35f01f7c5df5e235d4eac7274` |
| `Langlands.Representation.CompactCoefficient.SplittingStatement` | Worker 3 | `f683e51e99cb560486e099c22ec43409e0eff8f10d20c6dfcf0b745937c18407` | `de72b3a818583c88c486253dbea90225c854262513d49f72146780642257cdfc` |
| `Langlands.Representation.Smooth.Transfer.PullbackProof` | Worker 0 | `b0502abed8a3551e9a5c542f07605cd66b83649fafbcb38a23b05dddc3e691b6` | `46884ac73c7107c18ce746c2110810d14d19939b7fca6a608670a6c70265ddfb` |

`Langlands.Cohomology.SmoothExt` brings Worker 13's abelian structure
`Langlands.SmoothRep.abelian` and `Langlands.SmoothRep.enoughInjectives`.
The environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.

Draft check `86897976-731a-43cc-93ce-8ddb282185c6` compiled and printed the
module against copies of Worker 13's then-staged modules. After their
publication, check `a7ecb8dd-e2c3-4b51-b527-c479f6d1ff26` built this module with Lake
against the published imports, with no errors or warnings, and inspected
`SupercuspidalExtStatements` as a `Prop`-valued definition without universe
parameters, depending only on `propext`, `Classical.choice` and
`Quot.sound`. Check `594a704d-694c-4172-b754-399c83724678` printed the two
functors, the predicate, the three components and the conjunction, with
universe annotations for the functors, and the output was read. The prints
show:

- `restriction` is `ObjectProperty.lift` of `SmoothRep.toRep ⋙
  Rep.resFunctor H.subtype`, and `compactInduction` is `SmoothRep.toRep ⋙
  Induction.compactInductionFunctor H`, both in the single universe `u`;
- the reciprocity component asserts `Nonempty` of an `Iso` of functors
  `SmoothExt.ext R G ((compactInduction R G H).obj V) n ≅ restriction R G H ⋙
  SmoothExt.ext R H V n` for every open `H`, `V` and `n`;
- the second and third components carry every hypothesis on `G` and `μ` as
  an explicit instance binder (`IsTopologicalGroup`, `T2Space`,
  `LocallyCompactSpace`, `TotallyDisconnectedSpace`, `SigmaCompactSpace`,
  `MeasurableSpace`, `BorelSpace`, `IsHaarMeasure`, `Regular`,
  `IsMulRightInvariant`);
- the second component concludes `Injective ρ ∧ Projective ρ` in the
  category `SmoothRep ℂ G`; the third concludes `IsZero` of
  `Ext^{n+1}` evaluated at `π`.

Compilation and inspection establish well-formed statements; they do not
prove any of the three assertions.
