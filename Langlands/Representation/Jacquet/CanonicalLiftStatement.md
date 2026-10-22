# Core canonical Jacquet lift statements for p-adic block groups

This module states two linked representation-theoretic assertions using the
published constructions in `CanonicalLiftDefinitions` and
`BlockIwahoriDefinitions`. All three new declarations are Prop-valued
definitions, not proofs. Their namespace is `Langlands.Jacquet`.

## Parameters and hypotheses

Every declaration retains an arbitrary prime `p`, every finite p-adic field
`F : PadicField.{uF} p`, supplied `T : F.TopologicalData`, every natural rank
`n`, every `B : GeneralLinear.BlockShape n`, and a complex representation carrier
`V : Type uV`. The field and representation universes are independent. Each
clause installs precisely `T.topology` and
`T.generalLinearTopologicalGroup n`; it does not quantify over a replacement
topology or topological-group structure.

For every representation `ρ` of the actual `GeneralLinear n F.Carrier` on `V`,
`hAdmissible : IsAdmissible ρ` supplies the smoothness witness
`hρ := hAdmissible.1`. The remaining hypotheses are an actual open subgroup `K`,
its compactness witness `hK`, the existing predicate
`B.HasBlockIwahoriFactorization T K`, and a scalar tuple
`a : Fin B.length → F.Carrierˣ` satisfying
`B.IsStrictlyContracting T a`. Set `g := B.blockScalar F.Carrier a`.
These are all the hypotheses.

The factorization predicate uses multiplication of the actual lower radical,
common Levi, and upper radical intersections with `K`, and conjugation
containments for all weakly contracting block scalars. It is the published
stronger, weak-chamber specialization of Casselman's factorization condition.
Strict contraction means that every forward block ratio `a_i/a_j`, for `i < j`,
has normalized absolute value less than one. Thus the contracted radical is the
actual upper radical `N := B.unipotentSubgroup F.Carrier`. The embedded common
Levi is `M := B.leviSubgroup F.Carrier`, and its normalizer inclusion is the
published `B.leviSubgroup_le_normalizer_unipotentSubgroup F.Carrier`.

## The two assertions

Write `X := fixedVectors ρ K.toSubgroup` and
`C := compressedAction ρ hρ K hK g`. This is the existing endomorphism of `X`
that applies `ρ g` and then the normalized compact average.

`BlockPowerKernelJacquetClause F T B V` states the equality of submodules of `X`

\[
  \sup_{r\in\mathbb N}\ker(C^r)
  =\ker\bigl(\texttt{fixedJacquetMap}\;ρ\;N\;M\;hMN\;K\bigr).
\]

The left side is exactly the published `powerKernelSup`. The right side is the
kernel of the actual quotient map restricted to `K`-fixed vectors. In ambient
terms these are precisely the fixed vectors belonging to the actual upper
Jacquet relation submodule, not an independently chosen nilpotent subspace.

`BlockStableImageJacquetBijectiveClause F T B V` states
`Function.Bijective (stableImageJacquetMap ρ hρ K hK g N M hMN)`.
Its domain is exactly the published
`stableImage ρ hρ K hK g = ⨅ r : ℕ, LinearMap.range (C ^ r)`.
Its existing codomain is

```lean
fixedVectors (Jacquet.action ρ N M hMN) (K.toSubgroup.comap M.subtype)
```

Here `K.toSubgroup.comap M.subtype` is `M ∩ K` regarded as a subgroup of `M`.
The descended action is **unnormalized**. The published evaluation law identifies
this map with the original quotient of the stable-image vector in `V`.
Consequently the asserted bijectivity supplies a unique actual stable-image lift
of each vector in that codomain. No inverse is selected or supplied as input.

`BlockCanonicalLiftStatement F T B V` is exactly the conjunction of these two
clauses. Nilpotent-kernel equality, quotient surjectivity, admissibility of the
Jacquet module, canonical lifts, and pairings are not hypotheses. There is no
positive-rank, nonempty-block, proper-parabolic, or nonzero-representation
condition. Rank zero, empty and one-block shapes, and the zero representation
are retained. For at most one block the strict inequalities are vacuous, as in
the existing contraction predicate.

## Source and normalized-operator translation

Bill Casselman, *Introduction to admissible representations of p-adic groups*,
Chapter III: *Induced representations and the Jacquet module*, revision
April 29, 2019, section 5, pages 6–7: Lemma III.5.4 and Proposition III.5.5.
Section 4 and III.5.1 on page 5 specify the factorization and the coset operator;
III.5.2–III.5.3 on page 6 give its quotient and multiplication formulas.
Registered source: `casselman-2019-jacquet-module`; SHA256:
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
Retained original:
`/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter III - Induced representations and the Jacquet module--2019.pdf`.
The source's pages 5–7 were checked visually, including the overbars distinguishing
`N` and its opposite. No separate project errata file for this source was found.
Page 7 restricts the continuing argument to a field and explicitly retracts an
earlier general-Noetherian-coefficient proof. This module uses `ℂ`.

These statements are a concrete **derived specialization**, not a literal
transcription of the source's operator. Casselman's `τ_a` is the unnormalized
sum over `K g K / K`; III.5.1 writes it as the sum over
`K / (K ∩ g K g⁻¹)` acting on `ρ(g)v`. The implemented `C` uses normalized
averaging. To transfer the source argument one must prove the comparison
`τ_a = d_a C`, where `d_a = [K : K ∩ g K g⁻¹]` is a positive finite index,
viewed in `ℂ`. Its nonzero scalar factor would give equality of the kernels
and ranges of corresponding powers. One must also prove finite-dimensional
stabilization to identify the intersection of all ranges with the source's
sufficiently high power image. Neither the index comparison nor stabilization
is assumed in these clauses or proved in this module.

The source uses a normalized Jacquet action in its quotient formulas. The
present codomain deliberately uses the existing unnormalized descended action.
Identifying its compact-Levi fixed vectors with those of a normalized action
requires a proved restriction of the modulus to the compact subgroup; that
identification is not silently imposed here.

Ordinary finite-dimensional Fitting decomposition addresses stabilization,
the direct sum of stable image and generalized kernel, and invertibility on
the stable image. It does not identify the generalized kernel with Jacquet
relations and does not establish surjectivity onto the actual Levi-fixed
Jacquet quotient. Those are the representation-theoretic assertions stated
here, requiring the factorization and contraction arguments in their eventual
proofs.

No proof of either clause is included. Independence of the contracting tuple,
compatibility under nested compact subgroups and averaging, normalized-action
compatibility, canonical pairing construction, nondegeneracy, and full opposite
Jacquet duality remain separate statements and proof obligations. In
particular the uniqueness asserted for a fixed stable-image map does not itself
assert independence of its defining tuple or compact subgroup.
