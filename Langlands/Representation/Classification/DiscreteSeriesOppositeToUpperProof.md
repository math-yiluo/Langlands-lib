# Same-sigma opposite-to-upper discrete-series induction comparison (proof)

`Langlands.glTemperedDiscreteSeriesOppositeToUpper` proves
`Langlands.GLTemperedDiscreteSeriesOppositeToUpperStatement.{uF, uV, uW}` exactly, with no
hypotheses. The setting is the one of the statement: a prime `p`, a `PadicField.{uF} p` with
topological data `T`, positive `n`, a block shape `B` with actual product Levi `M`, a Borel
Haar measure `μ` on `M ⧸ Subgroup.center M`, an irreducible tempered `π` of `GL_n` on
`V : Type uV`, and an irreducible square-integrable-mod-center `σ` of `M` on `W : Type uW`,
together with an injective intertwiner `π → T.normalizedOppositeParabolicInduced B σ`.
The proof keeps the given `σ` in both inductions throughout.

## Proof

1. **Semisimplicity of both inductions.**
   `isSemisimple_bothInduced_of_squareIntegrable T B hn μ σ hσ hσSI`
   (module `Langlands.Representation.Classification.DiscreteSeriesInductionForms`) gives algebraic
   semisimplicity of the upper and the opposite normalized induction of the same `σ`. Its
   second component is the first conclusion of the statement. The proof therefore does not use
   `GLTemperedInductionStatement`.

2. **A quotient of the opposite Jacquet module.** Let `J = OppositeSupport.jacquetAction T B π`,
   the `M`-action on the coinvariants of `π` for the opposite unipotent radical.
   `OppositeSupport.quotient_iff_embedding` (opposite Frobenius reciprocity, admissibility of
   `π` from temperedness) turns the given embedding into a surjective intertwiner `J → σ`.
   `Parabolic.irreducibleOppositeJacquetFiniteLength` shows that `J` has finite length.

3. **From a quotient to a subrepresentation.** Let `cσ` be the unitary central character in
   `hσSI`. `exists_injective_of_scalarCentralSubs` (module
   `Langlands.Representation.ScalarSubReduction`) gives an injective intertwiner `σ → J`,
   provided the following holds: for every subrepresentation `τ ↪ J` on which the center of `M` acts
   by the scalar `cσ`, a surjection `τ → σ` yields an injection `σ → τ`. To check this condition:
   - `τ` carries the unitary central character `cσ`. The image of `τ` in `J` exhibits `τ` as a
     subquotient of `J`, so `glTemperedOppositeJacquetScalarLayer.{uF, uV, uV}` makes `τ`
     tempered modulo center for `μ`;
   - `glTemperedDiscreteSeriesIsotypic.{uF, uV, uW}` then gives an idempotent
     self-intertwiner `P` of `τ` whose range is the `σ`-isotypic part and whose kernel has
     no subrepresentation mapping onto `σ`;
   - `ScalarSubReduction.exists_injective_of_isotypicProjector` turns `P` and the
     surjection `τ → σ` into an injection `σ → τ`.

4. **Second adjointness.** The first component of
   `Parabolic.normalizedSecondAdjointness.{uF, uW, uV}` gives, for the admissible `σ` and `π`,
   a bijection between intertwiners `T.normalizedParabolicInduced B σ → π` and
   intertwiners `σ → J`. The preimage `g` of the injection from step 3 is nonzero, because `W`
   is nontrivial. Since `π` is irreducible, `g` is surjective.

5. **Splitting.** By step 1, the upper induction is semisimple as a module over the group
   algebra of `GL_n`, so `IsSemisimpleModule.lifting_property` gives a section
   `s : π → T.normalizedParabolicInduced B σ` with `g ∘ s = id`. This section is the
   required injective intertwiner.

This argument follows the conditional assembly
`glTemperedDiscreteSeriesOppositeToUpper_of` (module
`Langlands.Representation.Classification.DiscreteSeriesOppositeToUpperAssembly`). It discharges
four of that assembly's hypotheses with the published theorems named above. Instead of using its
tempered-induction hypothesis, steps 1 and 5 use the semisimplicity result for square-integrable
`σ`. The assembly also derived temperedness of `σ`, but no step here needs it.

## Provenance

This route is derived, and the Lean proof is internal. It composes the published results named
above and adds no hypotheses or new analytic assertions. It corresponds to one direction of
Silberger's Theorem 4.5.18 (printed p. 193, PDF p. 199, `silberger-1979-harmonic-analysis`). For an
irreducible tempered `π`, that theorem relates two things: a square-integrable `ω` occurring as a
quotient of the opposite Jacquet module, and `π` occurring as a summand of both completely reducible
inductions. Its proof follows Theorem 3.3.1 (printed pp. 126-127, PDF pp. 132-133) and requires the
auxiliary modules to be tempered. Here those auxiliary modules are the scalar layers `τ` of step 3,
and the scalar-layer theorem gives their temperedness. Second adjointness replaces the source's
direct comparison of the two inductions. Silberger's Lemma 4.5.15 (printed p. 191) obtains complete
reducibility of the inductions from unitarity. Step 1 uses the same idea: the published
coefficient-integral form makes `σ` unitarizable.
