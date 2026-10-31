# Nonzero Whittaker inheritance under normalized upper block induction

Authors: Worker 350; Worker 90 supplied the reused group-algebra
finite-generation argument.

`Langlands.Whittaker.normalizedInheritance.{uF,uV} F T` proves exactly
`Langlands.Whittaker.NormalizedInheritanceStatement.{uF,uV} F T`.
Its outer parameters are `{p : ℕ} [Fact p.Prime]`,
`F : PadicField.{uF} p` and arbitrary compatible `T : F.TopologicalData`.
The field and representation universes remain independent.

After installing `T.topology`, the theorem takes an ordered positive block
shape `B` of `n + 1`, smooth complex representations
`σ i : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)`,
and a bundled continuous nontrivial unitary additive character `ψ`. Each
block hypothesis supplies `m`, `h : B.size i = m + 1`, and genericity of
`(h ▸ σ i).representation`. The conclusion is a nonzero standard
Whittaker functional on the actual representation of
`(T.normalizedProductInductionFunctor B).obj σ`. The induced representation
may be reducible. Rank one is included.

## Published inputs and proof route

The proof imports the closed theorems
`Langlands.Whittaker.multiplicityOne` from
`Langlands.Representation.Whittaker.MultiplicityOneProof` and
`Langlands.inducedWhittakerType` from
`Langlands.Representation.Whittaker.InducedWhittakerTypeProof`.
Neither theorem is an additional hypothesis of this result.

The private helper `genericFactorData` obtains the three block properties
needed by the upper unnormalized heredity theorem. It eliminates the supplied
rank equality on the original smooth representation, then extracts
irreducibility, admissibility and a nonzero functional from `IsGeneric`.
Installing irreducibility as a local instance gives finite generation over
the actual block group algebra: Mathlib identifies the associated module as
simple and hence finitely generated. This concerns group-algebra finite
generation and imposes no finite complex dimension. The helper applies
`multiplicityOne.{uF,max uF uV}` and takes the existence part of its unique
scalar conclusion. Consequently every functional is a scalar multiple of
the extracted nonzero functional.

Both the helper and the main proof reconcile the supplied topology with the
canonical input topology of these closed theorems.
`T.topology_eq_canonicalNormTopology` supplies the equality. The proof
destructs `T`, eliminates this equality, and reconstructs its topological-data
record with the transported valuation, valuative-extension, module-topology
and local-field fields. It retains the original valuation data. Equality
elimination transports all dependent representation, smoothness, character
continuity, admissibility and induction data together. In this context the
canonical topologies used by the two imported statements agree definitionally.

For the main proof put `ρ i = (σ i).representation` and
`τ = T.blockHalfTwist B ρ`. These are the concrete positive-half twists.
`isAdmissible_blockHalfTwist_iff` transfers block admissibility, and
`finite_asModule_twist_iff` transfers finite generation over each block group
algebra. Since `blockHalfModulus_upperUnipotent` makes the twisting character
trivial on each block's upper unipotents, `twistFunctionalEquiv` identifies
the entire corresponding functional spaces. Its underlying linear map
preserves the chosen functional's values, hence nonvanishing. Applying its
inverse to an arbitrary twisted functional and then using linearity
transfers the spanning condition.

The raw heredity theorem uses an unbundled complex additive character.
The proof uses `ψ.complex`, its published continuity and norm-one laws, and
derives its nontriviality by character extensionality from `ψ.nontrivial`.
`entrywiseCharacter_eq_standardCharacter` identifies the block functional
spaces, and `mem_functionals_entrywiseCharacter_iff` converts their membership
to the raw matrix-entry covariance required by `inducedWhittakerType`.
The block-to-induced direction of that theorem yields a nonzero equivariant
linear form on

```text
Induction.smoothInduced (B.parabolic F.Carrier)
  ((FiniteTensor.external τ).comp (B.leviProjection F.Carrier)).
```

The proof retains that form and its nonvanishing. It converts the raw
covariance back to functional-submodule membership and identifies the
entrywise character with the standard superdiagonal-sum character.
Finally, `hasFunctional_iff_of_equiv` pulls this nonzero functional back
along `T.normalizedProductHalfAbsorptionEquiv B ρ`.

This equivalence starts at the target's actual normalized upper block
induction and ends at the displayed unnormalized induction of the
half-twisted factors. Its maps preserve every induced-function value. The
normalization is therefore the existing positive half modulus in left
parabolic covariance, with the existing right-translation group action.
The proof adds no irreducibility, genericity or functional-existence
assumption on the induced representation.

## Provenance and original sources

This is an internal composition of published theorems and concrete
transport constructions. Worker 350 authored it from the earlier private
conditional assembly after both substantive inputs became available.
Worker 90's reused contribution is the local-instance finite-generation
argument. The imported heredity and multiplicity-one proofs are reused by
Lean name; their companion Markdown describes their own constructions and
source routes.

For the composition used here, Worker 350 directly read the registered
JPSS original, printed pp.377 and 385–387, visually, and Kudla printed
pp.367–368, including visual verification of the normalization formula.
JPSS §2.1 distinguishes nonzero functional existence from dimension one,
and §2.3 states the dimension-one heredity equivalence for admissible
finite-type factors. Its induction there is normalized and lower
parabolic. The imported upper unnormalized theorem and the actual
positive-half absorption implement the comparisons used here; this module
asserts no definitional lower-to-upper identification. Kudla §1.1 records
upper parabolics, positive-half covariance and right translation.
No source-specific erratum affecting these passages was found in the
supplied project and Library notes.

- H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
  *Rankin–Selberg Convolutions*, American Journal of Mathematics 105 (1983),
  367–464, §0.3 printed p.377 and §§2.1–2.3 printed pp.385–387.
  Registered source `jpss-1983-rankin-selberg`, SHA256
  `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
- S. S. Kudla, *The local Langlands correspondence: the non-archimedean
  case*, in *Motives*, Part 2, Proceedings of Symposia in Pure Mathematics
  55 (1994), 365–391, §1.1 printed pp.367–368, especially (1.1.3)–(1.1.4).
  Registered source `kudla-1994-local-langlands-nonarchimedean`, SHA256
  `0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b`.
