# Cancellation of essential finite presentation in an algebra tower: proof

The theorem `Langlands.Algebra.essFinitePresentationTowerCancellation.{u, v, w}`
proves the published proposition
`Langlands.Algebra.EssFinitePresentationTowerCancellationStatement.{u, v, w}`.
Its complete type is exactly that proposition, with no outer parameters.
For commutative rings `R : Type u`, `S : Type v`, and `T : Type w`, given
`Algebra R S`, `Algebra S T`, `Algebra R T`, and `IsScalarTower R S T`, it proves

```text
EssFinitePresentation R S → EssFinitePresentation R T → EssFinitePresentation S T.
```

The three universes are independent. The conclusion uses the given
`S`-algebra structure on `T`. The statement, the `EssFinitePresentation`
predicate, and every imported Lean/Markdown pair are unchanged.

## Implemented proof

The private helper `essFiniteType_of_essFinitePresentation` converts a witness
of the published predicate into Mathlib's `Algebra.EssFiniteType R S`.
It unpacks the witness as a finitely generated ideal `I` of
`MvPolynomial (Fin n) R`, a submonoid `M` of the quotient `A`, and an
`R`-algebra equivalence `e : Localization M ≃ₐ[R] S`.
`Algebra.FinitePresentation.quotient hI` gives finite presentation of `A`
over `R`. Mathlib's instances then give finite type, essential finite type,
and essential finite type of `Localization M`. Finally,
`Algebra.EssFiniteType.iff_of_algEquiv e` transfers this property to `S`.
The helper adds no hypothesis and proves no cancellation assertion.

The closing theorem introduces the rings, their instances, and the two
essential-finite-presentation hypotheses `hS` and `hT`. Let

```lean
μ : S ⊗[R] T →ₐ[S] T := (AlgHom.liftEquiv R S T T) (AlgHom.id R T).
```

This is the canonical map `s ⊗ t ↦ algebraMap S T s * t`, using the given
`S`-action on `T`. It is surjective: every `t : T` is the image of `1 ⊗ t`.
The proof supplies this preimage explicitly and simplifies its image.

The published theorem `Langlands.Algebra.tensorRetractionKernelFG`,
applied to the essential-finite-type result from `hS`, gives
`(RingHom.ker μ.toRingHom).FG`. Its proof uses the finite essential
generators of `S` over `R`: the kernel is the ideal spanned by the differences
`s ⊗ 1 - 1 ⊗ algebraMap S T s` for those generators. Equality of the
two maps from `S` to the quotient follows from
`Algebra.EssFiniteType.algHom_ext`, and tensor induction gives equality of
that ideal with the kernel. This supporting theorem is imported from
`Langlands.Algebra.TensorRetractionKernelFGProof`.

Next `Langlands.Algebra.essFinitePresentation_baseChange S hT` gives
essential finite presentation of `S ⊗[R] T` over `S`, for its canonical
left-factor algebra structure. The published finitely generated ideal
quotient theorem `Langlands.Algebra.essFinitePresentationFiniteQuotient`
therefore gives

```text
EssFinitePresentation S ((S ⊗[R] T) / ker μ).
```

Mathlib's `Ideal.quotientKerAlgEquivOfSurjective hμ` is an `S`-algebra
equivalence from this quotient to `T`. Applying the published
`Langlands.Algebra.essFinitePresentation_of_algEquiv` transports the
quotient result to `EssFinitePresentation S T`, which is the required
conclusion for the given `S`-algebra structure.

## Derived provenance and scope

This is an internal proof of the already published cancellation statement.
It uses a tensor product, its finitely generated retraction kernel, and the
published base-change, finite-ideal-quotient, and algebra-equivalence
transport results. It implements a different route from the finite-denominator
lifting argument described informally in the statement companion. It is
not presented as a transcription of a separately numbered literature result.
The companion's original-source discussion supplies context for the target;
the implemented derivation is the sequence of Library and Mathlib results
explained above.

The Mathlib dependency is pinned at commit
`5ed2965256430c3649e86755f9576b54eca72435`, particularly
`Mathlib.RingTheory.EssentialFiniteness` and the quotient-kernel
algebra equivalence in `Mathlib.RingTheory.Ideal.Quotient.Operations`.
The proof assumes no locality, Noetherianity, field structure, injectivity,
nontriviality, finite generation of denominators, or equality of universes.
Arbitrary localization submonoids and zero rings are permitted by all the
interfaces used here.

Worker 696 implemented this cancellation proof and its explanation.
