# Local product geometry and normalized factor measures

This internal continuation of `CompactOpenFactorNormalization` concerns
literal ordered subgroup coordinates. The motivating source passages
are Waldspurger (2003), IV.1, printed p.279 (PDF p.45), and IV.1(12),
printed p.283 (PDF p.49). Their actual general reductive geometric and
analytic assertions remain separate obligations.

For a literal homeomorphism `m : H × X ≃ₜ G` with
`m(h,x) = h * s(x)`, the actual quotient chart sends `x` to `H*s(x)`.
If `A` is nonempty and `m '' (A × B) = T`, then
`factorQuotientHomeomorph_image_of_localProduct` proves
`c '' B = leftQuotientMap H '' T`. Multiplication by an element of `H`
does not change the left coset. One fixed element of `A` proves the
forward inclusion; the local factorization proves the reverse inclusion.
This lemma allows independent universes for `G` and `X`; `X` needs
only a topology and is not assumed to be a group.

Now let `H` and `K` be subgroups of a locally compact Hausdorff
topological group `G`, with `H` closed, and supply literal
`H × K` multiplication coordinates. Use Borel structures on `G`,
`H`, `K` and the actual left quotient. Let `μG`, `μH`, `μK`
be regular Haar measures, with right invariance on `μH` and `μK`,
and let `ν` be a compatible Weil measure for `μG` and `μH`.
Let `S` and `B` be compact open subgroups of `G` and `K`.

If `m '' ((H ∩ S) × B) = S`, the preceding set lemma supplies the
quotient orbit identity, since `1` belongs to `H ∩ S`.
`IsCompatible.measurePreserving_compactOpenFactorMeasure_of_localProduct`
therefore derives exact quotient preservation for the explicit
compact-open volume normalization. Neither a quotient orbit identity
nor a local mass identity is a separate input to this theorem.

`IsCompatible.compactOpenFactorMeasure_eq_of_localProducts` compares two
choices of compact open subgroups and two regular two-sided seed Haar
measures on `K`. Each choice must satisfy its own local product identity.
Both normalized measures equal the inverse-chart pushforward of the
same compatible measure `ν`, so they are equal. The ambient and
intersection measures and the literal chart are held fixed. This
establishes independence of those auxiliary choices without identifying
an independently prescribed source normalization.

The definition `compactOpenFactorProductMeasure` is `μH` times the
explicit normalized complement measure. If the seed product
`μH.prod μK` is regular and `μK` is S-finite, its regularity passes
to the new product: multiplication of the second factor by the finite
nonnegative real normalization scalar multiplies the product by that
scalar.

With `BorelSpace (H × K)` and S-finiteness of both seed factors,
`IsCompatible.measurePreserving_compactOpenFactorProductMeasure`
proves that literal multiplication pushes this constructed product
measure to `μG`. It applies the exact quotient result and the preceding
real Weil/Fubini product theorem. Regularity is required only for the
seed product and is transferred to the normalized product. No full
ambient product identity is assumed, and no second-countability
assumption is used.

The literal global coordinates, local compact-open product geometry,
compatible Weil measure and displayed measure/topological hypotheses
remain inputs to applications. Their general reductive realization and
comparison with separately fixed source measures remain open. The
construction does not introduce commutation or normality of the factors;
it does not assert that multiplication is a group homomorphism.
Intertwiner convergence, rational continuation and all whole-program
Plancherel completion conditions remain open.
