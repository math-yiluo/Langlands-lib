# Finite covers by relative Noether-normalization pieces

Author: Worker 90.

This module defines geometric data and states their existence. It contains no
existence proof or point-count estimate.

## The data

For a scheme morphism `f : X → S`, a `FiniteNormalizationCover f` consists of
finitely many pieces indexed by `Fin count`. Each piece has an affine scheme
`Tᵢ = base i`, an immersion `tᵢ : Tᵢ → S`, an immersion `jᵢ : Uᵢ → X`, a
natural number `dᵢ`, and a finite surjective morphism
`νᵢ : Uᵢ → A^(dᵢ)_(Tᵢ)`. The coordinate index is `ULift (Fin dᵢ)` to keep
relative affine space in the same universe. The maps satisfy
`νᵢ ≫ (A^(dᵢ)_(Tᵢ) → Tᵢ) ≫ tᵢ = jᵢ ≫ f`.

The `covers` field says that every actual morphism `Spec K → X`, for every
field `K` in that universe, factors through at least one `jᵢ`, over the same
field. No extension of the field is allowed in this condition. Pieces may
overlap. The `dimension_le` field says that for every point `t` of `Tᵢ`,
`dᵢ ≤ dim(X_(tᵢ(t)))`, where the right side is the topological Krull
dimension of the residue-field fibre of the original morphism `f`. Dimensions
are compared in `WithBot ℕ∞`, including empty fibres.

## The existence statement and provenance

`FiniteNormalizationCoverStatement` asserts the existence of these data for
every locally finite type, quasi-compact morphism over a Noetherian scheme.
The source and base have no separatedness, reducedness or equidimensionality
hypothesis.

Provenance: derived. The original normalization input is the Stacks Project,
Lemma 10.115.4, Tag 00OY, in `00OY.html` of registered source
`stacks-dimension-fibres-normalization-2026-11-04`. It gives a finite injective
polynomial algebra with number of variables equal to the dimension of a
nonzero finite-type algebra over a field. The original affine relative
formulation is Section 33.18, Tag 0CBG, especially Lemma 33.18.2, Tag 0CBI,
in `varieties.tex`, labels `section-noether-normalization` and
`lemma-noether-normalization-affine`, of registered source
`stacks-flasque-affine-vanishing-kunneth-a04446e5` (commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`). That lemma makes the
normalization finite on a specified fibre; it does not itself assert the
finite cover stated here.

The additional finite-cover assertion is a derived geometric prerequisite.
Its intended proof is Noetherian induction on reduced closed base subsets.
On each reduced irreducible base component, choose a dense affine open and
finitely many affine source charts. Apply field Noether normalization over
the generic residue field to each nonempty generic chart. Clear finitely
many denominators in the coordinates and monic integrality equations to
obtain finite maps over a smaller dense affine open of the base. The
polynomial algebra remains injective: a relation over the integral base
would give a relation over its fraction field. Thus these maps are
surjective on spectra. A chart with empty generic fibre becomes empty
after shrinking. Apply the induction hypothesis to the reduced closed
complement.

Reduced base strata suffice because all maps from spectra of fields kill
nilpotents and factor through the appropriate locally closed base stratum.
The source charts after this base change immerse into `X`, so every
field-valued point is covered without changing its field. Finite
surjectivity gives dimension `dᵢ` for each normalized fibre; the base
immersion preserves residue fields, and the source immersion then gives
the stated lower bound on the dimension of the original fibre.

## Intended consumer and status

The finite maps will give uniform bounds on the number of points above
each point of affine space. The base immersions make a field-valued base
lift unique, and `dimension_le` supplies the exponent needed for
`FamilyPointUpperBoundStatement`.

The existence statement remains unproved. Its fields are geometric
conditions, with no Lang–Weil, Hasse–Weil, Bertini or point-count conclusion
among them.
