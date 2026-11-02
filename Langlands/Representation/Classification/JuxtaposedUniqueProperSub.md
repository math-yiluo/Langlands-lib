# At most one nonzero proper subrepresentation of ⟨Δ₀⟩ × ⟨Δ₁⟩

Helper module for the juxtaposed case of Zelevinsky 1980, Proposition 4.6
(step (1)). It combines the earlier helper modules into the lattice conclusion of
the counting argument.

## Setting

`ρ` is a cuspidal datum of rank `r`, represented by the supercuspidal representation
`A`. `d` is a segment-product datum on `GL_((q+l) r)` with two segment socles:
`Δ₀ = d.segments 0` begins at `ν^l ρ` and has length `q`, and `Δ₁ = d.segments 1`
begins at `ρ` and has length `l`. `C` is the uniform shape `(r, …, r)` with `q + l`
blocks, and `J` is the normalized Jacquet functor along `C`. `τ_S` is the shuffle
tensor `⊗ₖ ν^(e_S(k)) A` of `TwoSegmentSocleShuffleJacquet`, with runs starting at
`l` and `0`.

## Statements

- `hasMultiplicityFreeCompositionSeries_jacquet`: assume the Library statement
  `TwoSegmentSocleShuffleJacquet` (statement task efe00a4a; its proof is task
  343ddfde) as a hypothesis. Then `J(d.induced)` has a multiplicity-free
  composition series.
- `eq_of_ne_bot_of_ne_top_induced`: the result also assumes the following.
  - `NonassociatedJacquetSubquotientsTheorem` on `GL_((q+l) r)` (BZ77 2.13(b), a
    Library statement, proved as `CuspidalSupport.nonassociatedJacquetSubquotients`
    in task b17b8c8c; here a hypothesis).
  - `hswap`: the two orders of `ν^a A × ν^b A` on the uniform shape `(r, r)` are
    isomorphic for all natural numbers `a, b` with `b + 1 < a`.

  Then any two subrepresentations of `d.induced` that are neither `⊥` nor `⊤` are
  equal.

## Proof

1. *Multiplicity freeness.* Clause 1 of the shuffle count gives a composition
   series with simple factors. Fix an irreducible `τ`. By clause 2 its
   multiplicity equals the number of shuffle sets `S` with `τ_S ≃ τ`. There is at
   most one such set: if `τ_S ≃ τ ≃ τ_{S'}`, then `S = S'` by
   `eq_of_shuffleTensor_equiv` (JuxtaposedShuffleDistinct). Every multiplicity is
   therefore at most `1`, and `hasMultiplicityFreeCompositionSeries_of_le_one`
   (JuxtaposedSupportLattice) applies.
2. *Lattice argument.* Apply `eq_of_ne_bot_of_ne_top` (JuxtaposedSupportLattice)
   with `A = J(d.induced)`, `Φ = jacquetImage` (the image of `J(X)` in
   `J(d.induced)`), and `Bad τ` meaning `τ ≃ τ_{S_id}`. Its hypotheses come from
   these lemmas:
   - Strict monotonicity of `Φ`: `jacquetImage_strictMono` (JuxtaposedJacquetImage).
     Its hypothesis, that every nonzero step quotient has a nonzero Jacquet
     module along `C`, is `nontrivial_jacquet_stepQuotient`
     (JuxtaposedJacquetPositivity). That lemma uses three inputs:
     - the embedding `d.induced ↪ i_C(τ_{S₀})` of `exists_injective_initShuffle`
       (JuxtaposedInitialEmbedding);
     - the Library theorem `minimalNonzeroJacquet`;
     - quasicuspidality of `τ_{S₀}`, from the Library theorem `glCuspidalTensor`
       applied to the twisted supercuspidal factors `segmentSupercuspidalFactor`.
   - `Φ` preserves intersections: `jacquetImage_inf`.
   - Any two `Bad` representations are equivalent, through `τ_{S_id}`.
   - Cover: `mem_jordanHolderSupport_jacquetImage_of_ne_id`
     (JuxtaposedJacquetCover).

Positivity of `q + l` comes from the positive length of `Δ₀`.

## Use

The final assembly applies this to the socle `ω₀`. Either `d.induced` is
irreducible, or its unique nonzero proper subrepresentation is `ω₀`. In the second
case every nonzero proper subrepresentation equals `ω₀`, so `ω₀` and
`d.induced / ω₀` are irreducible.
