# The field-descent formula for a root set and a fine Levi flat

`HasFieldDescentFormulaIn R a₁ b` is the descent formula of `HasFieldDescentFormula`
([GMFamilyFieldDescent](GMFamilyFieldDescent.md)) with a Levi flat `a₁` in place of the whole
space; `hasFieldDescentFormula_iff_top` records that the two agree for `a₁ = ⊤`. The theorem
`hasFieldDescentFormulaIn` proves it for a root set `R`, a Levi flat `a₁`, and a subspace
`b ⊆ a₁` that is preserved by the orthogonal projection to the central space
(`IsCentreSplit R b`, [GMFamilyCentreReduction](../LinearAlgebra/GMFamilyCentreReduction.md))
and special in `a₁` for some positive weights
(`IsSpecialSubspace`, [GMFamilySliceSpecial](../LinearAlgebra/GMFamilySliceSpecial.md)).
This is J. Arthur, *The invariant trace formula. I. Local theory* (1988), §7, Proposition 7.1,
printed p.357, `arthur-1988-invariant-trace-formula-I`, in the form used for Lemma 17.5 and
(17.13) of J. Arthur, *An introduction to the trace formula* (2005), printed pp.99–100,
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, including the smooth supplementary
functions at every parameter.

## Proof

1. *Fine chambers and the induced family.* `exists_fine_parabolic_extension` and
   `inducedFamily_eq_of_extension` give the first two conjuncts
   ([GMFamilyInducedValues](../LinearAlgebra/GMFamilyInducedValues.md)).
   The lemma `isFamily_inducedFamily` gives the third
   ([GMFamilyCoarseFamilies](../LinearAlgebra/GMFamilyCoarseFamilies.md)).
2. *Smooth relative functions.* `exists_smooth_cQM` gives smooth `cQ Q` agreeing with
   `cQM R a₁ c₁ Q` where the denominators of the Levi component of `Q` do not vanish.
3. *Offsets in general position.* For a transverse Levi flat `L` and a root `r` with nonzero
   restriction to `L`, `badOffsets` is the subspace of offsets `ξ ∈ a₁ ⊓ bᗮ` whose descent point
   on `L` is orthogonal to `r`. To prove it is proper, `badOffsets_ne_top` projects `r` onto `L`
   to obtain `q` and takes `ξ` to be `q` minus its orthogonal projection to `b`. By
   `existsUnique_descentPoint`, the descent point for this offset is `q`, whose pairing with `r`
   is `‖q‖² > 0`. A finite union of proper subspaces is proper, so `exists_generic_offset`
   gives an offset in general position (`IsGenericOffset`).
4. *The identity at generic parameters.* `theta_extendParam_ne_zero` shows that the denominators
   of the relevant Levi components do not vanish at extended generic parameters. Every root
   contributing a denominator factor has zero restriction to the transverse Levi flat `L` and
   nonzero restriction to `a₁`, so `restrictedRoot_eq_zero_of_transverse` forces its restriction
   to `b` to be nonzero. The theorem `cM_eq_descentSum` proves the identity for generic offsets
   and for parameters in `genericParams R b` (no nonzero restricted root vanishes).
   It enlarges `b` to its hull by the
   orthogonal central directions (`cM_hull`, `dDescent_hull`, `descentSection_hull`,
   `isSpecialSubspace_hull`, `isGenericOffset_hull_iff`), which contains the central space, and
   applies `specialDescentFormula` ([GMFamilySpecialDescent](../LinearAlgebra/GMFamilySpecialDescent.md)).
5. *Density and continuity.* `genericParams R b` is dense (`dense_genericParams`, a finite
   intersection of dense open sets by `dense_biInter_finset_of_isOpen`), `theta b S` is continuous
   (`continuous_theta`), and `cM` of a family is continuous on the open set `regularParams R b`
   where all denominators are nonzero (`isOpen_regularParams`, `continuousOn_cM`). Define `c₀` as
   the right-hand side for one fixed generic offset `ξ₀`; it is smooth and agrees with `cM` on a
   dense subset of the regular parameters, hence on all of them. For another admissible offset
   `ξ`, the two right-hand sides are continuous and agree on the dense set of generic parameters,
   hence everywhere; so the identity holds at every parameter, including `0`.
