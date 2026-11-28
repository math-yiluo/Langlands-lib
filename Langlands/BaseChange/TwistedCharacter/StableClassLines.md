# Twisted character distributions indexed by stable irreducible classes

Let `G` be a topological group with an automorphism `θ`. Any two
twisting isomorphisms of a θ-stable irreducible admissible representation
differ by a scalar. So for a fixed measure its twisted traces, and those
of equivalent representations, are scalar multiples of one distribution;
they span a space of dimension at most one. They can all vanish: for the
zero measure every twisted trace is zero. For a Haar measure, and when
arbitrarily small compact open subgroups are stable under `θ⁻¹`, they are
nonzero and the class distributions are linearly independent (see
below). This module indexes these distributions by equivalence classes.

## Classes and their distributions

- `StableIrreducibleClass θ` is the type of classes in
  `SmoothDualClass` (irreducible admissible representations with carrier
  in universe `z`, up to equivalence) that contain a representation with
  a twisting isomorphism `π ≃ π ∘ θ`.
- `smoothDualClass_ofRep_eq_iff`: two irreducible admissible
  representations have the same class exactly when they are equivalent.
- `StableIrreducibleClass.rep` and `StableIrreducibleClass.intertwiner`
  choose a representative and a twisting isomorphism.
  `StableIrreducibleClass.mk` is the class of a given pair.
  `nonempty_rep_equiv_mk` and `eq_of_equiv` relate classes to
  equivalence of representatives.
- `StableIrreducibleClass.trace θ μ c` is the twisted trace of the chosen
  representative with the chosen twisting isomorphism. The measure `μ` is
  left-invariant and finite on compact sets, on a locally compact totally
  disconnected Hausdorff group. This allows the zero measure, for which
  the trace is zero.
- `twistedDistribution_eq_smul_stableIrreducibleClass_trace`: the twisted
  trace of any irreducible admissible representation in the class `c`,
  with any twisting isomorphism, is a scalar multiple of
  `StableIrreducibleClass.trace θ μ c`. This is
  `exists_twistedDistribution_eq_smul_of_equiv`.
- `linearIndependent_stableIrreducibleClass_trace`: for a Haar measure,
  suppose arbitrarily small compact open subgroups are stable under
  `θ⁻¹`. Then the class distributions are linearly independent. This is
  `twistedDistribution_linearIndependent`, applied to the chosen
  representatives of finitely many distinct classes.

The private class type `StableClass` and its distributions in
`Langlands.BaseChange.TwistedCharacter.SpectrumLines` follow the same
construction; this module makes it public so that other modules can
index the distributions by classes.

## Heads

`Classification.IsIrreducibleHead ρ π` says that `π` is irreducible and
there is a surjection `q : ρ → π` such that every surjection of `ρ` onto
an irreducible representation, on a carrier in the universe of the
carrier of `ρ`, has the same kernel as `q`.

- `nonempty_twistingEquiv_of_isIrreducibleHead`: if `ρ` has a twisting
  isomorphism and `π` is its irreducible head, then `π` has one. Composing
  the quotient map with the twisting isomorphism of `ρ` gives an
  irreducible quotient of `ρ` onto `π ∘ θ`. Its kernel equals that of the
  head, so `π ≃ π ∘ θ`
  (`Classification.SegmentHeadJacquetReduction.nonempty_equiv_of_ker_eq`).
- `nonempty_equiv_of_isIrreducibleHead_of_isIrreducible`: an irreducible
  representation is equivalent to its irreducible head, since the quotient
  map is then injective.

Linear independence of twisted characters of pairwise inequivalent
σ-stable irreducibles is the Lemme of Henniart–Lemaire (2011), II.2.8,
printed p. 69.
