# Degree-bounded invariant lifts for actual Cartan tensor actions

This is an internal consequence of the actual bounded Cartan tensor action and
source compact averaging. It retains arbitrary number-field universe, every
natural rank and the whole standard compact subgroup.

Let `τ` be a finite dimensional continuous compact representation, let `V` be any
genuine enveloping module with its compatible complex scalar action, and let `j`
be a complex linear map from the canonical space of `τ` into `V`. Assume a compact
representation `ρ` on `V`, equivariance of `j`, and compatibility of `ρ` with the
actual enveloping conjugation action. No topology or finite continuous orbit
condition is imposed on `V`.

`cartanInvariantTensorAction` restricts the actual map
`P ⊗ v ↦ sym_p(P) • j(v)` to actual compact fixed Cartan covariants and takes values
in `ρ.invariants`. Equivariance of the previously constructed tensor action and
fixedness of its argument give fixedness of its image. This construction requires
only `Field K`; the averaging results additionally require `NumberField K`.

The existing compact covariant average is the algebraic finite-span integral
under normalized Haar measure. In this module the same measure is given a private
name, with explicitly named Borel and probability instances; its normalization
set is again the whole compact group. All these measures are definitionally the
same. The diagonal compact action preserves the actual bounded tensor span, so
the generic submodule-preservation result for source averages proves
`cartanSymmetricCovariantAverage_mem_degreeFiltration`.

If a tensor has a fixed image under the actual action map, equivariance makes
that image constant along its source orbit. The generic constant-image averaging
lemma therefore proves `cartanTensorAction_average_eq_of_fixed`. It integrates
only the source orbit, whose finite continuous span is already proved; the
target needs no integration construction.

For `exists_cartanInvariantTensorAction_preimage_degree`, start from a fixed
target vector in `cartanSymmetrizationSpan d • range j`. The previously proved
image equality supplies a tensor preimage with degree bound `d`. Its actual
compact covariant average remains within that bound, is compact fixed by its
codomain, and retains the target image by the constant-image lemma. This gives a
fixed preimage with exactly the same upper degree bound.

Finally, when `range j` is stable under every actual complex compact Lie
generator, the existing filtered Cartan spanning equality identifies this
bounded action span with `F_d • range j`. Rewriting by that equality gives
`exists_cartanInvariantTensorAction_preimage_envelopingDegree`.

These are degree-bounded invariant preimage results. They do not establish
finite central generation, admissibility or automorphic differential growth.
