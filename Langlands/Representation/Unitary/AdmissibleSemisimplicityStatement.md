# Admissible unitary representations are algebraically semisimple

`Langlands.AdmissibleUnitarySemisimplicityStatement` states a general
prerequisite for the complete-reducibility conclusion of tempered parabolic
induction. It is a proposition definition, not a proof.

## Exact scope

Let `G : Type uG` be a topological group for which every open subgroup contains
a compact open subgroup. Let `V : Type uV` be any algebraic complex module,
with `uV` independent of `uG`, and let `ρ` be an actual representation of `G`
on `V`. If `ρ` is admissible and unitarizable, then
`Representation.IsSemisimpleRepresentation ρ` holds.

The imported `IsAdmissible` predicate includes smoothness and finite-dimensional
fixed spaces for open subgroups. `IsUnitarizable` means the existence of an
actual invariant positive definite Hermitian form. The conclusion means that
every invariant subspace has an invariant algebraic complement, as expressed
by `ComplementedLattice (Subrepresentation ρ)`. The statement includes the zero
representation. It imposes no irreducibility, finite length, finite dimension
of `V`, chosen norm, or Hilbert completeness. The compact-open cofinality
hypothesis is explicit; local compactness and total disconnectedness are not
silently inferred for an arbitrary topological group.

## Internal provenance and derivation

This is an internal consequence of the Library's admissible smooth-dual
identification, rather than a new translation of an external source theorem.
The route uses the published constructions in
[HermitianDual](HermitianDual.md), together with admissibility inheritance under
injective intertwiners from
[EmbeddingProof](../Smooth/Admissibility/EmbeddingProof.md).

Choose an invariant positive form `b`. For any invariant subspace `S`, its
restriction is again a positive invariant form, and `S` is admissible. For
`v ∈ V`, the functional `s ↦ b(v,s)` on `S` is smooth, since the original
functional is smooth and pullback through the inclusion preserves smoothness.
The surjectivity of the smooth-dual identification for `S` gives `s₀ ∈ S`
with `b(s₀,s) = b(v,s)` for all `s ∈ S`. Hence `v - s₀` is orthogonal to `S`.
The orthogonal subspace is invariant by invariance of `b`, and intersects `S`
only at zero by positive definiteness. This proves the asserted complement
property. Finite-dimensional Riesz representation is needed only in the
already implemented smooth-dual identification, on compact-open fixed spaces.

This argument explains the proposed statement. Its exact Lean proof is a
separate publication obligation. It does not establish existence of a unitary
form for a tempered representation, preservation of that form by normalized
induction, or analytic temperedness of the induced representation.
