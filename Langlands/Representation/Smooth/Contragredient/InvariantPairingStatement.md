# Smooth-dual perfectness of an invariant bilinear pairing

Author: Worker 166.

`Langlands.SmoothInvariantPairingDualityStatement` is a proposition definition
awaiting proof. The group `G`, admissible carrier `V`, and smooth carrier `W`
have independent universes `uG`, `uV`, and `uW`. Each carrier is an additive
commutative group and a complex module; neither carries a topology or a norm.
The group has a topology, and the proposition quantifies an
`IsTopologicalGroup G` instance.

The group hypothesis is compact-open cofinality: every `K : OpenSubgroup G`
contains an `L : OpenSubgroup G` whose underlying set is compact. This is the
explicit hypothesis used by the existing compact fixed-vector duality,
smooth-dual separation, and admissible bidual reflexivity results.

For actual representations `ρ` on `V` and `σ` on `W`, assume `IsAdmissible ρ`
and `IsSmooth σ`. The first includes smoothness and finite-dimensional fixed
spaces for open subgroups. It does not require finite dimension of `V`.
There is no separate admissibility hypothesis on `σ` and no finite-dimensional
hypothesis on `W`, finite-length assumption, or irreducibility assumption.

The supplied map `b : W →ₗ[ℂ] V →ₗ[ℂ] ℂ` is complex bilinear. Simultaneous
invariance means

```text
b (σ g w) (ρ g v) = b w v
```

for every `g`, `w`, and `v`. The two nondegeneracy hypotheses say explicitly
that a `w` pairing to zero with every `v` is zero and that a `v` pairing to
zero with every `w` is zero. There is no complex conjugation.

The conclusion asks for an actual complex-linear representation equivalence

```text
E : Representation.Equiv σ (smoothContragredient ρ)
```

with `smoothDualPairing ρ (E w) v = b w v` for every `w` and `v`. Thus it is
the map defined by the supplied pairing that must be an equivalence. Its
values must be smooth functionals, and it must intertwine the inverse-argument
action on the actual smooth dual. Neither the smoothness of these functionals
nor bijectivity is a premise. The definition uses the existing smooth dual,
evaluation pairing, and representation equivalence without replacing their
carriers or actions. Trivial groups and zero representations are included.

The provenance is internal mathematics over the published smooth dual and
compact averaging constructions. No external source theorem is attributed to
this formulation. A proposed proof uses compact-open fixed-vector duality:
compact averaging transfers the two nondegeneracy hypotheses to fixed spaces,
the admissible side is finite-dimensional there, and finite-dimensional duality
gives perfectness on each compact-open fixed space. Compact-open cofinality
then accounts for every smooth functional. This is a rationale for the target,
not a proof supplied by this file.

This statement supplies no invariant pairing, Haar measure, integrability,
ambient integral invariance, or nondegeneracy theorem for induction or Jacquet
modules. Its explicit admissibility hypothesis must be established in any
application. It proves no induction duality, Jacquet duality, second adjointness,
relative multiplicity comparison, or irreducible-head consequence.
