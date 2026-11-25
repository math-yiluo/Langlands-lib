# Invariant generating sections along a cartesian étale relation

`Langlands.AlgebraicGeometry.Picard.EquivariantInvariantSectionStatement.{u}`
quantifies, in the scheme universe `u`, over:

- affine schemes `S` and `U` and a flat surjective morphism `p : U ⟶ S`;
- an actual étale equivalence relation `E`, with chart `E.U`, relation scheme
  `E.R` and projections `E.t, E.s : E.R ⟶ E.U`;
- a quasi-compact and quasi-separated morphism `f : E.U ⟶ U`;
- a proof of `IsPullback E.t (E.s ≫ f) (f ≫ p) p`, i.e. that the square

```text
E.R  --E.t-->  E.U
 |               |
E.s ≫ f        f ≫ p
 |               |
 v               v
 U  ----p---->   S
```

  is cartesian;
- an actual equivariant line bundle `B : EquivariantLineBundle E`, a global
  section `σ` of its chart bundle `B.bundle.obj`, and a point `x` of `E.U`
  with `x ∈ trivializationOpen B.bundle.obj σ`.

It asserts that some global section `m` of `B.bundle.obj` satisfies
`x ∈ trivializationOpen B.bundle.obj m` and
`E.IsInvariantOpen (trivializationOpen B.bundle.obj m)`.

`trivializationOpen M s` is the union of the opens on which the morphism
`O ⟶ M` sending `1` to `s` is an isomorphism; for a line bundle it is the
nonvanishing locus `X_s`. `E.IsInvariantOpen V` means
`E.s ⁻¹ᵁ V = E.t ⁻¹ᵁ V`. The hypotheses are those of the target
`PolarizedEtaleRelationEffectivityStatement` weakened to what the argument
below uses: `p` étale is replaced by flat, and `f` smooth and proper by
quasi-compact and quasi-separated. Ampleness is not assumed. Only the degree
one sections of the chart bundle occur; the statement says nothing about the
transport of `B` beyond the existence of an invariant generation locus.

## Provenance

Derived. Write `S = Spec A`, `U = Spec A'`, `X = E.U` and `L = B.bundle`.
The cartesian square identifies `E.R` with `X ×_S U`, and by the symmetry of
`E` also with `U ×_S X`. Flat base change for the quasi-compact and
quasi-separated morphism `X ⟶ S` identifies the global sections of `t^*L`
and `s^*L` on `E.R` with `Γ(X, L) ⊗_A A'` and `A' ⊗_A Γ(X, L)`. The
transport of `B` on the universal related pair, together with its cocycle
law on `E.R ×_{E.U} E.R`, is therefore a descent datum for the `A'`-module
`M = Γ(X, L)` along the faithfully flat ring map `A ⟶ A'`. Faithfully flat
descent of modules (Stacks Project, Section 35.3, tag
[023F](https://stacks.math.columbia.edu/tag/023F), Proposition 35.3.9, tag
[023N](https://stacks.math.columbia.edu/tag/023N): every descent datum on
modules along a faithfully flat ring map is effective, with inverse given by
the invariants) shows that `M ≅ A' ⊗_A M_0` for the invariant elements
`M_0`, so `M_0` generates `M` as an `A'`-module. Writing
`σ = Σ a_i m_i` with `m_i ∈ M_0`, some `m_i` does not vanish at `x`. An
invariant section has transport-compatible pullbacks along `E.t` and `E.s`,
so its nonvanishing locus is invariant.

This is the step of descending relatively ample line bundles in which global
generation of descended sections is checked; compare the proof of Lemma
74.13.1, tag [0D3C](https://stacks.math.columbia.edu/tag/0D3C), cited by the
target statement. The Lean statement isolates the single geometric
consequence needed by the target's proof.

## Intended use

In the proof of `PolarizedEtaleRelationEffectivityStatement`, the chart is
covered by invariant opens of the form `trivializationOpen L' m` for
equivariant powers `L'` of the polarization (see
`EquivariantLineBundleTensorPowStatement`), and
`ProperAmpleSectionOpenAffineStatement` makes these opens affine.

This module defines the proposition only and proves nothing.
