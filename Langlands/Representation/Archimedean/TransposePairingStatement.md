# Archimedean inverse-transpose pairing existence

This module states an unproved local prerequisite for the cuspidal
inverse-transpose argument. `RealTransposePairingStatement` and
`ComplexTransposePairingStatement` concern every positive matrix size
`n = r + 1` and every representation carrier `V : Type uV`, with `uV` free.
`ArchimedeanTransposePairingStatement` is their conjunction.

The hypotheses are exactly the existing `IsRealGKModule` or
`IsComplexGKModule`, `IsIrreducibleGKModule`, and `IsAdmissibleGKModule`
conditions. They include compact finiteness, continuity of compact matrix
coefficients, compatibility with differentiation, and compact adjoint
covariance. Irreducibility includes that `V` is nonzero and has no proper
nonzero subspace stable under both actions. Admissibility is finite
dimensionality of the intertwiner space from every continuous finite
dimensional compact representation.
No genericity, unitary structure, or choice of central character is supplied.

The conclusion is the existing `HasNonzeroTransposeGKPairing`. It asks for
a complex bilinear form `B : V × V → ℂ`, with `B ≠ 0`, satisfying

```text
B(ρ(k)y, ρ(transpose(k⁻¹))x) = B(y, x),
B(π(X)y, x) + B(y, π(ι(X))x) = 0.
```

Here `ι(z ⊗ Y) = z ⊗ (-transpose Y)`. The second equality quantifies over
the entire complexification of the underlying real matrix Lie algebra,
including at complex places. The first variable carries the original
action and the second carries its inverse-transpose twist. On real
orthogonal matrices the compact twist is the identity.

These are derived formulations of Aizenbud–Gourevitch,
*Generalized Harish-Chandra descent and applications to Gelfand pairs*,
arXiv:0803.3395v7 (17 May 2009), Theorem 8.2.1, p.23, with ordinary
transpose as the anti-automorphism. Definition 6.0.1, p.14, and
Corollary 7.6.3, p.22, supply its admissibility and distribution context.
Definition 8.1.1, p.22, specifies the admissible smooth Fréchet
representation category at archimedean places. Remark 8.2.2, p.23,
describes an alternative proof using Harish-Chandra regularity.
The theorem identifies the smooth contragredient with the inverse-transpose
twist. More explicitly, write `θ(g) = transpose(g⁻¹)` and choose the
resulting intertwining isomorphism `T : E^θ ≃ E^∨`. Evaluation gives the
complex bilinear form `B(y, x) = T(x)(y)`. Equivariance gives
`B(π(g)y, π(θ(g))x) = B(y, x)`. Restricting to the compact group and
differentiating gives the displayed two formulas, since the real
differential of `θ` is negative ordinary transpose. Extending that
differential complex linearly gives `ι` on the full tensor-product Lie
algebra.

Passing to the algebraic module uses globalization and restriction to
compact-finite vectors: Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), §4.4, p.120, between Theorem 4.4.14 and
Lemma 4.4.15. Apply the authors' October 2026 errata, p.1: the relevant
vectors in the Hilbert representation comparison are compact-finite,
and finite dimensional compact representations in the module definition
must be continuous. The Library module hypotheses retain that continuity:
each compact orbit span is finite dimensional and all its coordinate
matrix coefficients are continuous.

For the derived formulation, globalize the given irreducible admissible
module to `E`, identify the original module with `E`'s compact-finite
vectors, and restrict both arguments of the evaluation pairing to that
module. The inverse-transpose automorphism preserves the standard compact
group, so twisting preserves compact finiteness. Nonvanishing on the
restricted module uses the isomorphism `T`, continuity of its nonzero
dual functionals, and density of the compact-finite vectors in the
globalization. These are the category and nonvanishing comparisons a
formal proof must supply; they are not constructions in this module.

The provenance is derived, since this changes the source's smooth
Fréchet representation category (Definition 8.1.1, p.22) to the Library's
algebraic module category and requests only a nonzero pairing. A proof must
justify that comparison and the actual compact and differential formulas.
The module contains no such proof, no globalization construction, and no
claim of surjectivity onto a restricted dual. It also contains no global
tensor assembly or proof of the cuspidal target.

The source correspondence above was checked against the cited originals.
