# Nilpotence and commutation on actual generalized-weight blocks

Statement prepared by Worker 709; source comparison and formulation details
checked by Worker 1194. This proposition supplies no proof. Its
actual construction is imported from the published
`Langlands.Representation.IntegerLattice.GeneralizedWeightBlock` module.

`Langlands.CommutingTupleNormalizedBlockNilpotenceStatement` quantifies over
every natural rank `d`, every complex vector space `V : Type u` of finite
dimension, the actual commuting invertible tuple `A`, and every label tuple
`c : Fin d → ℂˣ`. On the actual intersection
`W = generalizedWeightBlock A c`, put `N_i = normalizedGeneratorDifference A c i`.
The conclusion asserts both

- `N_i ^ Module.finrank ℂ V = 0` for every coordinate;
- `Commute (N_i) (N_j)` for every pair of coordinates.

The imported block is the actual submodule

```lean
⨅ i : Fin d, (A.1 i : Module.End ℂ V).maxGenEigenspace (c i : ℂ)
```

If `G_i = generalizedWeightBlockGenerator A c i` is the restriction of the
actual tuple entry, its normalized difference is
`N_i = (c i : ℂ)⁻¹ • (G_i : Module.End ℂ W) - 1`.
Both conclusions are in `Module.End ℂ W`: multiplication is composition,
`1` is the identity map, and `0` is the zero map. The whole declaration has
type `Prop`, with only its carrier universe `u` external; all mathematical
inputs and instances are quantified inside the proposition.

The first equation gives actual nilpotence with an explicit common bound.
The bound uses the dimension of the ambient space, and need not be minimal.
There is no supplied nilpotence, commutation of normalized differences,
basis, decomposition, nonzero block or positive dimension hypothesis.
The commutation premise on the original invertible tuple remains part of
the published tuple type.

The source is Renard, *Représentations des groupes réductifs p-adiques*,
9 July 2026, Appendix C.III, printed p.280 / PDF286, in the proof of its
proposition. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
PDF285–286 were read directly for this draft. The source's strictly upper
triangular parts are pairwise commuting and nilpotent. This is their
basis-free form on the actual generalized-weight intersection. The explicit
ambient-dimension exponent is a derived strengthening, obtained from the
ambient-dimension description of each maximal generalized eigenspace and
scalar normalization, without needing a simultaneous basis first. Indeed, in finite dimension
`f.maxGenEigenspace μ = f.genEigenspace μ (Module.finrank ℂ V)`.
On `W`, the difference `G_i - (c i : ℂ) • 1` is therefore annihilated by
that exponent, and `N_i` is its scalar multiple by `(c i : ℂ)⁻¹`.
This explains the bound's provenance; the present module states the
conclusion and does not implement its proof. Quantifying over all unit label
tuples, including those with zero block, is part of this derived formulation.
The coordinates use zero-based `Fin d` in place of the source's `1, …, d`.

Rank zero gives an empty operator family. For zero `V`, the bound is zero;
the identity endomorphism of each zero block is zero, so the power equation
retains this case. Zero blocks at other labels are included.

The registered supplementary 2010 errata
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were read at PDF18–19. The C.III correction concerns parentheses in the
later product formula, already present in 2026 PDF286, and does not change
this assertion.
