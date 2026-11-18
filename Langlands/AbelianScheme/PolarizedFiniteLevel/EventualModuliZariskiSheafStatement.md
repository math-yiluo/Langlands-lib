# The ordinary polarized full-level moduli functor is a Zariski sheaf for large levels

`Langlands.AbelianScheme.PolarizedFiniteLevel.EventualModuliZariskiSheafStatement`
is a proposition definition. It is a statement target only; this module proves
nothing.

## The statement

For every `P : Prerequisites.{0}` and all natural numbers `g d` with `0 < g` and
`hd : 0 < d`, there is a natural number `N` with the following property. For every
level `n` with `N ≤ n` and every proof `hn : 3 ≤ n`, the published functor
`moduliFunctor P g d n hd hn : (LevelBase n)ᵒᵖ ⥤ Type 1` satisfies
`LevelBase.IsZariskiSheaf`. This is the sheaf condition for open covers, defined in the
module `LevelBaseZariski`.

Concretely, let `S` be a locally noetherian universe-zero scheme on which `n` is a unit,
and let `(U_i)` be an open cover of `S`. Let `ξ_i` be isomorphism classes of ordinary
polarized data with full level `n` structure over the `U_i` whose restrictions to the
overlaps `U_i ∩ U_j` agree. Then exactly one class over `S` restricts to every `ξ_i`. The
classes are those of the published `Moduli P S g d n`: data of dimension `g`, polarization
of degree `d²` and ordered full level `n`, up to polarized isomorphisms preserving the
level sections. Restriction is the published `Moduli.pullback`.

## Relation to `ModuliZariskiSheafStatement`

The published `ModuliZariskiSheafStatement` asserts the same sheaf property for every
`n ≥ 3`. It implies this statement with `N = 0`; the module
`LargeLevelRepresentabilityEventualReduction` records this as
`eventualModuliZariskiSheaf_of_moduliZariskiSheaf`. The eventual form is weaker, and it is
all that the published target `LargeLevelRepresentabilityStatement` needs, because that
target only asserts an eventual bound. The statement for every `n ≥ 3` needs Serre's
theorem on automorphisms fixing `n`-torsion (Mumford, *Abelian Varieties*, §21, Theorem 5),
which the Library does not have. The eventual form can use the rigidity for large levels
that the Library already has: `PolarizedIso.eq_refl_of_canonicalCubicSectionBasis_count` and
`Datum.polarizedIsoSubsingleton_of_cubicSectionBasis_count` in `CanonicalCubicRigidity`. Over
an algebraically closed field, these make a polarized isomorphism preserving the level
sections unique once `(m+1)·6^g·d·g!·n^{2g-2} < n^{2g}`, given the cubic Lefschetz embedding
(`CubicFieldEmbeddingStatement`). The hypothesis `0 < g` is the target's, and the numerical
condition needs it.

## Mathematical content and provenance

This statement is derived; no single source states it in this form. Like
`ModuliZariskiSheafStatement`, it combines two classical facts.

**Uniqueness of isomorphisms.** For large `n`, a polarized isomorphism between two data
that preserves the level sections is unique. The quotient `α` of two such isomorphisms is
an automorphism that preserves the polarization and fixes the `n`-torsion sections. At every
geometric point, `α` acts on the cubic Lefschetz embedding `A ⊂ ℙ^m` through a linear
automorphism `e` of projective space, and `e` fixes all `n^{2g}` torsion points. If `e` is
not a scalar, every fixed point lies in one of at most `m+1` proper eigenspaces, each
contained in a hyperplane. The hyperplane bound for torsion points (published
`CubicTorsionHyperplaneBoundStatement`) makes the torsion points too many for that once
`n` is large. So `e` is a scalar, and `α`, which the embedding determines, is the
identity there. The hyperplane count is Mumford–Fogarty–Kirwan, *Geometric Invariant
Theory*, Proposition 7.7 (printed p.138, PDF p.151 of the registered source
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`): fewer than
`n^{2g}/(m+1)` points of order `n` lie on any hyperplane. Corollary 7.8 (printed p.139,
PDF p.152) uses it for `n > 6^g·d·√(g!)`. The deduction of `e = scalar` is the Library's
`TorsionConfigurationRigidity`. The rigidity statement GIT Corollary 6.2 (printed p.116,
PDF p.129) then gives `α = 1` on every connected component of the base.

**Gluing.** Because isomorphisms are unique, the local isomorphisms between representatives
on overlaps satisfy the cocycle condition. So the abelian schemes, their polarizations and
their level sections glue along the cover. The same uniqueness glues isomorphisms, which
gives uniqueness of the glued class. The dual witness of the glued abelian scheme is
obtained as described in the Markdown of `ModuliZariskiSheafStatement`.

This statement is the sheaf input of the reduction
`largeLevelRepresentability_of_eventualSheaf` in the module
`LargeLevelRepresentabilityEventualReduction`.
