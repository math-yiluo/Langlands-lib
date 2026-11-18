# The ordinary polarized full-level moduli functor is a Zariski sheaf

`Langlands.AbelianScheme.PolarizedFiniteLevel.ModuliZariskiSheafStatement` is a
proposition definition. It is a statement target only; this module proves
nothing.

## The statement

For every `P : Prerequisites.{0}`, all natural numbers `g d n`, every proof
`hd : 0 < d` and every proof `hn : 3 ≤ n`, the published functor
`moduliFunctor P g d n hd hn : (LevelBase n)ᵒᵖ ⥤ Type 1` satisfies
`LevelBase.IsZariskiSheaf`, the sheaf condition for open covers defined in the
internal module `LevelBaseZariski`.

Concretely, let `S` be a locally noetherian universe-zero scheme on which `n`
is a unit, and let `(U_i)` be an open cover of `S`. Let `ξ_i` be isomorphism
classes of ordinary polarized data with full level `n` structure over the
`U_i`, whose restrictions to the overlaps `U_i ∩ U_j` agree. Then there is a
unique class over `S` restricting to every `ξ_i`. The classes are those of the
published `Moduli P S g d n`: data of dimension `g`, polarization of degree `d²`
and ordered full level `n`, up to polarized isomorphisms preserving the level
sections. Restriction is the published `Moduli.pullback`.

## Mathematical content and provenance

This statement is derived; no single source states it in this form. It
combines two classical facts.

**Uniqueness of isomorphisms.** For `n ≥ 3`, a polarized isomorphism between
two data that preserves the level sections is unique. Let `α` be the quotient
of two such isomorphisms, an automorphism of the abelian scheme that preserves
the polarization and fixes the `n`-torsion sections. At every geometric point,
`α` is the identity by Serre's theorem: Mumford, *Abelian Varieties* (1970),
§21, Theorem 5, printed p.207 (PDF p.108 of the registered scan
`mumford-abelian-varieties-full-scan`). That theorem says the restriction map
from automorphisms preserving an ample class up to `Pic⁰` to the automorphisms
of the `n`-torsion is injective for `n ≥ 3`. The rigidity statement
Mumford–Fogarty–Kirwan, *Geometric Invariant Theory*, Corollary 6.2 (printed
p.116, PDF p.129 of the registered source
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`)
then gives `α = 1` on every connected component of the base, because `α` and
the identity preserve the identity section.

**Gluing.** Because isomorphisms are unique, the local isomorphisms between
representatives on overlaps satisfy the cocycle condition. So the abelian
schemes, their polarizations and their level sections glue along the cover;
schemes and morphisms glue along open covers. The same uniqueness glues
isomorphisms, which gives uniqueness of the glued class. The resulting datum
also needs a dual witness for the glued abelian scheme. Relative duals of
abelian schemes exist Zariski locally, and the dual is determined by its
functor of points, so the local duals glue as well. By the published
`Datum.withDualWitness` and `withDualWitnessIso`, the class of a datum does not
depend on the choice of its dual witness.

The level hypothesis `3 ≤ n` is used for the uniqueness of isomorphisms: for
`n ≤ 2` the automorphism `-1` fixes all `n`-torsion sections. The hypothesis
`0 < d` is the published functor's hypothesis.

This statement is a prerequisite of the gluing step for the published target
`LargeLevelRepresentabilityStatement`, with
`LevelBaseOpenChartGluingStatement`.
