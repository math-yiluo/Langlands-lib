# Monomorphisms of finite-type group schemes

`Langlands.GroupScheme.FiniteTypeMonomorphismStatement.{u}` states that a
homomorphism of separated finite-type group schemes over any field is a
closed immersion if its underlying scheme map is a categorical monomorphism.
This file defines a proposition; it does not prove it.

Both `G` and `H` are actual group schemes over `Spec k`. Their structure maps
are locally of finite type, quasi-compact and separated. The first two
conditions express finite type. The homomorphism `f : G ⟶ H` is an actual
group-scheme homomorphism, and `Mono f.hom.hom.left` is monicity in the
category of schemes. This tests arbitrary scheme points, including
infinitesimal ones. The conclusion is closed immersion of that same map.
Neither group is assumed affine, smooth, reduced or connected; the field
has no perfectness or characteristic restriction.

The source is J. S. Milne, *Algebraic Groups* (2017), Theorem 5.34,
printed p.107 (PDF p.123). That theorem identifies monomorphisms of
algebraic groups with closed immersions. The Lean statement records its
forward implication using explicit separated finite-type scheme hypotheses.
The official author errata snapshot registered as
`milne-2017-algebraic-groups-errata-2026-11-02` has no correction to
Theorem 5.34. No use of the adjacent Theorem 5.36 is made here.
