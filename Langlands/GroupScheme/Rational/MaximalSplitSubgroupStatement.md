# Borel–Tits 7.2: a split reductive subgroup through a maximal split torus

`Langlands.GroupScheme.MaximalSplitSubgroupStatement.{u}` is a statement-only, `Prop`-valued
definition. This module proves nothing and adds no other declarations.

## Statement

For every field `k : Type u`, every group scheme `G` over `Spec k` with
`hG : IsConnectedReductive G`, every commutative group scheme `S` and every
`i : S.toGrp ⟶ G` with `IsMaximalSplitTorus i`, there exist

- a group scheme `F` over `Spec k` with `hF : IsConnectedReductive F`;
- a homomorphism `j : F ⟶ G` with `IsClosedSubgroup j` (a closed immersion);
- a homomorphism `f : S.toGrp ⟶ F` with `f ≫ j = i` and `IsMaximalTorus f`;

such that `roots f = {a | a ∈ roots i ∧ (2 : ℤ) • a ∉ roots i}`.

Here `roots` (module `Torus.Weights`) is the set of nonzero characters of `S` with a nonzero
weight space in the actual Lie algebra, for the `IsAffineHom` instances supplied by `hG` and
`hF`. For the maximal split torus `i`, `roots i` is the set of relative roots `Φ(S, G)` (see
the family-5 ledger, row I1). The right-hand side is the set `Φ'` of nonmultipliable relative
roots. Since `S` is a split torus (part of `IsMaximalSplitTorus i`) and `f` is a maximal torus
of `F`, the group `F` is split, with split maximal torus `S` and root system `Φ(S, F) = Φ'`.

No hypothesis on the field is made: any characteristic, perfect or not, finite or infinite.
Split rank zero is included; then `roots i` is empty and `F` can be the torus `S` itself.

## Source correspondence

Armand Borel and Jacques Tits, *Groupes réductifs*, Publications Mathématiques de l'IHÉS 27
(1965), registered as `borel-tits-1965-groupes-reductifs` (SHA-256
`ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`), Théorème 7.2, printed
p.117 (one-based PDF p.64), proof pp.117–121 (PDF pp.64–68):

> Supposons G réductif connexe. Soient S un tore déployé sur k maximal de G, Φ = Φ(S, G) le
> système des k-racines de G, Φ′ celui des racines non multipliables de Φ, et Δ l'ensemble des
> racines simples de Φ′ pour un ordre donné sur X*(S). Pour tout a ∈ Δ, soit E_a un k-sous-groupe
> de dimension un de U_(a) normalisé par S et soit V le groupe engendré par les E_a. Alors G
> possède un unique sous-groupe réductif F connexe déployé sur k contenant S·V. Le tore S est un
> tore maximal de F et Φ′ = Φ(S, F). […]

The Lean statement keeps the existence of `F` with `S` as a maximal torus and `Φ(S, F) = Φ′`.
It omits the choice of the groups `E_a`, the containment of `V`, the uniqueness of `F`, the
equality `W(F) = W(G)` of Weyl groups and the description `U_(d) ∩ F` of root groups. A
nonmultipliable root is defined just before the theorem (p.117): `d` is nonmultipliable when
the positive integral multiples of `d` in `Φ` are `{d}`; for a root system this is
`2d ∉ Φ`. The source works with varieties over an algebraically closed field with a
`k`-structure; here `F`, `j` and `f` are actual group schemes and homomorphisms over `k`.

The proof on p.121 cites 1965 3.22 for the triviality of `R_u(F)` through `V ∩ V⁻ = {e}`, the
intersection of subgroups of opposite ambient unipotent radicals. The project erratum
[borel-tits-1965-closed-root-intersection](../../../notes/errata/borel-tits-1965-closed-root-intersection.md)
gives a counterexample to the general closed-root assertion 3.22(b). A proof of this statement
must not use 3.22(b); the opposite-cell factorization covers the special case needed here.

## Use

`Langlands.GroupScheme.simplyConnectedQuasiSplitEnvelope_of_maximalSplitSubgroup`
(module `SimplyConnected.QuasiSplitEnvelopeReduction`) derives
`SimplyConnectedQuasiSplitEnvelopeStatement` from this statement and
`NonmultipliableCorootSpanStatement`.
