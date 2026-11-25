# Cuspidal complex representations of `GL_n(k)` and their isomorphism classes

This module defines Harish-Chandra cuspidality for complex representations of
`Langlands.GeneralLinear n k`, and the set of isomorphism classes of irreducible
cuspidal complex representations. The count statement in
`CuspidalClassCountBoundStatement` is stated with these definitions. Its
conventions follow the p-adic analogue `GeneralLinear.SupercuspidalClass` in
`Langlands/Representation/Classification/Supercuspidal.lean`.

## Cuspidality: `IsCuspidal`

Let `k` be a field, `n : ℕ`, and let `ρ : Representation ℂ (GeneralLinear n k) V` be a
complex representation on any complex vector space `V`. Then `IsCuspidal ρ` says:

> for every block shape `B : GeneralLinear.BlockShape n` with `B.parabolic k ≠ ⊤`,
> every vector `v : V` with `ρ u v = v` for all `u ∈ B.unipotentSubgroup k` is `0`.

`BlockShape`, `BlockShape.parabolic` and `BlockShape.unipotentSubgroup` are the
Library's standard ordered block shapes. They give the upper block parabolic and its
block unipotent radical as subgroups of `GL_n(k)` (`Langlands/Group/GL/Blocks.lean`).
Properness is the literal condition `B.parabolic k ≠ ⊤`. So the definition says that no
proper standard parabolic subgroup has a nonzero vector fixed by its unipotent radical.

Relation to the usual formulations, none of which is proved here:

- **Standard parabolics suffice.** The source condition quantifies over all proper
  parabolic subgroups. Every parabolic subgroup of `GL_n(k)` is conjugate to a standard
  block parabolic, and `ρ(g)` maps the `U`-fixed vectors bijectively onto the
  `gUg⁻¹`-fixed vectors. So for a representation of the whole group, the two conditions
  are equivalent. The Lean predicate uses only the standard ones.
- **Invariants versus components.** The source says that no proper parabolic `P` with
  unipotent radical `U` has an irreducible component of `ρ|_P` that is trivial on `U`.
  The `U`-fixed vectors form a `P`-stable subspace because `U` is normal in `P`. So for
  a finite group (where restrictions are completely reducible), a nonzero `U`-fixed
  vector exists exactly when such a component exists.
- **Invariants versus coinvariants.** For a finite group over `ℂ`, averaging over `U`
  identifies the `U`-invariants with the `U`-coinvariants. So the definition agrees
  with the coinvariant (Jacquet module) formulation used in the p-adic `IsSupercuspidal`.

`IsCuspidal` alone does not require irreducibility, finite dimensionality or finiteness
of `k`. It is stated for any field `k` and any `n`, a larger domain than the source's
finite fields and `n ≥ 1`. Mathematically, for `n = 0` or `n = 1` the only block
shape gives the whole group as its parabolic, so every representation satisfies
`IsCuspidal`. For `n = 1` this matches the source, where every irreducible
representation of `GL_1(k)` is cuspidal. For `n = 0` this is a convention only, and
the count statement in `CuspidalClassCountBoundStatement` excludes `n = 0`.

`IsCuspidal.of_equiv` and `isCuspidal_iff_of_equiv` prove that cuspidality is
invariant under equivalence of representations (`Representation.Equiv`), including
between carriers in different universes.

## Irreducible cuspidal objects and their isomorphism classes

All three definitions take a universe parameter `w` for the representation carriers,
explicit in the order `.{u, w}`, where `k : Type u`.

- `cuspidalProperty.{u, w} n k` is the object property of Mathlib's category
  `Rep.{w} ℂ (GeneralLinear n k)` (complex representations on carriers in `Type w`)
  given by `A.ρ.IsIrreducible ∧ IsCuspidal A.ρ`. Irreducibility is Mathlib's
  `Representation.IsIrreducible`: the subrepresentation lattice is a simple order, so
  the representation is nonzero and has no subrepresentations other than `⊥` and `⊤`.
- `CuspidalRep.{u, w} n k` is the full subcategory of these objects.
- `CuspidalClass.{u, w} n k` is the quotient of `CuspidalRep.{u, w} n k` by
  Mathlib's `isIsomorphicSetoid`, which relates two objects when an isomorphism exists
  between them. It is the set of isomorphism classes of irreducible cuspidal complex
  representations of `GL_n(k)` on carriers in `Type w`. It is not resized, and lives in
  `Type (max u (w + 1))`.

Supporting API: `CuspidalRep.of` bundles an irreducible cuspidal representation;
`CuspidalRep.isIrreducible` and `CuspidalRep.isCuspidal` project the two properties;
`CuspidalRep.isoClass` is the quotient map; `CuspidalRep.isoClass_surjective` says
every class has a representative; `CuspidalRep.isoClass_eq_iff` proves that two
objects have the same class exactly when their underlying representations are
equivalent (`Nonempty (A.obj.ρ.Equiv B.obj.ρ)`). The proof uses `Rep.mkIso` and
`Representation.equivOfIso`.

Over a finite field every irreducible complex representation of the finite group
`GL_n(k)` is finite dimensional, and every isomorphism class has a representative on
a carrier in `Type 0`. So for `k` finite and any `w`, `CuspidalClass.{u, w} n k`
represents the usual set of equivalence classes of irreducible cuspidal
representations. That comparison between universes is not proved in this module.

## Sources

- Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups*, Annals of
  Math. Studies 129 (1993), printed p. 268 (PDF p. 280), proof of the exhaustion
  theorem in §8. For a reductive `k_F`-group `𝒢`, a representation `ϑ` that is not
  cuspidal is described there as having "a proper parabolic subgroup `𝒱` of `𝒢` such
  that `ϑ | 𝒱` has an irreducible component `ϑ*` which is trivial on the unipotent
  radical `𝒰` of `𝒱`". Source ID `bushnell-kutzko-1993-admissible-dual-gln`, SHA256
  `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
- Bushnell–Kutzko, *Simple types in GL(N): computing conjugacy classes*, Contemp.
  Math. 177 (1994), printed p. 125 (PDF p. 138): (3.5)(ii) is called "the cuspidality
  condition", and (3.6) and the following paragraph speak of "equivalence classes of
  irreducible cuspidal representations of `GL(f, k_E)`". This is the set that
  `CuspidalClass` formalises. Source ID
  `bushnell-kutzko-1994-simple-types-conjugacy-classes`, SHA256
  `fd2077476192d9db15188feea9ff73774fe96296a2a31412d612f2081581efaa`.
- The condition is Harish-Chandra's standard definition of cuspidal representations of
  finite groups with a split `BN`-pair (see also Springer, *Cusp forms for finite
  groups*, LNM 131, 1970). Springer was not consulted for this record.

## Not claimed

No existence of cuspidal representations, no count of the classes, and no
characterisation by matrix coefficients, characters or Deligne–Lusztig theory is
stated or proved here. The equivalences listed under "Relation to the usual
formulations" are explanations, not Lean theorems.
