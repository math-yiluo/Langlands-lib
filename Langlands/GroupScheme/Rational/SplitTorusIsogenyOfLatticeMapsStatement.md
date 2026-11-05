# Statement: injective character and cocharacter maps give an isogeny of split tori

Authors: Worker 1428, Worker 1520.

This module states one unproved proposition, the `Prop`-valued `def`
`Langlands.GroupScheme.SplitTorusIsogenyOfLatticeMapsStatement` with one
universe parameter `u`. Nothing is proved here, and no other declaration is
introduced.

The module imports `Langlands.GroupScheme.CentralIsogeny.Basic`,
`Langlands.GroupScheme.Torus.Lattice` and `Langlands.GroupScheme.Torus.Split`.
It reuses by name the Library declarations `CommGroupScheme`,
`CommGroupScheme.groupHom`, `IsSplitTorus`, `characterLattice`,
`cocharacterLattice` and `IsIsogeny`.

## The statement

```lean
def SplitTorusIsogenyOfLatticeMapsStatement : Prop :=
  ∀ (k : Type u) [Field k] (T T' : CommGroupScheme (Spec (CommRingCat.of k))) (t : T ⟶ T'),
    IsSplitTorus T.toGrp → IsSplitTorus T'.toGrp →
    Function.Injective (fun χ : characterLattice T' => t ≫ χ) →
    Function.Injective (fun ν : cocharacterLattice T => ν ≫ t) →
      IsIsogeny (CommGroupScheme.groupHom t)
```

In words: let `k : Type u` be an arbitrary field (no perfectness,
separable-closedness or characteristic hypothesis), let `T` and `T'` be split
tori over `k`, and let `t : T ⟶ T'` be a homomorphism of commutative group
schemes. Suppose that

- the character map `X(t) : X(T') → X(T)`, `χ ↦ t ≫ χ`, is injective, where
  `characterLattice T'` is the group of homomorphisms `T' ⟶ 𝔾_m`; and
- the cocharacter map `Y(t) : Y(T) → Y(T')`, `ν ↦ ν ≫ t`, is injective, where
  `cocharacterLattice T` is the group of homomorphisms `𝔾_m ⟶ T`.

Then `t` is an isogeny: `IsIsogeny (CommGroupScheme.groupHom t)`
(`AbelianScheme/Isogeny.lean`) says that the underlying morphism of schemes
of `t` is finite, flat and surjective.

## Relation to the published converse

The published `SplitTorusIsogenyCocharacterStatement`
(`Rational/SplitTorusIsogenyCocharacter.lean`, proved as
`splitTorusIsogenyCocharacter` in `Rational/SplitTorusIsogenyCocharacterProof.lean`)
is a converse. For split tori `A`, `T` over a field and `f : A ⟶ T` with
`IsIsogeny (CommGroupScheme.groupHom f)`, it concludes that
`RealTorusSpace.cocharacterMapInt f`, the ℤ-linear map `ν ↦ ν ≫ f` on
cocharacters, is injective with finite cokernel (and that its rational and
real scalar extensions are bijective). The present statement goes the other
way: it assumes injectivity of the character and cocharacter maps and
concludes `IsIsogeny`. Its cocharacter hypothesis is the injectivity part of
that conclusion, written directly as `fun ν => ν ≫ t` rather than through
`cocharacterMapInt`. It does not assume finiteness of a cokernel; that
finiteness is part of the argument below, not of the statement.

## Why it is true (derived statement)

The statement is derived, not quoted: Milne does not state it as one result.
It combines three passages of J. S. Milne, *Algebraic Groups* (Cambridge
University Press, 2017), source ID `milne-2017-algebraic-groups`, where the
printed page is the PDF page − 16.

- The remark after Definition 23.1 (printed p.484, PDF p.500) says that for a
  homomorphism `f : X' → X` of free ℤ-modules of finite rank, the conditions
  "(a) `f` is injective with finite cokernel" and "(b) both `f` and `f^∨` are
  injective" are equivalent. Here `f = X(t)`, and under the perfect pairing
  between characters and cocharacters of split tori, `f^∨ = Y(t)`. So `X(t)`
  is injective with finite cokernel `C`.
- Theorem 12.9 (printed p.233, PDF p.249): `M ↦ D(M)` is an exact contravariant
  equivalence between finitely generated commutative groups and diagonalizable
  groups. Applied to `0 → X(T') → X(T) → C → 0`, it gives an exact sequence
  `e → D(C) → T → T' → e`. So `t` is a quotient map, which is faithfully flat
  (Milne Definition 5.5, printed p.99, PDF p.115), with finite kernel `D(C)`.
- Finiteness of `t`: in coordinates, `t` is `Spec` of the group-algebra map
  `k[X(T')] → k[X(T)]`. Since `X(T')` has finite index in `X(T)`, `k[X(T)]` is
  a free `k[X(T')]`-module with basis indexed by a set of coset
  representatives of `X(T)/X(T')`, which is finite.

The Library has tools for this route: the group-algebra description of maps
of split tori (`diagonalizableMap_hom_left`,
`Rational/SplitTorusIsogenyCharacters.lean`) and flatness, surjectivity and
the coset basis for an injective lattice map
(`flat_and_surjective_restrictMap` and `cosetLinearMap_bijective`,
`Torus/DiagonalizableFaithfullyFlat.lean`). These are suggestions for a
proof, not part of the statement.

The official Milne errata snapshot of 2026-11-02
(`milne-2017-algebraic-groups-errata-2026-11-02`) has no entry for 5.5, 12.9
or printed p.484.

## Use

This statement is meant to supply the isogeny property of `t` in a later
proof of `SplitCentralTorusQuotientStatement` (statement task
`2ea05a8b-453e-49c8-8d20-9b2ad61ac047`; not yet in the Library), whose
hypotheses on `t` are exactly the two injectivity conditions. There the
isogeny property is to be used for finiteness of the kernel of `t` and for
descending homomorphisms along `t`. This module itself proves none of this.
