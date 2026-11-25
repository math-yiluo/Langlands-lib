# Constant actual characters detect diagonalizability

`Langlands.GroupScheme.RelativeCharacterConstancyStatement.{u}` is a
Prop-valued statement in every universe. For every scheme `S`, every group
scheme `H` over `S`, and every proof
`hH : RelativeMultiplicativeType.IsMultiplicativeType H`, it states

```text
RelativeMultiplicativeType.IsDiagonalizable H ↔
  ∃ M : AddCommGrpCat.{u}, AddGroup.FG M ∧
    Nonempty (hH.characters ≅ EtaleLocalSystem.constant S M).
```

Here `EtaleLocalSystem` denotes the namespace
`Langlands.AlgebraicGeometry.EtaleLocalSystem`.

## Meaning

The left side is the published definition of diagonalizability: `H` is
isomorphic over `S` to `D_S(Λ)` for some finitely generated abelian group
`Λ : Type u`. It permits torsion.

On the right side, `hH.characters` is the published actual relative Cartier
character functor, with values at `T ⟶ S` canonically identified with
`Hom_T(H_T,Gm_T)`. Its restriction maps pull back those homomorphisms.
The target of the natural isomorphism is the published constant model:
locally constant functions from each test scheme to the discrete group
`M`, with pointwise addition and pullback of functions.

The natural isomorphism is on the whole category `(Over S)ᵒᵖ`.
The right side asserts a single global coefficient group and a global
natural isomorphism; it is stronger than the existence of separate local
models on an étale cover. `Nonempty` records the isomorphism existentially,
so the entire statement is Prop-valued.

There is no hypothesis that `S` is connected, normal, nonempty, affine or
noetherian. There is no restriction on the characteristic or on torsion
in the finitely generated groups.

## Source and derived provenance

Brian Conrad, *Reductive group schemes* (2014), Proposition B.3.4,
printed pp.290–292, especially the character anti-equivalence on p.291,
identifies groups of multiplicative type with locally constant abelian
étale sheaves having finitely generated geometric fibres. Under this
anti-equivalence `D_S(M)` corresponds to the constant sheaf `M`.
Consequently a group of multiplicative type is diagonalizable exactly
when its character sheaf is constant with finitely generated coefficients.
The proof of Corollary B.3.6 on p.293 uses this consequence to translate
splitting into constancy of the character sheaf.

The registered source is `conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`,
at
`/home/taskhub/central-library/Conrad--Reductive group schemes (SGA3 notes)--2014.pdf`.

The Lean proposition records only this constant-object consequence,
using the published big relative character functor. The big-site
comparison includes arbitrary test schemes: the characters of `D_S(M)`
are the locally constant `M`-valued functions, naturally under pullback.
Conversely the global character identification reconstructs a
diagonalizable model by the character anti-equivalence. This is the
provenance of the reformulation, not a claimed Lean proof.

## Scope

This module supplies the exact statement; it is proved as
`relativeCharacterConstancy` in
[`RelativeCharacterConstancyProof`](RelativeCharacterConstancyProof.md). It asserts no
construction of the full anti-equivalence and supplies no finite étale
cover. The normal-base isotriviality assembly
([`MultiplicativeTypeNormalIsotrivialAssembly`](MultiplicativeTypeNormalIsotrivialAssembly.md))
uses the implication from constant actual characters to diagonalizability after
base change.
