# Closed linear embeddings of flat affine groups over Dedekind domains

`Langlands.GroupScheme.DedekindLinearEmbeddingStatement.{u}` asserts that,
for every commutative ring `R : Type u` with `[IsDedekindDomain R]` and every
actual group scheme `G : GroupScheme (Spec (CommRingCat.of R))` whose
structure morphism `G.X.hom` is flat, affine and locally of finite type,
there exist `N : ℕ` and an actual representation

```text
ρ : MatrixRepresentation G (Fin N)
```

such that `IsClosedSubgroup ρ` holds.

## Exact meaning and hypotheses

The group scheme uses the existing `Grp (Over S)` architecture, with
`S = Spec R`. `MatrixRepresentation G (Fin N)`, from
[`MatrixRepresentation`](MatrixRepresentation.md), is an actual morphism of
group objects from `G` into the matrix-coordinate group scheme
`GeneralLinear.groupScheme (Fin N) (CommRingCat.of R)`, which is `GL_N` over
`R`. `IsClosedSubgroup ρ`, as defined in
[`Reductive.Basic`](Reductive/Basic.md), means
`IsClosedImmersion ρ.hom.hom.left` for the underlying morphism of schemes.
The conclusion therefore says that `G` is isomorphic, as a group scheme, to
a closed subgroup scheme of `GL_N` over `R`, with the scheme structure of
the image included.

The hypotheses on `G` are:

- `Flat G.X.hom`: `G` is flat over `R`;
- `IsAffineHom G.X.hom`: `G` is affine over `R`, so `G` is an affine scheme
  because the base is affine, and the structure morphism is quasi-compact;
- `LocallyOfFiniteType G.X.hom`: together with quasi-compactness, the
  structure morphism is of finite type.

These are exactly "flat affine group scheme of finite type over `R`" in the
source. There is no smoothness, connectedness, reductivity or fibre
condition. The rank `N` is an existential natural number.

Mathlib's `IsDedekindDomain R` means a Noetherian integrally closed domain
of Krull dimension at most one. It includes fields. For a field `R` the
statement is the field case, Conrad's Exercise 5.5.7(i), which is also the
Library statement
[`AffineLinearEmbeddingStatement`](AffineLinearEmbeddingStatement.md)
(Milne 4.9 and 4.10). Allowing fields therefore adds no content beyond the
source.

## Source correspondence

Source: Brian Conrad, *Reductive group schemes* (SGA3 summer school notes,
2014), Exercise 5.5.7, printed p. 184. The exercise reads: "In the proof of
Theorem 5.3.5, we used that any flat affine group scheme G of finite type
over a Dedekind domain R occurs as a closed subgroup of some GL_n over R.
(i) Prove the analogous result over fields ... (ii) Make your argument in
(i) work over R (for flat affine groups of finite type) by using that any
finitely generated torsion-free R-module is projective (and hence a direct
summand of a finite free R-module)."

The Lean proposition is the claim in the first sentence of the exercise,
whose proof is part (ii). "Occurs as a closed subgroup of some `GL_n`" is
encoded as a group homomorphism `G → GL_N` over `R` that is a closed
immersion. The source's `n` is the Lean `N`.

Source ID: `conrad-2014-reductive-group-schemes`. Retained PDF:
`/home/taskhub/central-library/Conrad--Reductive group schemes (SGA3 notes)--2014.pdf`
(SHA256 `1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`).
The cited page was read (PDF page index 183, zero-based).

## Provenance

The statement is derived from the source exercise; Conrad gives no proof.
The encoding copies the published field statement
`AffineLinearEmbeddingStatement`, replacing the field by a Dedekind domain
and adding the flatness hypothesis that the source requires.

## Proof boundary

This module defines a proposition; it proves no existence result and adds
no axiom. A separate exact-target proof must produce the representation and
its closed immersion for every stated Dedekind domain and group scheme. The
source only gives a hint: adapt a field proof, such as one that takes a
finitely generated subcomodule of the coordinate ring `R[G]` containing
algebra generators. Over a Dedekind domain such a subcomodule is
torsion-free because `R[G]` is flat, hence projective and a direct summand
of a finite free module. These comodule and module
comparisons are proof obligations, not hypotheses of this statement.
