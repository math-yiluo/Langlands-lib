# A geometrically semisimple faithful representation forces reductivity

`Langlands.GroupScheme.GeometricallySemisimpleRepresentationReductiveStatement.{u}`
is a Prop-valued definition. This module defines the proposition and proves
nothing.

## Statement

The proposition says: for every field `k : Type u` and every group scheme
`G : GroupScheme (Spec (CommRingCat.of k))` whose structure morphism is
affine (`[IsAffineHom G.X.hom]`), if `Smooth G.X.hom` and
`ConnectedSpace G.X.left`, then for every `n : ℕ` and every
`ρ : MatrixRepresentation G (Fin n)`,

```text
IsClosedSubgroup ρ →
  IsSemisimpleRep n ρ →
  IsSemisimpleRep n (ρ.baseChange (toAlgebraicClosure k)) →
  IsConnectedReductive G
```

Here `IsSemisimpleRep` is a local abbreviation inside the statement. It takes
an implicit field `F : Type u` and an implicit group scheme `H` over
`Spec (CommRingCat.of F)`, so that it applies both to `ρ` (over `k`) and to
its base change (over `AlgebraicClosure k`):

```text
IsSemisimpleRep n σ :=
  sSup {W : Submodule F (Fin n → F) | σ.IsStableSubspace W ∧ W ≠ ⊥ ∧
    ∀ U : Submodule F (Fin n → F), σ.IsStableSubspace U → U ≤ W →
      U = ⊥ ∨ U = W} = ⊤
```

In words: a connected group variety over `k` that has a faithful semisimple
finite-dimensional representation which remains semisimple over an algebraic
closure of `k` is reductive.

Every ingredient is an existing declaration, used without change:

- `MatrixRepresentation G (Fin n)` (from
  [`MatrixRepresentation`](../MatrixRepresentation.md)) is a homomorphism of
  group schemes `ρ : G ⟶ GL_n` over `k`, that is, a representation of `G` on
  `kⁿ` with its standard basis. Every finite-dimensional representation is
  isomorphic to one of these.
- `IsClosedSubgroup ρ` (from [`Reductive.Basic`](Basic.md)) says that the
  morphism of schemes underlying `ρ` is a closed immersion. This is how the
  Library's `AffineLinearEmbeddingStatement` expresses a faithful
  representation.
- `toAlgebraicClosure k` (from [`Reductive.Basic`](Basic.md)) is the morphism
  `Spec (AlgebraicClosure k) → Spec k` induced by `algebraMap`.
  `ρ.baseChange b` (from
  [`Rational.ValuedRepresentationBaseChange`](../Rational/ValuedRepresentationBaseChange.md))
  is the base change of `ρ` along `b`, followed by the canonical isomorphism
  `(GL_n)_{k^a} ≅ GL_n` over `k^a`. So
  `ρ.baseChange (toAlgebraicClosure k)` is a representation of the group
  scheme `(GroupScheme.baseChange (toAlgebraicClosure k)).obj G = G_{k^a}` on
  `(k^a)ⁿ`. By `pointMatrix_baseChange` (same module), its matrix at a point
  of `G_{k^a}` is the matrix of `ρ` at the corresponding point of `G`. This is
  Milne's `(V, r) ⊗ k^a` with `V = kⁿ`.
- `σ.IsStableSubspace W` (from
  [`MatrixRepresentation.StableSubrepresentation`](../MatrixRepresentation/StableSubrepresentation.md))
  says: for every commutative `F`-algebra `A`, every point `x` of the group
  with values in `A`, every `v ∈ W` and every `F`-linear map `ℓ : A → F`,
  applying `ℓ` to the coordinates of `σ(x)v` gives a vector of `W`. Since
  `W ⊗ A` is the set of vectors of `Aⁿ` all of whose images under such `ℓ`
  lie in `W`, this says that `σ(x)(W ⊗ A) ⊆ W ⊗ A` for all `A` and `x`.
  Applying it to `x⁻¹` gives equality. So the stable subspaces are the
  subrepresentations.
- The set inside `sSup` is the set of simple subrepresentations: nonzero
  stable subspaces `W` whose only stable subspaces contained in `W` are `0`
  and `W`. So `IsSemisimpleRep n σ` says that `Fⁿ` is the sum of the simple
  subrepresentations of `σ`. This is the same encoding as in the Library's
  `SemisimpleRepresentationUnipotentStatement` (Milne 19.16 and 19.17) and
  `CharZeroReductiveSemisimpleRepresentationStatement` (Milne 22.42). For
  `n = 0` the condition holds trivially.
- `IsConnectedReductive G` (from [`Reductive.Basic`](Basic.md)) is a structure
  with four fields: `Smooth G.X.hom`, `IsAffineHom G.X.hom`,
  `ConnectedSpace G.X.left`, and `HasTrivialUnipotentRadical` of the base
  change `G_{k^a}` along `toAlgebraicClosure k`. The last field says that
  every smooth connected unipotent closed subgroup of `G_{k^a}` with normal
  range is trivial, that is, the geometric unipotent radical `R_u(G_{k^a})`
  is trivial. `Reductive/Basic.md` relates this structure to Milne 6.46.

`G` is assumed affine and smooth; smoothness includes local finite
presentation, and an affine morphism is quasi-compact, so `G` is of finite
type over `k`. Together with `ConnectedSpace G.X.left` these hypotheses say
that `G` is a connected (affine) group variety in Milne's sense (see the
provenance). The first three fields of `IsConnectedReductive G` are therefore
hypotheses; the content of the statement is the fourth field.

## Provenance (derived)

Source: J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups` (SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`). Printed page
numbers are given; the PDF page is the printed page plus 16.

The statement is Corollary 19.18 on printed p. 401 (PDF p. 417): "A connected
group variety G is reductive if it admits a faithful semisimple representation
that remains semisimple over k^a." The 2022 corrected reprint (in the project
literature folder) has the same wording on its printed p. 401.

The surrounding conventions are:

- Algebraic groups and group varieties. "An algebraic group over k is a group
  object in the category of algebraic schemes over k", and "an algebraic
  k-scheme is a scheme of finite type over k" (printed p. 6). Printed p. 13:
  ""group variety" = "smooth algebraic group"". The notation section, printed
  p. 4, says "After p. 162, all algebraic groups are affine." Printed p. 162:
  "We now concentrate on affine algebraic groups. By "algebraic group" we shall
  mean "affine algebraic group" and by "group variety" we shall mean "affine
  group variety"." Chapter 19 lies after p. 162, so a connected group variety
  there is a smooth connected affine algebraic group, which the Lean
  hypotheses express.
- Reductive. 6.46 (printed p. 135): "A connected group variety G over an
  algebraically closed field is said to be reductive if R_u(G) = e. A
  connected group variety over a field k is said to be reductive if G_{k^a} is
  reductive, i.e., if its geometric unipotent radical R_u(G_{k^a}) is
  trivial." This is `IsConnectedReductive G`, with Mathlib's
  `AlgebraicClosure k` as `k^a`.
- Faithful. Chapter 4, printed p. 83: "A linear representation r is faithful
  if r(R): G(R) → Aut_{R-linear}(V_R) is injective for all k-algebras R. For
  finite-dimensional linear representations, this is equivalent to r being a
  closed immersion (3.35)." This is `IsClosedSubgroup ρ`. Faithfulness is
  required over `k` only, as in Milne.
- Semisimple. Definition 4.15, printed p. 90: "A representation of an
  algebraic group is simple if it is ≠ 0 and its only subrepresentations are
  0 and itself. It is semisimple if it is a sum of simple
  subrepresentations." `IsSemisimpleRep` is this definition for a
  representation on `Fⁿ`.
- Remaining semisimple over `k^a`. Proposition 4.19 (printed p. 90) writes
  "(V, r) ⊗ k′" for the representation of `G_{k′}` obtained by extending
  scalars to an extension `k′` of `k`. "Remains semisimple over k^a" means that
  `(V, r) ⊗ k^a` is a semisimple representation of `G_{k^a}`, which is the
  third hypothesis of the Lean statement.

The provenance is derived for these reasons:

- Milne's representations need not be finite-dimensional. The Lean statement
  covers finite-dimensional representations, given in coordinates as
  homomorphisms to `GL_n` on `kⁿ`. Nothing is lost (not formalized): if `V`
  is a faithful semisimple representation with `V ⊗ k^a` semisimple, write
  `V = Σ_{i ∈ I} S_i` with simple `S_i`. Since `O(G)` is noetherian, some
  finite subsum `S_J = Σ_{j ∈ J} S_j` is already faithful: the kernels of the
  actions of `G` on the `S_J` form a downward directed family of algebraic
  subgroups with trivial intersection (this is the argument recorded in the
  Markdown of `SemisimpleRepresentationUnipotentStatement` for 19.17). `S_J`
  is finite-dimensional (4.16) and semisimple, and `S_J ⊗ k^a` is a
  subrepresentation of the semisimple `V ⊗ k^a`, hence semisimple: by
  Proposition 4.17 (printed p. 90) a subrepresentation `W` of a semisimple
  representation `V′` is a direct summand, `V′ = W ⊕ W′`, so `W ≅ V′/W′` is a
  sum of images of simple subrepresentations, each simple or zero.
- Milne's hypothesis says that the representation is semisimple and stays
  semisimple over `k^a`. The Lean statement keeps both hypotheses, although
  the first follows from the second by Proposition 4.19(a) (printed p. 91: "If
  (V′, r′) is simple (resp. semisimple), then so also is (V, r)").
- Faithfulness of a finite-dimensional representation is expressed by the
  closed immersion condition, which Milne states is equivalent (3.35).
- `k`, `G` and the algebraic closure lie in an arbitrary universe `u`, and the
  test algebras in `IsStableSubspace` lie in the same universe. This is a
  formalization convention.

Errata. The official errata snapshot of 2026-11-02 for the 2017 book (source
ID `milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`) lists, for
Chapter 19, only Definition 19.7 (p. 399); for Chapter 1, a note that
Notation 3.2 should be placed earlier and corrections on pp. 18, 20, 21 and
26; under the heading Chapter 3, corrections on p. 80 (3.52) and p. 85
("G_W is the stabilizer of W in G (not V)"); for Chapter 4, only a correction
on p. 95 (proof of 4.29); for Chapter 6, only p. 136 (Example 6.48) (an entry
on 6.19, p. 129, sits inside an HTML comment and is not displayed). None
changes Corollary 19.18, Proposition 19.17, Summary 1.36, 6.46, Definition
4.15, Propositions 4.16, 4.17 and 4.19 or the conventions of pp. 4, 6, 13, 83
and 162.

## For the later proof (not part of this unit)

Milne's proof, printed p. 401: "The hypothesis implies that the unipotent
radical of G_{k^a} is trivial." In detail:

- `G_{k^a}` is a connected group variety: smoothness and affineness are stable
  under base change, and Summary 1.36 (printed p. 17) says that an algebraic
  group is connected if and only if it is geometrically connected.
- `ρ_{k^a} := ρ.baseChange (toAlgebraicClosure k)` is faithful: a closed
  immersion stays a closed immersion after base change, and `ρ.baseChange` is
  that base change followed by an isomorphism.
- `ρ_{k^a}` is semisimple by hypothesis. Proposition 19.17 over `k^a`
  ("If a connected group variety G admits a faithful semisimple
  representation, then its unipotent radical is trivial", printed p. 401)
  gives `R_u(G_{k^a}) = e`, the fourth field of `IsConnectedReductive G`.

The Library states 19.17 as the second conjunct of
`SemisimpleRepresentationUnipotentStatement` (module
`Langlands.GroupScheme.Reductive.SemisimpleRepresentationUnipotentStatement`);
applied to `k^a`, `G_{k^a}` and `ρ_{k^a}` it gives
`HasTrivialUnipotentRadical G_{k^a}` directly. The hypothesis
`IsSemisimpleRep n ρ` over `k` is not needed in this argument.
