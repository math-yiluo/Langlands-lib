# Statement: groups of multiplicative type over normal bases are locally isotrivial

Worker 75.

`Langlands.GroupScheme.MultiplicativeTypeNormalIsotrivialStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- [`Torus.RelativeMultiplicativeType`](RelativeMultiplicativeType.md), for the relative
  predicates `RelativeMultiplicativeType.IsDiagonalizable` and
  `RelativeMultiplicativeType.IsMultiplicativeType` (Conrad, Definition B.1.1); the
  base-change functor `GroupScheme.baseChange` comes transitively;
- Mathlib's `Mathlib.AlgebraicGeometry.Morphisms.Etale` and
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`, for `Etale` and `IsFinite`.

`GroupScheme S` is `Grp (Over S)`. Inside the definition the namespace
`RelativeMultiplicativeType` is open, so `IsDiagonalizable` and `IsMultiplicativeType` refer
to the relative predicates, not to the field-level `IsMultiplicativeType` of
[`Torus.MultiplicativeType`](MultiplicativeType.md).

## Predicates and constructions used

- `IsDiagonalizable H`, for `H : GroupScheme S`: `H` is isomorphic, as a group scheme over
  `S`, to the diagonalizable group `D_S(Λ)` of some finitely generated abelian group `Λ`.
- `IsMultiplicativeType H`: `H` becomes diagonalizable on the members of some fppf cover
  of `S` (Conrad, Definition B.1.1).
- `S.presheaf.stalk x`: Mathlib's local ring `𝒪_{S,x}` of `S` at `x`.
- For `U : S.Opens`, `U.toScheme` is the open subscheme on `U` and `U.ι : U.toScheme ⟶ S`
  its inclusion. For `p : U' ⟶ U.toScheme`, `(GroupScheme.baseChange (p ≫ U.ι)).obj H` is
  the base change of `H` along the composite `U' → U → S`, which is the base change of the
  restriction `H|_U` along `p`.
- `IsFinite p`, `Etale p`, `Surjective p`: Mathlib's morphism properties.
- `IrreducibleSpace S`: the underlying topological space of `S` is irreducible (in
  particular nonempty).

## Statement and quantifiers

The proposition quantifies over every scheme `S` such that for every point `x : S` the local
ring `𝒪_{S,x}` is a domain (`IsDomain`) that is integrally closed (`IsIntegrallyClosed`),
and over every `H : GroupScheme S` with `IsMultiplicativeType H`. It asserts the
conjunction of:

1. **Local isotriviality.** For every point `s : S` there is an open `U : S.Opens` with
   `s ∈ U`, a scheme `U'` and a morphism `p : U' ⟶ U.toScheme` that is finite, étale and
   surjective, such that the base change of `H` along `p ≫ U.ι` is diagonalizable.
2. **Isotriviality over irreducible bases.** If `S` is irreducible, there are a scheme `S'`
   and a finite, étale and surjective morphism `p : S' ⟶ S` such that the base change of
   `H` along `p` is diagonalizable.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are the
printed page numbers.

- Corollary B.3.6, p.293: "Let S be a normal scheme. Every S-group H → S of multiplicative
  type is locally isotrivial: there is a Zariski-open cover {U_i} of S such that each H|U_i
  is isotrivial (i.e., splits over a finite étale cover of U_i). If S is irreducible (e.g.,
  connected and locally noetherian) then H → S is isotrivial. In particular, for
  irreducible normal S and a geometric point s̄ of S, the functor H ⇝ Hom_{S-gp}(H, G_m)_s̄
  is an anti-equivalence from the category of multiplicative type S-groups to the category
  of discrete π1(S, s̄)-modules that are finitely generated as abelian groups."
- Definition B.1.1 and the following paragraph, p.280: groups of multiplicative type, and
  "split (or diagonalizable)" groups `G ≃ D_S(M)`.

Conrad's proof (pp.293–295) uses the anti-equivalence of Proposition B.3.4 to reduce to
showing that a locally constant étale sheaf `F` of finitely generated abelian groups on a
normal scheme is isotrivial, first over a field, then over an integrally closed local
domain, then over an irreducible normal scheme by gluing. This is explanation only.

## Derivation from the source

- **Normal scheme.** In the standard definition, a scheme is normal when all its local
  rings are integrally closed domains. The hypothesis states this pointwise with
  `IsDomain` and `IsIntegrallyClosed` of each stalk. No noetherian or finiteness hypothesis
  is added, as in the source.
- **Group of multiplicative type.** Definition B.1.1, the relative `IsMultiplicativeType`.
- **Isotrivial.** Conrad's parenthesis defines "isotrivial" as "splits over a finite étale
  cover", and "splits" means "becomes diagonalizable". A finite étale cover of `U` is a
  finite étale surjective morphism `U' → U`.
- **Zariski-open cover.** "There is a Zariski-open cover {U_i} of S such that each H|U_i is
  isotrivial" is stated pointwise: every point `s` lies in an open `U` on which `H` is
  isotrivial. The two formulations are equivalent (take the family of all such `U`). The
  restriction `H|_U` followed by base change along `p` is the base change of `H` along
  `p ≫ U.ι`.
- **Irreducible.** `IrreducibleSpace S`. Conrad's example "connected and locally
  noetherian" is a sufficient condition and is not encoded.

## Scope and omissions

All schemes are in universe `u`. The statement covers the first two sentences of
Corollary B.3.6. It omits the third sentence, the anti-equivalence with finitely generated
discrete `π₁(S, s̄)`-modules, and the following example sentences (tori over connected
locally noetherian normal bases, and `Z`-tori being split).

## Related Library statements

- [`MultiplicativeType`](MultiplicativeType.md) and
  [`RelativeMultiplicativeType`](RelativeMultiplicativeType.md) define the field-level and
  relative predicates of multiplicative type.
- `ChevalleyGroupClassificationStatement`
  ([`Reductive.ChevalleyGroupClassificationStatement`](../Reductive/ChevalleyGroupClassificationStatement.md))
  cites the consequence of Corollary B.3.6 that all `Z`-tori are split; its Markdown records
  that Corollary B.3.6 for general normal bases was not stated there.
