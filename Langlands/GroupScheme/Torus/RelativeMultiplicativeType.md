# Diagonalizable groups and groups of multiplicative type over a base scheme

Worker 75.

This module defines, for group schemes over an arbitrary base scheme `S`, the diagonalizable
group `D_S(Λ)` of a commutative group `Λ`, the predicate of being diagonalizable, and the
predicate of being of multiplicative type (Conrad 2014, Definition B.1.1). It also proves
that both predicates are invariant under isomorphism and stable under base change, and that
diagonalizable groups are of multiplicative type. It asserts no other existence,
classification or representability result.

All declarations are in the namespace `Langlands.GroupScheme.RelativeMultiplicativeType`. The
module imports [`Multiplicative`](../Multiplicative.md) (for `Gm.toSpecZ`),
[`Torus.Diagonalizable`](Diagonalizable.md) (for `Diagonalizable.groupScheme`),
[`Descent.Data`](../Descent/Data.md) (for `Descent.pullbackComparison` and the base-change
comparison isomorphisms) and Mathlib's flatness and finite-presentation morphism classes.

## Definitions

- `diagonalizable S Λ : GroupScheme S`, for `S : Scheme.{u}` and an additive commutative
  group `Λ : Type u`, is the base change along `Gm.toSpecZ S : S ⟶ Spec ℤ` (the unique
  morphism to `Spec (ULift ℤ)`) of the published diagonalizable group
  `Diagonalizable.groupScheme (CommRingCat.of (ULift ℤ)) Λ`, the spectrum of the group
  algebra `ℤ[Λ]` with points `Hom(Λ, Γ(T, 𝒪_T)ˣ)` over every test scheme `T`. So its points
  over an `S`-scheme `T` are the group homomorphisms `Λ → Γ(T, 𝒪_T)ˣ`.
- `IsDiagonalizable H`, for `H : GroupScheme S`, says that there are an additive commutative
  group `Λ : Type u` that is finitely generated (`AddGroup.FG Λ`) and an isomorphism of
  group schemes `H ≅ diagonalizable S Λ` over `S`.
- `IsMultiplicativeType H`, for `H : GroupScheme S`, says that there is an fppf cover
  `𝒰 : Scheme.Cover.{u} (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) S`,
  i.e. a jointly surjective family of flat morphisms locally of finite presentation
  `𝒰.f i : 𝒰.X i ⟶ S`, such that for every index `i` the base change of `H` along `𝒰.f i`
  is diagonalizable. The character group may vary with `i`.

## Results

- `diagonalizableBaseChangeIso b Λ`, for `b : S' ⟶ S`: an isomorphism of group schemes over
  `S'` from the base change of `diagonalizable S Λ` along `b` to `diagonalizable S' Λ`. It
  composes the base-change composition isomorphism with the equality
  `b ≫ Gm.toSpecZ S = Gm.toSpecZ S'`, which holds because `Spec ℤ` is terminal.
- `IsDiagonalizable.of_iso` and `IsMultiplicativeType.of_iso`: the predicates transfer along
  isomorphisms `G ≅ H` of group schemes over `S`.
- `IsDiagonalizable.baseChange` and `IsMultiplicativeType.baseChange`: the predicates are
  stable under base change along any `b : S' ⟶ S`. For multiplicative type the cover is
  pulled back along `b`, as in the published `RelativeTorus.IsTorus.baseChange`.
- `IsMultiplicativeType.of_isDiagonalizable`: a diagonalizable group is of multiplicative
  type, using the identity cover of `S`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are the
printed page numbers.

- Appendix B.1, p.280, before Definition B.1.1: for a finitely generated abelian group `M`,
  `D_S(M)` is the `S`-group representing the functor of characters of the constant group
  `M_S`; "it is the base change to S of the analogous group scheme over Spec Z".
- Definition B.1.1, p.280: "A group scheme G → S is of multiplicative type if there is an
  fppf covering {S_i} of S such that G_{S_i} ≃ D_{S_i}(M_i) for a finitely generated abelian
  group M_i for each i."
- The paragraph after Definition B.1.1, p.280: such a `G` "is split (or diagonalizable) over
  S if G ≃ D_S(M) for some M".

## Derivation from the source

- **`D_S(M)`.** The Library's `Diagonalizable.groupScheme R Λ` is `Spec R[Λ]` over `Spec R`
  with the character functor as functor of points. Following the source, `D_S(Λ)` is its
  base change from `Spec ℤ`. `ULift ℤ` is used so that `Spec ℤ` lives in the universe of
  `S`, as in `Gm.toSpecZ`.
- **Diagonalizable.** The source writes "for some M", where `M` ranges over finitely
  generated abelian groups as in Definition B.1.1. The definition requires `AddGroup.FG Λ`.
- **fppf covering.** An fppf covering of `S` is a jointly surjective family of flat
  morphisms locally of finite presentation. This is the Library's existing encoding of fppf
  covers, `Scheme.Cover.{u} (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) S`,
  used for example in `SpecialLinearCentralExtensionSplitStatement`. The members of the
  cover are arbitrary schemes, not necessarily open subschemes of `S`.
- **`G_{S_i} ≃ D_{S_i}(M_i)`.** This is `IsDiagonalizable` of the actual base change
  `(GroupScheme.baseChange (𝒰.f i)).obj H`, an isomorphism of group schemes over the member
  `𝒰.X i`.

## Relation to existing Library predicates

- The field-level predicate `IsMultiplicativeType` of
  [`Torus.MultiplicativeType`](MultiplicativeType.md) is a different declaration
  (`Langlands.GroupScheme.IsMultiplicativeType`, over `Spec k` for a field `k`). It asks for
  diagonalizability after some field extension. Over a field, an fppf cover can be refined
  to a field extension, so the two notions are expected to agree; this module does not
  prove that.
- `RelativeTorus.IsTorus` of [`Torus.Relative`](Relative.md) asks for split tori on an étale
  cover. Tori are expected to be of multiplicative type; this module does not prove that.

## Provenance

The definitions transcribe the source; they are derived content of this module. The
results are routine invariance and base-change facts proved here.
