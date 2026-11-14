# Statement: groups of multiplicative type split étale-locally

Worker 75.

`Langlands.GroupScheme.MultiplicativeTypeQuasiIsotrivialStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- [`Torus.RelativeMultiplicativeType`](RelativeMultiplicativeType.md), for the relative
  predicates `RelativeMultiplicativeType.IsDiagonalizable` and
  `RelativeMultiplicativeType.IsMultiplicativeType` (Conrad, Definition B.1.1); the
  base-change functor `GroupScheme.baseChange` comes transitively;
- Mathlib's `Mathlib.AlgebraicGeometry.Morphisms.Etale` and
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`, for `Etale` and `IsFinite`;
- Mathlib's `Mathlib.RingTheory.Henselian`, for `HenselianLocalRing`.

`GroupScheme S` is `Grp (Over S)`. Inside the definition the namespace
`RelativeMultiplicativeType` is open, so `IsDiagonalizable` and `IsMultiplicativeType` refer
to the relative predicates, not to the field-level `IsMultiplicativeType` of
[`Torus.MultiplicativeType`](MultiplicativeType.md).

## Predicates used

- `IsDiagonalizable H`, for `H : GroupScheme S`: there are a finitely generated additive
  commutative group `Λ` and an isomorphism of group schemes over `S` from `H` to
  `D_S(Λ)`, the base change from `Spec ℤ` of the diagonalizable group `Spec ℤ[Λ]`.
- `IsMultiplicativeType H`: there is an fppf cover of `S` (a jointly surjective family of
  flat morphisms `S_i ⟶ S` locally of finite presentation) such that each base change
  `H_{S_i}` is diagonalizable, with a character group that may depend on `i`.
- `Scheme.Cover.{u} (Scheme.precoverage @Etale) S`: an étale cover of `S`, a jointly
  surjective family of étale morphisms `𝒰.f i : 𝒰.X i ⟶ S` indexed by `𝒰.I₀`. The Library
  uses this encoding for étale covers, for example in `RelativeTorus.IsTorus`.
- `(GroupScheme.baseChange p).obj H`: the base change of `H` along `p`, with the induced
  group law.
- `HenselianLocalRing A` (Mathlib): `A` is a local ring satisfying Hensel's lemma for
  monic polynomials over its maximal ideal.

## Statement and quantifiers

The proposition is a conjunction of two parts.

1. For every scheme `S` and every `H : GroupScheme S` with `IsMultiplicativeType H`, there
   is an étale cover `𝒰` of `S` such that for every index `i`, the base change of `H` along
   `𝒰.f i` is diagonalizable.
2. For every commutative ring `A : Type u` with `HenselianLocalRing A` and every
   `H : GroupScheme (Spec A)` with `IsMultiplicativeType H`, there are a scheme `S'` and a
   morphism `p : S' ⟶ Spec A` that is finite, étale and surjective, such that the base
   change of `H` along `p` is diagonalizable.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are the
printed page numbers.

- Proposition B.3.4, pp.290–291: "Let H → S be an S-group scheme that becomes
  diagonalizable (of finite type) fppf-locally on S. Then H is diagonalizable étale-locally
  on S; i.e., H is quasi-isotrivial. More specifically, the functor
  H ⇝ Hom_{S-gp}(H, G_m) is an anti-equivalence between the category of S-groups of
  multiplicative type and the category of locally constant abelian étale sheaves on S whose
  geometric fibers are finitely generated abelian groups. If S = Spec A for a henselian
  local A then H splits over a finite étale cover of S."
- Definition B.1.1 and the following paragraph, p.280: a group of multiplicative type
  becomes isomorphic to `D_{S_i}(M_i)`, `M_i` finitely generated, on an fppf covering
  `{S_i}`; it is "split (or diagonalizable) over S if G ≃ D_S(M) for some M".

Conrad's proof (pp.291–292) reduces to a strictly henselian local noetherian base, lifts a
splitting of the special fibre over the completion with Theorem B.3.2, and descends it by
fpqc descent using the finite étale Cartier duals of the torsion subgroups `H[n]`. The
henselian assertion follows because every étale cover of a henselian local scheme is refined
by a finite étale one (EGA IV₄ 18.5.11). This is explanation only.

## Derivation from the source

- **Hypothesis.** "Becomes diagonalizable (of finite type) fppf-locally on S" is
  Definition B.1.1 of multiplicative type, the relative `IsMultiplicativeType H`.
- **Diagonalizable étale-locally.** "Diagonalizable étale-locally on S" means that there is
  an étale covering of `S` on whose members `H` becomes diagonalizable. Part 1 asserts this
  with an étale cover in the Library's encoding and `IsDiagonalizable` of each base change.
  The character group may depend on the member, as in Definition B.1.1.
- **Henselian local base.** `S = Spec A` with `HenselianLocalRing A`. "H splits over a
  finite étale cover of S" means that `H` becomes split, i.e. diagonalizable, after base
  change along a finite étale surjective morphism `S' → S`. A single morphism is used:
  a finite étale cover of `S` in this sense is one finite étale surjective `S'`.

## Scope and omissions

All schemes and the ring `A` are in universe `u`. The base `S` in part 1 is arbitrary, as in
the source. The statement covers the first and last assertions of Proposition B.3.4. It
omits the middle assertion, the anti-equivalence `H ⇝ Hom_{S-gp}(H, G_m)` between groups
of multiplicative type and locally constant étale sheaves of finitely generated abelian
groups.

## Related Library statements

- `RelativeTorus.IsTorus` ([`Torus.Relative`](Relative.md)) defines tori by splitting on an
  étale cover; for tori, part 1 is built into the definition used in the Library.
