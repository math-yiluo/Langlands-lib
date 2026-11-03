# Absence of tori under field extension, from Milne 17.81

Worker 1395 wrote this module. It reduces
[`NoTorusBaseChangeStatement`](NoTorusBaseChangeStatement.md) (Worker 1379)
to [`NoTorusUnipotentStatement`](NoTorusUnipotentStatement.md), the Lean
form of Milne, *Algebraic Groups* (2017), Proposition 17.81. The other
inputs are invariance of unipotence under field extension (Milne,
Corollary 14.9) and triviality of homomorphisms from tori to unipotent
groups (Milne, Corollary 14.18(b)), both proved in the `Unipotent`
modules. Proposition 17.81 itself stays a hypothesis.

## Statements (namespace `Langlands.GroupScheme`)

- `SubgroupFunctor.eq_zero_of_range_eq_bot`: for group schemes `H G`
  over any base scheme and a homomorphism `f : H ⟶ G`, if
  `SubgroupFunctor.range f = ⊥` then `f = 0`. This is the converse of
  `SubgroupFunctor.range_zero` (module `Unipotent.SplitTorusHom`).
- `NoTorusBaseChangeReductionStatement.{u}` is the proposition
  `NoTorusUnipotentStatement.{u} → NoTorusBaseChangeStatement.{u}`: if every
  smooth connected affine group over a field whose homomorphisms from tori
  are all trivial is unipotent, then for every field extension `K/k` in
  `Type u` and every smooth affine group `Q` over `Spec k` whose
  homomorphisms from tori over `k` are all trivial, every homomorphism from
  a torus over `K` to `Q_K` is trivial.
- `noTorusBaseChangeReduction : NoTorusBaseChangeReductionStatement.{u}`
  proves it.

The reduction statement is an internal assembly, not a numbered result of
Milne: it records one step of Milne's proof of Theorem 17.82 (printed
p.379, one-based PDF p.395), namely that "`Q` contains no nontrivial
torus" is invariant under field extension by 17.81 and 14.9.

## Proof

`eq_zero_of_range_eq_bot`: the identity morphism of `H.X`, viewed as a
point of `H` over the test scheme `H.X`, lies in the range of `f`, with
image `f.hom.hom`. The range is `⊥`, so `f.hom.hom = 1`. Since
`Grp.forget` is faithful, `f = 0`.

`noTorusBaseChangeReduction`: let `k`, `K`, `Q`, the
hypothesis `hQ` on `Q`, a torus `T` over `K` and `g : T.toGrp ⟶ Q_K` be
given. Write `φ = algebraMap k K` and `Q⁰ = identityComponent Q` (module
`IdentityComponent`), with inclusion `ι : Q⁰ ⟶ Q`. The Library makes `Q⁰`
a smooth affine group scheme with connected underlying space.

1. `Q⁰` is unipotent. Apply `NoTorusUnipotentStatement` to `Q⁰`. For a
   torus `T'` over `k` and `g' : T'.toGrp ⟶ Q⁰`, the hypothesis `hQ`
   applied to `g' ≫ ι` and `eq_zero_of_range_eq_bot` give `g' ≫ ι = 0`,
   which equals `0 ≫ ι`. The inclusion `ι` is a monomorphism, so `g' = 0`,
   and `SubgroupFunctor.range_zero` gives `range g' = ⊥`.
2. The base change `(Q⁰)_K` is unipotent, by `IsUnipotent.baseChange`
   (module `Unipotent.BaseChange`).
3. `T` is a torus, so its underlying space is connected
   (`IsTorus.connectedSpace`, module `Torus.Geometry`). Therefore `g`
   factors through the identity component of `Q_K`:
   `g = IdentityComponent.factor _ g ≫ identityComponentι _`. The Library
   isomorphism `IdentityComponent.baseChangeIso Q φ : (Q⁰)_K ≅ (Q_K)⁰` is
   compatible with the inclusions, so `g = j ≫ (baseChangeIso Q φ).hom ≫
   identityComponentι _` with `j = IdentityComponent.factor _ g ≫
   (baseChangeIso Q φ).inv : T.toGrp ⟶ (Q⁰)_K`. The `simp` call proving
   this uses only the factorization and the inverse cancellation.
4. `j = 0` by `IsTorus.hom_eq_zero_of_isUnipotent` (module
   `Unipotent.TorusHom`), since `(Q⁰)_K` is affine and unipotent. Hence
   `g = 0`, and `SubgroupFunctor.range_zero` gives `range g = ⊥`.

This is the derivation described in the source section of
`NoTorusBaseChangeStatement`, following the proof of Milne's Theorem
17.82 (printed p.379, one-based PDF p.395). The proof adds no hypothesis
on `k`, `K` or `Q`, and uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.
