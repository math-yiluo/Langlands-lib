# Splitting over an étale diagonalizable quotient

Module
`Langlands.GroupScheme.Trigonalizable.EtaleExtensionSplitStatement`.

`Langlands.GroupScheme.EtaleDiagonalizableExtensionSplitStatement.{u}` is a
proposition definition. This module defines the proposition and proves
nothing. It is the one premise from which
`ExtensionSplitPerfectSmooth.trigonalizableExtensionSplit_of_etale` proves
the published target `TrigonalizableExtensionSplitStatement` (Milne 16.26).

## Statement

For every field `k : Type u` with characteristic exponent `p : ℕ`
(`[ExpChar k p]`), every group scheme
`G : GroupScheme (Spec (CommRingCat.of k))` with
`[LocallyOfFiniteType G.X.hom]` and `[IsAffineHom G.X.hom]`, every group
scheme `U` over `Spec k` with a homomorphism `i : U ⟶ G`, every
`Λ : Type u` with `[AddCommGroup Λ]` and `[AddGroup.FG Λ]`, and every
homomorphism `q : G ⟶ D(Λ)`, where
`D(Λ) = (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp`, assume, in
the order of the explicit binders,

- `PerfectField k`;
- `Finite Λ` and `Nat.Coprime (Nat.card Λ) p`;
- `IsClosedSubgroup i`;
- `Smooth U.X.hom` and `ConnectedSpace U.X.left`;
- `IsUnipotent U`;
- `(SubgroupFunctor.range i).IsNormal`;
- `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q`.

Then there is a homomorphism `s : D(Λ) ⟶ G` with `s ≫ q = 𝟙 D(Λ)`.

All ingredients are those of the published
`TrigonalizableExtensionSplitStatement` (see
[`ExtensionSplitStatement`](ExtensionSplitStatement.md), whose Markdown
explains them), used without change. Only the hypotheses differ. Each is an
explicit binder: perfectness of `k`; the two conditions
on `Λ`, which replace the disjunction of cases of the target; and case (b)'s
smoothness and connectedness of `U`. `ExpChar k p` is Mathlib's
characteristic exponent: `p = 1` if `k` has characteristic zero, and `p` is
the characteristic if it is positive. Since it determines `p`, the binders
`(p : ℕ) [ExpChar k p]` name the characteristic exponent and restrict
nothing; they are placed right after `[Field k]`, as in the Library's
`EtaleMultiplicativeTypeOrderStatement` and
`DiagonalizableSmoothConnectedCriteriaStatement`. Smoothness is written `Smooth U.X.hom`
and placed right after `IsClosedSubgroup i`, and the binders of `Λ` are
`[AddCommGroup Λ] [AddGroup.FG Λ]`, as in the published target and in the
corrected Milne 16.27 (`TrigonalizableSectionConjugacySmoothStatement`, module
[`SectionConjugacySmoothStatement`](SectionConjugacySmoothStatement.md)), so that
the two statements state these hypotheses in the same form. `[AddGroup.FG Λ]` follows from `Finite Λ`; it is
kept so that `D(Λ)` and the encoding of the extension are literally those of
the target.

## Meaning

The two conditions on `Λ` say that `Λ` is finite of order prime to the
characteristic exponent `p` of `k`. In characteristic zero (`p = 1`) the
second condition always holds; in characteristic `p > 0` it says that `p`
does not divide the order of `Λ`. So they say that `D(Λ)` is a finite étale diagonalizable
group (its coordinate ring is the group algebra `k[Λ]`, which is étale over
`k` exactly when `Λ` is finite of order invertible in `k`). This remark
explains the hypothesis and is not proved here. In the language of Milne
16.26 the proposition says: over a perfect field, an extension
`e → G_u → G → D → e` of a finite étale diagonalizable group `D` by a smooth
connected unipotent group `G_u` splits. The encoding of the extension by `i`
and `q` is that of the published target.

## Source and provenance

M. Raynaud, SGA 3 Exposé XVII, Gille–Polo recomposed edition (November 2008),
`sga3-expose-xvii-gille-polo-2008`, SHA256
`687f333c4f86221e7898f44c1706845d8e0b79af50ab31f3ed9a3b0f696ae25b`:

- Théorème 5.1.1 (printed p.345, margin pp.573–574, PDF p.21) fixes the
  notation: `U` a unipotent algebraic `k`-group, `H` a `k`-group of
  multiplicative type, `E` an algebraic `k`-group extension
  `1 → U → E → H → 1`; "l'extension `E` est triviale" means that `E → H` has
  a homomorphic section.
- Lemme 5.2.3 i) c) (printed pp.346–347, margin pp.575–576, PDF pp.22–23):
  "Avec les notations de 5.1.1, supposons `H` étale. Alors : i) L'extension
  `E` est triviale dans chacun des cas suivants : ... c) `k` est parfait et
  `U` est connexe."

The proposition is the special case of Lemme 5.2.3 i) c) in which `H = D(Λ)`
is diagonalizable (split) and `U` is moreover smooth. It is also a special
case of Théorème 5.1.1 i) b) (`k` perfect and `U` connected). Within Milne's
Theorem 16.26 (Milne, *Algebraic Groups* (2017), `milne-2017-algebraic-groups`,
printed p.332) it is case (b) for an étale `D`.

The source proves 5.2.3 i) c) in the following steps (printed pp.346–348,
PDF pp.22–24).

1. It replaces `E` by its reduced subgroup. Then `U` becomes smooth and
   connected, hence `k`-résoluble (4.1.4 b)), which is case d).
2. In case d), Lemme 5.2.1 c) gives a scheme section of `E → H`. Over each
   point of `H` (a finite separable extension `K` of `k`), `H¹(K, U_K) = 0`
   because `U_K` has a composition series with quotients `𝔾ₐ`.
3. A characteristic composition series with commutative quotients reduces the
   question to commutative `U`, that is, to case a). There the extension is
   trivial if `H²(H, U) = 0` (App. I 3.1).
4. Lemme 5.2.4 shows that the Hochschild groups `Hⁱ(H, U)`, `i > 0`, are
   killed by the rank `n` of the finite étale group `H`. Corollaire 5.2.4 bis
   then gives `Hⁱ(H, U) = 0`. There `n` is prime to the characteristic `p`,
   because an étale group of multiplicative type has order prime to `p`, and
   raising to the `n`-th power is an isomorphism of the commutative unipotent
   group `U`. So multiplication by `n` on `Hⁱ(H, U)` is both an isomorphism
   and zero.

The smoothness hypothesis here makes the first step unnecessary.
