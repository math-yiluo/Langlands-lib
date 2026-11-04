# Interface of the rational-side contradiction

Module `Langlands.GroupScheme.Reductive.RadicalFieldExtension.RationalSideInterface`.

This module defines the proposition `RationalSideStatement`. It is an internal interface of
the proof of `Langlands.GroupScheme.AlgebraicallyClosedRadicalFieldExtensionStatement`, not a
statement from the literature. It splits that proof into two halves that compile
separately: the module `KSide` proves the target from `RationalSideStatement`
(`algebraicallyClosedRadicalFieldExtensionStatement_of_rationalSide`), and the module
`RationalSide` proves `RationalSideStatement` (`rationalSide`). Its content is the
specialization step of the source argument (Conrad, Exercise 3.4.1; Milne, Proposition
19.5): over the small field, the specialized data contradict the triviality of the unipotent
radical.

## Statement

`RationalSideStatement.{u}` says the following. Let `k : Type u` be an algebraically closed
field and `G` a group scheme over `Spec (CommRingCat.of k)` with `Smooth G.X.hom`,
`IsAffineHom G.X.hom` and `HasTrivialUnipotentRadical G`. Connectedness of `G` is not
assumed. Let `N : Type` be a finite type with decidable equality and
`ρ : MatrixRepresentation G N` a representation whose underlying scheme morphism
`ρ.hom.hom.left` is a closed immersion. Let `𝔭` be a prime ideal of the global functions
`Γ(G.X.left, ⊤)` with

- `𝔭 < ker(e^*)`, a strict inclusion, where `e^*` is evaluation at the identity rational
  point, the ring map `(1 : Spec k ⟶ G).left.appTop` on global functions.

Let `Γ` be a subgroup of the group `G(k)` of rational points
(`Over.mk (𝟙 (Spec k)) ⟶ G.X`) such that

- `Γ` is normal in `G(k)` (`Γ.Normal`),
- `Γ` is solvable (`Group.IsSolvable Γ`),
- `ρ(g) - 1` is nilpotent for every `g ∈ Γ`, where `ρ(g) = ρ.rationalMatrix g` is the
  matrix in `Matrix N N k`, and
- every rational point `x` whose evaluation `x^*` on global functions kills `𝔭`
  (`𝔭 ≤ ker(x^*)`) lies in `Γ`.

Then `False` holds.

In words: over an algebraically closed field, a smooth affine group scheme with trivial
unipotent radical has no prime `𝔭` strictly inside the augmentation ideal whose rational
zeros all lie in a normal solvable group of rational points acting unipotently in a
closed embedding into `GL_N`. The proof in module `RationalSide` builds, from such data, a
nontrivial smooth connected normal unipotent closed subgroup: the identity component of the
Zariski closure of `Γ`.
