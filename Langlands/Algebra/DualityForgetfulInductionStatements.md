# Duality intertwines the forgetful and induction functors (Renard I.4.2, Theorem): statements

Module `Langlands.Algebra.DualityForgetfulInductionStatements`. Namespace `Langlands.Algebra`.
Universe parameters `uA`, `uB` (the algebras) and `v` (module carriers).
The module contains two **statements**, the `Prop`-valued definitions
`DualityForgetfulStatement` and `DualityInductionStatement`. It proves nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`. The Theorem of I.4.2 had no published statement. The
published note
[duality-coefficient-conventions](../../notes/renard/duality-coefficient-conventions.md)
(Worker 6) analyses why: Renard's hypotheses, read as additive ring-bimodule conditions, do
not make the complex scalars recovered from `A` agree with those recovered from `B`. The
evaluation formula of Renard's proof needs that agreement. This unit states the Theorem
under the common-coefficient reading that the note identifies as sufficient. The
unrestricted additive reading is not stated here.

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read I.4.2, printed pp.23–24 / PDF pp.29–30:

> Théorème. Soient `A` et `B` des algèbres à idempotents, et supposons que `B` soit muni
> d'une structure de `A`-bimodule non dégénéré. On suppose que les actions à droite de `A`
> et `B` sur `B` commutent avec les actions à gauche, de sorte que `B` est aussi un
> `A − B` et un `B − A`-bimodule. Le foncteur d'oubli `F_AB` et le pseudo foncteur d'oubli
> `ˇF_AB`, et leurs adjoints respectivement à droite et à gauche `I_AB` et `P_AB` sont
> alors définis comme dans la section précédente (avec les adaptations évidentes lorsqu'on
> considère des modules à droite plutôt qu'à gauche). On a alors, pour tout `B`-module à
> gauche non dégénéré `N`, `ˇF_AB(Ñ) = F_AB(N)^∼`, et pour tout `A`-module à gauche non
> dégénéré `M`, `I_AB(M̃) = P_AB(M)^∼`.
>
> Les égalités de foncteurs énoncées dans ce théorème sont bien évidemment à interpréter
> comme étant simplement l'existence d'isomorphismes naturels (par ailleurs explicites)
> entre eux.

The proof identifies `ˇF_AB(Ñ) = Hom_B(B, Ñ)_A` with `Hom_ℂ(B ⊗_B N, ℂ)_A` by the
tensor–Hom identity of I.2.2. The second identity follows by the same method or by
adjunction from the Lemma (I.4.2.1).

## Published objects used

- `NonUnitalModuleDual.leftToRightFunctor hA : (NondegenerateModuleCat A)ᵒᵖ ⥤
  RightNondegenerateModuleCat A`, the duality `M ↦ M̃` of I.4.1. The dual of `M` is the
  nondegenerate part of `Hom_ℂ(M, ℂ)`, for the complex scalars recovered from the
  `A`-action (I.2.1), with right action `(λ · a)(m) = λ(a · m)`. Right modules are left
  modules over `Aᵐᵒᵖ`, and `RightNondegenerateModuleCat A = NondegenerateModuleCat Aᵐᵒᵖ`.
- `NondegenerateTensorFunctor.regularF hA hB hAB hLeft : M(B) → M(A)`, Renard's
  `F_AB(N) = B ⊗_B N` (I.2.3.1), with the supplied left `A`-action on `B` and the right
  regular `B`-action.
- `NondegenerateTensorFunctor.regularP hB hBA hRight : M(A) → M(B)`, Renard's
  `P_AB(M) = B ⊗_A M`, with the left regular `B`-action and the supplied right `A`-action.
- `RenardRightHomFunctors.rightPseudoF hAB hA : M(B)_d → M(A)_d`, the right-module
  pseudo-forgetful functor `X ↦ Hom_{B°}(B, X)_A` with `(φ · a)(b) = φ(a · b)`
  ([RenardRightHomFunctors](RenardRightHomFunctors.md)).
- `RenardRightHomFunctors.rightI hBA hB : M(A)_d → M(B)_d`, the right-module induction
  `X ↦ Hom_{A°}(B, X)_B` with `(ψ · b′)(b) = ψ(b′ b)`.
- `ActionsCommute A B B` (left `A` commutes with right `B`), `IsNondegenerate`,
  `IsRightNondegenerate`.

## The statements

Let `A` and `B` be complex algebras with idempotents: `NonUnitalRing`, `Module ℂ`, the
compatibility classes `IsScalarTower ℂ _ _` and `SMulCommClass ℂ _ _` for the
multiplication, and `IsIdempotented`.

**`DualityForgetfulStatement`.** Let `B` carry a left `A`-action that is nondegenerate,
commutes with right multiplication by `B`, and satisfies `(c a) · b = c (a · b)` for
`c ∈ ℂ` (`IsScalarTower ℂ A B`). Then the two functors `(M(B))ᵒᵖ → M(A)_d`

```text
N ↦ ˇF_AB(Ñ)    and    N ↦ F_AB(N)^∼
```

are naturally isomorphic.

**`DualityInductionStatement`.** Let `B` carry a right `A`-action that is nondegenerate,
commutes with left multiplication by `B`, and satisfies `b · (c a) = c (b · a)`
(`IsScalarTower ℂ Aᵐᵒᵖ B`). Then the two functors `(M(A))ᵒᵖ → M(B)_d`

```text
M ↦ I_AB(M̃)    and    M ↦ P_AB(M)^∼
```

are naturally isomorphic.

## Formalization choices

- **Common complex coefficients.** The statements assume that the `A`-actions on `B` are
  compatible with the complex structures of `A` and `B`. This is the reading of "`B` muni
  d'une structure de `A`-bimodule" as a bimodule of complex algebras. Without it, the
  complex structure on `F_AB(N)` recovered from `A` and the one on `Ñ` recovered from `B`
  need not match. The published note gives the example `A = B = ℂ` with
  `a · b = conj(a) b`: there Renard's evaluation `φ ↦ (b ⊗ n ↦ φ(b)(n))` does not land in
  complex-linear functionals. Whether some other natural isomorphism exists under the bare
  additive hypotheses is not decided. That reading is not stated here, and the ledger
  records it as open.
- **One-sided hypotheses.** Each identity uses only one of the two `A`-actions on `B`. The
  first uses the left action, with the right regular action of `B`. The second uses the
  right action, with the left regular action of `B`. Each statement assumes only the
  action, commutation, nondegeneracy and compatibility it uses. Renard's other hypotheses
  (the other `A`-action, commutation of the two `A`-actions) are not needed, so each
  statement covers the source's setting.
- **Natural isomorphisms.** As Renard says, the equalities mean the existence of natural
  isomorphisms. The statements assert `Nonempty (G₁ ≅ G₂)` in the category of functors. The
  explicit isomorphisms are described below.
- **Right-module functors.** "Les adaptations évidentes" are the published right-module
  functors `rightPseudoF` and `rightI`, which use exactly the actions listed above.
- **Universes.** `N` has carrier in `Type v`. `F_AB(N)`, `ˇF_AB(Ñ)` and their duals have
  carriers in `Type (max uB v)`, as the published functors produce. The same holds for the
  second identity.

## Why the statements are true

1. For `φ ∈ ˇF_AB(Ñ) = Hom_{B°}(B, Ñ)_A` put `Φ(φ)(b ⊗ n) = φ(b)(n)`. This is balanced
   because `φ(b b′) = φ(b) · b′` and `(λ · b′)(n) = λ(b′ n)`.
   - `Φ(φ)` is complex-linear for the scalars recovered from `A`. If `e ∈ A` fixes `b`, then
     `c · (b ⊗ n) = ((c e) · b) ⊗ n = (c b) ⊗ n` by the tower law, and
     `φ(c b) = c φ(b)` because original intertwiners of nondegenerate modules are
     complex-linear (I.2.1).
   - `Φ(φ)` is fixed by any idempotent of `A` that fixes `φ`, and `Φ` is `A`-equivariant.
   - The inverse sends `λ` to `b ↦ (n ↦ λ(b ⊗ n))`. It uses the same two facts, and
     idempotents of `B` fixing `b` on the right.
   - Naturality in `N` is immediate from the formulas.
2. The same construction with `Ψ(ψ)(b ⊗ m) = ψ(b)(m)`, using the right tower law, gives
   `I_AB(M̃) ≅ P_AB(M)^∼`. Alternatively, the second identity follows from the first by the
   adjunctions of I.2.3 and the Lemma (I.4.2.1), as in Renard's proof.

## Remaining obligations

The proofs are a separate obligation. The unrestricted ring-bimodule reading of the Theorem
remains a source-correspondence question.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Algebra.NonUnitalModuleDualFunctor` | `NonUnitalModuleDual.leftToRightFunctor` |
| `Langlands.Algebra.RenardRightHomFunctors` | `RenardRightHomFunctors.rightPseudoF`, `RenardRightHomFunctors.rightI` |
| `Langlands.Algebra.NondegenerateTensorFunctor` | `NondegenerateTensorFunctor.regularF`, `NondegenerateTensorFunctor.regularP` |
