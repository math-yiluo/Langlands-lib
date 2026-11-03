# Evaluation formulas for genuine dual-frame coordinates

Let `S : Scheme.{u}`, `M : S.Modules`, and `n : ℕ`. The genuine frame
`e : LocalFrame M n U` is an isomorphism from the free sheaf on
`ULift (Fin (n + 1))` to `M.over U`. Its published `dual` is a genuine
frame for the actual internal dual sheaf `Langlands.Scheme.Modules.dual M`.
This module identifies the dual coordinates with evaluation and computes their
transition coefficients. All assertions hold over the original scheme universe.

## Coordinate functionals and evaluation

For `i : Fin (n + 1)`, `dual_localBasisCoordinate` proves the equality of
actual sheaf morphisms on the category of opens contained in `U`:

```text
localBasisCoordinate e.dual ⟨i⟩
  = localDualEvaluation (localBasisSection e ⟨i⟩).
```

The right side evaluates a local dual section on the compatible family of
sections given by the `i`th original basis vector. This assertion concerns
sheaf morphisms, so its components work on every smaller open.

The implemented proof expands the published inverse of `dualLocalFreeIso`.
That inverse is the finite sum of evaluations followed by the free-sheaf
inclusions. Composing with the `i`th free coordinate projection leaves exactly
the `i`th evaluation, using `ιFree_freeCoordinate` and the finite-sum
identities in the additive category.

If `V ≤ U`, write `b_e(i)|V` for
`(localBasisSection e ⟨i⟩).val (op (Over.mk (homOfLE h)))`.
For `φ : Γ(dual M, V)`, `dual_coordinates_apply` then gives

```text
e.dual.coordinates V h φ i = dualEval M V φ (b_e(i)|V).
```

Its proof applies the preceding sheaf-morphism equality to the component on `V`.

## Dual transition coefficients

Let `e : LocalFrame M n U` and `f : LocalFrame M n V`. Let `W` lie in both
opens, with inclusions `hWU : W ≤ U` and `hWV : W ≤ V`.
For indices `i, j : Fin (n + 1)`, `dual_change_single` proves

```text
(e.dual.change f.dual W hWU hWV) (Pi.single j 1) i
  = (f.change e W hWV hWU) (Pi.single i 1) j.
```

Here `Pi.single j 1` is the `j`th standard coefficient vector.
`e.change f` takes the coefficient vector in frame `e`, reconstructs its
section, and takes its coefficients in frame `f`. Thus the matrix of the
dual transition is the transpose of the reverse primal transition matrix.
The reversal of `e` and `f` is part of the statement.
`dual_change_single` is a defined proof of this equality, with its complete proof
body included; it is not a proposition definition awaiting a proof.

The proof first identifies the reconstructed `j`th dual vector using
`coordinates_symm_single`. The published `dualLocalFreeIso_basis` identifies
that vector with the restriction of the original `j`th coordinate functional.
The evaluation formula above evaluates it on the `i`th `f` basis vector.
Applying `coordinates_symm_single` to the reverse primal change gives exactly
the same expression. No tensor comparison or coordinate-transition hypothesis
is assumed.

## Provenance and scope

These are derived consequences of the published genuine-frame construction,
its finite dual-basis isomorphism, and actual internal-dual evaluation. No
additional assertion from external literature is invoked.

The formulas supply a step toward comparing genuine tensor-frame cocycles.
They do not yet prove the scalar relation between those cocycles or construct
a tensor-line projective-bundle isomorphism. The cubic embedding, Hilbert
quotient and `LargeLevelRepresentabilityStatement` remain further obligations.
