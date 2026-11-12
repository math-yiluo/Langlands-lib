# Renard I.2.3: the right adjoint and forgetful comparisons

Author: Worker 134. The theorem
`Langlands.Algebra.RenardForgetfulFunctor.renardForgetfulFunctorStatements`
proves the published proposition
`Langlands.Algebra.RenardForgetfulFunctor.RenardForgetfulFunctorStatements`
without changing its hypotheses or its independent universes `uA`, `uB`, `uM`.
The entry module is `Langlands.Algebra.RenardForgetfulFunctorProof`.

## Source and scope

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, I.2.3, printed pp.16–18 / PDF pp.22–24. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The target formalizes the unital right adjoint on printed p.16 and the closing
Remark on printed p.18. The statement module explains the generalization from
unital complex algebras to rings, and the nonunital additive-module setting.
This proof uses exactly that published formulation: two-sided local units along
`φ`, arbitrary specified module actions, and carrier universe `max uB uM` for
the two functor comparisons. No idempotentedness hypothesis on `B` is added.

The local-unit and categorical helper declarations in this module are derived
constructions used to prove the target. They are not additional source assertions.
The tensor comparison imports the published
`Langlands.Algebra.RegularTensorContraction` proof.

## Unital coextension adjunction

`unitalCoextensionAdjunction` uses
`ModuleCat.restrictCoextendScalarsAdj φ`. Its Hom equivalence sends a map
`g : φ_* N → M` to `n ↦ (b ↦ g (b • n))`. For this adjunction the formula in the
target is definitionally equal to its right side, so `rfl` closes that clause.
The adjunction itself packages the bijection and its naturality.

## Local-unit consequences

`imageIdempotent φ e` is the actual idempotent of `B` with value `φ(e)`:
multiplicativity carries `e * e = e` to its idempotency equation.

`target_isIdempotented` applies the two-sided local-unit hypothesis to a finite
subset of `B`. The resulting `φ(e)` fixes each element on both sides, hence
each element lies in its corner. `image_filtering` applies the same hypothesis
to the finite image of a family of idempotents of `B`.

For `fixed_iff`, if `f • m = m`, choose `e` with `φ(e) f = f` and compute
`φ(e) • m = φ(e) • (f • m) = f • m = m`. Conversely, `φ(e)` is an idempotent of
`B`, so any vector fixed by it is fixed by a `B`-idempotent. This works for every
ambient `B`-module, including degenerate ones.

## Tensor forgetful comparison

`tensorForgetfulRemark` installs the left action `a • b = φ(a) * b` and the
right regular action of `B` on `B`. Associativity proves commutation. The
left-local-unit consequence of the hypothesis proves left nondegeneracy;
right regular nondegeneracy follows from the derived `IsIdempotented B`.

For each nondegenerate `B`-module `N`, the component from `F(N)` to `φ_* N` is
the published contraction

`c_N : B ⊗_B N → N`, `b ⊗ n ↦ b • n`.

Its `A`-linearity is proved for the actual residual tensor action by equality
of additive maps. Tensor extensionality reduces this equality to
`(φ(a) * b) • n = φ(a) • (b • n)`. Published contraction injectivity applies
because `B` is idempotented. For surjectivity, an idempotent `e` fixing `n`
gives the preimage `e ⊗ n`. Naturality is the published
`RegularTensorContraction.contraction_naturality`.

The private helper `isoOfBijective` turns each bijective additive intertwiner
into a categorical isomorphism. It constructs the inverse additive equivalence,
proves its scalar compatibility by applying the injective forward equivalence,
and checks both inverse identities pointwise. `NatIso.ofComponents` assembles
the contraction components.

## Pseudo-forgetful comparison

`pseudoForgetfulRemark` installs the left regular `B`-action and the right
`A`-action `op a • b = b * φ(a)`. Associativity proves commutation. The regular
left action is nondegenerate because `B` is idempotented, and the right
local-unit equation directly proves right nondegeneracy.

The proof first constructs the natural isomorphism in the direction
`φ_* N → pseudoF(N)`, then takes its inverse. Its component is

`u_N(n) : b ↦ b • n`.

This is a `B`-intertwiner on the left regular source. Restriction preserves
nondegeneracy, so choose `e` with `φ(e) • n = n`. Then
`u_N(n)(b φ(e)) = (b φ(e)) • n = b • n`, which places it in the actual
`A`-nondegenerate Hom part by `RenardHomFunctors.mem_pseudoPart`.
Additivity is pointwise; `A`-linearity is
`b • (φ(a) • n) = (b φ(a)) • n`, exactly the published precomposition action.

If `u_N(n) = u_N(m)`, choose a `B`-idempotent fixing `n - m`. Evaluating at that
idempotent shows `n - m = 0`, proving injectivity. For a Hom element `ψ` in the
part, choose `e` with `ψ(b φ(e)) = ψ(b)` for all `b`. Its preimage is
`ψ(φ(e))`, since `B`-linearity gives
`b • ψ(φ(e)) = ψ(b φ(e)) = ψ(b)`. Naturality is the scalar compatibility
`b • f(n) = f(b • n)` of the original morphism `f`.

`forgetfulFunctorRemark` assembles these five clauses.
`renardForgetfulFunctorStatements` pairs that theorem with the unital
adjunction theorem, yielding the exact published conjunction.
