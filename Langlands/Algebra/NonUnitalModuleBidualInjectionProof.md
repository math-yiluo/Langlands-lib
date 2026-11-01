# Separation and the canonical bidual injection: proof

Worker 735 wrote this proof alone.

The module `Langlands.Algebra.NonUnitalModuleBidualInjectionProof` proves the
published closed proposition
`Langlands.Algebra.NonUnitalModuleBidualInjectionStatements.BidualInjection`.
The final theorem is

```lean
theorem bidualInjection : BidualInjection.{uA, uM}
```

Its complete type is the unchanged closed target, with independent algebra and
module universes `uA` and `uM`. The statement pair and the evaluation
constructions are imported unchanged. The only new import is Mathlib's
`Mathlib.LinearAlgebra.Dual.Lemmas`, for separation by the full dual of a vector
space. The proof adds no hypothesis: no unit, nontriviality, faithfulness,
admissibility, reflexivity, finite dimension or prior complex module structure
on an original carrier. The algebra and module may be zero.

## Source

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026,
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The canonical-injection corollary of I.4.1 and its proof are on printed p.23 /
one-based PDF p.29. The actual duals are on printed pp.22–23 / PDF pp.28–29.
Original actions and nondegeneracy are on printed pp.5–7 / PDF pp.11–13, and the
recovered complex scalars of I.2.1 are on printed p.14 / PDF p.20.
The supplement `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pp.1–2, corrects the older argument to require a nonzero vector. The target
and the proof below separate only nonzero vectors.

The source's proof takes a full complex-linear functional `λ` that is nonzero at
`m` and an idempotent `e` with `e·m = m`. Then `λ · e` lies in the
nondegenerate dual and is still nonzero at `m`. The Lean proof follows this
route for the left module. The right module is the same argument over the
opposite algebra.

## Left separation

Fix the nonunital complex algebra `A`, its idempotentedness `hA`, an original
left module `M` and its nondegeneracy `hM`.

- `idempotent_smul_mem` uses the published full-dual action
  `fullAction hA hM`. For a full functional `ψ : FullDual hA hM` and an
  idempotent `e`, the functional `op e • ψ` sends `m` to `ψ (e • m)`. It is fixed
  by `op e`, since `e • e • m = e • m`. By the published `mem_dual_iff`, it
  belongs to `nondegeneratePart hA.op (FullDual hA hM)`, which is
  `Dual hA hM`.
- `idempotentCut hA hM ψ e : Dual hA hM` packages this element; it is
  Renard's `λ · e`. `idempotentCut_apply` gives its value
  `ψ (e • m)` by definition. `idempotentCut_apply_of_fixed` gives the value
  `ψ m` when `e • m = m`.
- `exists_fullDual_ne_zero` produces, for `m ≠ 0`, a full functional `ψ` with
  `ψ m ≠ 0`. Here `FullDual hA hM` is `Module.Dual ℂ M` for the complex scalars
  `NondegenerateScalars.complexModule hA hM` recovered from the original action.
  The proof applies Mathlib's `Module.Projective.exists_dual_ne_zero ℂ`. A
  complex vector space of any dimension is free (Mathlib chooses a basis),
  hence projective.
- `leftSeparation : LeftSeparation hA hM` combines these facts. For `m ≠ 0`, it
  takes `ψ` from `exists_fullDual_ne_zero` and an idempotent `e` with
  `e • m = m` from the nondegeneracy witness `hM m`. Then
  `idempotentCut hA hM ψ e` takes the value `ψ m ≠ 0` at `m`.

## Left injectivity

- `eq_of_forall_dual_apply_eq` shows that if `φ.val m = φ.val n` for every
  `φ : Dual hA hM`, then `m = n`. Otherwise `m - n ≠ 0`, so `leftSeparation`
  gives `φ` with `φ.val (m - n) ≠ 0`. This contradicts additivity of `φ.val`.
- `evaluation_injective` proves injectivity of the exact published
  `evaluation hA hM`, with target `Bidual hA hM` and action
  `bidualAction hA hM`. If `evaluation hA hM m = evaluation hA hM n`, then
  applying both sides to any `φ : Dual hA hM` gives `φ.val m = φ.val n`. This is
  the published formula `evaluation_apply`, which holds by definition.
- `evaluationLinear_injective` proves injectivity of the exact
  `evaluationLinear hA hM`. It uses the recovered complex modules
  `NondegenerateScalars.complexModule hA hM` and
  `NondegenerateScalars.complexModule hA (bidual_isNondegenerate hA hM)`. Its
  underlying function is definitionally `evaluation hA hM`, so the previous
  result applies.
- `leftEvaluationInjective : LeftEvaluationInjective hA hM` is the conjunction
  of these two results.

## Right side

Now `M` is an original right module, that is, a `NonUnitalModule Aᵐᵒᵖ M` with
`hM : IsNondegenerate Aᵐᵒᵖ M`.

- `rightSeparation : RightSeparation hA hM` is `leftSeparation hA.op hM`. The
  left argument applies verbatim to the opposite algebra `Aᵐᵒᵖ` with
  `hA.op`. The resulting functionals lie in `Dual hA.op hM`, as the target
  requires.
- `rightEvaluation_injective` proves injectivity of the exact published
  `rightEvaluation hA hM`. Its target is the actual `RightBidual hA hM` with
  `rightBidualAction hA hM`, so the first dual is transported back to `A`
  before the second dualization. The value of `rightEvaluation hA hM m` at
  `φ : Dual hA.op hM` is `φ.val m` by definition, as in the published
  `rightEvaluation_apply`. So equal images give equal values under every
  `φ : Dual hA.op hM`, and `eq_of_forall_dual_apply_eq hA.op hM` concludes.
- `rightEvaluationLinear_injective` treats the exact
  `rightEvaluationLinear hA hM`. It uses the recovered modules
  `NondegenerateScalars.complexModule hA.op hM` and
  `NondegenerateScalars.complexModule hA.op (rightBidual_isNondegenerate hA hM)`.
  The underlying function is definitionally `rightEvaluation hA hM`.
- `rightEvaluationInjective : RightEvaluationInjective hA hM` is their
  conjunction.

## Categorical monomorphisms

- `mono_of_injective` is a general helper. In `NondegenerateModuleCat A`, a
  morphism `f` whose underlying additive map `f.hom.toAddMonoidHom` is injective
  is a `Mono`. Given `g ≫ f = h ≫ f`, the proof applies `ObjectProperty.hom_ext`
  for the full subcategory and `NonUnitalModuleHom.ext`. It then compares
  values pointwise and cancels `f` by injectivity.
- `evaluationMonomorphisms : EvaluationMonomorphisms hA` treats the two
  families of components. For `M : NondegenerateModuleCat A`, the underlying
  additive map of `(evaluationNatTrans hA).app M` is definitionally
  `evaluation hA M.property`, which is injective by `evaluation_injective`. For
  `M : RightNondegenerateModuleCat A`, which is `NondegenerateModuleCat Aᵐᵒᵖ`,
  the underlying additive map of `(rightEvaluationNatTrans hA).app M` is
  definitionally `rightEvaluation hA M.property`, which is injective by
  `rightEvaluation_injective`. In both cases `mono_of_injective` gives `Mono`.
  The published `evaluationNatTrans_app_hom` and
  `rightEvaluationNatTrans_app_hom` laws state these identifications.

## Assembly

`bidualInjection` takes the algebra, its instances and `hA`. It returns
`leftSeparation` and `leftEvaluationInjective` for every original left module,
`rightSeparation` and `rightEvaluationInjective` for every original right
module, and `evaluationMonomorphisms hA`. This is exactly the body of
`BidualInjection.{uA, uM}`.

The proof is complete, with no `sorry` or new axiom. It does not use the full-dual
or corner comparisons, fixed-part duality, duality exactness, or I.4.2–I.4.3.
