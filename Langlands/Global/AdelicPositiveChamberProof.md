# Nonemptiness of the adelic parabolic positive chamber

`Langlands.Global.positiveChamberNonempty` proves the unchanged
`Langlands.Global.PositiveChamberNonemptyStatement.{u}`. It applies
`ParabolicRootPresentation.exists_zeroRegularParameter` to the given actual
parabolic, rational Levi and split component over a number field. The witness
satisfies the strict inequalities of `IsRegularParameter` at threshold zero
for the Weyl-induced form of that presentation.

## Implemented proof

1. Let `B` be `weylInducedCharacterForm hA hT r.data.f r.data.i` on
   `Vstar A = ℝ ⊗[ℤ] X^*(A)`. The character lattice of the split torus is
   finitely generated over `ℤ`, so `Vstar A` is finite-dimensional.
   `weylInducedCharacterForm_nondegenerate` makes `B.toDual` an equivalence.
   Take `v` mapping to `r.splitComponentEvaluation`; then `B(v, –)` is
   evaluation on the defining split-component cocharacter of `r`.
2. The private lemma `realParameterRestriction_surjective` lifts `v` to a
   real character parameter `y` of `P`. The rational Levi retraction `q : P → M`
   satisfies `l ≫ q = 𝟙 M`, so restriction along `l` on characters has right
   inverse given by restriction along `q`. After tensoring with `ℚ`, compose
   this surjection with `IsSplitComponent.rationalCharacterRestrictRat_surjective`
   for `a : A → M`. Tensoring the composite with `ℝ` preserves surjectivity;
   `rationalRealTensorEquiv_naturality` identifies the result with
   `realParameterRestriction (a ≫ l)`.
3. Map `y` into the complex parameter space by applying `Complex.ofReal` to
   the scalar tensor factor. Tensor extensionality and `Complex.ofReal_re`
   show that taking the real part recovers `y`. Thus the restricted real
   part of the chosen `λ` is `v`.
4. A member of `r.unipotentRoots` is a nonzero restriction `α = r.data.f ≫ β`
   of a positive ambient root `β`. By `restrict_positive_eq_zero_or_mem`, it
   is an intrinsic positive root: the zero alternative is ruled out by
   membership in `r.unipotentRoots`. The connected reductive hypothesis
   supplies smoothness, hence the local finite-type instance used by this
   lemma. Now `splitComponentEvaluation_tmul` identifies `B(v, 1 ⊗ α)` with
   the real cast of the positive integral pairing of `α` with the defining
   cocharacter. If there are no unipotent roots, the inequalities are vacuous.

## Source and provenance

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*,
J. Amer. Math. Soc. 37 (2024), §§2.1–2.2, pp. 190–191 (PDF pp. 4–5;
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`), identify the
character parameter space in the number-field case and use the positive Weyl
chamber as the starting region for convergence. This proof establishes the
nonemptiness used there, not convergence or continuation. The cocharacter
argument adapts the regular-parameter construction `exists_regularParameter`
(module `AdelicEisensteinRegularRegion`) as documented in
`AdelicIntertwiningCocycleReduction`. This module
uses public algebraic results, not the private helpers or the analytic
reductions, and does not need to rescale the witness at threshold zero.
