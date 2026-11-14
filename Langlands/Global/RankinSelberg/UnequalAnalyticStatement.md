# Global analytic theory for unequal-rank cuspidal pairs

`Langlands.Global.RankinSelbergGlobal.UnequalAnalyticStatement` is a Prop-valued, unproved formulation of the analytic and functional-equation clauses of J. W. Cogdell, *Analytic theory of L-functions for GL_n* (2004), §2.2, Theorem 2.1, printed p.207, together with the absolute-convergence discussion on p.205. The source is registered as `cogdell-2004-analytic-theory-gln`; its PDF SHA-256 is `8117f145869274324b12344dc83fa3289e3bd27c515b8d0d4a0211cd64174944`. The PDF locators are pp.208–210. Unfolding and factorization are separate statements.

## Objects and character hypotheses

The number field ranges over `Type u`, with `[CompactSpace (AdeleQuotient F)]`. The actual cusp realizations have ranks `n = r + 1` and `m = t + 1` with `t < r`. Every vector of each realization is quantified over. The functions are exactly `cuspFunction` from the imported definition module: the Library's actual `toContinuous` functions transported by `continuousGeneralLinearEquiv` and evaluated on actual group-scheme adelic points. No abstract representation carrier, supplied integral, analytic continuation or convergence hypothesis occurs.

`IsStandardAdditiveCharacter F ψ` means that `ψ` is continuous, nontrivial, trivial on the diagonal copy of `F`, and has complex norm one everywhere. It fixes precisely the additive-character convention of the task and source. The word “standard” here specifies these properties, not an additional chosen trace character. For its inverse, complex conjugation agrees with inversion.

## Exact assertion

With `φ`, `φ'` the functions of the two vectors and `φdual(g) = φ(w_n ᵗg⁻¹)`, `φ'dual(g) = φ'(w_m ᵗg⁻¹)`, the conclusion asserts:

1. For every `s : ℂ`, the defining unequal global integrand is Bochner integrable on `GL_m(F)\GL_m(𝔸)`.
2. For every `s : ℂ`, the defining dual integrand of `φdual`, `φ'dual` is Bochner integrable on the same quotient.
3. The scalar function `s ↦ I(s;φ,φ')` is `Differentiable ℂ` on all of `ℂ`, hence entire.
4. It is bounded on every closed vertical strip.
5. For every `s : ℂ`, `I(s;φ,φ') = Ĩ(1-s;φdual,φ'dual)`.

The second integrability clause makes explicit the convergence of the other defining integral in the source's functional equation; it is not an input to that equation. `BoundedInVerticalStrips f` means that for each `a ≤ b` there exists a finite nonnegative real bound for `‖f(s)‖` on `a ≤ Re(s) ≤ b`. There are no removed points or poles in this unequal-rank assertion.

All integrability claims, differentiability, bounds, and the functional equation occur in the conclusion. The definitions remain raw totalized Bochner integrals; the statement does not assign an analytic continuation by definition. It asserts convergence everywhere for the actual cusp forms. Bochner integrability of this complex-valued scalar function expresses absolute integrability, including measurability, and excludes relying on the zero value of a nonintegrable totalized integral.

## Measures and source comparison

The reductive quotient measure is exactly `AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F m)` from the definition module, the quotient of the Library's ambient Haar by rational counting measure. The projection uses `AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure`, of total mass one on its compact unipotent rational quotient. These conventions also define the Library global Whittaker coefficients. Cogdell leaves the reductive Haar scale implicit. The same exact scale is used on both sides of the stated functional equation.

The source defines the projection on the mirabolic subgroup. The imported definition extends its displayed compact-integral formula to the full ambient `GL_(m+1)` so that conjugation by transpose inverse is well-typed. Both defining global integrals use it only at the required block matrices. `dualProjection` uses transpose inverse without a Weyl factor, while `dualFunction` includes the source's rational long Weyl matrix; rational invariance relates the equivalent source expressions.

No entire-function result or functional equation has been proved in this module. The local affine and smooth instances only expose the existing actual scheme facts so that the quotient measure can be elaborated; they add no assumptions to the statement. Existing Library pairs are unchanged.
