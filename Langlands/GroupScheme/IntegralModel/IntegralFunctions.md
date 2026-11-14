# Integral functions on the generic fibre and their finite generation

Module `Langlands.GroupScheme.IntegralModel.IntegralFunctions`.

## Definitions

Let `R` be a commutative ring, `K` an `R`-algebra and `A` a commutative
`R`-algebra.

- `genericEval R K A φ : K ⊗[R] A →ₐ[K] K`, for an `R`-point
  `φ : A →ₐ[R] R`, is the `K`-algebra map with `c ⊗ a ↦ c * φ(a)`
  (`genericEval_tmul`). It evaluates a function on the generic fibre at the
  `K`-point induced by `φ`.
- `integralFunctions R K A : Subalgebra R (K ⊗[R] A)` is the intersection over
  all `R`-points `φ` of the preimages of `⊥ = image(R → K)` under
  `genericEval R K A φ`. By `mem_integralFunctions`, an element `f` lies in it
  exactly when `genericEval R K A φ f` lies in the image of `R` for every
  `R`-point `φ`.

These definitions are internal names for a classical object. When `R` is a
domain, `K` its fraction field and `A` is flat, so that `A ⊆ K ⊗[R] A`,
`integralFunctions R K A` is the ring of rational functions on the generic
fibre of `X = Spec A` that are regular at every `R`-section of `X`. This is
Bruhat–Tits II (`bruhat-tits-1984-reductive-local-groups-ii`), §1.7.3 f) (the ring of functions satisfying condition (ET))
and the ring underlying the "étoffé" models of BT II §1.7. It contains the image
of `A`.

## Statement

`IntegralFunctionsFiniteTypeStatement.{u}`: let `R : Type u` be a Henselian
discrete valuation ring whose residue field is algebraically closed, `K` its
fraction field, and `A : Type u` a commutative Hopf algebra over `R` that is
flat and of finite type over `R` and whose generic fibre `K ⊗[R] A` is smooth
over `K`. Then `integralFunctions R K A` is a finitely generated `R`-algebra.

## Source and relation to smoothening

Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), §A.6 (printed
pp.645–646, PDF pp.676–677), construct the smoothening of `X = Spec A` by
iterated dilatations: `X(0) = X`, `X(i+1)` is the dilatation of `X(i)` along the
Zariski closure `Y(i)` of the reduction of the `R`-points, and Theorem A.6.2
(after Bosch–Lütkebohmert–Raynaud, *Néron Models*, §3.3, Proposition 5) shows
the sequence stops at a smooth affine model `X(n)` with `X(n)(R) = X(R)`. Since
`R` is Henselian with algebraically closed residue field, the strict
Henselization of `R` is `R`, so the source's points over the maximal
unramified integers are the `R`-points used here.

The statement follows from this termination. Every coordinate ring `O(X(i))`
is contained in `integralFunctions R K A`, because the `R`-points do not change
(KP Fact A.5.5). If `N` is a smooth affine model with `K ⊗ O(N) = K ⊗[R] A` and
`N(R) = X(R)`, then `O(N) = integralFunctions R K A`. Indeed, for `f = g/π^m`
with `g ∈ O(N)` not divisible by the uniformizer `π` and `m ≥ 1`, the reduction
of `g` is a nonzero function on the reduced special fibre of `N`. It is nonzero
at some `k`-point (Nullstellensatz), which lifts to an `R`-point `x` by Hensel's
lemma for smooth schemes. Then `f(x) = g(x)/π^m ∉ R`. Applied to `N = X(n)`,
this shows that `integralFunctions R K A = O(X(n))` is finitely generated.

The hypotheses are the source's: an affine flat finite-type group scheme over a
Henselian discrete valuation ring, with smooth generic fibre. The residue field
is specialized to be algebraically closed, as in
`Langlands.GroupScheme.IntegralModel.SmootheningStatement`. This statement is
the finite-generation input of the planned proof of that smoothening target.
The algebraically closed residue field is used in this comparison: it makes
the reductions of the `R`-points of a smooth model Zariski dense in its special
fibre.
