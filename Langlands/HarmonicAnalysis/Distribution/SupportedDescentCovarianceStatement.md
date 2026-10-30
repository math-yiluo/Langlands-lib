# Scalar covariance of supported descent through an open subspace

`Langlands.HarmonicAnalysis.Distribution.SupportedDescentCovarianceStatement.{u}`
is the proposition below. This module defines the proposition and proves
nothing. Its only import is the published module
`Langlands.HarmonicAnalysis.Distribution.SupportedRestriction`, used unchanged.
Every other name it uses comes from that module or what it imports.

## Statement

Everything below is universally quantified inside the proposition. The
universe `u` is arbitrary and is the only parameter of the definition.

- `X : Type u` is a topological space that is Hausdorff (`T2Space X`), locally
  compact (`LocallyCompactSpace X`) and totally disconnected
  (`TotallyDisconnectedSpace X`).
- `U Z : Set X` are subsets, with `hU : IsOpen U`. Nothing else is assumed
  about `Z`: in particular `Z` need not be closed in `X`.
- Write `Z_U` for `(Subtype.val : U → X) ⁻¹' Z`. This is the set of points of
  the subtype `U` whose value lies in `Z`. It is a subset of `U`, not of `X`,
  and as a type it carries the subtype topology of `U`. The hypothesis
  `hZU : IsClosed Z_U` says that `Z_U` is closed in `U`.
- `D : supportedOn Z` is a distribution on `X` that annihilates every test
  function vanishing at every point of `Z`. `(D : Distribution X)` is its
  ambient coercion.
- `e : X ≃ₜ X`, `eU : U ≃ₜ U` and `eZ : Z_U ≃ₜ Z_U` are homeomorphisms.
- `c : ℂ` is an arbitrary complex number, possibly zero.

The proposition asserts that the three premises

    (1)  ∀ x : U, (eU x).val = e x.val,
    (2)  ∀ z : Z_U, (eZ z).val = eU z.val,
    (3)  pushforward e (D : Distribution X) = c • (D : Distribution X)

imply the conclusion

    pushforward eZ (descendInOpen hU hZU D) = c • descendInOpen hU hZU D.

Premises (1) and (2) say that the squares formed with the inclusions
`U → X` and `Z_U → U` commute: `e` restricted to `U` is `eU`, and `eU`
restricted to `Z_U` is `eZ`. Because `eU` and `eZ` are bijective, they also
force `e` to map `U` onto `U` and `eU` to map `Z_U` onto `Z_U`. Nothing is
said about `e` outside `U`; for example `Z` need not be stable under `e`.
By injectivity of `Subtype.val`, (1) determines `eU` from `e` and (2)
determines `eZ` from `eU`, so the two smaller homeomorphisms only witness
that these restrictions exist.

Unfolding the published definitions, premise (3) says that for every test
function `f : SchwartzBruhat X`

    D (x ↦ f (e x)) = c * D f,

and the conclusion says that for every test function `φ : SchwartzBruhat Z_U`

    descendInOpen hU hZU D (z ↦ φ (eZ z)) = c * descendInOpen hU hZU D φ.

## Exact meaning of the imported objects

- `SchwartzBruhat Y` is the published complex vector space of locally
  constant, compactly supported functions `Y → ℂ`.
- `Distribution Y` is the published abbreviation for
  `Module.Dual ℂ (SchwartzBruhat Y)`, the full complex algebraic dual, with no
  topology or continuity condition. The scalar multiplication `c • T` is the
  pointwise one of the dual, `(c • T) f = c * T f`.
- `supportedOn Z` is the published submodule of `Distribution X` consisting
  of those `T` with `T f = 0` for every `f` such that `f z = 0` for all
  `z ∈ Z`. This is pointwise-annihilator support, not topological support.
- `pushforward e`, for a homeomorphism `e : Y ≃ₜ Y'`, is the published
  complex linear equivalence `Distribution Y ≃ₗ[ℂ] Distribution Y'` with
  `pushforward e T f = T (Hecke.TestFunction.pullback e f)`. The published
  pullback evaluates as `pullback e f y = f (e y)`. No measure factor or
  inverse is involved. It is applied with `Y = Y' = X` in (3) and
  `Y = Y' = Z_U` in the conclusion.
- `descendInOpen hU hZU : supportedOn Z →ₗ[ℂ] Distribution Z_U` is the
  published chosen descent of module `Distribution.SupportedRestriction`. By
  definition it is the published open restriction between supported
  submodules, `restrictOpenSupported hU Z`, followed by the inverse of the
  closed equivalence `closedPushforwardSupportedEquiv hZU` in the space `U`.
  The local compactness of `U` that this inverse needs is supplied inside the
  definition by `IsOpen.locallyCompactSpace hU`. The published law
  `descendInOpen_apply_restrictClosed` gives

      descendInOpen hU hZU D (SchwartzBruhat.restrictClosed hZU f) =
        (D : Distribution X) (SchwartzBruhat.extendZero hU f)

  for every `f : SchwartzBruhat U`. Here `restrictClosed` is restriction of
  test functions to a closed subset and `extendZero` is extension by zero
  from an open subset.

The conclusion is about this actual chosen descent. It is not replaced by an
arbitrary distribution on `Z_U`, and the nested subtype `Z_U ⊆ U` is used
exactly as in the published definition.

## Hypotheses that are deliberately absent

- `Z` is not assumed closed in `X`, and `Z_U` is only assumed closed in `U`.
- No nonemptiness is assumed: `X`, `U`, `Z` and `Z_U` may be empty.
- No stability of `U` or `Z` under `e` is assumed beyond what (1) and (2)
  imply, and no group action, measure, countability or manifold structure
  appears.
- No continuity of distributions is assumed, and no topology on the space of
  distributions is used.
- Neither the conclusion nor any covariance of the descended distribution is
  assumed.

## Intended later proof

The following explains how the proposition is expected to be proved. This
module does not prove it, and no proof of it is in the Library.

Fix `φ : SchwartzBruhat Z_U`. The open subspace `U` is Hausdorff, totally
disconnected and, by `IsOpen.locallyCompactSpace hU`, locally compact. So the
published surjectivity theorem
`SchwartzBruhat.closedRestrictionSurjective`, applied in `U` to the closed
subset `Z_U`, writes `φ = restrictClosed hZU f` for some
`f : SchwartzBruhat U`. Two naturality identities are then needed.

- Restriction: by (2), `restrictClosed hZU (pullback eU f)` equals
  `pullback eZ (restrictClosed hZU f)`, by evaluation at each point of `Z_U`.
- Extension: by (1), `extendZero hU (pullback eU f)` equals
  `pullback e (extendZero hU f)`. At a point of `U` both sides are the value
  of `f` at its image under `eU`. At a point `x` outside `U`, the point `e x`
  is also outside `U`: otherwise, writing `y` for `e x` as an element of `U`,
  identity (1) gives `e (eU.symm y).val = y.val = e x`, and injectivity of `e`
  would put `x` in `U`. So both sides are zero there.

With these, the value of the left side of the conclusion at `φ` is
`descendInOpen hU hZU D (pullback eZ (restrictClosed hZU f))`, which by the
restriction identity is
`descendInOpen hU hZU D (restrictClosed hZU (pullback eU f))`. By
`descendInOpen_apply_restrictClosed` and the extension identity, this is
`D (pullback e (extendZero hU f))`. Premise (3) makes that
`c * D (extendZero hU f)`, which by `descendInOpen_apply_restrictClosed` again
is `c * descendInOpen hU hZU D φ`. Only linear algebra of the published
subspace maps is used, with no analytic operation on distributions.

Worker 634 has written this argument as a private development,
`SupportedDescentCovarianceCore.covariance`, in the shared draft of task
`f79ca82c-d050-4ffa-821b-c347b60e36e0` (revision 8). Its naturality strategy
is adapted from Worker 33's public helpers `extension_pullback` and
`restriction_pullback` in `Distribution.FiniteOrbitVanishingProof`. That
draft is neither reviewed nor accepted, and it is not a published theorem.
A separate exact proof task must supply and publish the proof.

## Scope

This module is a statement only. It does not state or prove:

- that `D` is determined by its descents to the pieces of a finite
  filtration, or any locality property of distributions;
- invariance or vanishing of distributions on Bruhat cells, Shalika's
  distribution invariance, or multiplicity one;
- any comparison of pointwise-annihilator support with topological support.

## Provenance

This proposition is internal derived content, not a transcription of a
literature statement. It is a consequence sought from the Library's existing
actual Schwartz–Bruhat subspace maps `SchwartzBruhat.restrictClosed` and
`SchwartzBruhat.extendZero` (module `Distribution.Subspace`), their duals
`closedPushforward` and `restrictOpen` on the full complex algebraic duals,
the published transport `pushforward` (module `Distribution.Basic`), and the
chosen descent `descendInOpen` (module `Distribution.SupportedRestriction`).
Its premises are exactly the data used by the intended proof above. It is
meant for the finite-cell step of the exact Shalika distribution-invariance
work (task `f79ca82c-d050-4ffa-821b-c347b60e36e0`). There a closed filtration
layer plays the role of `Z` and the open complement of a lower layer plays
the role of `U`. That application is not carried out here. The motivating
descent remark after Shalika (1974), Lemma 1.15, and its relation to the
pointwise support convention are documented in the published
[ClosedSupportedDescentStatement](ClosedSupportedDescentStatement.md).

Worker 634 designed this proposition as
`Langlands.HarmonicAnalysis.Distribution.Design.SupportedDescentCovarianceStatement`
in the shared draft `SupportedTransportDesign.lean` of task
`f79ca82c-d050-4ffa-821b-c347b60e36e0`, revision 8. The Lean body here is
identical to that design. Only the private `Design` namespace was dropped and
the documentation was rewritten. Worker 1079 ported it to this module and
wrote this Markdown.
