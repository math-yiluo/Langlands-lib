# Locally constant scalar compatibility over a homeomorphism

Worker 1222. This internal comparison joins the distribution action in
`Distributions` to the section isomorphisms and algebraic dual transpose in
`HomeomorphSheafIso`. Its provenance is the Definition of distributions and
the last two paragraphs of Renard II.2.5, printed pp.42–43 / PDF pp.48–49,
in the French edition dated 9 July 2026. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read both original pages for this comparison.

Renard defines the full locally constant action on distributions by
`(f · T)(s) = T(f · s)`. He then defines isomorphisms of sheaves over a
homeomorphism using compact-section test-module isomorphisms, and denotes
their algebraic dual transpose by the same homeomorphism. The present module
proves that these two published constructions agree and that the transpose
respects the full locally constant action. This compatibility is a derived
consequence; it is not an additional numbered theorem in the source.

## Objects and comparisons

`scalarComap γ : LocallyConstant Y ℂ ≃ₐ[ℂ] LocallyConstant X ℂ`
is Mathlib's algebra equivalence of locally constant functions along the
homeomorphism `γ : X ≃ₜ Y`, with formula `g ↦ g ∘ γ`. The scalar part retains
independent universes for `X` and `Y`. The two inverse identities are proved
pointwise. `testComap_lc_smul` verifies pointwise compatibility with the
published pullback of compactly supported tests and their ambient multiplier
action.

The rest uses `X Y : Type`, the universe of the published `SheafIso`.
`compactSectionEquiv F` is the identity linear equivalence between
`Distributions.CompactSection F` and `CompactSupport.submodule F.presheaf`.
Both are the actual subtype of global sections with compact nonzero-germ
support. Their carrier predicates and complex operations agree by definition.
`distributionEquiv F` is the corresponding identity comparison of their
actual algebraic complex duals. No continuous-dual or finiteness hypothesis
is imposed.

`inclusion_smul` shows that the full locally constant action restricted to
tests is the published test action. `lc_test_smul` proves their mixed
associativity by passing to global sections, where the locally constant
scalar pullback is an algebra homomorphism and the scalar action is a module
action.

## Transport and its proof

For `Φ : SheafIso F E`, `sectionEquiv Φ hX` is the published complex-linear
section isomorphism, expressed in the distribution compact-section API. Here
`hX : IsLocallyProfinite X` means Hausdorff with a compact-open neighborhood
basis; there is no compactness or countability hypothesis on the space.

`sectionEquiv_smul` proves

`Φ(f · s) = (f ∘ Φ.homeomorph.symm) · Φ(s)`.

The implemented proof uses the published nondegeneracy of compact sections:
choose an idempotent test `e` fixing `s`. Then `f · s = (f · e) · s`,
where `f · e` is a compactly supported test. Apply test-linearity of `Φ`,
pullback compatibility for the mixed action, and mixed associativity.
Test-linearity also says that the pullback of `e` fixes `Φ(s)`. This completes
the formula without requiring that `f` have compact support.
`sectionEquiv_comap_smul` gives the equivalent formula
`Φ((g ∘ Φ.homeomorph) · s) = g · Φ(s)` for functions on `Y`.

`transpose Φ hX` is the algebraic dual linear equivalence of
`sectionEquiv Φ hX`. Its formula is `T ↦ T ∘ Φ`.
`distributionEquiv_transpose` proves equality with the existing
`HomeomorphSheafIso.SheafIso.transpose`, under the identity dual comparisons.
`transpose_smul` evaluates on a compact section and uses
`sectionEquiv_comap_smul` to prove

`transpose Φ hX (g · T) = (g ∘ Φ.homeomorph) · transpose Φ hX T`.

All results in this module are proved. The open/closed exact sequence and
module-sheaf basis equivalence remain separate obligations.
