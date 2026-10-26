# Generalized-coefficient kernel criterion for scalar uniqueness

`Langlands.Whittaker.GeneralizedCoefficientKernelStatement.{uG,uV}` is an
internal conditional proposition. This module states it as a `Prop`-valued
definition; it does not prove it. The kernel comparison described below is a
plan for a separate proof.

## Exact statement

Let \(G\) be a Hausdorff locally compact totally disconnected topological group
with its Borel measurable structure. Let \(\mu\) be a left Haar measure that
is also right invariant and inversion invariant. In Lean, `IsHaarMeasure μ`
supplies left invariance, finiteness on compact sets, and positivity on nonempty
open sets; right and inversion invariance are explicit additional instances.
Let \(\rho\) be an admissible irreducible complex representation on \(V\).
Here `IsAdmissible ρ` includes smoothness and finite-dimensional fixed spaces
for every open subgroup. The universes of \(G\) and \(V\) are independent.
There is no countability assumption on \(G\) or topology on \(V\).

Let \(\tau:G\to G\) be an actual homeomorphism satisfying
\[
 \tau^2=\mathrm{id},\qquad \tau(gh)=\tau(h)\tau(g),\qquad \tau_*\mu=\mu.
\]
The last hypothesis is `MeasurePreserving τ μ μ`. Let
\(W\subseteq V^*=\operatorname{Hom}_{\mathbf C}(V,\mathbf C)\) be any complex
submodule. Fix a nonzero element
\[
 \eta\in (V^\vee)^*,\qquad V^\vee=\mathrm{SmoothDual}\,\rho.
\]
Both stars denote full algebraic duals. Neither \(\ell\in W\) nor \(\eta\)
is required to be smooth.

Use the published test-function space
\(H=\mathrm{HarmonicAnalysis.SchwartzBruhat}\,G\), integrated action
\(\pi(f)=\mathrm{Hecke.integratedAction}(\mu,\rho,h_{\mathrm{Admissible}}.1,f)\),
and full-transpose smoothing
\[
 S_\ell(f)(v)=\ell(\pi(f)v),\qquad S_\ell(f)\in V^\vee.
\]
The actual generalized-coefficient distribution is
\[
 D_{\ell,\eta}(f)=\eta(S_\ell(f))
   =\mathrm{generalizedCoefficient}
      (\mu,\rho,h_{\mathrm{Admissible}}.1,\ell,\eta)(f).
\]
Assume, for every \(\ell\in W\),
\[
 \mathrm{HarmonicAnalysis.Distribution.pushforward}(\tau)(D_{\ell,\eta})
       =D_{\ell,\eta}.
\]
The published pushforward convention is
\((\tau_*D)(f)=D(f\circ\tau)\), with no additional measure factor.
Then, for all \(\ell_1,\ell_2\in W\) with \(\ell_1\ne0\), there is a unique
\(c\in\mathbf C\) such that \(\ell_2=c\ell_1\).
Lean expresses this equality inside the subtype `W`; it is equivalent to
equality of the underlying algebraic functionals.

No unitary structure, genericity, multiplicity hypothesis, or self-duality
assumption is imposed. If \(W\) has no nonzero element, the conclusion is
vacuous. The nonzero \(\eta\) is an explicit input, not a construction supplied
by this statement.

## Internal provenance and scope

The motivation is the nonunitary kernel-comparison argument in Bernstein and
Zelevinsky, *Representations of the group GL(n,F) where F is a non-Archimedean
local field* (1976), printed p.58, §§7.6–7.8. Section 7.6 determines an
intertwiner up to scalar from its kernel; §7.7 compares the two kernels of a
bilinear form, and §7.8 supplies a symmetry that exchanges them. That argument
uses compact induction and bilinear forms. The present criterion instead uses
the Library's actual generalized coefficients on the whole test-function
space and is an internal reformulation, not a literal transcription of those
sections or a claim that their specific symmetry is already available here.

The source is registered as `bernstein-zelevinsky-1976-representations-gln`,
SHA256 `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`,
English translation, *Russian Mathematical Surveys* 31:3 (1976), pp.1–68.
The mathematical rationale for the broader abstract formulation is the
following kernel argument, using the explicit hypotheses above.

## Planned kernel comparison

All steps in this section belong to the separate proof obligation. They
describe why the proposition is sound and identify existing interfaces; this
module introduces no replacement definitions or proof of the criterion.

1. Compact open subgroups are cofinal among open subgroups:
   `Hecke.TestFunction.commonCompactOpenBiInvariance`, applied to the empty
   finite set of test functions, supplies this fact.
   `CompactSplitting.isIrreducible_smoothContragredient` and
   `isAdmissible_smoothContragredient_of_compact_cofinal` then make
   \(\sigma=\rho^\vee\) irreducible and admissible. Applying these facts again
   gives the same properties for \(\sigma^\vee\). The existing smooth-bidual
   results supply separating pairings; they require no second countability.

2. For nonzero \(\ell\), the image of \(S_\ell:H\to V^\vee\) is nonzero by
   `smoothFunctional_eq_zero_iff`, which uses Haar local units. It is stable
   under \(\rho^\vee\), by `smoothFunctional_rightTranslate`. Irreducibility
   therefore makes \(S_\ell\) surjective. Applying the same argument to the
   representation \(\sigma\) and the nonzero functional \(\eta\) shows that
   its smoothing map \(S_\eta^\sigma:H\to (V^\vee)^\vee\) is surjective.
   Define, for this explanation only,
   \[
    T_\eta(g)=S_\eta^\sigma(\check g),\qquad \check g(x)=g(x^{-1}).
   \]
   Inversion is a bijection of the actual test-function space, so
   \(T_\eta\) is also surjective.

3. The existing `smoothFunctional_convolution` and
   `Hecke.integratedTranspose_eq_integratedAction_inversion` give
   \[
    D_{\ell,\eta}(f*g)
       =\eta\bigl(\pi^\vee(\check g)S_\ell(f)\bigr)
       =T_\eta(g)\bigl(S_\ell(f)\bigr).
   \]
   The inversion-invariant measure hypothesis justifies the transpose
   identity with exactly this order. For nonzero \(\ell\), let
   \[
    L_D=\{f:\ \forall g,\ D_{\ell,\eta}(f*g)=0\},\qquad
    R_D=\{g:\ \forall f,\ D_{\ell,\eta}(f*g)=0\}.
   \]
   Surjectivity of \(T_\eta\) and separation by the smooth dual give
   \(L_D=\ker S_\ell\). Surjectivity of \(S_\ell\) and the actual evaluation
   pairing give \(R_D=\ker T_\eta\). Thus the two convolution annihilators
   separate the two factors, and \(R_D\) depends only on the fixed \(\eta\).

4. Write \(P_\tau f=f\circ\tau\), the existing test-function pullback.
   The anti-multiplicativity and measure hypotheses give
   \[
    P_\tau(f*g)=(P_\tau g)*(P_\tau f).
   \]
   This convolution-reversal identity must still be established for the
   actual convolution in the separate proof. The assumed distribution
   invariance and \(P_\tau^2=\mathrm{id}\) then yield
   \[
    f\in L_D\ \Longleftrightarrow\ P_\tau f\in R_D,\qquad
    \ker S_\ell=P_\tau^{-1}(\ker T_\eta).
   \]
   Hence \(\ker S_\ell\) is independent of the nonzero \(\ell\in W\).

5. When \(\ell_1,\ell_2\) are nonzero, equal kernels and surjectivity define
   a linear endomorphism \(A\) of \(V^\vee\) by
   \(A(S_{\ell_1}(f))=S_{\ell_2}(f)\).
   The right-translation formula makes \(A\) equivariant for \(\rho^\vee\).
   `admissibleSchur_scalarEndomorphism`, applied to that admissible
   irreducible representation, gives \(A=c\,\mathrm{id}\).
   Bilinearity of smoothing gives \(S_{\ell_2-c\ell_1}=0\).
   `smoothFunctional_eq_zero_iff` recovers the equality of the original
   full algebraic functionals, \(\ell_2=c\ell_1\).
   Its local-unit proof uses `Hecke.exists_normalizedIndicator_fixes` for
   each vector; it does not assume either original functional is smooth.

6. If \(\ell_2=0\), take \(c=0\). In both cases, the assumption
   \(\ell_1\ne0\) makes the scalar unique.

The parent Whittaker application must separately construct the relevant
nonzero \(\eta\), using the Gelfand–Kazhdan equivalence, and prove the
distribution invariance for its actual Whittaker-functional subspace and
unsigned long-Weyl transpose. Neither that equivalence nor the required
Shalika distribution theorem is an asserted result of this module.
The parent's `MultiplicityOneStatement` is unchanged.
