# Invariant functionals on twisted homogeneous-space tests

These statements use `HomogeneousFunctions.renardSpace H hH`, the published
submodule of actual locally constant complex functions on the original group,
with covariance `f(hg) = (δ_G(h)/δ_H(h)) f(g)` and support contained in `H K`
for some compact subset `K` of `G`. All groups are Hausdorff, locally compact
and totally disconnected; `H` is any closed subgroup. No countability,
unimodularity or compactness restriction is imposed on `G` or `H`.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French
version of 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Locators: II.3.9, last paragraph on printed p.48 / PDF p.54, Theorem and averaging
proof on printed pp.49–50 / PDF pp.55–56, and Remark on printed p.50 / PDF p.56.
The module-to-sheaf construction cited by the Remark is II.2.4–II.2.5,
printed pp.38–42 / PDF pp.44–48. The compact-induction comparison below is a
derived internal bridge to the published compact-function induction model;
II.3.9 does not itself name that model.

Declarations are in
`Langlands.HarmonicAnalysis.HomogeneousFunctions.Renard`.

`InvariantFunctionalStatement` gives an actual complex-linear functional on the
whole twisted space that is strictly positive on every nonzero pointwise
nonnegative real-valued function and invariant under the published right
representation. Every invariant functional in its full complex algebraic dual
is a unique complex multiple of this one; every strictly positive invariant
functional is a unique positive real multiple. This records the Theorem and
its positive-scalar consequence without replacing the full dual by measures
or by a restricted class of functionals.

`AveragingStatement` specifies an actual complex-linear map `p` by the source
integral
`p(f)(g) = ∫ h:H, f(hg) δ_G(h)⁻¹ dμ_H(h)`.
The subgroup has its induced topology and Borel space; closedness supplies
local compactness. Every displayed integrand is required to be integrable.
The map lands in the existing twisted space, is surjective and commutes with
the actual right action on both tests and twisted functions. A right-invariant
functional on the twisted space factors the actual right Haar distribution
`Distribution.ofMeasure μ_G.inv` through `p`. The map is existentially specified
by its values at every group point, which determine it uniquely; no arbitrary
averaging operator or assumed invariance is supplied as input.

`QuotientTestStatement` gives the trivial-character identification with the
existing `SchwartzBruhat (Induction.LeftQuotient H)`. Its linear equivalence is
specified pointwise as pullback along the exact published quotient projection
to `H\G`, with its quotient topology.

`CompactInductionStatement` constructs a smooth unit-valued complex character
whose values are exactly the same positive relative modular values, and an
identity-on-values equivariant linear equivalence with the existing
`Induction.CompactFunctions H (characterRepresentation χ.toMonoidHom)`.
That carrier requires one open right stabilizer for the whole function and
compact projected nonzero support. These conditions are not silently identified
with local constancy and the compact-lift condition: the equivalence explicitly
retains the obligation to prove they coincide in the present closed-subgroup
setting. The target uses the actual compact-induction action. Equality with
the separately published `Hecke.Homomorphism.relativeModularCharacter`, when
its nonarchimedean hypotheses are supplied, follows from the same pointwise
character formula; no second induced-function carrier is introduced.

`PointwiseModuleSheafStatement` asserts that the actual quotient is locally
profinite, and gives a nondegenerate action of the already published pointwise
test algebra on the original twisted space. The action is constrained at every
point to be multiplication by the pullback of the scalar test. It then uses
the actual `ProjectorBasisSheaf.basisSheaf` of that action, whose sheaf condition
is already proved in the Library. A compact-open projector fixes exactly the
functions supported over that compact open in the quotient. Restrictions of
sections of this specific sheaf are pointwise multiplication by its
characteristic function, again pulled back to `G`. Thus the Remark is compared
to a published sheaf construction on the specified action, without assuming a
category equivalence as an input or replacing the action by arbitrary data.

`Statements` is the conjunction of these five closed `Prop`-valued targets.
They supply no proofs. Positivity refers to real-valued nonnegative complex
functions and involves no conjugation. Renard's modular convention is the
reciprocal of Mathlib's, as in the imported `Distribution.renardModular`.
