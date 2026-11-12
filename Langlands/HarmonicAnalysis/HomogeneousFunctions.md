# Renard II.3.9: actual twisted homogeneous functions

This definition unit constructs a submodule of the existing
`LocallyConstant G ℂ`, its right-translation representation, and the relative
modular character for a closed subgroup with its induced topology. It does not
assert the invariant functional theorem or quotient comparison.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French
version of 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Locator: II.3.9 definition, conditions (a)–(b), right action and trivial-twist
sentence, printed p.48 / PDF p.54. The invariant functional Theorem and module
Remark are on printed pp.49–50 / PDF pp.55–56 and remain later obligations.

All declarations are in
`Langlands.HarmonicAnalysis.HomogeneousFunctions`.
`CompactModulo H f` is literally existence of a compact subset `K` of the
original group such that the nonzero locus of `f` lies in `H*K`.
`space H χ` consists of the actual locally constant functions satisfying that
condition and `f(h*x)=χ(h)f(x)`, with the nonnegative-real character embedded
into the complex scalars. For locally constant functions the nonzero locus is
closed, hence is the source's topological support. The generic space permits
any character into `ℝ≥0`; its source specialization is `renardSpace H hH`.

The submodule proof uses the empty compact for zero, the union of the two
compact bounds for addition, and the same bound for scalar multiplication.
`rightTranslate H χ g` sends the function to `x ↦ f(x*g)` and transports its
compact bound `K` to `K*g⁻¹`. Its linear-map fields and the representation laws
in `rightAction` follow from the underlying pointwise formulas and group
associativity. No smoothness or invariant-functional result is assumed in
constructing this action.

`relativeModular H hH` is exactly
`Distribution.renardModular (h:G) / Distribution.renardModular (G:=H) h`.
Closedness installs local compactness on the existing subgroup subtype, without
changing its topology. The multiplicative fields follow from those of the two
published characters. For a t.d. group, a closed subgroup is again t.d.; no
second-countability, unimodularity or compactness hypothesis is imposed on it.

The existing `Langlands.Induction.LeftQuotient H` is the actual right-coset
quotient `H\G`, and its projection is `Langlands.Induction.quotientMap H`.
Those published objects are imported for the subsequent trivial-character
comparison; no new quotient or topology is introduced. Existing compact
induction uses `Langlands.Induction.CompactFunctions` with a uniform open right
stabilizer and compact projected support. This unit follows the source's local
constancy and explicit compact lift condition directly; their exact
identity-on-values comparison, including the needed uniform stabilizer and
compact-lift results, remains an explicit statement obligation. It is not
silently treated as a definitional equality with compact induction.
