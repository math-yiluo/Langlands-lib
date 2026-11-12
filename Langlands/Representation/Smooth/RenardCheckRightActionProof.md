# The right Hecke action through inversion

Author: Worker 139. The theorem `Langlands.Renard.Smooth.checkRightActionExists`
proves exactly `CheckRightActionExistsStatement` in independent group and carrier
universes. Its right action satisfies the published `IsCheckRightAction`
predicate by definition.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
9 July 2026 (registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`),
III.1.15, printed p.69 / PDF p.75, together with the anti-involution in II.3.12,
printed p.52 / PDF p.58. II.3.7, printed p.47 / PDF p.53, explains that inversion
of the left Haar measure gives the right Haar measure, with the modular factor
when expressed against the original left measure.

The proof constructs the right action directly. For any measure finite on
compact sets, `CheckAction.operator` sends f to the published integrated action
of the inverted test function for the pushforward measure μ.inv. It is complex
linear in f and a complex linear endomorphism in the representation vector.
Changing variables through the measurable inversion equivalence gives

`L(operator f v) = ∫ g, f(g) L(ρ(g⁻¹)v) dμ(g)`

for every algebraic complex linear functional L. This is `CheckAction.dual`.
No left invariance of μ.inv is used.

For a left invariant μ, `CheckAction.convolution` proves that convolution
reverses the order of these operators. After applying an arbitrary algebraic
linear functional, it expands the convolution as a double integral. The kernel
is continuous and supported in `(supp f · supp g) × supp f`, a compact set.
The published compact-support Fubini theorem therefore permits the integral
swap without global sigma-finiteness. Left translation of the inner variable
then changes ρ(z⁻¹) to ρ(z⁻¹)ρ(y⁻¹), and the scalar evaluation identity computes
the two iterated actions. Algebraic dual functionals separate vectors, proving
the operator identity itself.

The internal `CheckAction.module` uses these operators as an action of the
opposite Hecke algebra. Operator linearity supplies all additive laws, and the
reversed convolution identity supplies `mul_smul`. This proves the existence
assertion for all the original hypotheses, including nonunimodular groups.
The statement module and its imports are unchanged.
