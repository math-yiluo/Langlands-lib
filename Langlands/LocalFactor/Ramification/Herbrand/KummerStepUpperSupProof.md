# Kummer-step upper ramification proof

The module proves
`Langlands.Ramification.Kummer.kummerStepUpperSup.{u}` with type exactly
`Langlands.Ramification.Kummer.KummerStepUpperSupStatement.{u}`. For every
prime `p`, every `F : PadicField.{u} p`, every uniformizer `ϖ`, every
`α : AlgebraicClosure F.Carrier` satisfying `α^p = ϖ`, and every real
`-1 ≤ x ≤ b = kummerBreak F = p e_F/(p - 1)`, it proves
`(adjoinFiniteIntermediate F α).field.fixingSubgroup ⊔ G_F^x = ⊤`.
It also proves `kummerStep_upper_le_fixingSubgroup`: for every `x > b`,
`G_F^x ≤ (adjoinFiniteIntermediate F α).field.fixingSubgroup`.
Here `G_F^x` is the published absolute upper ramification group and
`e_F` is the canonical absolute ramification index. The field `F` is
arbitrary in its universe and need not contain the `p`-th roots of unity.

The implemented arithmetic lemmas use the Library's actual canonical order.
`ord_pow` specializes its integer-power law. A uniformizer is not a `p`-th power
because its order is one, whereas a `p`-th power has order divisible by `p`.
Mathlib's prime-degree binomial irreducibility theorem therefore proves
irreducibility of `X^p - ϖ`. Its monicity and the specified root equation identify
the minimal polynomial, and the standard simple-adjoin degree formula gives
`[F(α):F] = p`. These arguments do not require roots of unity or normality.

The arithmetic and subsequent helpers are internal deductions using the
published canonical valuation, ramification and Herbrand APIs and the
imported Mathlib algebraic identities. The target's original source map is
in the published paired documentation of
`Langlands.LocalFactor.Ramification.Herbrand.KummerTowerStatement`.
The proof follows the cyclotomic tame-descent route, with the
prime-index argument below supplying the final transitivity step.

The extension-arithmetic calculation also proves that the root
has canonical order one, the absolute ramification index is multiplied by `p`,
and the relative residue degree is one. In any supplied degree-`p` extension,
order comparison yields `e_F p ord(β) = e_L`; the degree identity yields
`e_L f = p e_F`. Cancellation gives `ord(β) f = 1`, and positivity forces both
factors to be one. This proof does not use normality.

The cyclotomic-order calculation proves
`(p - 1) ord(ζ - 1) = e` for every primitive prime-order root in a p-adic
field. It first proves that associated elements of the actual canonical
integer ring have equal order: a unit has valuation one, hence order zero.
The root itself has order zero and therefore lies in that integer ring.
Mathlib's cyclotomic-unit identity makes each nontrivial root difference
associated to `ζ - 1`. Multiplying these associations and using
`IsPrimitiveRoot.prod_one_sub_pow_eq_order` identifies the product with `p`.
Taking the canonical order gives the formula. This is an internal derivation
from the cited Mathlib identities and the Library's normalization laws.

For two distinct roots of the same nonzero prime-degree radical, their ratio
is a primitive root of unity. Multiplicativity of the order then gives the
exact difference order. When the radical is a uniformizer, the Library's
uniformizer criterion characterizes membership in the lower group at `i` by
fixing the radical or by `(p - 1) i ≤ e_L`. Residue degree one supplies the
surjective residue map needed by that criterion. Fixing a generating radical
implies that an automorphism is the identity, by the power-basis extension
principle. The lemma `kummerStep_root_ord_and_ramificationIndex` exports the
root-order and absolute-ramification-index conclusions for the actual
simple intermediate field.

For a Galois degree-`p` radical step, there is a nonidentity automorphism.
Applying the cyclotomic-order calculation to its radical ratio produces a
natural number `t` with `(p - 1) t = e_L = p e_F`. Thus `t` is precisely
`kummerBreak F`. The lower groups are the whole automorphism group through
`t` and trivial thereafter. The Library's inverse Herbrand computation for
prime-order filtrations gives `ψ(t) = t`. Antitonicity gives the full upper
group at every real index at most `t`; strict monotonicity of `ψ` and the
ceiling definition of real lower numbering give triviality above `t`.
These filtration calculations are internal deductions from the preceding
order formulas and the published ramification and Herbrand APIs.

The Bézout reduction replaces a radicand of positive order `r`
coprime to `p` by one of order one. If `r a + p b = 1` and `η` is a base
uniformizer, the new radical is `δ = β^a η^b`, with radicand
`ϖ^a η^(p b)`. The canonical integer-power and multiplicative order laws
give its radicand order one. In a degree-`p` extension this radical generates
the extension, since its irreducible polynomial has degree `p`. This is an
internal algebraic reduction for the subsequent tame-base-change argument.

The tame-extension lemmas are complete. On the first lower group, taking a
`p`-th power is surjective because its order is prime to `p`. The integer-ring
power lemma moves such powers one step deeper. Induction and termination of
the lower filtration therefore make every positive lower group trivial.
The floor formula for the actual Herbrand function then gives `φ(x)=x/|G₀|`
for nonnegative `x`. The Library inertia-order identity identifies this
relative ramification index and proves `φ(b_N)=b_F`.

The abstract tame-descent argument is also implemented. The tower inverse
Herbrand law identifies the subgroup parameter with `ψ_{N/F}(x)`. The
subgroup formula therefore puts every automorphism over `N` in the ambient
upper group at `b_F`. Above `b_F`, the tame quotient upper group is trivial,
so every ambient automorphism lies in the restriction kernel. The kernel
equivalence and the radical upper profile then make it the identity. These
are internal deductions from the published tower and subgroup theorems.

The theorem `cyclotomic_adjoin_finrank_lt` bounds `[F(ζ):F]` by `p - 1`
using divisibility of the minimal polynomial by the cyclotomic polynomial
and its degree `φ(p) = p - 1`. Irreducibility of the cyclotomic polynomial
over `F` is unnecessary. In particular, the cyclotomic degree is prime to `p`.

The theorem `exists_finite_kummer_upper_model` constructs both fields inside
the given algebraic closure. It takes `N = F(ζ)` for a primitive `p`-th root
and `M` to be the intermediate field generated by all roots of `X^p - ϖ`.
The latter is an actual finite Galois splitting field. Both `α` and `ζα`
belong to `M`; their quotient shows that `ζ` belongs to `M` and therefore
`N ≤ M`. All the resulting p-adic fields use the existing canonical
topological data and specified field inclusions.

Let `r` be the inertia order of `N/F`. The canonical order comparison gives
`ord_N(ϖ) = r`, and `r` is positive and prime to `p` because it divides
`[N:F]`. The order argument proves `X^p - ϖ` irreducible over `N`.
The splitting-field instance extends scalars from `F` to `N`, and
Mathlib's prime-radical splitting-field degree theorem, using `ζ ∈ N`,
gives `[M:N] = p`. The Bézout reduction and Galois radical profile above
therefore apply to `M/N`. Some `N`-automorphism of `M` moves `α`:
otherwise the fixed-field criterion would put `α` in `N`, contradicting
its radicand's order being prime to `p`. Tame descent puts this automorphism
in `Gal(M/F)^b` and proves `Gal(M/F)^x = 1` for `x > b`.

For the absolute conclusions, `mem_adjoin_fixingSubgroup_iff` identifies
the fixing subgroup of `F(α)` with the automorphisms fixing `α`, by
the simple-adjoin extension principle. The published
`HerbrandBridge.absoluteUpperFiniteImage` lifts the moving finite
automorphism at `b` to an element of `G_F^b` moving `α`.
For `x > b`, every element of `G_F^x` restricts to the identity on `M`,
so it fixes `α` and hence the whole simple intermediate field. This
proves the strict upper-bound auxiliary
`kummerStep_upper_le_fixingSubgroup`.

Finally put `H = Gal(Ω/F(α))` and `U = G_F^x` for `x ≤ b`.
The degree formula gives `[G_F:H] = p`, and antitonicity puts the
moving element of `G_F^b` in `U`. Thus `H < H ⊔ U`. Finite-index
strict antitonicity gives `[G_F:H ⊔ U] < p`, while index
divisibility makes it a divisor of `p`. It must be one, proving
`H ⊔ U = ⊤`. The theorem retains the target's hypothesis `-1 ≤ x`;
the same argument happens to work for every `x ≤ b`.

The source motivation is the operator plan note *Formalizing the large
external inputs of the local Langlands correspondence for GL_n*
(16 November 2026), Remark 4.1(i), lines 586–603, registered as
`operator-external-inputs-plan-2026-11-16`, and the operator route note
*Numerical local Langlands for GL_n, counts on the two sides and the
recommended route* (16 November 2026), Corollary `cor:kummer`,
lines 890–897, registered as `operator-numerical-llc-route-2026-11-16`.
The relevant classical ramification conventions are Serre,
*Local Fields*, IV §§1–3, printed pp. 61–75
(`serre-1979-local-fields`). The implemented proof uses the published
finite tower, subgroup, prime-pattern and absolute finite-image
theorems; it does not use a field-of-norms comparison or an external
Kummer ramification theorem.

The canonical order of a power uses `UnramifiedBaseChange.ord_pow`. The radical splitting field and its finite-dimensional instance use `KummerNorm.radicalField` from `KummerRadicalFields`.
