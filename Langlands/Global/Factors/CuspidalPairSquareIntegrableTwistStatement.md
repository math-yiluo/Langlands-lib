# Sections of a cuspidal pair are square integrable up to an imaginary twist

Module `Langlands.Global.Factors.CuspidalPairSquareIntegrableTwistStatement` defines the
proposition
`Langlands.Global.CuspidalPairEisenstein.CuspidalPairSquareIntegrableTwistStatement`. It gives no
proof.

## Statement

Let `F : Type` be a number field with `[CompactSpace (AdeleQuotient F)]`, `r t : ℕ`,
`N = r + t + 2`. Let `T : CuspidalOperatorRealization F r` and
`T' : CuspidalOperatorRealization F t` both have `HasUnitaryCentralCharacter`, and let `φ` satisfy
`IsSection T T' φ` (module `Langlands.Global.Factors.CuspidalPairEisensteinSeries`).

The group-scheme data are:

- the scheme `GL_N` (`groupScheme (Fin N)`);
- the scheme block parabolic `P` of type `(r + 1, t + 1)` (`blockParabolicHom`), with its
  block-unipotent radical (`blockUnipotentInclusion`) and block-diagonal Levi `M`
  (`blockLeviInclusion`);
- `K = standardCompactPoints F N`, with the Iwasawa height of `isIwasawaCompact_blockParabolic`;
- the standard matrix embedding.

Then there are a real parameter `y ∈ X^*(P) ⊗ ℝ` and a function `ψ` on `GL_N(𝔸)`, the adelic
points of the scheme, such that

1. `φ (adelicHomeomorph F N x) = ψ x · m_P(x)^{iy}` for every adelic point `x`, where
   `m_P(x)^{iy} = (isIwasawaCompact_blockParabolic F _).heightPower (imaginaryParameter F P y) x`
   is `exp ⟨iy, H_P(x)⟩`;
2. for every smooth structure `hsmooth`, `hcalc` of `GL_N`,
   `IsSquareIntegrableInducedForm K _ (standard embedding) hsmooth hcalc p iU l ψ`. That is,
   `ψ` lies in Lapid's space `A^2_P`. It is an automorphic form on `U(𝔸) M(F) \ GL_N(𝔸)`, it
   satisfies `ψ(a g) = δ_P(a)^{1/2} ψ(g)` for `a` in the split component `A_M`, and
   `∫_{K × A_M M(F) \ M(𝔸)} δ_P(m)^{-1} |ψ(m k)|² < ∞` for the Library's canonical measures.

The field is in `Type` because `IsSquareIntegrableInducedForm` is defined for `F : Type` only: its
measure `RestrictionSplitCentre.canonicalMeasure` is built from the Weil restriction of `M` to
`ℚ`, which is taken inside one universe.

## Mathematical content

By `IsSection`, on each compact slice `m ↦ δ_P(m)^{-1/2} φ(m k)` the section is a finite linear
combination of products `f(m₁) f'(m₂)`. Here `m = (m₁, m₂) ∈ GL_(r+1) × GL_(t+1)`, and `f`, `f'` are
cusp forms in the spaces of `π` and of `(π')^∨`.

**The exponent.** The split component `A_M` (`RestrictionSplitCentre.canonicalSubgroup F M`) is
the group of positive real points of the split component, the largest central split torus, of
`Res_{F/ℚ} M`. It sits in `M(𝔸_F)` through the archimedean places, with finite components equal
to one. It is the identity component of the real points of that torus, not the whole group of real
points. On `A_M` the cusp forms transform by the
central characters `ω` of `π` and `ω'^{-1}` of `(π')^∨`. These are unitary, so on the positive
real scalars they are `a ↦ a^{iτ}` and `a ↦ a^{-iτ'}` for real `τ`, `τ'`. The two block
determinant characters have independent nonzero scale factors there. So a real combination `y` of
them gives `exp ⟨iy, H_P(a)⟩` the same values on `A_M`. Then `ψ = φ · m_P^{-iy}` satisfies Lapid's
condition `ψ(a g) = δ_P(a)^{1/2} ψ(g)`. Here `δ_P` is the modulus character, the norm of
`det(Ad | Lie P)` (`modulusParameter`). On `M` this is `|det m₁|^{t+1} |det m₂|^{-(r+1)}`, the
factor used by `IsSection`.

**Automorphy.** The factor `m_P^{-iy}` is smooth, left `U(𝔸) M(F)`-invariant, right
`K`-invariant and of modulus one. Multiplying by it multiplies the normalized Levi slices by a
character of `M(𝔸)`; this character may be nontrivial on the centre of `GL_N(𝔸)`. Invariance and
modulus alone do not give center-finiteness, which is part of the definition of an automorphic
form (Mœglin–Waldspurger I.2.17, condition (iv)). Bernstein–Lapid §2.2 gives
`φ · m_P^λ ∈ A_P` for every `φ ∈ A_P` and every parameter `λ`, in particular for `λ = -iy`. By
the definition of automorphic forms in Mœglin–Waldspurger I.2.17, this includes
center-finiteness. So `ψ` is automorphic when `φ` is.

**Square integrability.** The compact translates of the section span a finite-dimensional space
(`IsSection`). So on `K` the slices are combinations of finitely many products of Levi
coefficients, with coefficients bounded on `K`. With
`J` summands, the Cauchy–Schwarz bound `|∑_j a_j|² ≤ J ∑_j |a_j|²` reduces the integrability of
`δ_P(m)^{-1} |ψ(m k)|²` on `K × A_M M(F) \ M(𝔸)` to that of `|f(m₁) f'(m₂)|²` for single cusp
forms. Mœglin–Waldspurger I.2.18 gives integrability modulo the full adelic centre for unitary
central characters. The residual centre, modulo `A_M` and the rational central points, is a
product of compact norm-one idele class groups. So the integral over the split-component quotient
is finite as well.

## Source

- The spaces `A^n_P` and `A^2_P`: E. Lapid, *On Arthur's asymptotic inner product formula of
  truncated Eisenstein series*, Clay Math. Proc. 13 (2011), §2, p. 311, together with the
  decomposition (1) on the same page. The decomposition writes an element of `A_P` as a sum of
  terms `e^{⟨λ_i, H_P⟩} Q_i(H_P) ψ_i` with `ψ_i ∈ A^n_P`. For a nonzero cuspidal-pair section
  there is one term, with imaginary exponent `λ = iy` and `Q = 1`. The zero section allows `y = 0`
  and `ψ = 0`.
- Cusp forms: C. Mœglin and J.-L. Waldspurger, *Spectral Decomposition and Eisenstein Series*
  (1995), I.2.17 (pp. 37–38: automorphic forms on `U(𝔸) M(k) \ G` with the center-finiteness
  condition (iv), and the central character condition (v)) and I.2.18 (p. 39). Cuspidal forms
  are rapidly decreasing, and for a unitary central character the cuspidal space is pre-Hilbertian
  for the integral over `Z_M U(𝔸) M(k) \ G`.
- The twist of automorphic forms on `U(𝔸) M(F) \ G(𝔸)`: J. Bernstein and E. Lapid, *On the
  meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc. 37 (2024), §2.2 (p. 191),
  `φ_λ = φ m_P^λ ∈ A_P` for `φ ∈ A_P` and every parameter `λ`.

The statement is derived: it combines these facts for the cuspidal datum
`(GL_(r+1) × GL_(t+1), π ⊗ (π')^∨)`, in the Library's group-scheme formulation. Its purpose is
the following parameter identity. The group-scheme Eisenstein series of the transported section
at `s λ₁` has the same terms as the series of `ψ` at `iy + s λ₁`, because
`exp ⟨s λ₁, H⟩ · exp ⟨iy, H⟩ = exp ⟨iy + s λ₁, H⟩`. For `Re s = 0` the parameter `iy + s λ₁` is
imaginary, so `EisensteinImaginaryAxisHolomorphyStatement` (Lapid 2011, Proposition 6), whose
input is a form in `A^2_P`, applies to `ψ` there.
