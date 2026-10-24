# Weak induction of a Hecke character on unramified spectra

This module defines the unramified matching condition of Harris's weak
automorphic induction from a Hecke character. It compares a numerical
spectral system of a number field `E` with a Hecke character `χ` of a finite
extension `E'`. It involves no cuspidal representation and asserts no
existence. Attaching the relation to actual cuspidal classes is a separate
definition. That definition will use the spectral systems that such classes
carry.

## Setting

`E` and `E'` are number fields, in independent universes, with an algebra
map `E → E'`. Finite places of `E` are the Library's `Global.FinitePlace E`,
the height-one primes of the ring of integers. For such a place `v`,
`FinitePlacesAbove E' v` is the finite type of height-one primes `w` of
`𝓞 E'` lying over `v`. `FiniteCompletion E' w` is the completion of `E'` at
`w`. `χ.finiteComponent w` is the continuous character of its unit group
obtained by restricting the actual Hecke character `χ` of `E'`, a continuous
character of the idele-class group.

## Definitions

- `WeakInduction.IsUniformizerFamily v ϖ` says that `ϖ w` has valuation
  `exp (-1)` at every place `w` above `v`. This is the uniformizer convention
  of `Automorphic.Unramified.HeckeEulerProductRigidityStatement`.
- `WeakInduction.IsUnramifiedAbove χ v` says that every place `w` above `v`
  has ramification index `1` over `𝓞 E` and that `χ` is unramified at `w`.
  The index is Mathlib's `Ideal.ramificationIdx`. Being unramified means
  `HeckeCharacter.IsUnramifiedAt`: triviality on the local integral units.
- `WeakInduction.inducedEulerPolynomial χ v ϖ` is the product over the
  places `w` above `v` of `1 - χ_w(ϖ_w) X ^ f(w|v)` in `ℂ[X]`. The exponent
  `f(w|v)` is Mathlib's `Ideal.inertiaDeg` of `w` over `𝓞 E`: the degree of
  the residue field at `w` over the residue field at `v`.
- `SpectralSystem.IsWeakInductionOf s χ`, for
  `s : SpectralSystem (FinitePlace E) n`, has two conjuncts:
  - the rank `n` equals `[E' : E]`;
  - for all finite places `v` of `E` outside some finite set, if `v` is
    not exceptional for `s`, then `IsUnramifiedAbove χ v` holds. In
    addition, for every uniformizer family `ϖ` above `v`, the Euler
    polynomial of `s` at `v` equals `inducedEulerPolynomial χ v ϖ`.

The Euler polynomial of `s` at `v` is `∏ (1 - α X)` over the multiset of
eigenvalues of `s` at `v`, counted with multiplicity
(`Representation/Unramified/SpectralSystem`).

## Source and normalization

Harris, *The local Langlands conjecture for GL(n) over a p-adic field,
n < p*, Invent. Math. 134 (1998), Definition 1.3(b), printed p. 186 (PDF
p. 10), is the source. Its retained TeX is `math_9611226v1.tex`, lines 570–597. Let
`π ∈ Isob(n, E)` and `π' ∈ Isob(m, E')` with `n = m[E' : E]`. Let `S` be a
finite set of finite places of `E` containing the ramification of `π`, and
let `S'` be the set of places above `S`, containing the ramification of `π'`.
Then `π` is a weak automorphic induction of `π'` relative to `S` if
`σ(π_v) = Ind_{E'_v/E_v} σ(π'_{v'})` for every finite `v ∉ S` and every
`v' | v`. Harris remarks that this condition is equivalent to the
partial Euler product equality `L^S(s, π) = L^{S'}(s, π')`. Here we treat
the rank-one case: `m = 1` and `π' = χ`.

**Correction.** The displayed local identity has the wrong dimension unless
`v` has a single place above it. The correct identity is the direct sum over
all places above `v`. This sum is what Harris's equivalent Euler-product
formulation states. It is also Tate's restriction formula for induced
representations: Tate, *Number theoretic background*, Corvallis Part II
(1979), (2.3.5), printed p. 12, gives
`(Ind_{E/F} V)_v = ⊕_{w|v} Ind_{E_w/F_v} V_w`. We formalize the corrected
form, place by place.

**Local factors.** At a finite place `v ∉ S`, Harris (printed p. 184, TeX
lines 481–487) uses the unramified correspondence. It matches spherical representations
`τ` of `GL(n, E_v)` with unramified completely decomposable
`n`-dimensional representations `σ(τ)` of the Weil group, and it preserves
`L`-factors. Therefore the corrected condition at `v` is the local equality
`L(s, π_v) = ∏_{w|v} L(s, Ind_{E'_w/E_v} χ_w)`. Unramified semisimple
representations of the Weil group are determined by their Frobenius
characteristic polynomial, so this equality is equivalent to the
`σ`-identity.

On the induced side, `L`-factors are inductive (Tate (3.3), printed p. 14),
so `L(s, Ind χ_w) = L(s, χ_w)`. For unramified `χ_w`, Tate (3.1.3), printed
p. 13, gives `L(s, χ_w) = (1 - χ_w(ϖ_w) q_w^{-s})^{-1}`. Since
`q_w = q_v ^ f(w|v)`, this is `(1 - χ_w(ϖ_w) X ^ f(w|v))^{-1}` with
`X = q_v^{-s}`. Its denominator is the `w`-th factor of
`inducedEulerPolynomial`.

On the base side, `L(s, π_v) = (∏ (1 - α q_v^{-s}))^{-1}` over the Satake
parameters `α` of `π_v` in the unitary normalization. These are the
eigenvalue multisets supplied by `PresentedUnramifiedData`, in Gross's
convention (`Representation/Unramified/HeckeOperators`, Gross 1998
(6.5)–(6.7)). This module only compares numbers; that interpretation is a
property of the construction that supplies `s`.

## Design choices

- **Finite exceptional set.** "Outside a finite set" is
  `∀ᶠ v in Filter.cofinite`. This amounts to Harris's choice of some finite
  `S`, uniform for the base field, with all places above it removed. Places
  in `s.exceptional` are vacuous, so the relation does not depend on how
  large that finite set is.
- **Ramification of `E'/E`.** Harris does not list it among the
  hypotheses on `S`, but it is forced. At a place ramified in `E'/E`, the
  base side has degree `n = [E' : E] = Σ e(w|v) f(w|v)`, while the induced
  side has degree `Σ f(w|v) < n`. We state unramifiedness explicitly.
- **Rank.** The conjunct `n = [E' : E]` is Harris's hypothesis
  `n = m[E' : E]` with `m = 1`. At any matching unramified place it also
  follows from the degree count.
- **Uniformizers.** `χ` is unramified at each `w`, and two uniformizers
  differ by an integral unit. So `χ_w(ϖ_w)` does not depend on the choice,
  and requiring the identity for every family is equivalent to requiring it
  for one. This equivalence is not proved here.
- **Arbitrary rank `m`.** For an unramified `π'` of rank `m`, the same
  computation replaces each factor by `P'_w(X ^ f(w|v))`, where `P'_w` is the
  Euler polynomial of `π'_w`. That general relation is not defined here; the
  present product is its rank-one case.

## Not asserted

This module does not assert or prove any of the following:

- the existence of a weak induction;
- uniqueness of the spectrum or of `χ`;
- any compatibility at ramified places;
- conditions of Harris's class `U(n, E)`, namely cohomological infinity
  type, conjugate self-duality and square-integrable places;
- the hypotheses of Harris's Proposition 4.8, namely general position and
  supercuspidal places.

These conditions belong to separate predicates and statements. The relation
uses no Weil group, global or local.
