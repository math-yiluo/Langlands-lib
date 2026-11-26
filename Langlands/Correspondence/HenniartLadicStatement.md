# ℓ-adic Swan strata, Weil transport and Laumon's twist bijection

Let `K` be a nonarchimedean local field, `Ω` a separable closure of `K`, and
`p` the characteristic of its residue field `𝓀[K]`. Write `E = PadicAlgCl ℓ`
for the algebraic closure of the ℓ-adic coefficient field and fix a ring
embedding `ι : E →+* ℂ`. The representation carriers on both sides use the
same universe, independent of the universes of `K` and `Ω`. The definitions
apply in both characteristics and for every prime `ℓ`. The four proposition
statements use `ℓ ≠ p`, expressed by the nonzero image of `ℓ` in the relevant
residue field.

## Swan exponent and refined orbit strata

`LadicHasSwan K Ω ℓ ι ρ s` holds if the class of `ρ`, restricted to the local
Weil group of `Ω/K` and extended to `ℂ` along `ι`, underlies a continuous
irreducible Weil class of the same rank with `HasWeilSwan K Ω σ s`. The
existential witness supplies the continuity, irreducibility, and rank of the
transported class. If the transport admits no such Weil class, the predicate
is false. This encoding uses the numerical Swan exponent of
`HenniartLocalNumerical` through `ladicWeilTransport`. It is motivated by
Henniart's use of the Swan exponent for ℓ-adic classes and his passage to
complex coefficients. Laumon defines the ℓ-adic Swan conductor by the
slope decomposition, after establishing finiteness of the wild inertia
image. [Henniart 1988, §§4.1–4.2, pp. 509–510](#sources) and
[Laumon 1987, (2.1.2.2) and (2.1.2.4)–(2.1.2.5), p. 152](#sources).

`ladicRefinedStratum K Ω ℓ ι k s f` consists of the unramified-twist orbits
containing an irreducible ℓ-adic class of rank `k + 1` with Swan exponent
`s` in this sense and torsion number `f`. The definition uses
`ladicUnramifiedOrbitClass` and `ladicTorsionNumber` from
`HenniartLadicClasses`, so `f` counts the unramified ℓ-adic characters that
fix the class. This is the ℓ-adic counterpart of `W_K(k+1,s,f)` as encoded
by `weilRefinedStratum`. [Henniart 1988, §4.2, p. 510, and the numerical route
note, §2.2](#sources).

## Finite inertia and the complex Weil class

`LadicFiniteInertiaStatement` states that the image of `absoluteInertia K Ω`
is finite for each irreducible representation of `Ω ≃ₐ[K] Ω` over `E` that is
continuous and defined over a finite extension of `ℚ_[ℓ]`, when `ℓ ≠ p`.
This assertion is quantified uniformly over the coefficient embedding, and
its conclusion uses only the original action. Henniart gives finiteness under
irreducibility of the inertia restriction. The statement here uses
irreducibility under the whole Galois group. To see the scope of this form,
restrict to the dense Weil group, whose stable subspaces are Galois-stable
by continuity. In Tate's account of the monodromy theorem, the kernel of
the nilpotent monodromy operator is Weil-stable. Irreducibility gives zero
monodromy, so an open subgroup of inertia acts trivially and the image of
inertia is finite. [Henniart 1988, §4.1, pp. 509–510, and Tate 1979, (4.1.5),
p. 20, and (4.2.1)–(4.2.3), pp. 21–22](#sources).

`LadicWeilTransportStatement` states that for `ℓ ≠ p` and each `ι`, the
transport of every rank-`k + 1` irreducible ℓ-adic class underlies a
continuous irreducible complex Weil class of rank `k + 1`. This makes the
transport eligible for the Swan predicate. Together with the Weil-side
conductor, it gives a Swan exponent for each ℓ-adic class. Henniart's change
of coefficients is given on finite-image classes. For the transport here,
finite inertia image gives an open kernel on inertia, which is open in the
Weil group. The kernel on inertia acts trivially after base change, so the
complex representation is continuous. Restriction to the dense Weil group
preserves irreducibility, and extending an irreducible representation from
the algebraically closed field `E` preserves rank and irreducibility.
[Henniart 1988, §4.2, p. 510, and Tate 1979, (4.2.3)–(4.2.4), p. 22](#sources).

## Orbit comparison

`LadicWeilOrbitComparisonStatement` states that for `ℓ ≠ p` and each `ι`
there is an equivalence `e` from the ℓ-adic unramified-twist orbit space to
the complex Weil unramified-twist orbit space at `localDegree K Ω`. Its
first condition sends the orbit of `ρ` to the orbit of `⟨k.succPNat, σ⟩`
whenever `σ` of the same rank underlies the transport of `ρ`. Its second
condition identifies the image under `e` of each `ladicRefinedStratum`
with the corresponding `weilRefinedStratum` for all `k`, `s`, and `f`.
The degree map uses the Library's local Weil group, with separable closedness
and algebraicity supplied by `IsSepClosure K Ω`.

The twists on the Galois side are continuous ℓ-adic characters trivial on
inertia with values in a finite extension of `ℚ_[ℓ]`. The Weil twists are
parametrized by `ℂˣ` via their value on geometric Frobenius. In either orbit
space, finite inertia image means that some power of Frobenius centralizes
the inertia image. This power acts by a scalar by irreducibility. Twisting
Frobenius by a root of the inverse scalar makes that power act trivially,
giving a finite-image representative. On the Galois side compactness makes
the scalar and its root ℓ-adic units, so that the twist extends continuously
to the procyclic unramified quotient. Henniart's finite-image comparison
then uses the algebraic closure of `ℚ`, which `ι` identifies on both sides.
For the stabilizers, comparing determinants forces the Frobenius value of a
self-twist to be a root of unity of order dividing the rank. These
finite-order unramified characters correspond under `ι`.
[Henniart 1988, §§4.1–4.2, pp. 509–510, and the
numerical route note, §2.2 and the proof of Corollary `cor:Laumon`](#sources).

## Laumon's bijection over a Laurent series field

`LaumonLadicTwistBijectionStatement` uses `X = LaurentSeries 𝓀` for a finite
field `𝓀`, with Mathlib's topology and the Library's valuative relation and
local-field instance, and uses `Ω = SeparableClosure X`. For any `ι`, any
`d = k + 1` and `s ≥ 1`, and any prime `ℓ` with nonzero image in `𝓀`, it
states that there is a single bijection from the subtype of rank-`d` classes
satisfying `LadicHasSwan` at `s` onto the analogous subtype of rank `d + s`.
For each unramified ℓ-adic Galois character `χ` and each source class, a
witness `h` puts its twist back in the source subtype. Applying the bijection
to that twisted class gives the same underlying class as twisting its image
by `χ`. The subtype limits the bijection's domain and codomain to the two
Swan-`s` strata of classes.

With the two traits taken over the same finite residue field and their
uniformizers identified with the Laurent series parameter, Laumon's local
Fourier transform `F^(0,∞')` preserves the Swan conductor, adds it to the rank,
and gives an equivalence onto the representations of slopes less than one.
An irreducible target of rank `d + s` and Swan conductor `s` has a single
slope `s / (d + s) < 1`, so lies in this essential image. Laumon uses the
resulting bijection of irreducible isomorphism classes in (2.6.2) for Swan
conductor one and ranks `p^n` and `p^n + 1`.
Henniart §4.3 gives compatibility with unramified twists, which are pulled
back from the common residue field in the geometric construction. The
Lean proposition expresses the bijection using the transported Weil Swan
predicate. Identifying this predicate with Laumon's slope formula is part
of deriving that proposition from the Fourier transform.
[Laumon 1987, (2.1.2.4)–(2.1.2.5), (2.4.1), (2.4.3)(i) b)–c), and (2.6.2), and
Henniart 1988, §4.3](#sources).
[Local Fourier transform source map](../../notes/henniart/laumon-local-fourier-source-map.md)

## Sources

- G. Laumon, *Transformation de Fourier, constantes d'équations
  fonctionnelles et conjecture de Weil* (1987), `laumon-1987-fourier-weil`.
  Lemme (2.1.2.2) and (2.1.2.4)–(2.1.2.5), p. 152, (2.4.1), p. 162,
  Théorème (2.4.3)(i) b)–c), p. 163, and (2.6.2), p. 172. Retained PDF SHA-256
  `c666e214ae586651b9f171f6a39d755e58f96379970ffa98bafb2d9be591fc8e`.
- G. Henniart, *La conjecture de Langlands locale numérique pour GL(n)*
  (1988), `henniart-1988-numerical`, §§4.1–4.3, pp. 509–510.
  Retained PDF SHA-256
  `3de93884b6c4b26106d614e648cfb7f293f9f40a66ef352c0751e222a602f25c`.
- J. Tate, *Number theoretic background* (1979),
  `tate-1979-number-theoretic-background`, (4.1.5), p. 20, and
  (4.2.1)–(4.2.4), pp. 21–22. Retained Corvallis Part II PDF SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
- *The numerical local Langlands correspondence for GL_n: counts on the two
  sides and the recommended route of proof* (16 November 2026),
  `operator-numerical-llc-route-2026-11-16`, `numerical-LLC-route.tex`, §2.2
  and §5.4, including Corollary `cor:Laumon` and its proof. Registered
  directory SHA-256
  `faece16e4d4722c37c1ba0e7ebba30a11d94b64639f20f19a6aa7ccff3faba3f`.
