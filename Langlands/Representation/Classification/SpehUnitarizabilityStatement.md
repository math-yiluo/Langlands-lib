# Unitarizability of Speh representations

Author: Worker 1810. This pair contains one Prop-valued statement definition,
`Langlands.Classification.SpehUnitarizability`. It proves nothing. It adds no
axiom, structure field, or hypothesis asserting that a Speh quotient exists or
that any classification result holds.

## Statement

Fix a prime `p`, `F : PadicField.{uF} p` and `T : F.TopologicalData`, with
independent universes `uF` and `uV`. `SpehUnitarizability F T` is the
proposition

> for every `d : SpehDatum.{uF, uV} F T` with `d.IsDiscreteSeries`, and every
> `π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear d.degree F.Carrier)`
> with `d.IsSpeh π`, `IsUnitarizable π.representation` holds.

Smoothness uses the topology `T.topology` on `F`. Everything else comes from the
published module `Langlands.Representation.Classification.TadicUnitaryStatement`
and the modules it imports:

- `d` consists of positive integers `rank = r` and `length = k` and a smooth
  complex representation `delta` of `GL_r(F)`. `d.degree` is `k*r`.
- `d.IsDiscreteSeries` requires `delta` to be irreducible, unitarizable, and
  square-integrable modulo the actual center (`T.IsSquareIntegrable`, which
  includes a unitary central character).
- `IsUnitarizable` (from `Langlands.Representation.Unitary.Basic`) means that
  there is a `G`-invariant positive definite Hermitian form on the smooth
  carrier itself. No norm, completion or finite-dimensionality is involved.

The `d.IsDiscreteSeries` premise repeats the first conjunct of `d.IsSpeh π`.
It is kept because the task contract prescribes this exact form, which also
puts the source hypothesis `δ ∈ D^u` in plain view.

## Source

Tadic 1986 (`tadic-1986-unitary`), Appendix, printed p.375 (PDF p.42; PDF page
= printed page - 333):

> In the rest of this section we suppose that the characteristic of the field
> F is zero. Let δ ∈ GL(m, F)^ be a square-integrable representation and
> n ∈ ℕ. Then the induced representation
> ν^{(n-1)/2}δ × ν^{(n-3)/2}δ × … × ν^{-(n-1)/2}δ has a unique irreducible
> quotient. This quotient was denoted by u(δ, n).
>
> A.8. THEOREM. Suppose that char F = 0. Let δ ∈ Irr be a square-integrable
> representation and let n ∈ ℕ. Then u(δ, n) is a unitarizable representation.

The proof is on printed pp.375-377 (PDF pp.42-44). The same definition of
`u(δ, n)`, for `δ ∈ D^u`, appears in the introduction on printed p.338 (PDF
p.5). There `D^u` is "the set of all square integrable classes in Irr^u".

How the notation corresponds:

- Tadic's `m` (with `δ` a representation of `GL(m, F)`) is `d.rank = r`.
  Tadic's `n` is `d.length = k`. The group `GL(nm, F)` is
  `GeneralLinear d.degree F.Carrier`, with `d.degree = k*r`.
- `δ ∈ D^u` ("square-integrable", which in Tadic implies unitarizable) is
  `d.IsDiscreteSeries`.
- `char F = 0` needs no separate hypothesis. A `PadicField p` is a finite
  extension of `ℚ_p`, so it has characteristic zero.
- The induced representation is `d.centeredInduced`, the normalized product
  `T.twistedProductInduced` on the uniform block shape with `k` blocks of rank
  `r`. It has the constant factor `delta` and exponents
  `d.exponent i = (k-1)/2 - i` for `i < k`, giving
  `ν^{(k-1)/2}δ × … × ν^{-(k-1)/2}δ` in Tadic's decreasing order.

## How `IsSpeh` matches `u(δ, k)`

`d.IsSpeh π` has three parts. First, `d.IsDiscreteSeries`. Second, `π` is an
irreducible quotient of `d.centeredInduced`, witnessed by an actual surjective
intertwiner. Third, every irreducible smooth quotient of `d.centeredInduced`
in the same carrier universe is isomorphic to `π`. This is exactly Tadic's
description of `u(δ, k)` as "the unique irreducible quotient". The uniqueness
is uniqueness of the isomorphism class, which matches Tadic's convention that
`u(δ, n)` is a class in `Irr`.

So the Lean statement says that every representative of the class `u(δ, k)` in
this carrier universe is unitarizable. Informally, this loses nothing:
pulling an invariant form back along an isomorphism keeps it invariant and
positive definite.

The statement does not assume that a Speh quotient exists. Existence is the
separate published target `SpehExistenceUniqueness`, which another task
proves. For data where no such `π` exists in the carrier universe, the
statement is vacuously true. That is the correct reading of A.8 with
existence kept separate.

## Related results A.9 and A.10

Tadic's A.9 (printed p.377) says that the representations `L(a(n,d)^(ρ))`,
for positive integers `n, d` and unitary cuspidal `ρ`, are unitarizable. Tadic
states it as "a direct consequence of the preceding theorem". In §3.1
(printed p.352, PDF p.19), `Δ[m]` is the centered segment
`[(-m+1)/2, (m-1)/2]` and
`a(n,d) = (Δ[d]_{(-n+1)/2}, Δ[d]_{(-n+3)/2}, …, Δ[d]_{(n-1)/2})`. Its
`ρ`-version, defined in §4.6 (printed p.358, PDF p.25), is
`a(n,d)^(ρ) = (ν^{-(n-1)/2}Δ[d]^(ρ), ν^{1-(n-1)/2}Δ[d]^(ρ), …,
ν^{(n-1)/2}Δ[d]^(ρ))`: the `n` shifts of the centered length-`d` segment
`Δ[d]^(ρ)`. Tadic
§7.4 (printed p.370, PDF p.37) defines
`u(δ, n) = L(ν^{-(n-1)/2}δ, …, ν^{(n-1)/2}δ)` for `δ ∈ D^u`, characterizes it
as the unique irreducible quotient of
`ν^{(n-1)/2}δ × … × ν^{-(n-1)/2}δ`, and states
`L(a(n,d)^(ρ)) = u(L(Δ[d]^(ρ)), n)`. So A.9 is A.8 applied with
`δ = L(Δ[d]^(ρ))` and Speh length `n`, and the `L(a(n,d)^(ρ))` are exactly
the `u(δ, n)` with `δ ∈ D^u`. A.10 (printed p.377, proof through p.379)
restates the classification of the unitary dual for `char F = 0` and uses A.9.

This module formalizes only A.8 in its `u(δ, k)` form. The translation into
Zelevinsky and Langlands multisegment notation is not formalized here. The
downstream consumer is task 3fcabfac-7cbc-4d66-90b2-40b466df00f2 (Worker
1792). Its target, the published `TadicUnitaryDualExhaustion`, needs Speh
unitarizability as a prerequisite.

## The source proof is global (outstanding obligation)

Nothing is proved here. Tadic's proof is global, and every global input it
uses is missing from the current Library:

1. **Globalization of `δ`.** Tadic picks a division algebra `H` central over
   `F` of dimension `m²`, a number field `k`, a place `w` with `k_w ≅ F`, and
   an inner form `G` given by a division algebra over `k`, as in §5 of
   Rogawski [22]. The proof of [22] Proposition 5.15, or alternatively the
   Bernstein-Deligne-Kazhdan-Vignéras volume [3] (the Deligne-Kazhdan-Vignéras
   local-global comparison), then gives an irreducible cuspidal automorphic
   representation `σ = ⊗_v σ_v` of `GL(m, 𝔸)` with `σ_w ≅ δ`. The restricted
   tensor-product factorization is Flath [9].
2. **Residual spectrum.** Assume first that the central character `η` of `σ`
   is trivial on the group of central ideles that equal `1` at every finite
   place and equal one common positive real number at every infinite place. Let
   `π` be the representation `σ|det|^{(n-1)/2} ⊗ … ⊗ σ|det|^{-(n-1)/2}` of
   the Levi subgroup `GL(m)^n`. Jacquet [16, §2] gives an intertwining
   operator `E : Ind(π) → L²(ω, GL(mn, 𝔸))` whose image `τ` is irreducible.
   Here `ω` is the central character determined by `η`, and `L²(ω, …)` is the
   unitary right-translation representation on `ω`-equivariant automorphic
   functions that are square-integrable modulo the center.
3. **Local conclusion.** Write `τ = ⊗_v τ_v`. Local Hecke algebras are
   idempotented, so this yields a surjection `Ind(π_w) → τ_w`. Here `Ind(π_w)`
   is `ν^{(n-1)/2}δ × … × ν^{-(n-1)/2}δ`, so `τ_w ≅ u(δ, n)`. Since `τ` lies
   in `L²`, `τ_w` is unitarizable.
4. **General central character.** Twisting `δ` by a suitable character
   reduces this case to the previous one.

Tadic's bibliography entries for these inputs are as follows. [3] is
I. N. Bernstein, P. Deligne, D. Kazhdan, M.-F. Vignéras, *Représentations des
groupes réductifs sur un corps local*, Hermann, 1984. [9] is D. Flath (1979;
registered as `flath-1979-tensor-products`). [16] is H. Jacquet, *On the
residual spectrum of GL(n)*, Lecture Notes in Math. 1041 (1984), 185-208. [22]
is J. Rogawski, *Representations of GL(n) and division algebras over a p-adic
field*, Duke Math. J. 50 (1983), 161-196. Only Tadic's account of [3], [16]
and [22] has been read; those works are not in the central library.

Moeglin-Waldspurger, *Le spectre résiduel de GL(n)*, Ann. Sci. ENS (4) 22
(1989), 605-674 (`moeglin-waldspurger-1989-residual-spectrum`), Introduction
pp.605-606. It later identifies the whole residual spectrum of `GL(N)` as the
sum of the representations `J(V)`, each the unique irreducible quotient of an
induced representation at the exponent `((m-1)/2, …, (1-m)/2)`, as conjectured
by Jacquet. It is cited as the standard reference for the residual spectrum
behind step 2. Tadic does not cite it, and the argument above needs only
Jacquet's operator.

A proof of `SpehUnitarizability` is therefore separate later work. Either it
formalizes the global route (automorphic forms on `GL(n, 𝔸)`, Eisenstein
residues, the local-global comparison with an inner form), or it gives a
different argument. Neither is supplied here.
