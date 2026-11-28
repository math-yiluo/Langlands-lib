# The degree-one Artin–Schreier comparison

Katz (1986), (1.4.5), p. 80. For an `𝔽_p`-algebra `B`, let `F : B → B` be the absolute Frobenius
and `℘ = 1 − F`. On `Z = Spec(A)`, any affine `𝔽_p`-scheme, the Artin–Schreier sequence
`0 → 𝔽_p → 𝔾_a → 𝔾_a → 0` of étale sheaves (with `℘` as the second map) gives a long exact
sequence. Katz combines it with `Hⁱ(Z_ét, 𝔾_a) = A` for `i = 0` and `0` for `i > 0` (SGA 4, IX
3.5 and VII 4.3) and obtains

- `H⁰(Z_ét, 𝔽_p) ≅ Ker(℘ : A → A)`,
- `H¹(Z_ét, 𝔽_p) ≅ A/℘A`, "the Artin–Schreier quotient of `A`",
- `Hᵠ(Z_ét, 𝔽_p) = 0` for `q ≥ 2`.

He then observes that `R[T] ⊆ R((T⁻¹)) = R[T] ⊕ T⁻¹R[[T⁻¹]]` induces a bijection on
Artin–Schreier quotients: the decomposition is `F`-stable, and `F` is `T⁻¹`-adically
topologically nilpotent on `T⁻¹R[[T⁻¹]]`, so `℘` respects the decomposition and is bijective on
the second summand. Here `R((T⁻¹))` is the ring of formal Laurent series in `T⁻¹`, with
finitely many negative powers of `T⁻¹`. On p. 76 Katz calls `K((T⁻¹))` a field for a coefficient
field `K`. In (1.4.2), p. 79, and (1.4.5), p. 80, the coefficients form an `𝔽_p`-algebra `R`,
and `R((T⁻¹))` is then only a ring.

This module states both facts. Throughout, `p` is a prime and the rings are commutative rings
in which `p` vanishes. The hypothesis is `(p : B) = 0`, the form used by weil-conjectures, and
it allows the zero ring.

## Definitions

- `natCast_eq_zero_of_ringHom` and `natCast_eq_zero_Γ_Spec` transport `(p : B) = 0` along a ring
  map and to the global sections of `Spec B`.
- `artinSchreierRange p B hB` is the image of weil-conjectures's `artinSchreierAddHom p hB`,
  `x ↦ x ^ p − x`. This is `(F − 1)B`, which equals `℘B = (1 − F)B`.
- `artinSchreierQuotient p B hB = B ⧸ artinSchreierRange p B hB` is the Artin–Schreier quotient,
  an additive group.
- `artinSchreierQuotientMap p φ hB` is the map of Artin–Schreier quotients induced by a ring map
  `φ : B → C`.
- `artinSchreierLaurentHom R : R[T] → LaurentSeries R` sends `T` to `single (-1) 1`. Mathlib's
  `LaurentSeries R` is the ring of finite-tailed Laurent series `R((u))` in `u = T⁻¹`, and `T`
  goes to `u⁻¹`. This is Katz's inclusion `R[T] ⊆ R((T⁻¹))`.
- `constantZModPullback p f q : Hᵠ(Y_ét, ℤ/p) → Hᵠ(X_ét, ℤ/p)` is the pullback along a morphism
  `f : X → Y`. It is weil-conjectures's `AlgebraicGeometry.Etale.cohomologyMap` followed by the
  identification `f^*(ℤ/p)_Y ≅ (ℤ/p)_X` of constant sheaves
  (`AlgebraicGeometry.Scheme.upperStarConstantSheafIso`). weil-conjectures composes the same
  maps to compare constant-coefficient cohomology under base change.
- `artinSchreierCohomologyClass p B hB : B → H¹(Spec B_ét, ℤ/p)` is the connecting map of the
  Artin–Schreier sequence. The element `b` is read as a global section of `𝔾_a` through
  `ΓSpecIso` and `Sheaf.H.equiv₀` at the terminal étale object (`Scheme.isTerminalEtale`).
  Mathlib's connecting homomorphism `Sheaf.H.δ` of the short exact sequence
  `artinSchreierSequence_shortExact` (`0 → Ker ℘ → 𝔾_a → 𝔾_a → 0`) sends it to `H¹(Ker ℘)`.
  The isomorphism `constantZModIsoKernelGaArtinSchreier : ℤ/p ≅ Ker ℘` then gives an element of
  `H¹(ℤ/p)`. This is the class of the Artin–Schreier torsor `yᵖ − y = b`.
- `artinSchreierInvariantsMap p B hB : H⁰(Spec B_ét, ℤ/p) → B` is induced by the inclusion
  `constantZModToGaSheaf : ℤ/p → 𝔾_a` and `Sheaf.H.equiv₀`.

weil-conjectures writes `℘(x) = xᵖ − x`, the negative of Katz's `℘ = 1 − F`. This changes
neither the image nor the kernel, and the connecting map changes only by the sign of the class.

## `AffineArtinSchreierCohomologyStatement`

For every prime `p`, every ring `B` with `(p : B) = 0`, and `Z = Spec B`:

1. `artinSchreierInvariantsMap` is injective with image the kernel of `x ↦ x ^ p − x`:
   `H⁰(Z_ét, ℤ/p) ≅ Ker ℘`;
2. `artinSchreierCohomologyClass` is surjective with kernel `artinSchreierRange p B hB`. It
   therefore induces an isomorphism `artinSchreierQuotient p B hB ≅ H¹(Z_ét, ℤ/p)`
   (`QuotientAddGroup.quotientKerEquivOfSurjective`);
3. `Hᵠ(Z_ét, ℤ/p) = 0` for `q ≥ 2`. This is weil-conjectures's
   `AlgebraicGeometry.Scheme.subsingleton_sheafH_constantZMod_of_isAffine`, restated for
   completeness;
4. naturality: for every ring map `φ : B → C`, `constantZModPullback` along `Spec φ` sends the
   class of `b` to the class of `φ b`. So the isomorphism of clause 2 is natural in `B`: it
   carries `artinSchreierQuotientMap p φ hB` to the pullback.

Katz states clauses 1–3. Clause 4 makes explicit the naturality he uses in (1.4.4)–(1.4.5),
where the map `H¹(𝔸¹_R, 𝔽_p) → H¹(Spec R((T⁻¹)), 𝔽_p)` is identified with the map of
Artin–Schreier quotients. It holds because the connecting maps of the Artin–Schreier sequences
on `Spec C` and `Spec B` are compatible with pullback, as are `𝔾_a` and its sections.

## `ArtinSchreierLaurentPolynomialStatement`

For every prime `p` and ring `R` with `(p : R) = 0`, `artinSchreierQuotientMap` along
`artinSchreierLaurentHom R` is a bijection from the Artin–Schreier quotient of `R[T]` to that of
`R((T⁻¹))`.

The proof route is Katz's. The additive decomposition `R((u)) = R[u⁻¹] ⊕ uR[[u]]` is stable under
`F`. On the second summand, `F` carries `uⁿR[[u]]` into `u^{pn}R[[u]]` for `n ≥ 1`, so it is
topologically nilpotent for the `u`-adic filtration. (A coefficient may be killed by `F`, as `ε`
with `ε² = 0` in `𝔽_p[ε]/(ε²)`, so `F` need not multiply orders exactly by `p`.) The coefficientwise convergent series `Σ_{m ≥ 0} Fᵐ`
inverts `1 − F` there. Hence the polynomial part carries the whole Artin–Schreier quotient.

## Declarations used

The module imports `Langlands.MathlibBase` and three modules of weil-conjectures. From
weil-conjectures it uses `artinSchreierAddHom`, `artinSchreierAddHom_apply`,
`AlgebraicGeometry.Scheme.constantZMod`, `AlgebraicGeometry.Scheme.gaSheaf`,
`AlgebraicGeometry.Scheme.artinSchreierSequence`,
`AlgebraicGeometry.Scheme.artinSchreierSequence_shortExact`,
`AlgebraicGeometry.Scheme.constantZModIsoKernelGaArtinSchreier`,
`AlgebraicGeometry.Scheme.constantZModToGaSheaf`, `AlgebraicGeometry.Scheme.isTerminalEtale`,
`AlgebraicGeometry.Etale.cohomologyMap` and
`AlgebraicGeometry.Scheme.upperStarConstantSheafIso`. Under `#print axioms` each of them depends
only on `propext`, `Classical.choice` and `Quot.sound`, and so does every declaration of this
module (`natCast_eq_zero_of_ringHom` uses only `propext` and `Quot.sound`). The theorem
`AlgebraicGeometry.Scheme.subsingleton_sheafH_constantZMod_of_isAffine` cited under clause 3 has
the same status.
