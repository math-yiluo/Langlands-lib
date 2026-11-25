# The residue projection of a separable closure: the valuation and the integers

`Langlands.Galois.Local.ResidueProjectionIntegers` proves two clauses of
`ResidueProjectionProperties K Ω` (`Galois/Local/ResidueProjectionStatement.lean`) about
the valuation and the integers of a separable closure: the fifth (integrality over
`𝒪[K]` is membership in the integers) and the sixth (Galois invariance of the
valuation). The objects are those of `Galois/Local/AbsoluteDefinitions.lean`, namespace
`Langlands.LocalGalois.SepClosed`.

## Setting

Both theorems take, as the statement does,

```lean
(K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
(Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
```

in independent universes `uK` and `uΩ`. The file installs, as local instances with names
specific to this module, `Algebra.IsAlgebraic K Ω` (from separability,
`Algebra.IsSeparable.isAlgebraic`; it is declared first, because once the normed-field
instances are present, instance search for it exceeds the default limit), and the Library's local
norm on `K`: `localNormedField K`, `localNormedField_ultrametric K`,
`localNormedField_complete K`. With them, `closureIntegers K Ω` is the closed unit ball of
the spectral norm of `Ω` over `K` and `closureValuation K Ω : Valuation Ω ℝ≥0` is that
norm as a valuation.

## Statements

**`SepClosed.isIntegral_iff_mem_closureIntegers`.** An element of `Ω` is integral over the
valuation ring `𝒪[K]` of `K` exactly when it lies in the integers of `Ω`:

```lean
theorem Langlands.LocalGalois.SepClosed.isIntegral_iff_mem_closureIntegers
    (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (Ω : Type uΩ) [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] (x : Ω) :
    IsIntegral 𝒪[K] x ↔ x ∈ closureIntegers K Ω
```

**`SepClosed.closureValuation_algEquiv_apply`.** Every automorphism of `Ω` over `K`
preserves the valuation of `Ω`:

```lean
theorem Langlands.LocalGalois.SepClosed.closureValuation_algEquiv_apply
    (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (Ω : Type uΩ) [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] (σ : Ω ≃ₐ[K] Ω) (x : Ω) :
    closureValuation K Ω (AlgEquiv.toAlgHom σ x) = closureValuation K Ω x
```

## Proofs

*Integrality.* The Library's `integral_iff_mem_spectralIntegers`
(`Galois/Local/SpectralProof.lean`) says that, for any algebraic extension of a complete
ultrametric field, an element is integral over the unit ball `baseIntegers K` of the
base exactly when its spectral norm is at most one. The unit ball of the local norm of
`K` is `𝒪[K]` (`localNormedField_integer`), so the two subrings of `K` are equal; the
ring isomorphism `RingEquiv.subringCongr` between them commutes with the inclusions into
`Ω`, and `RingEquiv.isIntegral_iff` transports integrality from one to the other.

*Invariance.* The value of `closureValuation K Ω` is the spectral norm, and Mathlib's
`spectralNorm_eq_of_equiv` says that the spectral norm is invariant under every
`K`-algebra automorphism.

Neither proof uses that `Ω` is separably closed: they hold for every algebraic
extension; the hypothesis `[IsSepClosure K Ω]` is that of the statement.

## Declarations, in order

1. `rpIntegersIsAlgebraic`, `rpIntegersNormedField`, `rpIntegersUltrametric`,
   `rpIntegersComplete` (local instances, namespace `Langlands.LocalGalois.SepClosed`).
2. `SepClosed.isIntegral_iff_mem_closureIntegers` (theorem; fifth clause).
3. `SepClosed.closureValuation_algEquiv_apply` (theorem; sixth clause).

## Literature

- Jürgen Neukirch, *Algebraic Number Theory*, Grundlehren 322, Springer (1999), file
  `/srv/central-library/Neukirch--Algebraic number theory (book)--1999.pdf` (SHA-256
  `4f4406e097cf7cc4bfcc3eb818153d8361c5b0d8f5fb9848053d68d6c6239210`): Chapter II, §4,
  Theorem (4.8), printed p. 131, with its proof on p. 132. A valuation of a complete field
  extends uniquely to any algebraic extension; for a finite extension the proof shows that
  the valuation ring of the extension is the integral closure of the valuation ring of the
  base. The Library's integers are the unit ball of the spectral norm, which for
  `K` complete is this unique extension; the statement here is for the infinite
  extension `Ω` directly.
- Jean-Pierre Serre, *Local Fields*, GTM 67, Springer (1979), file
  `/srv/central-library/Serre--Local Fields--1979.pdf` (SHA-256
  `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`): Chapter II, §2,
  Proposition 3, printed p. 28, and Corollaries 2 and 3, p. 29. For a complete discrete
  valuation and a *finite* extension, the integral closure is a discrete valuation ring,
  the valuation extends uniquely (Corollary 2), and conjugate elements have the same
  valuation (Corollary 3), which is the invariance proved here. Serre's valuations are
  discrete and additive; the Library's `closureValuation` is a multiplicative valuation
  with values in `ℝ≥0` on the infinite extension `Ω`, whose value group is not discrete.
