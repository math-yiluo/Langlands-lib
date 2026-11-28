# Kummer lines, the Gauss line and their Fourier transforms

Laumon 1987, Remarque (1.1.3.7), p. 140, Lemme (1.4.3.1) and Proposition (1.4.3.2), pp. 149–150,
compute the Fourier transform of the extension by zero of a Kummer sheaf on `𝔾_m = A ∖ {0}`: it is
the extension by zero of the Kummer sheaf of the inverse character, twisted by the Gauss sum line.
This module constructs the arithmetic Kummer line and the arithmetic Gauss line from the operations
of weil-conjectures and states the formula, with the cleanliness, rank and concentration
properties it rests on; for the trivial character it states the constant and punctual formulas.
It does not prove the statement.

Notation and normalizations are those of the module `FourierRealization`: `k` is a finite field,
`ℓ ≠ char k` a prime, `Λ = Profinite.padicAlgClRingObj ℓ`, `ψ : k → ℚ̄_ℓ` an additive character, and
`ambientArithmeticFourier` and `boundedConstructibleArithmeticFourier` are the ambient and the
bounded constructible arithmetic transforms on `A = 𝔸¹_k`. The statement quantifies over every
nontrivial `ψ` and specializes to `Langlands.Henniart.Laumon.fourierCharacter k ℓ` by
`fourierCharacter_ne_one k ℓ` in `Traits`. The arithmetic structure of a complex on `Spec k` is the
action of `Gal(k̄/k)`. The geometric Frobenius acts on `E(1)` by `q⁻¹` and on `E(−1)` by `q` for
`q = #k`, with the convention of §1 of `notes/henniart/laumon-local-fourier-weil-conjectures-design.md`
and weil-conjectures' `WeilSheaf.cyclotomicUnit_eq`. The Tate twist
`boundedConstructibleTateTwist ℓ X (-1) n` of clause 6 is Laumon's `(−1)`, shifted by `n`.

## The punctured line

- `lineCoordinate k` is the coordinate `x` of `affineLine k`; `puncturedLineInclusion k` is the
  inclusion `j : 𝔾_m ↪ A` of the basic open `D(x)`, an open immersion; `fourierPuncturedLine k` is
  `𝔾_m` over `k` and `fourierPuncturedInclusion k` the inclusion as a morphism over `k`.
- `puncturedCoordinate k` is the unit `x` on `𝔾_m`; `puncturedLineCompactification k` is the
  compactification `𝔾_m ⊂ A ⊂ D` of `𝔾_m → Spec k` (`affineTraceLineCompactification (Spec k)`
  precomposed with `j`).
- `fourierOrigin k` is the origin `0 : Spec k → A`, weil-conjectures' `affineLine.zero`, a closed
  immersion and hence proper.

## The Kummer line

Laumon, Remarque (1.1.3.7): for `N` prime to `p` with `μ_N ⊂ k`, the Kummer covering
`[N] : 𝔾_m → 𝔾_m` is a `μ_N(k)`-torsor, and a character `χ` of `μ_N(k)` gives the rank one lisse
sheaf `K_χ` (the torsor pushed out by `χ⁻¹`). Here `k` contains a primitive `n`-th root of unity
`ζ₀` (`IsPrimitiveRoot ζ₀ n`, `n ≠ 0`; then `p ∤ n` and `n ∣ q − 1`), and `χ : AddChar (ZMod n) E`
is a character of `μ_n(k) = ⟨ζ₀⟩`, `m ↦ ζ₀ᵐ`. A character of `lim μ_N(k)` with values in a finite
extension of `ℚ_ℓ` factors through some `μ_N`, and after a finite extension of `k` the needed roots
of unity are present, so this covers Laumon's characters.

- `puncturedRootOfUnity k ζ₀` is `ζ₀` as a function on `𝔾_m`, with `n`-th power `1`
  (`puncturedRootOfUnity_pow`).
- `kummerCovering k n` is weil-conjectures' `Scheme.kummerCover` of the coordinate, the scheme of
  `n`-th roots `t` of `x`, with projection `Scheme.kummerCoverπ` (`t ↦ tⁿ`). The covering,
  pushforward, deck action, projector, Kummer line and Gauss line take `[NeZero n]`, so the
  order `n` is positive. For `n` prime to `p` and a primitive `n`-th root `ζ₀` in `k`, this is a
  `μ_n(k)`-torsor over `𝔾_m` (weil-conjectures' `Scheme.EtaleTorsor.kummer`) with deck
  transformations `Scheme.kummerVadd`, `t ↦ ζ₀ᵐ t`.
- `kummerPushforward k ℓ n` is the pushforward of the regular coefficient module along the Kummer
  covering, and `kummerDeckAction k ℓ n hζ₀ m` the action of `t ↦ ζ₀ᵐ t` on it by pullback of
  sections, built exactly as weil-conjectures' `condensedArtinSchreierTranslationAction` (adjunction
  unit, identification of the pulled back regular module, composition of pushforwards).
- `kummerProjector k ℓ n hζ₀ χ` is `e_χ = n⁻¹ ∑_{m ∈ ℤ/n} χ(m)⁻¹ σ_m`, the analogue of the
  Artin–Schreier projector `q⁻¹ ∑_c ψ(−c) σ_c` of `condensedArtinSchreierProjector`, the scalars
  acting through `Profinite.PadicAlgCl.constRingHom`.
- **`kummerLine k ℓ n hζ₀ χ`** is the image of `e_χ`: the sections on which `σ_m` acts by `χ(m)`.
  It is a module over the coefficient ring on `𝔾_m`; that it is bounded constructible (in fact lisse
  of rank one) is not proved in weil-conjectures, so the definition is the module and its bounded
  constructibility is a clause of the statement below.
- `puncturedArtinSchreierLine k ℓ ψ` is `Lψ(x)|_{𝔾_m}`, `condensedArtinSchreierSheafOf` of the
  coordinate.
- **`gaussLine k ℓ n hζ₀ χ ψ`** is the arithmetic complex `RΓ_c(𝔾_m ⊗ k̄, K_χ ⊗ Lψ)[1]` on `Spec k`:
  the ambient compact support pushforward `rightDerivedLowerShriekOfCompactification` for
  `puncturedLineCompactification k` of the derived tensor product of `K_χ` and `Lψ` in degree `0`,
  shifted by one. Its degree `0` cohomology is Laumon's `G(χ, ψ) = H_c¹(U ⊗ k̄, K_χ(x) ⊗ Lψ(x))`
  with its continuous action of `Gal(k̄/k)` ((1.4.3.2)); the action of the geometric Frobenius is
  the arithmetic structure of the complex on `Spec k`.

Laumon pushes the torsor out by `χ⁻¹`; the projector here selects the sections on which the deck
transformations act through `χ`, the convention of weil-conjectures' Artin–Schreier sheaves. The
formula below holds in either convention, because the Gauss line is defined by the cohomology of
`K_χ ⊗ Lψ` and the inversion `t ↦ t⁻¹` of `𝔾_m` carries `K_χ` to `K_{χ⁻¹}` in both.

## The statement

**`KummerGaussFourierStatement`** uses Laumon, Remarque (1.1.3.7), p. 140, Lemme (1.4.3.1) and
Proposition (1.4.3.2)(i) and (iii), pp. 149–150, and SGA 4½, *Sommes trig.* (4.3) and (4.20).
The statement takes `n > 0`, a finite field `k` containing a primitive `n`-th root of unity `ζ₀`,
a prime `ℓ ≠ char k`, a character `χ` of `ℤ/n` and a nontrivial `ψ`.

- if `χ ≠ 1`:
  1. `K_χ` and `K_{χ⁻¹}`, placed in degree `0`, are bounded constructible complexes on `𝔾_m`;
  2. (cleanliness, Lemme (1.4.3.1)) `Rj_* K_χ ≅ j_! K_χ` on `A`, with `Rj_*` the ambient derived
     pushforward and `j_!` the ambient compact support pushforward for the factorization of `j`
     with identity proper part. Since the cone of `j_! → Rj_*` is supported at the origin, an
     isomorphism exists exactly when the canonical map is an isomorphism;
  3. (Proposition (1.4.3.2)(i)) the pullback of the Gauss line to `Spec k̄` along
     `Spec k̄ → Spec k` is isomorphic to the regular coefficient module in degree `0`: the
     compactly supported cohomology `H_c^i(𝔾_m ⊗ k̄, K_χ ⊗ Lψ)` vanishes for `i ≠ 1` and
     `H_c¹` is free of rank one;
  4. (Proposition (1.4.3.2)(iii)) `FTψ(j_! K_χ[1]) ≅ j'_! K_{χ⁻¹}[1] ⊗ G(χ, ψ)`, with `G(χ, ψ)`
     the Gauss line pulled back to `A'` along `A' → Spec k` (a geometrically constant line), the
     tensor product that of the ambient derived category, and the ambient transform of
     `FourierRealization`;
- for the trivial character (Laumon (1.2.3.1), p. 144, and (1.2.2.2), p. 142, for `E = A`):
  5. `FTψ(δ₀) ≅ E_{A'}[1]`, with `δ₀` the pushforward of the unit of `Spec k` along the origin;
  6. `FTψ(E_A) ≅ δ_{0'}(−1)[−1]`, the pushforward along the origin of `E(−1)[−1]`
     (`boundedConstructibleTateTwist ℓ (Spec k) (-1) (-1)`).

Clauses 5 and 6 are stated on bounded constructible complexes with
`boundedConstructibleArithmeticFourier`; they are the arithmetic forms of weil-conjectures' proved
Weil formulas `nonempty_iso_fourierTransform_obj_delta` and
`nonempty_iso_fourierTransform_obj_adicConstant`. For the trivial character
the localization triangle `j_! E_{𝔾_m} → E_A → δ₀ → j_! E_{𝔾_m}[1]` identifies
`j_! E_{𝔾_m}[1]` with the cone of the restriction `E_A → δ₀`. Its transform is the cone of the
transformed restriction map between the objects in clauses 5 and 6. Clauses 2 and 4 use
the ambient operations on `K_χ`, and clause 1 supplies the property for bundling `K_χ` as a
bounded constructible complex.

Laumon's proof of (iii): by (1.4.2.1)(ii) both sides are middle extensions, so it suffices to compare
them on `U'`; the homothety action `m(u, x) = ux` of `𝔾_m` on `A` and (1.2.3.4) reduce this to the
fibre at `x' = 1`, which is `G(χ, ψ)`, with `K_{χ⁻¹}(x') = K_χ(x'⁻¹)` from (1.1.3.7).

## External declarations and their axioms

All declarations of weil-conjectures (commit `a25955cde4f85f67bef3149a6efc3efe20c22132`) and of
Mathlib used here were checked with `#print axioms` in the pinned environment and depend only on
`propext`, `Classical.choice` and `Quot.sound`: `AlgebraicGeometry.affineLine`,
`AffineSpace.coord` (Mathlib), `affineTraceLineCompactification`, `Compactification.precomp`,
`Compactification.ofIsOpenImmersion`, `affineLine.zero`, `Scheme.kummerCover`,
`Scheme.kummerCoverπ`, `Scheme.kummerVadd`, `Scheme.kummerVadd_comp_π`, `Scheme.EtaleTorsor.kummer`
(cited), `CategoryTheory.Mod.regular`,
`CategoryTheory.Mod.regularEndRingHom`, `ProEtale.upperStarFromPoint`, `ProEtale.condensedRingObj`,
`CondensedRing.upperStar`, `CondensedRing.lowerStar`, `CondensedRing.upperStarLowerStarAdjunction`,
`CondensedRing.lowerStarComp`, `CondensedRing.rightDerivedLowerShriekOfCompactification`,
`CondensedRing.boundedConstructibleLowerStarOfIsProper`,
`CondensedRing.boundedConstructibleTateTwist`, `ProEtale.condensedArtinSchreierSheafOf`,
`ProEtale.boundedConstructible`, `Profinite.padicAlgClRingObj` and
`Profinite.PadicAlgCl.constRingHom`, together with `AlgebraicGeometry.affineLine.zero_over`,
`CategoryTheory.MonObj.Γ.mapFunctorMonoidHom` (the scalars of the projector),
`CategoryTheory.Functor.leftDerivedFunctor` and `CategoryTheory.Functor.rightDerivedFunctor`, besides
those of `FourierRealization`, whose declarations are listed there. The results cited in the
explanations, `ProEtale.condensedArtinSchreierTranslationAction`,
`ProEtale.condensedArtinSchreierProjector`, `nonempty_iso_fourierTransform_obj_delta`,
`nonempty_iso_fourierTransform_obj_adicConstant` and `WeilSheaf.cyclotomicUnit_eq`, have the same
three axioms. The declarations of this module have the same three axioms. As in
`FourierRealization`, the global instances `CategoryTheory.sfbRegularAbMonoidal` and
`WeilConjectures.CompletedCoefficientPushforward.hasDerived` are removed in this file.
