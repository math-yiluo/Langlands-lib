# Original subfield automorphisms and cyclicity

This pair constructs reduction of original field automorphisms on the actual
residue quotient and proves existence of an original cyclic Galois full-residue
subfield. It is internal work derived from the imported actual norm, residue,
Hensel, and full-residue polynomial constructions and Mathlib's spectral norm,
simple-root uniqueness, power bases, and finite-field Galois results.

## Objects and assumptions

Let `K : Type u` be a nonarchimedean local field with the supplied valuative
relation and topology, and let `D : Type u` be a finite-dimensional central
division algebra over `K`. Its actual valuation is
`v = localReducedNormValuation K D`. Write `R = DivisionValuation.Residue v` for
the actual quotient of `v.integer` by its strict-value ideal. The field structure
on `R` is `localDivisionResidueField K D`; its algebra structure over the original
base residue field `𝓀[K]` is `localDivisionResidueAlgebra K D`.

For an original finite field extension `L : Type uL` with an injective algebra
homomorphism `ι : L →ₐ[K] D`, write `w = localDivisionSubfieldValuation K D ι`,
`ρ = DivisionValuation.reduction w`, and
`τ = localDivisionSubfieldResidueMap K D ι`. Thus `w` is the actual restricted
valuation, and `τ` is the residue inclusion induced by the original embedding.
The universe `uL` is independent. There is no characteristic restriction.

## Original norm and integer-ring automorphisms

`localDivisionSubfield_norm_aut` proves that every `σ : L ≃ₐ[K] L` preserves the
norm pulled back from the normalized determinant absolute value of `D`. The
original finite-dimensional normed algebra is over the complete normed field
`K`, so its norm equals the spectral norm. Spectral norm invariance under the
original algebra equivalence gives the result. This helper does not require
centrality of `D`.

`localDivisionSubfieldValuation_aut` uses the previously proved exact equivalence
between norm order and restricted valuation order to conclude
`w (σ x) = w x` for every original `x : L`.

`localDivisionSubfieldIntegerAut` restricts `σ` and `σ.symm` to `w.integer`.
Valuation preservation supplies their membership proofs, and the ring laws and
inverse laws follow from those of the original automorphism.

`localDivisionSubfieldResidueAutHom` descends that restriction through the actual
strict-ideal quotient, using preservation of values less than one.
`localDivisionSubfieldResidueAut` uses the descended action of `σ.symm` as its
inverse. Surjectivity of original reduction proves both inverse laws. The exact
identity is

```
localDivisionSubfieldResidueAut ... σ (ρ x) =
  ρ (localDivisionSubfieldIntegerAut ... σ x).
```

## Action on the actual full residue

Assume `hsurj : Function.Surjective τ`.
`localDivisionSubfieldFullResidueRingAut` conjugates the preceding quotient action
by the actual isomorphism `RingEquiv.ofBijective τ ⟨τ.injective, hsurj⟩`.
It therefore acts on the original division-algebra residue `R` and satisfies

```
localDivisionSubfieldFullResidueRingAut ... hsurj σ (τ (ρ x)) =
  τ (ρ (localDivisionSubfieldIntegerAut ... σ x)).
```

`localDivisionSubfieldFullResidueAut` gives this action its structure of an algebra
automorphism over the original `𝓀[K]`. Every base residue class has a representative
in `𝒪[K]`. The compatibility theorem
`localDivisionSubfieldBaseIntegerMap_reduction` identifies its scalar image with
`τ (ρ (...))`, and `σ.commutes` fixes that original integral scalar. This proves
scalar compatibility without choosing an unrelated algebra structure.

`localDivisionSubfieldGaloisReduction` packages these automorphisms as a group
homomorphism

```
(L ≃ₐ[K] L) →* (R ≃ₐ[𝓀[K]] R).
```

The identity and multiplication laws are checked on `τ (ρ x)`, which exhausts
`R` by the two actual surjectivities.

## Faithfulness from a simple integral generator

`localDivisionSubfield_simpleRoot_unique` takes two elements of `w.integer`
which are roots of the same polynomial over `𝒪[K]`, have equal image under
`τ ∘ ρ`, and at whose first residue the reduced derivative is nonzero. It proves
the original integral elements equal. Injectivity of `τ` makes their difference
reduce to zero, hence makes it a nonunit of the actual integer ring. The nonzero
reduced derivative makes the original derivative evaluation a unit. Mathlib's
`IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub` then gives equality. This
helper does not require finite dimensionality of `L`.

`localDivisionSubfieldIntegerAut_eval₂` states that evaluation of a polynomial
over original integral base scalars commutes with the integer automorphism.
Its coefficient identity is exactly the original algebra automorphism's scalar
compatibility.

`localDivisionSubfieldGaloisReduction_injective` assumes a power basis of `L/K`
whose generator is represented by `a : w.integer`, a polynomial `f` over
`𝒪[K]` vanishing at `a`, and separability of its base residue reduction. If two
original automorphisms have the same residue action, their images of `a` have
the same actual residue. Both are original integral roots of `f`. Reduction of
their root equation and separability make the reduced derivative nonzero.
The preceding uniqueness theorem makes the images equal. Power-basis
`algHom_ext` then makes the original automorphisms equal.

`localDivisionSubfield_isCyclic` applies `isCyclic_of_injective` to this group
homomorphism and its proved injectivity. The target is the Galois automorphism
group of the actual finite residue extension and is cyclic by Mathlib's
finite-field result. The generic criterion neither assumes nor proves that
`L/K` is Galois; Galoisness is supplied internally in the following existence
result.

## Unconditional original cyclic subfield

`exists_localDivision_fullResidue_cyclic_subfield` produces
`b : v.integer` such that, with `E = residueGeneratorSubalgebra K D (b : D)`
and its original field structure `residueGeneratorField`, all of the following
hold:

- The original element `(b : D)` is separable over `K`.
- The actual restricted-valuation residue inclusion from `E` onto `R` is
  surjective.
- `Module.finrank K E = Module.finrank 𝓀[K] R`.
- `IsGalois K E`.
- `IsCyclic (E ≃ₐ[K] E)`.

The proof retains the original polynomial and generator provided by
`exists_localDivision_fullResidue_polynomial_subfield`. The polynomial is monic,
its reduction is the minimal polynomial of the actual residue of `b`, and its
image over `K` is the original minimal polynomial of `(b : D)`. The finite base
residue field is perfect, so the residue polynomial is separable. It splits in
`R` by finite-field Galoisness. The imported original-root lifting and splitting
theorem makes the original minimal polynomial split in `E`. The singleton-adjoin
splitting-field helper and original element separability give `IsGalois K E`.

The original integral generator of `E` is a root of the original scalar
polynomial: its evaluation maps to the zero minimal-polynomial evaluation in
`D`, and the original inclusion is injective. It is exactly the generator of
`residueGeneratorPowerBasis`. Thus the new faithful reduction criterion supplies
cyclicity for this same `E`, while preserving the residue surjectivity and degree
equality from the original joint witness.

Only the finite base residue field is used as a perfect field. The original
local field may have positive characteristic. This pair does not compare
`[E : K]` with the reduced degree of `D`, prove ramification identities, move
arbitrary units into `E` modulo commutators, prove local SK1, or prove the full
local Kneser–Tits proposition.
