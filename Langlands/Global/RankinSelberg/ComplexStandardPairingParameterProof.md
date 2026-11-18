# The local pairing premise at a complex place

Module `Langlands.Global.RankinSelberg.ComplexStandardPairingParameterProof`. The main theorem
is in namespace `Langlands.Global.RankinSelbergGlobal` and the helpers are in
`Langlands.Global.RankinSelbergGlobal.ComplexStandardPairing`. Worker 5665 wrote it for Task 7399
(prove `ComplexPlaceFunctionalEquationStatement`, Jacquet 2009, Theorem 2.1, at a complex
place). Provenance: internal.

Main theorem:
`Langlands.Global.RankinSelbergGlobal.complexStandardPairingParameter :
ComplexStandardPairingParameterStatement`.

## What is proved

`ComplexStandardPairingParameterStatement` (the local pairing premise L) is stated in
`Langlands.Global.RankinSelberg.ComplexPlaceContragredientPremises`. Let `d` and `dd` be lists
of `n` complex characters. Suppose the `U(n)`-finite complex standard modules `X(d)` and
`X(dd)` are both irreducible in the sense of `IsComplexStandardIrreducible`. Suppose also that
`P : X(d) × X(dd) → ℂ` is a nonzero bilinear form with `IsComplexStandardInvariantPairing n d
dd P`, that is, invariant under right translation by `U(n)` and under the right derivatives
along `𝔤𝔩_n(ℂ)`. Then `dd` is a permutation of `d.map ComplexCharacterData.inv`.

The theorem has no premise. The proof uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Idea

The form `P` turns `X(dd)` into a nonzero intertwining map `φ : X(dd) → X(d)^∨` into the
`U(n)`-finite dual of `X(d)`. Since `X(d)` is irreducible and admissible, `X(d)^∨` is an
irreducible admissible `(𝔤𝔩_n(ℂ), U(n))`-module. The Library's duality `dualEquiv n d`
identifies `X(d)^∨` with the standard module of the inverse characters
`d⁻¹ = d.map complexCharacterDataInv`. So both `X(dd)` and `X(d⁻¹)` map nonzero into the same
irreducible admissible module.

Sort `dd` and `d⁻¹` into the Langlands order. By permutation invariance the sorted standard
modules are isomorphic to the unsorted ones. The uniqueness half of the Langlands
classification (`complexLanglandsQuotientUnique`) then shows that the sorted lists are
permutations of each other. So `dd` is a permutation of `d⁻¹`.

## Declarations

### Inverse characters (namespace `ComplexStandardPairing`)

- `complexCharacterData_ext`: two `ComplexCharacterData` with equal character, weight and
  exponent are equal.
- `inv_eq_complexCharacterDataInv`: `ComplexCharacterData.inv` (used in the statement) and
  `complexCharacterDataInv` (used by the Library's duality) agree. The characters agree pointwise
  by `rfl`.

### Translations and derivatives

The statement uses `complexStandardTranslate` and `complexStandardDerivative`. The Library's
`(𝔤, K)`-module results use `complexStandardRep` and `complexStandardLie`. The identity map is an
intertwining map (`isComplexStandardIntertwining_id`), which gives:

- `translate_eq_rep`: `complexStandardTranslate n ds k f` equals `complexStandardRep n ds k f`,
  where the second `k` is the unitary matrix underlying `k`;
- `rep_eq_translate`: the converse direction for a unitary matrix `k`;
- `derivative_eq_lie`: `complexStandardDerivative n ds X f = complexStandardLie n ds (1 ⊗ X) f`;
- `isIrreducibleGKModule_of_isComplexStandardIrreducible`: `IsComplexStandardIrreducible n ds`
  implies `IsIrreducibleGKModule (complexStandardRep n ds) (complexStandardLie n ds)`. A subspace
  stable under the latter actions is stable under translations and derivatives.

### The pairing (section `Pairing`)

Let `hP : IsComplexStandardInvariantPairing n d dd P`.

- `pairing_rep`: `P (k f) (k f') = P f f'` for a unitary matrix `k`, with the actions
  `complexStandardRep`.
- `pairing_lie`: `P ((1 ⊗ X) f) f' + P f ((1 ⊗ X) f') = 0`, with the actions
  `complexStandardLie`.
- `flip_rep`: `P.flip`, the map `f' ↦ P (·) f'` from `X(dd)` to the algebraic dual of `X(d)`, is
  equivariant for the dual representation `(complexStandardRep n d).dual`. Apply `pairing_rep`
  to `k⁻¹ f` and `f'`.
- `flip_lie`: `P.flip ((1 ⊗ X) f') f = -(P.flip f' ((1 ⊗ X) f))`, from `pairing_lie`.

### The main theorem

`complexStandardPairingParameter` proceeds in these steps.

1. `X(d)` and `X(dd)` are irreducible `(𝔤, K)`-modules, by
   `isIrreducibleGKModule_of_isComplexStandardIrreducible`. `X(d)` is a `(𝔤𝔩_n(ℂ), U(n))`-module
   (`isComplexGKModule_complexStandardModule`) and admissible
   (`ComplexStandardHomTransposeProof.isAdmissibleGKModule_principalSeriesRep`).
2. The `U(n)`-finite dual `V = kDual (complexStandardRep n d)` with `kDualRep` and
   `ComplexContragredient.dualLie` is a `(𝔤𝔩_n(ℂ), U(n))`-module
   (`ComplexContragredient.isComplexGKModule_kDual`). It is irreducible
   (`ComplexContragredient.isIrreducible_kDual`) and admissible (`KFiniteDual.admissible_kDual`).
3. `φ` is `P.flip` with values restricted to `V`. The values are `U(n)`-finite by
   `ComplexStandardHomTransposeProof.isFiniteVector_dual_of_equivariant` and `flip_rep`. `φ`
   intertwines the actions on `X(dd)` with `kDualRep` and `dualLie`, by `flip_rep` and
   `flip_lie`. It is nonzero because `P` is nonzero.
4. `ψ = ComplexTransposeStandardDuality.dualEquiv n d` is a linear isomorphism from `X(d⁻¹)` to
   `V`. It is an intertwining map, by `dualEquiv_rep`, `dualEquiv_lie` and
   `IsComplexStandardIntertwining.comp`. Since `ψ` is injective, `V` is irreducible and `X(d⁻¹)`
   is nontrivial (`complexStandardNontrivial`), `X(d⁻¹)` is irreducible
   (`isIrreducibleGKModule_of_injective`).
5. Let `es₁` and `es₂` be `dd` and `d⁻¹` sorted by `complexLanglandsLE`. They are permutations of
   the original lists (`List.mergeSort_perm`) and Langlands-ordered
   (`isComplexLanglandsOrdered_mergeSort`). `complexStandardPermutation` gives bijective
   intertwining maps `T₁ : X(es₁) → X(dd)` and `T₂ : X(es₂) → X(d⁻¹)`. It uses the irreducibility
   of `X(dd)` and of `X(d⁻¹)`.
6. `A = φ ∘ T₁` and `B = ψ ∘ T₂` are intertwining maps into `V`
   (`IsComplexStandardIntertwining.comp`). `A` is nonzero because `φ` is nonzero and `T₁` is
   surjective. `B` is nonzero because `X(es₂)` is nontrivial and `ψ ∘ T₂` is injective.
7. `complexLanglandsQuotientUnique` applied to `V`, `A` and `B` gives `es₁.Perm es₂`. Hence
   `dd ~ es₁ ~ es₂ ~ d⁻¹`. Finally, `d.map ComplexCharacterData.inv = d⁻¹` by
   `inv_eq_complexCharacterDataInv`.

## Library results used

- Representation theory of the complex standard modules: `isComplexStandardIntertwining_id`,
  `isComplexGKModule_complexStandardModule`, `complexStandardNontrivial`,
  `complexStandardPermutation`, `complexLanglandsQuotientUnique`,
  `isIrreducibleGKModule_of_injective`, `IsComplexStandardIntertwining.comp`,
  `IsComplexStandardIntertwining.map_rep`, `IsComplexStandardIntertwining.map_lie`,
  `complexLanglandsLE` and `isComplexLanglandsOrdered_mergeSort`.
- The finite contragredient: `ComplexContragredient.isComplexGKModule_kDual`,
  `ComplexContragredient.isIrreducible_kDual`, `KFiniteDual.admissible_kDual`,
  `KFiniteDual.dual_apply_apply`.
- The duality with the inverse characters: `ComplexTransposeStandardDuality.dualEquiv`,
  `dualEquiv_rep` and `dualEquiv_lie`.

## Implementation notes

- `rep_eq_translate` passes the element `⟨Unitary.toUnits k, k.2⟩` of `unitaryCompact ℂ n`
  explicitly. With a placeholder, unification times out.
- The module uses `backward.isDefEq.respectTransparency false` and
  `attribute [local instance 100] LieRing.ofAssociativeRing`, as the Library's modules on
  complex standard modules do.

## Provenance

Internal. Mathematically, this is the standard identification of the contragredient of an
irreducible principal series of `GL_n(ℂ)` with the principal series of the inverse characters,
followed by the uniqueness of Langlands parameters. The proof assembles these steps from the
Library results above and introduces no new definitions beyond the helper lemmas.
