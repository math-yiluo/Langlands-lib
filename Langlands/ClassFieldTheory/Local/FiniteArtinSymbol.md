# Finite Artin maps from cyclic symbols

Author: Worker 4966.

This helper module constructs, for every finite abelian extension `D` of a p-adic
field `F` (with `D` in the same universe as `F.Carrier`), a homomorphism

```lean
FiniteArtinSymbol.artinSymbol F D : F.Carrierˣ →* Gal(D/F.Carrier)
```

and proves that it is surjective, that its kernel is exactly the actual norm
subgroup `normSubgroup F.Carrier D`, that it is compatible with restriction in
towers, and that it sends an element of order one to the arithmetic Frobenius of an
unramified extension. All declarations are in the namespace
`Langlands.ClassFieldTheory.Local.FiniteArtinSymbol`. The module adds no hypotheses
and no axioms; the only inputs are published Library theorems and Mathlib.

## Provenance

This is a derived, internal construction. It follows the characterization of the
reciprocity map in Jean-Pierre Serre, *Local Fields* (English translation, 1979,
registered as `serre-1979-local-fields`), Chapter XI, §3, Proposition 2
(printed pp. 169–170, PDF pp. 175–176). For a character `χ` of the Galois group,
that proposition gives `χ((a, F/E)) = inv_E(ā ∪ δχ)`. Here `χ` takes values
in `ℤ/n` instead of `ℚ/ℤ`, and the class `ā ∪ δχ` is the Library's explicit carry
class `cyclicClass F.Carrier D χ a` (module
`Langlands.ClassFieldTheory.Local.CyclicClass`, algebra in `CyclicClassAlgebra`). The
invariant is the relative invariant of the published local invariant family. In
Serre's notation, the symbol `artinSymbol F D a` built here is the arithmetic
`(a, D/F)`. The proofs of surjectivity and of the kernel equality do not follow
Serre's cohomological route; they are described below.

## Duality

For a finite commutative group `G` whose order divides `n ≠ 0`, the characters
`G →* Multiplicative (ZMod n)` behave like a full dual group, because
`Multiplicative (ZMod n)` has enough roots of unity (`hasEnoughRootsOfUnity`,
`hasEnoughRootsOfUnity_exponent`). The module records the needed consequences of
Mathlib's finite abelian duality (`CommGroup.monoidHomMonoidHomEquiv`,
`CommGroup.forall_apply_eq_apply_iff`, `CommGroup.forall_monoidHom_apply_eq_one_iff`):

- `eq_of_forall_character`: two elements with equal values under all such characters
  are equal.
- `mem_of_forall_character`: an element killed by every character that kills a
  subgroup `H` lies in `H`.
- `dualEquiv` and `apply_dualEquiv`: every homomorphism `s` from the character group
  to `Multiplicative (ZMod n)` is evaluation at a unique element `dualEquiv hG s`, so
  that `χ (dualEquiv hG s) = s χ`.

`scaleHom k hn : ZMod e →+ ZMod n` is multiplication by `k` when `n = e * k`.
`scaleHom_val` computes its standard representative. `denominatorEquiv_scaleHom`
shows that it is compatible with the published identifications
`denominatorEquiv : ZMod d ≃+ (1/d)ℤ/ℤ`.

## The symbol

Fix a finite Galois extension `D/F.Carrier` of degree `n`; `finrank_neZero` is a
scoped instance recording `n ≠ 0`. `relInv F D` is the relative invariant
`(localInvariantFamily unramifiedH2Exhaustion p).relative F D` from
`relativeCohomology F.Carrier D 2` to `ℚ/ℤ`. It is injective (`relInv_injective`,
from `localInvariantFamilyRelativeImages`).

For a character `ψ : Gal(D/F.Carrier) →* Multiplicative (ZMod e)` with `e ≠ 0`, the
class `cyclicClass F.Carrier D ψ a` is killed by `e`, since `ψ ^ e = 1`. So its
invariant lies in `(1/e)ℤ/ℤ` (`relInv_cyclicClass_mem`). `symbolValue ψ a : ZMod e`
is the residue corresponding to this invariant under `denominatorEquiv`
(`symbolValue_eq_iff`, `denominatorEquiv_symbolValue`). By the published additivity of
carry classes, it is additive in the character (`symbolValue_mul_character`,
`symbolValue_one_character`) and in the unit (`symbolValue_mul`).

For `e = n`, `symbolHom F D a` packages `ψ ↦ symbolValue ψ a` as a homomorphism on
the character group. When `Gal(D/F.Carrier)` is commutative, its order divides `n`
(`card_galois_dvd`), and duality gives the element

```lean
artinSymbolFun F D a = dualEquiv (card_galois_dvd F D) (symbolHom F D a)
```

with `ψ (artinSymbolFun F D a) = ofAdd (symbolValue ψ a)` for every `ψ`.
`artinSymbol F D` is this function. It is multiplicative because both sides of
`a * b` have the same character values (`eq_of_forall_character`). Its defining
property is `character_artinSymbol`.

- `character_artinSymbol_of_dvd` extends the defining property to characters into
  `ℤ/e` for every divisor `e` of `n`. Compose with `scaleHom`. Then use the published
  `cyclicClass_eq_of_val_eq`: proportional representatives have the same carry
  class. `denominatorEquiv_character_artinSymbol` states the result as an equality of
  invariants.
- `artinSymbol_eq_of_arithmeticCoordinate`: let
  `χ : Gal(D/F.Carrier) ≃* Multiplicative (ZMod n)` be an arithmetic unramified
  coordinate (`IsArithmeticUnramifiedCoordinate`), and let `a` have canonical order
  one. Then `artinSymbol F D a = χ.symm (ofAdd 1)`, the arithmetic Frobenius. The
  published `localInvariantFamilyArithmetic` gives the invariant `1/n` of the carry
  class of `(χ, a)`, so `χ (artinSymbol F D a) = ofAdd 1`.

## Restriction in towers

Let `F ⊆ E ⊆ D` be a tower of finite Galois extensions. `relInv_relativeInflation`
(from `localInvariantFamilyInflation`) shows that relative invariants commute with
inflation. It follows that inflation is injective (`relativeInflation_injective`).

`restrictNormalHom_artinSymbol`: if both Galois groups are commutative, then
`AlgEquiv.restrictNormalHom E (artinSymbol F D a) = artinSymbol F E a`. For a
character `χ` of `Gal(E/F)` into `ℤ/[E : F]`, the composite with restriction is a
character of `Gal(D/F)` into `ℤ/[E : F]`, a divisor of `[D : F]`. The published
`relativeInflation_cyclicClass` identifies its carry class with the inflation of the
carry class of `χ`. Hence both elements have the same `χ`-values, by
`denominatorEquiv_character_artinSymbol` at both levels.

## Kernel

For a character `χ` into `ℤ/e`, `kernelFieldCharacter χ` is the injective character
of `Gal(fixedField χ.ker / F)` through which `χ` factors
(`kernelFieldCharacter_comp`, `kernelFieldCharacter_injective`; the factorization
uses `IsGalois.normalAutEquivQuotient`).
`cyclicClass_eq_zero_iff_mem_normSubgroup` then gives the following. The carry class of `(χ, a)`
vanishes exactly when `a` is a norm from `fixedField χ.ker`. The proof inflates from
the fixed field (injective by the previous section) and applies the published
`cyclicClass_eq_zero_iff_of_injective`.

`character_artinSymbol_eq_one_iff` translates `χ (artinSymbol F D a) = 1` into the
vanishing of this carry class, using injectivity of `relInv`.
`normSubgroup_le_ker_artinSymbol` follows. A norm from `D` is a norm from every
intermediate field (`normSubgroup_le_of_tower`), so every character kills its symbol.

## Surjectivity and the exact kernel

For an abelian extension (`IsAbelianGalois F.Carrier D`):

- `artinSymbol_surjective`: by `mem_of_forall_character`, it suffices to show that a
  character `χ` trivial on the image is trivial. Its carry classes all vanish, so
  every unit is a norm from `fixedField χ.ker`. The published norm index theorem
  `normSubgroup_index_eq_finrank` then forces that field to have degree one, so
  `χ.ker` is the whole group.
- `ker_artinSymbol`: `(artinSymbol F D).ker = normSubgroup F.Carrier D`. By
  surjectivity the kernel has index `[D : F]`, and the norm subgroup has the same
  index by `normSubgroup_index_eq_finrank`. The norm subgroup is contained in the
  kernel, so the relative index is one and the two subgroups are equal.
