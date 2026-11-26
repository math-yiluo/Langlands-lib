# Restriction of a compatible rank-one realization to a finite extension

Let `F'/F` be an extension of number fields, `χ` a Hecke character of `F` and
`ψ` a family of `λ`-adic characters of the absolute Galois group of `F` with
coefficients in a number field `L`, such that
`IsCompatibleLambdaAdicRealization ι χ ψ` holds. The main theorem
`isCompatibleLambdaAdicRealization_normComp` states that, for every closure
embedding `θ : F̄ → F̄'` over `F`, the composites
`(ψ λ) ∘ restrictionAlongClosure θ` form a compatible realization of the norm
pullback `HeckeCharacter.normComp χ = χ ∘ N_{F'/F}`. This is the familiar
statement that restricting the Galois character attached to `χ` to `F'`
gives the Galois character attached to `χ ∘ N_{F'/F}`. Here it is proved
from the stated Frobenius and uniformizer comparison, not from class field
theory.

## Local lemmas

- `residueCharacteristic_eq_of_liesOver` and
  `residueCardinality_eq_pow_of_liesOver`: for `w | v`, the residue
  characteristics agree and `q_w = q_v ^ f(w|v)` (Mathlib's
  `Ideal.absNorm_pow_inertiaDeg`).
- `completionMap_norm_le_one_iff` and `completionMap_isAlgebraic`: the
  completion map `F_v → F'_w` of
  `Langlands.Global.AdelicFunctoriality.FiniteExtension` preserves integrality
  and is algebraic (indeed finite).

## Commuting squares

`restriction_square_eq` treats a commuting square of field embeddings
`F → F' → C` and `F → B → C`. Restriction from the absolute group of `C` to
that of `F` through `F'`, along `θ`, and through `B`, along Mathlib's chosen
lifts, are two restrictions along closure embeddings `F̄ → C̄` over `F`. By
`closureChange_intertwines` they are conjugate in the absolute group of `F`,
so a character with values in a commutative group takes the same value on
both. `restriction_localGroup_eq` is the instance
`B = F_v`, `C = F'_w`.

## Proof of the realization

Take the exceptional set of `χ`, enlarge it by the places of `F'` above it
and by the finitely many places ramified in `F'/F`
(`eventually_ramificationIdx_eq_one`), and fix a good place `w` of `F'` above
`v`, with inertia degree `f`. Let `a ∈ L` be the common Frobenius value of the
realization of `χ` at `v`.

- Hecke side: `HeckeCharacter.normComp_isUnramifiedAt` gives unramifiedness
  of the norm pullback at `w`. For an unramified place,
  `HeckeCharacter.normComp_finiteComponent_uniformizer` gives the value
  `χ_v(ϖ_v) ^ f` at a uniformizer of `F'_w`. Hence the new Frobenius value is
  `a ^ f`.
- Galois side: by `restriction_localGroup_eq` the local character at `w` is
  the local character at `v` composed with `Gal(F̄'_w/F'_w) → Gal(F̄_v/F_v)`.
  `QuadraticFrobeniusPatching.map_mem_inertia_iff` sends inertia into
  inertia, which gives unramifiedness. By
  `QuadraticFrobeniusPatching.residueAction_map_eq_pow`, a geometric Frobenius
  lift at `w` maps to the `f`-th power of a geometric Frobenius lift at `v`
  modulo inertia. Hence its value is `a ^ f`, sent into the completion
  `L_λ`. The residue characteristic condition at `w` is the one at `v`.

## Forms for a twisted algebra structure

`isCompatibleLambdaAdicRealization_normComp_hom` restates the theorem for the
algebra structure induced by a field homomorphism `f : F → F'`, with the
restriction `restrictionAlongClosureHom` of
`Langlands.Galois.ClosureRestrictionGalois`. `ideleClassNorm_algebra_twist`
compares the idele-class norms for two algebra structures `A₁, A₂` on `F'`
with `σ ∘ A₁ = A₂` for a field automorphism `σ` of `F'`. It is a special case
of `ideleClassNorm_equiv`.
