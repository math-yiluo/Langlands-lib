# Antisymmetrization of Hecke characters on CM fields

This module supplies the final steps of
`Langlands.Global.CMUnramifiedInfinityRealizationStatement`. For any Hecke character `ψ` of a
CM number field `K : Type u`, the antisymmetrization `ψ / (ψ ∘ c)` is conjugate self-dual. If
`ψ` has an anticyclotomic infinity type, the antisymmetrization has twice that infinity type.
Unramifiedness is only preserved, not created: the antisymmetrization is unramified at every
finite place when `ψ` itself is unramified at every finite place, which holds in particular
when `ψ` is trivial on the integral ideles with trivial archimedean part (the hypothesis of
`realization_of_base`). Without such a hypothesis the conclusion fails: a character with a
ramified component at a finite place `v` and a trivial component at `c(v)` keeps the ramified
component at `v` after antisymmetrization, as in the proof of Henniart's Lemma 2 below. This
module does not construct `ψ`; the base character comes from a separate module.

## Construction and provenance

`antisymmetrize ψ` is `ψ * ψ.complexConj⁻¹`, that is `x ↦ ψ(x) / ψ(c x)`, where `c` is the
published arithmetic CM involution `AdelicFunctoriality.ideleClassComplexConj` and
`HeckeCharacter.complexConj` is the published pullback along it (`complexConj_apply` is
`rfl`). This is the device in Guy Henniart, *Une preuve simple des conjectures de Langlands
pour GL(n) sur un corps p-adique* (2000), Section 3.6, proof of Lemma 2, printed p.451
(one-based PDF p.13): "On pose alors Z = λ/(λ ∘ c)." There `λ` is a finite-order character
of the idele class group whose components at two finite places `0, 0'` are prescribed and
whose components at `c(0), c(0')` are trivial; our `ψ` plays the role of `λ`. Registered
source: `henniart-2000-simple-proof`, SHA-256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`; Worker 1233 read
that page directly. Henniart applies it to finite-order characters; here it is applied to a
character of anticyclotomic infinity type, which is a derived use. The infinity-type and
unramifiedness bookkeeping below is internal.

## Declarations

- `isUnramifiedAt_of_integral`: if `ψ` is trivial on every integral idele (in the published
  `ClassField.Global.integralIdeles K`: valuation one at every finite place) whose
  archimedean part `(x : Adeles K).1` is `1`, then `ψ` is unramified at every finite place
  `w`. Proof: a local unit `a` at `w` has valuation one
  (`adicCompletionIntegers.mem_units_iff_valued_eq_one`), so `finiteIdeleInclusion K w a` is
  integral, by `ideleCoordinate_ofAdicCompletion_self` at `w` and
  `ideleCoordinate_ofAdicCompletion_of_ne` elsewhere; its archimedean part is `1` by
  definition.
- `antisymmetrize ψ` and `antisymmetrize_apply`:
  `antisymmetrize ψ x = ψ x * (ψ (ideleClassComplexConj x))⁻¹`.
- `antisymmetrize_complexConj`: `antisymmetrize ψ (c x) = (antisymmetrize ψ x)⁻¹`, from
  the published involutivity `ideleClassComplexConj_involutive`.
- `ideleEquiv_complexConj_infiniteIdelesInclusion`: transporting an archimedean idele
  `infiniteIdelesInclusion K y` by the CM involution gives again an archimedean idele,
  namely the inclusion of its own archimedean part, because the finite-adele transport maps
  `1` to `1`.
- `toCharacter_complexConj`: for an anticyclotomic `b`, the infinity character
  `InfinityType.toCharacter b` takes the inverse value on that transported archimedean part.
  By `toCharacter_anticyclotomic` it is a product of `(z_v / z̄_v) ^ b(v)` over infinite
  places, and the published `ideleComplexConj_infinite_coordinate` replaces each coordinate
  `z_v` by `z̄_v`.
- `toCharacter_two_mul`: the weights `2 * b` give the square of the character of `b`.
- `antisymmetrize_hasPrescribedInfinityComponent`: if `b` is anticyclotomic and
  `ψ.atInfinity = toCharacter b`, then `(antisymmetrize ψ).atInfinity = toCharacter (2 * b)`:
  on `y`, the value is `toCharacter b y * (toCharacter b y)⁻¹⁻¹ = toCharacter b y ^ 2`.
- `isUnramifiedAt_complexConj`: if `ψ` is unramified at every finite place, so is
  `ψ.complexConj`, by the published `HeckeCharacter.isUnramifiedAt_comap_iff` at the place
  `(finitePlaceEquiv c).symm w`.
- `antisymmetrize_isUnramifiedAt`: then `antisymmetrize ψ` is unramified at every finite
  place, since the finite component at `w` is the product of the two components.
- `realization_of_base`: for an anticyclotomic `a`, a positive `n` and a Hecke character
  `ψ` with `ψ.HasPrescribedInfinityComponent (toCharacter (n * a))` that is trivial on the
  integral ideles with trivial archimedean part, the conclusion of
  `CMUnramifiedInfinityRealizationStatement` for `K` and `a` holds with `m = 2 * n` and
  `χ = antisymmetrize ψ`. The weights `n * a` are anticyclotomic, and
  `(2 * n : ℕ) * a σ = 2 * (n * a σ)` after casting.

All hypotheses of `realization_of_base` are explicit; no axiom or proof hole is used.
