# The order bound for second idele-class cohomology

Author: Worker 229. The module imports, without modification, the published
statement pair `Langlands.ClassField.Global.IdeleClassH2OrderStatement`, the
published statement `FundamentalClass.IdeleClassH1Vanishing`, the published
proof module `Langlands.ClassField.Global.H1VanishingProof` (theorem
`ideleClassH1Vanishing : FundamentalClass.IdeleClassH1Vanishing.{u}`), the published
proof module `Langlands.ClassField.Global.IdeleClassGaloisDescentProof` (theorem
`ideleClassGaloisDescent : IdeleClassGaloisDescent.{u, v}`, by Worker 327), the
published proof module `Langlands.ClassField.Global.CyclicIdeleClassHerbrandAssembly`
(theorem `cyclicIdeleClassHerbrandQuotient : CyclicIdeleClassHerbrandQuotient.{u, v}`,
by Worker 343), the published idele-class inclusion maps of
`Langlands.ClassField.Global.CohomologyMaps`, and the generic helper module
`Langlands.Cohomology.H2OrderReduction` by the same author.

## Main theorem

`ideleClassH2OrderBound : IdeleClassH2OrderBound.{u, v}` is unconditional; its
type is exactly the published statement. It applies the auxiliary theorem
`IdeleClassH2Order.ideleClassH2OrderBound_of`, which proves
`IdeleClassH2OrderBound.{u, v}` from the proposition
`FundamentalClass.IdeleClassH1Vanishing.{v}` (`H¹(Gal(E/F), C_E) = 0`), to the
published proof `ideleClassH1Vanishing.{v}`. The cyclic Herbrand quotient and
Galois descent for idele classes enter `h2PrimeLayerBound` directly as the
published theorems `cyclicIdeleClassHerbrandQuotient.{v, v}` and
`ideleClassGaloisDescent.{v, v}`. No axioms beyond Lean's standard `propext`,
`Classical.choice` and `Quot.sound` are used.

Every field that occurs is `E` or an intermediate field of `E/F`, so all
inputs are needed only at the universe `v` of `E`, while `F` stays in its
independent universe `u`. The coefficients are throughout the published
`relativeIdeleClassRepresentation`, the additive wrapper of the actual idele
class group `NumberField.IdeleClassGroup (𝓞 E) E` with the published action
`relativeIdeleClassAut`.

## Proof

Fix a Galois extension `E/F` of number fields and write `G = Gal(E/F)` and
`A = relativeIdeleClassRepresentation F E`. Since `#G = [E : F]`
(`IsGalois.card_aut_eq_finrank`), it suffices to verify the two hypotheses of
`Langlands.Cohomology.finite_card_dvd_of_primeLayers` for `A`.

`fixedFieldAutEquiv H` is the group isomorphism `Gal(E/K') ≃* H` for a subgroup
`H ≤ G` with fixed field `K'`. It is Mathlib's `fixingSubgroupEquiv`, followed
by the Galois correspondence `fixingSubgroup_fixedField`. On elements it is
restriction of scalars from `K'` to `F` (`fixedFieldAutEquiv_apply`, by `rfl`).
The published action `relativeIdeleClassAut` is defined through the underlying
ring automorphism. So restricting `A` along this isomorphism gives exactly the
representation `relativeIdeleClassRepresentation K' E`, with the identity on
coefficients.

**Degree-one vanishing on subgroups** (`h1VanishesOnSubgroups`). For `H ≤ G`
with fixed field `K'`, `groupCohomology.mapIso` along `fixedFieldAutEquiv H` and
the identity identifies `H¹(H, A)` with `H¹(Gal(E/K'), C_E)`. That group is a
subsingleton by `IdeleClassH1Vanishing` for `E/K'`.

**Prime-index layers** (`h2PrimeLayerBound`). Let `N ⊴ H ≤ G` with `[H : N]`
prime. Let `K'` be the fixed field of `H`, `N'` the preimage of `N` in
`Gal(E/K')`, and `M` the fixed field of `N'`, an intermediate field of `E/K'`.
Then `M/K'` is Galois, `Gal(E/M) = N'` and
`φ : Gal(M/K') ≃* H ⧸ N` is Mathlib's `IsGalois.normalAutEquivQuotient`
followed by `QuotientGroup.congr`. On a restriction `σ|_M`, `φ` gives the
class of the image of `σ` in `H`.

The published inclusion `ideleClassInclusionLinear K' M E : C_M → C_E` is
equivariant along restriction `Gal(E/K') → Gal(M/K')`
(`ideleClassInflationCoefficients`). Hence its image lies in the
`N`-invariants: an element of `N` comes from some `σ ∈ N'`, which restricts to
the identity on `M`. The first conjunct of the published Galois descent
`ideleClassGaloisDescent` for `E/M` makes the
corestricted map injective. For surjectivity, let `y` be an `N`-invariant
class. It is fixed by every `σ ∈ Gal(E/M)`, because `σ` restricted to `K'` lies
in `N'`. So the second conjunct of descent for `E/M` gives a preimage in `C_M`.
The resulting linear equivalence intertwines the action of `Gal(M/K')` on
`C_M` with the action of `H ⧸ N` on the invariants via `φ`. This is checked
on restrictions `σ|_M`, which exhaust `Gal(M/K')`
(`AlgEquiv.restrictNormalHom_surjective`). `groupCohomology.mapIso` then
identifies `H²(H ⧸ N, A^N)` with `relativeIdeleClassCohomology K' M 2`.

Now `#Gal(M/K') = [H : N]` is prime, so `Gal(M/K')` is cyclic
(`isCyclic_of_prime_card`). The cyclic Herbrand quotient for `M/K'`
(`cyclicIdeleClassHerbrandQuotient`) makes
`relativeIdeleClassCohomology K' M 2` finite with order
`[M : K'] · #H¹(Gal(M/K'), C_M)`. That `H¹` is a subsingleton by
`IdeleClassH1Vanishing` for `M/K'`, so the order is `[M : K'] = #Gal(M/K') = [H : N]`.
In particular it divides `[H : N]`.

**Assembly** (`ideleClassH2OrderBound_of`). The two facts above feed
`finite_card_dvd_of_primeLayers`. It gives finiteness of
`relativeIdeleClassCohomology F E 2` and divisibility of its order by
`#G = Module.finrank F E`.
Finally `ideleClassH2OrderBound` supplies degree-one vanishing to
`ideleClassH2OrderBound_of` by the published `ideleClassH1Vanishing.{v}`.

The file sets `backward.isDefEq.respectTransparency false` for
`h2PrimeLayerBound` only, as other published Library files do. Without it,
the `AddCommMonoid` structure of the invariant submodule is not found while
the linear equivalence is elaborated.

## Source correspondence

Source: Emil Artin and John Tate, *Class Field Theory*, AMS Chelsea Publishing,
2009, registered as `artin-tate-2009-class-field-theory`, SHA256
`af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`. Chapter XIV
§3, printed p.152 (PDF p.161), applies Lemma 1 of §2 (printed pp.147–148, PDF
pp.156–157) with `r = 2`, `ν = 1`. In the idele-class formation, `H¹` vanishes
on every layer, so degree-two inflation–restriction is exact, and the
prime-degree bound gives `order of H²(K/F) ∣ [K : F]` in every normal layer.
The source obtains the prime-degree bound from its Axiom I″, using the first
inequality and Kummer theory. Here the prime-degree layer instead uses the
cyclic Herbrand quotient together with degree-one vanishing, which gives
equality `#H² = [M : K']`. Galois descent identifies the subgroup and quotient
layers of `Gal(E/F)` acting on `C_E` with the idele-class layers of
intermediate fields. Artin–Tate, Preliminaries §1, printed pp.1–2 (PDF
pp.10–11), states this identification of base idele classes with Galois-fixed
classes.
