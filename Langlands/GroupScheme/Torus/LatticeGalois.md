# Galois transport of character and cocharacter lattices

Worker 207.

This module defines the Galois action on the character and cocharacter
lattices of a commutative group scheme after base change. For a field
extension `K / k`, an automorphism `σ ∈ Aut_k(K)` acts on `X^*(T_K)` and on
`X_*(T_K)` for a commutative group scheme `T` over `Spec k`. The action is
built from actual morphisms of group schemes: base change along `Spec σ`,
followed by the canonical descent identification. It is packaged as a
`Representation ℤ (K ≃ₐ[k] K)` on each lattice.

## Sources

Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`
(printed page = PDF page − 16):

- §12.a, printed p.230 (PDF 246): characters `G → 𝔾_m` form a commutative
  group `X(G)`, written additively, and cocharacters are homomorphisms
  `𝔾_m → G`.
- §12.g, printed p.239 (PDF 255): for an algebraic group `G` over `k`,
  `X^*(G) = X(G_{k^s})` consists of the characters of `G` defined over `k^s`,
  and the Galois group `Γ = Gal(k^s/k)` acts on `X^*(G)`. Theorem 12.23
  (printed p.240, PDF 256) classifies groups of multiplicative type by
  these Galois modules.

Milne gives no formula for the action in §12.g. The standard formula is
`(σχ)(t) = σ(χ(σ⁻¹ t))`. The definitions here are **derived**: they realise
this action for an arbitrary ring extension `k → K` with `K` commutative
(`[CommRing k] [CommRing K] [Algebra k K]`), for `σ` in the group
`K ≃ₐ[k] K` of `k`-algebra automorphisms, and for any commutative group scheme
`T` over `Spec k`. Milne's setting is the special case `K = k^s`, with `T` an
algebraic group of multiplicative type. Continuity of the action is not
formalized.

## Changing the structure of a test scheme

The module works over a base `B`, with `b : S ⟶ B`, an endomorphism
`a : S ⟶ S` and `ha : a ≫ b = b`. For a group scheme `G` over `B` and a test
object `T : Over S`, the published `Langlands.GroupScheme.CocharacterTransport`
provides `descentTestIso b a ha T` and `descentBaseChangeIso b a ha G`. Here
`(Over.map a).obj T` is the same scheme `T.left` with structure map
`T.hom ≫ a`.

- `descentPoint b a ha G T y` sends a point `y : T ⟶ G_S.X` of the base change
  to the point of `G_S` over `(Over.map a).obj T` that has the same underlying
  point of `G` over `B`. The lemma `baseChangePointsEquiv_descentPoint` states
  this property, and the definition is characterised by it.
  `descentPoint_mul` and `descentPoint_injective` say that `descentPoint` is
  an injective multiplicative map. `descentPoint_id` says the change along
  `𝟙 S` is the evident identification. `descentPoint_comp` says two successive
  changes compose to one change along `a ≫ c`.
- `transportCharacter b a ha G χ`, for a character
  `χ : G_S ⟶ 𝔾_{m,S}`, is the composite of the inverse of
  `descentBaseChangeIso`, the base change of `χ` along `a`, and the published
  `Gm.baseChangeIso a`. This is the character analogue of the published
  `transportCocharacter`. On points (`transportCharacter_points`), the
  transported character at `y` is `χ` evaluated at `descentPoint … y`, read
  as a unit of `Γ(T, 𝒪_T)`. The lemmas `transportCharacter_id` and
  `transportCharacter_comp` say that transport along `𝟙 S` is the identity
  and that transport along `c` then along `a` is transport along `a ≫ c`.
- `descentPoint_transportCocharacter` is the matching description of the
  published `transportCocharacter`: seen through `descentPoint`, the
  transported cocharacter at a unit `s` is the original cocharacter at the
  same unit `s`.

## Transport on the lattices

For `T : CommGroupScheme B`, the published lattices of `T_S :=
(CommGroupScheme.baseChange b).obj T` are `characterLattice T_S = T_S ⟶ 𝔾_{m,S}`
and `cocharacterLattice T_S = 𝔾_{m,S} ⟶ T_S`. They come from
`Langlands.GroupScheme.Torus.Lattice`.

- `characterLattice.transport b a ha T` and
  `cocharacterLattice.transport b a ha T` are the transports above, as
  additive maps (`→+`). Additivity is checked on points, where sums of
  homomorphisms act by products.
- `groupHom_transport` unfolds them to `transportCharacter` and
  `transportCocharacter`.
- `characterLattice.transport_points` and
  `cocharacterLattice.descentPoint_transport` restate the point formulas
  above.
- `transport_id`, `transport_transport`, `transport_of_eq_id` and
  `transport_transport_of_eq` give the identity and composition laws.

## Point comparisons and extensionality

These are internal helpers.

- `comp_baseChange_X` and `comp_groupHom_X` are `rfl` lemmas. They restate a
  composite `x ≫ f` with a different, definitionally equal, implicit codomain.
  The codomain can be written as the base change as a commutative group
  scheme, as the base change as a group scheme, or as the codomain of the
  underlying monoid morphism. Rewriting with these lemmas changes only that
  implicit argument. This keeps kernel checking of concrete instances cheap.
  The kernel otherwise unfolds both sides of such comparisons inside
  evaluation maps.
- `characterLattice.ext_points`: two characters are equal if they agree on
  all points after reading values in `𝔾_m` as units
  (`Gm.pointsEquiv`).
- `cocharacterLattice.ext_points`: two cocharacters are equal if they agree
  on all points.

Both reduce to the published `CommGroupScheme.hom_ext_points`.

## Lattices along isomorphisms

For an isomorphism `e : T ≅ T'` of commutative group schemes:

- `characterLattice.congr e : characterLattice T ≃+ characterLattice T'` is
  `χ ↦ e.inv ≫ χ`, with inverse `ψ ↦ e.hom ≫ ψ`.
- `cocharacterLattice.congr e : cocharacterLattice T ≃+ cocharacterLattice T'`
  is `ν ↦ ν ≫ e.hom`, with inverse `ν ↦ ν ≫ e.inv`.
- `latticePairing_congr`: over `Spec k` with `k` a domain, these
  identifications preserve the published pairing `latticePairing`.

## Galois action

Fix `[CommRing k] [CommRing K] [Algebra k K]` and `T` a commutative group
scheme over `Spec k`.

- `algebraBaseMap k K := Spec.map (algebraMap k K)` is the structure morphism
  `Spec K ⟶ Spec k`. It is a reducible abbreviation.
- `galoisBaseMap k K σ := Spec.map σ` for `σ : K ≃ₐ[k] K`. The lemma
  `galoisBaseMap_over` says it is a morphism over `Spec k`.
  `galoisBaseMap_one` says `Spec 1 = 𝟙`, and `galoisBaseMap_mul` says
  `Spec (σ τ) = Spec σ ≫ Spec τ`. `Spec` is contravariant and Lean writes
  composition in diagrammatic order, so this is the order that makes the
  action below a left action.
- `characterLattice.galoisRepresentation k K T :
  Representation ℤ (K ≃ₐ[k] K) (characterLattice T_K)` sends `σ` to transport
  along `Spec σ` (`galoisRepresentation_apply`).
- `cocharacterLattice.galoisRepresentation k K T` is the same for
  cocharacters.

Being a monoid homomorphism into `Module.End ℤ` amounts to two laws. The
identity acts trivially, by `transport_of_eq_id` and `galoisBaseMap_one`. And
`σ τ` acts as `σ` after `τ`, by `transport_transport_of_eq` and
`galoisBaseMap_mul`. So both lattices are actual `ℤ[Aut_k(K)]`-modules, and
Mathlib's representation API applies.

The action of `σ` on points is given by two lemmas.

- `characterLattice.galoisRepresentation_points`: for a test object `U` over
  `Spec K` and a point `y` of `T_K` over `U`, the value of `σ χ` at `y` is
  the value of `χ` at the same point of `T`. That point is read over the test
  scheme with `K`-structure changed by `Spec σ` (`descentPoint`).
- `cocharacterLattice.descentPoint_galoisRepresentation`: seen through the
  same change of structure, `σ ν` at a unit `s` is `ν` at `s`.

Take `U = Spec A` for a `K`-algebra `ι : K → A`. Changing the structure by
`Spec σ` replaces `ι` by `ι ∘ σ`. Evaluating `χ` there applies `σ` to the
coefficients of `χ`. This is the classical `(σχ)(t) = σ(χ(σ⁻¹ t))`.

## Scope

No hypothesis on `T` beyond commutativity is used. In particular, `T` need
not be a torus, of finite type, or smooth. The lattices carry no topology,
and continuity of the action is not addressed. The concrete instance for the
Deligne torus, where complex conjugation exchanges the two coordinates of
`X^*(S_ℂ) ≅ ℤ²`, is the companion module
`Langlands.Shimura.Unitary.DeligneLattices`.
