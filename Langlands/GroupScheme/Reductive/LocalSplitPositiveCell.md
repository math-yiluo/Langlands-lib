# Products of positive root points over local rings

This module proves that, for a split reductive group over an arbitrary commutative
ring, a finite product of positive root points over a local test ring is a product
of the positive big-cell factors. The base ring may have nilpotents, and the local
test ring needs no condition on its residue field. The result is a pointwise form,
over local rings, of the closedness of the product of the positive root groups under
multiplication (Conrad, *Reductive group schemes*, Theorem 5.1.13). The module also
gives the consequence for big-cell points: right multiplication by a positive root
point changes only the positive coordinates.

## Statement

`LocalSplitPositiveProductStatement.{u}` concerns:

- a commutative ring `R`, a finite type `I` and a type `J`, all in universe `u`;
- a group scheme `G` over `Spec R` whose structure morphism is affine (instance
  binder `IsAffineHom`, which the definition of `IsFibrewiseRootDatumOf` needs) and
  which is reductive (`IsReductive`);
- a coordinate split torus `i : T_I → G` that is maximal on every residue-field fibre
  (`IsFibrewiseMaximalTorus`);
- a coordinate root datum `P : RootDatum J (I → ℤ) (I → ℤ)` that is a fibrewise root
  datum for `i` in `G` (`IsFibrewiseRootDatumOf`), and a base `b` of `P`;
- a family `u : J → (𝔾ₐ ⟶ G)` with `u α` a root parametrization of `i` for
  `P.root α` (`IsRootParametrization`) for every root `α`;
- enumerations `neg : Fin m ≃ {α // ¬ b.IsPos α}` and `pos : Fin n ≃ {α // b.IsPos α}`
  of the non-positive and the positive roots. The enumeration `neg` does not occur in
  the conclusion. Its role is to make the hypotheses provide the full big cell, which
  the proof uses;
- a commutative local ring `B : Type u`, a morphism `s : Spec B ⟶ Spec R`, a list
  `e : Fin r → J` of positive roots (`b.IsPos (e k)` for every `k`), and global
  functions `c : Fin r → Γ(Spec B, ⊤)`.

The conclusion is that there are global functions `z : Fin n → Γ(Spec B, ⊤)` with

`u_{e 0}(c 0) · … · u_{e (r-1)}(c (r-1)) = u_{pos 0}(z 0) · … · u_{pos (n-1)}(z (n-1))`

as points of `G` over `s`, where `u_α(c)` is `rootPoint (u α)` at `c` and the
products are the `orderedProduct`s of `Langlands.GroupScheme.Reductive.LocalSplitCell`.
The module proves this proposition at full universe as `localSplitPositiveProduct`.

The namespace `LocalSplitCell` also contains the general results the proposition is
built from:

- `exists_orderedProduct_eq_pos`: the same conclusion for any family `u`, any
  enumerations `neg : Fin m → J` and `pos : Fin n → J` whose cell map is an open
  immersion, and any torus equivariance `TorusEquivariant i ch u` with exponent
  characters `ch : J → I → ℤ`. One needs a cocharacter `ν : I → ℤ` with
  `⟨ch (neg k), ν⟩ < 0` for all `k` and `⟨ch (e k), ν⟩ > 0` for all `k`. Here
  `⟨x, ν⟩ = coPairing x ν = ∑ⱼ x j * ν j`. No condition is imposed on the pairings of
  the characters of `pos`;
- `exists_orderedProduct_mul_rootPoint_eq_pos` and `exists_comp_cellMap_mul_rootPoint`:
  if also `⟨ch (pos k), ν⟩ > 0` for all `k` and `⟨ch α, ν⟩ > 0`, then
  `(∏ₖ u_{pos k}(w k)) · u_α(a)` is a positive-factor product, and for every cell
  point `x` over a local test ring, `Ω(x) · u_α(a) = Ω(x')`. Here `Ω` is the cell map
  and `x'` has the negative and torus coordinates of `x`;
- `exists_coPairing_eq_height`: for a root datum `P` on `I → ℤ` and a base `b`, there
  are an integer `d > 0` and a cocharacter `ν` with `⟨P.root j, ν⟩ = d * b.height j` for
  every root `j`. `exists_cocharacter_of_base` deduces a `ν` that pairs positively with
  the positive roots and negatively with the other roots;
- `exists_orderedProduct_eq_pos_of_isPos` and `exists_comp_cellMap_mul_rootPoint_of_isPos`:
  the two statements above under the hypotheses of the proposition, with `neg`, `pos`
  the root enumerations and `ν` from `exists_cocharacter_of_base`.

## Proof

**Cocharacters.** `cocharPoint ν Z t` is the torus point with coordinates `t ^ ν j`,
for a global unit `t` on `Z`. The exponent character `ch` takes the value
`t ^ ⟨ch, ν⟩` there (`torusChar_cocharPoint`). Torus equivariance gives
`T · (∏ₖ u_{e k}(c k)) · T⁻¹ = ∏ₖ u_{e k}(ch(e k)(T) · c k)` for a torus point `T`
(`torus_mul_orderedProduct_mul_inv`). Conjugating a cell point by `T⁻¹` divides its
root coordinates by the characters and keeps its torus coordinate
(`torus_inv_mul_cellMap_mul`). The identity is the cell point with zero root
coordinates and trivial torus coordinate (`mkCellPoint_one_comp_cellMap`).

**Contraction.** In `exists_orderedProduct_eq_pos`, let `g = ∏ₖ u_{e k}(c k)` over
`Spec B`, and write `⟨ch (e k), ν⟩ = d_k > 0`. For an object `W` over `Spec B` and a
global function `t` on `W`, put `S(t) = ∏ₖ u_{e k}(t ^ {d_k} · c k)`. This is natural
in `W`. It equals `1` at `t = 0`, and for a unit `t` it equals `ν(t) · g · ν(t)⁻¹`.
The proof uses three local rings from the imported module
`LocalSplitGeneratorRelations` (namespace `GenericLine`). The first is
`A₀ = AtPoint B 0`, the local ring of `B[X]` at the point `X = 0` of the closed fibre.
The second is `K = Generic B`, the local ring of `B[X]` at the generic point of the
closed fibre. The third is `B` itself, reached from `A₀` by evaluation `X ↦ 0`
(`evalAt 0`).

1. Over `A₀`, let `E₀ = S(X)`. Its pullback along evaluation at `0` is `S(0) = 1`, the
   cell point `(0, 1, 0)`. The closed point of `Spec A₀` is the image of the closed
   point of `Spec B`, so `E₀` maps it into the open cell. The imported
   `exists_lift_of_localPoint_closedPoint_mem` then factors `E₀ = Ω(Y₀)` for a cell
   point `Y₀` over `A₀`. Since `Ω` is a monomorphism, `Y₀` pulls back to `(0, 1, 0)`
   at `X = 0`.
2. The map `toGeneric 0 : A₀ → K` is injective, and `X` becomes a unit in `K`. Over
   `K`, the pullback of `E₀` is `ν(X) · g · ν(X)⁻¹`. So the pullback of `g` to `K` is
   `ν(X)⁻¹ · Ω(Y₀) · ν(X) = Ω(Y')`. The negative coordinates of `Y'` are
   `X ^ {q_k} · negCoord Y₀ k` with `q_k = -⟨ch (neg k), ν⟩ > 0`, and its torus coordinate
   is that of `Y₀`. The composite `B → K` is a local homomorphism
   (`isLocalHom_algebraMap_generic_comp_C`). So the closed point of `Spec K` maps to
   the closed point of `Spec B`, and `g` maps that closed point into the open cell.
   Hence `g = Ω(y)` for a cell point `y` over `B`.
3. Pull `y` back to `A₀`, giving `y₀`. Its further pullback to `K` is `Y'`, because
   `Ω` is a monomorphism. Restriction of global functions along the injective map
   `A₀ → K` is injective (`specMap_appTop_injective`). Over `A₀`, therefore,
   `negCoord y₀ k = X ^ {q_k} · negCoord Y₀ k`, and `y₀` and `Y₀` have the same torus
   coordinate. Evaluation at `X = 0` returns `y`. Since `q_k > 0`, the negative
   coordinates of `y` vanish, and the torus coordinate of `y` is that of
   `(0, 1, 0)`, which is trivial.

So `g = Ω(0, 1, posCoord y) = ∏ₖ u_{pos k}(posCoord y k)`.

**Translation of cell points.** `orderedProduct_snoc` appends one root point to an
ordered product. Applying the contraction to the list `pos` followed by `α` gives
`exists_orderedProduct_mul_rootPoint_eq_pos`. Since `Ω(x) = A · τ · B` with `B` the
positive factor, `Ω(x) · u_α(a) = A · τ · (B · u_α(a))`, which gives
`exists_comp_cellMap_mul_rootPoint`.

**Cocharacter of a base.** `exists_coPairing_eq_height` casts characters to `I → ℚ`.
The simple roots are linearly independent over `ℤ` (`b.linearIndepOn_root`), hence
over `ℚ`. Mathlib's `Subspace.dualLift` extends to all of `I → ℚ` the linear form that
is `1` on every simple root and is defined on their span. Its values on the
coordinate vectors are rational numbers. Mathlib's
`IsLocalization.exist_integer_multiples_of_finite` gives a nonzero integer `c` and
integers `a j` with `a j = c · f(e_j)`, where `f` is the extended form. With
`ν = c · a`, the pairing of `x` with `ν` is `c² · f(x)`. Every root is an integer
combination of the simple roots whose coefficients sum to its height
(`b.exists_root_eq_sum_int`, `RootPairing.Base.height_eq_sum`). So
`⟨P.root j, ν⟩ = c² · b.height j`. Heights of positive roots are positive and heights
of the other roots are negative (`b.height_ne_zero`, `RootPairing.Base.isPos_iff`),
which gives `exists_cocharacter_of_base`.

**Root families.** Under the hypotheses of the proposition, the imported
`LocalSplitBigCell.isOpenImmersion_cellMap` shows that the cell map for the root
enumerations is an open immersion. The equivariance field of `IsRootParametrization`
is torus equivariance with characters `ch α = P.root α`. The cocharacter from
`exists_cocharacter_of_base` pairs negatively with all non-positive roots and
positively with all positive roots. So `exists_orderedProduct_eq_pos_of_isPos` and
`exists_comp_cellMap_mul_rootPoint_of_isPos` follow, and the proposition is
`exists_orderedProduct_eq_pos_of_isPos`.

## Provenance and scope

The corresponding published result is Conrad's Theorem 5.1.13 (B. Conrad, *Reductive
group schemes*, in *Autour des schémas en groupes*, Panoramas et Synthèses 42–43,
2014). For a split reductive group over any nonempty scheme and a positive system of
roots, it states that the product of the positive root groups in any order is a
closed subgroup `U_{Φ⁺}`, and that `U_{-Φ⁺} × T × U_{Φ⁺} → G` is an open immersion.
Conrad's proof identifies `U_{Φ⁺}` with the subgroup `U_G(λ)` of the dynamic method
(Theorem 4.1.7 there) for a cocharacter `λ` positive on `Φ⁺`. The subgroup `U_G(λ)`
consists of the points `g` with `lim_{t→0} λ(t) g λ(t)⁻¹ = 1`. SGA 3, Exp. XXII, §5
gives a different construction of `U_{Φ⁺}`.

The present module states and proves only the pointwise consequence over local test
rings: a product of positive root points has the form `∏ₖ u_{pos k}(z k)` for the
given enumeration `pos`. It does not prove that the multiplication map of the
positive factors is a closed immersion or a subgroup functor. It also does not prove
that the coordinates `z` are unique, which the open immersion of the big cell would
give. The proof is an explicit construction of this module. Following the dynamic
method, it contracts the product along a cocharacter. In place of limits, it uses
the local rings of the affine line at `X = 0` and at the generic point of the closed
fibre. The cocharacter construction from a base is likewise internal. Conrad's proof of
Theorem 5.1.13 also starts by picking a cocharacter `λ ∈ M^∨` that is positive
exactly on `Φ⁺`.

This module does not prove the local split Isomorphism Theorem. In the planned
application, its right-translation form transfers relations `Ω(x) · u_a(c) = Ω(y)` to
the positive coordinates. That transfer is still to be combined with structure
constants for the group laws of the positive factors, which this module does not
provide.
