# Proof of the two-block cell sections

Author: Worker 731.

The theorem `Langlands.Whittaker.twoBlockCellSection` proves exactly the
published proposition `Langlands.Whittaker.TwoBlockCellSectionStatement.{uF,uV}`.
The statement module and the modules it imports are unchanged. The theorem
uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Write `A = a + 1`, `B = b + 1`, `P = twoBlockParabolic F a b` (the standard
upper parabolic of block shape `(A, B)`), `Q` for the opposite unipotent
radical `(twoBlockShape a b).oppositeUnipotentSubgroup F.Carrier`, and
`w = Shahidi.blockWeyl A B F.Carrier`. For a `B × A` matrix `x`, the Library
defines `Shahidi.lower A B F.Carrier x = w n(x) w⁻¹`, where
`n(x) = Shahidi.intertwiningUnipotent A B F.Carrier x`. It is the block matrix
`[[1, 0], [x, 1]]`. `Shahidi.lowerCoordinates A B g` reads off the lower-left
`B × A` block of `g`.

## Route

JPSS construct the section in (5.5), printed pp. 424–425, by integrating a
function supported in `Q Ū_Q` over the parabolic. The Lean proof does not
follow that integral. It applies the Library theorem
`Geometric.closedOrbitSectionExtension` to the double coset `P · 1 · Q`. The
section is first built at the point `1` with the opposite radical `Q`, and
then right translated by `w⁻¹`.

1. On `Q` define `f0 q = Ψ(lowerCoordinates q) • v`.
2. Extend `f0` to an element `f` of the compact induction from `P`, supported
   in the open orbit `P Q / P`, with `f(q) = f0(q)` for `q ∈ Q`.
3. Put `f' = ξ(w⁻¹) f`, so `f'(g) = f(g w⁻¹)`. Then
   `f'(w n(x)) = f(w n(x) w⁻¹) = f(lower x) = Ψ(x) • v`.

## Helpers

### Section `Lower` (any field `R`, block sizes `m, n > 0`)

- `lower_zero`: `Shahidi.lower m n R 0 = 1`.
- `lower_add`: `lower (x + y) = lower x * lower y`. It follows from
  `Shahidi.intertwiningUnipotent_add` after conjugation by `w`.
- `lower_mem_oppositeUnipotentSubgroup`: `lower x` lies in the opposite
  unipotent subgroup of `Shahidi.twoBlocks m n hm hn`. The proof checks the
  block conditions of `BlockShape.mem_oppositeParabolic_iff` with the published
  entry lemmas `Shahidi.lower_first_second`, `Shahidi.lower_first_first` and
  `Shahidi.lower_second_second`.
- `eq_lower_of_mem_oppositeUnipotentSubgroup`: every `g` in that subgroup
  equals `lower (lowerCoordinates g)`. The proof compares the four blocks of
  entries.
- `eq_one_of_mem_parabolic_of_mem_oppositeUnipotentSubgroup`: `P ∩ Q = 1`. An
  element of `Q` is `lower (lowerCoordinates g)`. Membership in `P` makes the
  lower-left block zero (`Shahidi.twoBlocks_mem_parabolic_iff`).
- `lowerCoordinates_one`, `lowerCoordinates_mul`: on `Q`, `lowerCoordinates`
  sends `1` to `0` and products to sums.
- `oppositeCoordinateHom`: the resulting homomorphism from `Q` to
  `Multiplicative (Matrix (Fin n) (Fin m) R)`.

### Section `Topology` (any topological group `G`)

- `isOpen_mul_of_openSubgroup`: let `P` and `Q` be subgroups and `K` an open
  subgroup. If every element of `K` is a product `p q` with `p ∈ P` and
  `q ∈ Q`, then the set `P Q` is open. Each point `p q` of `P Q` has the open
  neighbourhood `p K q`, which lies in `P Q`.
- `isOpen_cosetOrbit_one`: if `P Q` is open, then the orbit
  `Geometric.cosetOrbit P Q 1` of the base coset in `P \ G` is open. Its
  preimage under the quotient map is exactly `P Q`, and the quotient map by
  `QuotientGroup.rightRel P` is a quotient map.

### Section `Invariance`

`SchwartzBruhat.exists_openSubgroup_invariant` applies to an additive
topological group `X` that is Hausdorff, locally compact and totally
disconnected. Every Schwartz–Bruhat function `Ψ` on `X` is then invariant
under translation by some open subgroup `H` of `Multiplicative X`:
`Ψ(x + h) = Ψ(x)`. The proof transfers `Ψ` to `Multiplicative X` and applies
the published `Hecke.TestFunction.commonCompactOpenBiInvariance` to the
singleton family.

### Field topology

The private theorem `fieldTotallyDisconnected` shows that `F.Carrier` is
totally disconnected for the topology of any `T : F.TopologicalData`. It is
copied from the Library module
`Langlands.Representation.CuspidalSupport.LeviAdmissibleFactorizationProof`,
where the same theorem is private. The topology is nonarchimedean through
`ValuativeRel.nonarchimedeanRing`, and Mathlib then supplies total
disconnectedness.

### Section `Cell` (`F : PadicField p`)

- `oppositeLower F a b x` is `Shahidi.lower A B F.Carrier x` as an element of
  `Q`.
- `exists_openSubgroup_subset_parabolic_mul_opposite`: for the canonical
  topology there is an open subgroup `K` of `GL_{A+B}(F)` whose elements are
  all products `p q` with `p ∈ P` and `q ∈ Q`. The published
  `BlockShape.exists_compactOpenSubgroup_hasBlockIwahoriFactorization` gives a
  compact open `K` with a block Iwahori factorization. Each element of `K` is
  then a product `l m u` with `l` in `K ∩ Q`, `m` in the Levi part and `u` in
  the upper radical. Applying this to `k⁻¹` gives
  `k = u⁻¹ m⁻¹ l⁻¹ ∈ P Q`.

## Main proof

The theorem introduces all data of the statement. It installs the canonical
topology `T = F.canonicalTopologicalData` with its field instances,
`fieldTotallyDisconnected T`, and the group instances of `GL_{A+B}(F)`:
topological group, nonarchimedean, locally compact, Hausdorff and
σ-compact. It also gives the matrix space `Matrix (Fin B) (Fin A) F.Carrier`
its product instances.

- `P` and `Q` are closed (`isClosed_parabolic`,
  `isClosed_oppositeUnipotentSubgroup`).
- The inducing representation `twoBlockInducingRepresentation F a b π₁ π₂` is
  smooth. The pair representation is smooth by
  `Shahidi.isSmooth_pairRepresentation`. It stays smooth after pullback along
  the continuous Levi projection (`isSmooth_comp`) and after the twist by the
  half modulus, whose kernel is open (`isSmooth_twist_iff`). This gives the
  smooth representation `A` of `P` required by the extension theorem.
- The stabilizer `S = Geometric.orbitStabilizer P Q 1` is trivial: its image in
  `P` lies in `P ∩ Q = 1`. So the covariance condition for `f0` under `S` holds
  trivially.
- Smoothness of `f0`: take `H` from `SchwartzBruhat.exists_openSubgroup_invariant
  Ψ`, and pull it back along the continuous homomorphism
  `oppositeCoordinateHom` to an open subgroup `K` of `Q`. By
  `lowerCoordinates_mul`, `f0` is right `K`-invariant.
- Compact support: the support of `f0` is the image under `oppositeLower` of
  the support of `x ↦ Ψ(x) • v`. That support is compact. It is closed
  because the function is locally constant, and it lies in the function's
  `tsupport`, which is compact by `HasCompactSupport.smul_right`. Its image in
  `S \ Q`, under the continuous map induced by `oppositeLower`, is therefore
  compact. `Induction.compactFunctionOf`
  then gives an element `g` of the compact induction from `S` to `Q` with
  values `f0`.
- The orbit `U = Geometric.cosetOrbit P Q 1` is open by
  `exists_openSubgroup_subset_parabolic_mul_opposite`,
  `isOpen_mul_of_openSubgroup` and `isOpen_cosetOrbit_one`. It is closed in
  itself.
- `Geometric.closedOrbitSectionExtension` with `w = 1` and this `U` gives `f`
  in the compact induction from `P`. Its values vanish outside `P Q`, and
  `f(1⁻¹ q) = f0(q)` for `q ∈ Q`.
- `f' = twoBlockInduced F a b π₁ π₂ w⁻¹ f.val`. Its value at `w n(x)` is
  `f(lower x) = f0(oppositeLower x) = Ψ(lowerCoordinates (lower x)) • v`,
  which equals `Ψ x • v` by `Shahidi.lowerCoordinates_lower`.
- Membership in `twoBlockCellSubmodule`:
  - Support. If `f'(g) ≠ 0`, then `f(g w⁻¹) ≠ 0`. So `g w⁻¹ = p q` with
    `p ∈ P` and `q ∈ Q`. Write `q = w n(y) w⁻¹` with
    `y = lowerCoordinates q`. Then `g = p w n(y)` lies in the cell.
  - Compact support of the restriction. The restriction equals
    `x ↦ Ψ x • v`, and `Ψ` has compact support.

## Scope

The proof establishes only the statement as published: one `f` for each
`(Ψ, v)`, with no uniqueness, linearity or continuity in `(Ψ, v)`. It uses
smoothness of `π₁` and `π₂` and nothing about Whittaker models.
