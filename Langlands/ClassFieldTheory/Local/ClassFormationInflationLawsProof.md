# Fundamental-class cup inflation laws of a finite class formation

Author: Worker 272.

This module proves the published proposition
`Langlands.ClassFieldTheory.Local.ClassFormationInflationLawsStatement`
(module `Langlands.ClassFieldTheory.Local.ClassFormationCupLawsStatement`).
The exact-target theorem is

```
theorem classFormationInflationLaws :
    ClassFormationInflationLawsStatement.{u}
```

in the namespace `Langlands.ClassFieldTheory.Local`. Unfolded, it says: for
every prime `p` and every raw invariant family `I : InvariantFamily.{u,u} p`
with `I.RelativeClassFormation`, both `I.PositiveTateInflation` and
`I.OrdinaryInflation` hold. So for every p-adic field `F` and every tower
`F ⊆ L ⊆ M` with `L/F` and `M/F` finite Galois, if `c` and `d` are the
fundamental classes of `L/F` and `M/F` for `I`, then

```
Inf (c ∪ x) = [M : L] • (d ∪ Inf x)
```

for every `x` in positive Tate degree `n` (Tate cup `relativeTateCup`, Tate
inflation `relativePositiveTateInflation` and
`integralPositiveTateInflation`), and for every `x` in every ordinary degree
`n ≥ 0` (ordinary cup `relativeOrdinaryCup`, inflations
`relativeInflationLinear` and `integralInflation`).

The module also proves, without class-formation hypotheses, that the ordinary
cup product commutes with a change of group, and that the unscaled cup
inflation diagrams `OrdinaryCupInflation` and `PositiveTateCupInflation` hold
for every tower `K ⊆ L ⊆ M` with `L/K` normal (and both finite in the Tate
case).

## Source

Jean-Pierre Serre, *Local Fields*, GTM 67, Springer, 1979 (registered source
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`):

- Chapter XI, §3 (printed page 168, PDF page 174): the fundamental classes
  satisfy `Inf(u_{F/E}) = [F' : F] · u_{F'/E}` for a tower `F' ⊃ F ⊃ E`.
- Chapter XI, §3 (printed page 169, PDF page 175): the cup maps
  `θⁿ(F/E) : x ↦ u_{F/E} · x` satisfy `Inf ∘ θⁿ(F/E) = [F' : F] · θⁿ(F'/E) ∘ Inf`.
  Serre says this follows from the formula for `Inf(u_{F/E})` and known cup
  product formulas. He cites Cartan–Eilenberg, Chapter XII, for those formulas.

Serre does not prove the cup formula he cites. Here it is proved directly on
explicit cocycles, for ordinary cohomology, and then carried to positive Tate
degrees through the published positive comparison isomorphisms.

## General lemmas (namespace `Langlands.Tate`)

Let `f : G' →* G` be a group homomorphism, and let `R` be a commutative ring.

- `iCocycles_cocyclesMap`: for a map `α : Rep.res f A ⟶ B`, the cocycle map
  `cocyclesMap f α n` sends a cocycle `a` to `x ↦ α (a (f ∘ x))`. Proof:
  `HomologicalComplex.cyclesMap_i` for `cochainsMap f α`.
- `ordinaryCupCocycles_map`: let `φ : Pairing A B C` and
  `φ' : Pairing A' B' C'` be pairings of `G`- and `G'`-representations, and
  let `α`, `β`, `γ` be maps from the restrictions of `A`, `B`, `C` along `f`
  with `γ (φ a b) = φ' (α a) (β b)`. Then the cocycle map of `γ` sends the
  explicit cup `ordinaryCupCocycles φ p q a b` to the explicit cup of the
  mapped cocycles. Proof: evaluate both cocycles at `x : Fin (p + q) → G'`
  with `ordinaryCupCocycles_apply` and the previous lemma. The two sides
  differ only in how the left factor acts on the second value: through
  `f` applied to the product of the first `p` arguments, against the product
  of their images under `f`. These agree by `map_list_prod` and
  `List.map_ofFn`. Then `Rep.hom_comm_apply β` moves this action past `β`.
- `ordinaryCup_map`: the same compatibility for `ordinaryCup` on cohomology.
  Proof: choose cocycle representatives (`π` is surjective), then use
  `ordinaryCup_π_π` and `π_map_apply`.
- `map_degree_transport`: `groupCohomology.map f α` commutes with transport
  along an equality of degrees. Proof: `subst` the equality, then `rfl`.

## The unscaled local laws

Let `K ⊆ L ⊆ M` be a tower with `L/K` normal.

- `inflationUnitCoefficients` is the unit inclusion `Lˣ → Mˣ`, viewed as a
  morphism from the restriction of `unitsRepresentation K L` along
  `AlgEquiv.restrictNormalHom L` to `unitsRepresentation K M`.
  `integralInflationCoefficients` is the identity on the trivial integral
  representation. With these two maps, `relativeInflationLinear_eq_map` and
  `integralInflation_eq_map` show by `rfl` that the published inflation maps
  are `groupCohomology.map` along normal restriction.
- `ordinaryCupInflation : OrdinaryCupInflation K L M`. Unfold
  `relativeOrdinaryCup`. Then `map_degree_transport` with
  `Nat.add_comm 2 n` moves inflation inside the degree transport, and
  `ordinaryCup_map` closes the goal. Its compatibility hypothesis
  `ι (r • a) = r • ι a` for the scalar pairings holds by `map_smul`.

Now assume also that `L/K` and `M/K` are finite.

- `integralOrdinaryToTate_integralTateToOrdinary`: in positive degree `n`,
  the published `integralOrdinaryToTate` inverts `integralTateToOrdinary`.
  Proof: `Langlands.Tate.ordinaryToTate_pos` identifies the comparison with
  the inverse of `TateCohomology.isoGroupCohomology n`.
- `relativeTateCup_nsmul`: `relativeTateCup K L n (k • c) =
  k • relativeTateCup K L n c`, because `integralH2Cup` is linear in its
  degree-two argument.
- `relativeTateToOrdinary_relativeTateCup`: in positive degree `n`,
  `relativeTateToOrdinary K L (n + 2) (relativeTateCup K L n c x) =
  relativeOrdinaryCup K L n c (integralTateToOrdinary K L n x)`. Proof: the
  published `relativeOrdinaryCup_comparison` with the previous lemma. Its
  degree transport between `((n + 2 : ℕ) : ℤ)` and `(n : ℤ) + 2` is the
  identity. In degree `n + 2` the comparison `relativeOrdinaryToTate` is by
  definition the inverse of `relativeTateToOrdinary`.
- `positiveTateCupInflation : PositiveTateCupInflation K L M`. Apply the
  injective map `relativeTateToOrdinary K M (n + 2)`. The published
  `relativePositiveTateInflation_comparison` and
  `integralPositiveTateInflation_comparison`, with the previous lemma on both
  sides, reduce the goal to `ordinaryCupInflation`.

## The implemented proof of the target

For `I` with `hI : I.RelativeClassFormation`, a tower `F ⊆ L ⊆ M`, and
fundamental classes `c` of `L/F` and `d` of `M/F`:

1. `FiniteDimensional L M` follows from `FiniteDimensional.right`.
2. The published `InvariantFamily.fundamentalInflation_of_relativeClassFormation`
   (module `FundamentalConsequencesProof`) gives
   `relativeInflationLinear F L M 2 c = [M : L] • d`. Here `relativeInflation`
   and `relativeInflationLinear` agree by `rfl`.
3. `positiveTateInflation_of_relativeClassFormation`: rewrite with
   `positiveTateCupInflation`, then with step 2, then with
   `relativeTateCup_nsmul` and `LinearMap.smul_apply`.
4. `ordinaryInflation_of_relativeClassFormation`: rewrite with
   `ordinaryCupInflation` and step 2. Then `map_nsmul` and
   `LinearMap.smul_apply` pull the scalar out of the ordinary cup and the
   degree transport.
5. `classFormationInflationLaws` pairs the two results.

## Notes

- Axioms used by the target theorem: `propext`, `Classical.choice`,
  `Quot.sound`.
- The module imports only published Library modules:
  `ClassFormationCupLawsStatement` and `FundamentalConsequencesProof`.
