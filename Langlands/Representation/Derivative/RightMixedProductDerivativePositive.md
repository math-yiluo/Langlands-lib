# The right mixed-product derivative filtration at positive `GL` rank

Authors: Worker 723 (Lean module and Markdown), Worker 969 (Markdown revisions
and submission).

This module proves the positive-`GL`-rank case of Bernstein–Zelevinsky (1977),
Corollary 4.14(b), in the exact shape of the published proposition
`Langlands.Derivative.RightMixedProductDerivativeFiltrationStatement`. Here the
input category is pairs `(B, A)` with `B` smooth on `P_(r+1)` (Library
`mirabolic r`) and `A` smooth on `GL_(k+1)`. The proof assumes five published
proposition definitions as explicit hypotheses:

- `MirabolicProductMinus.RightPsiCompatibility.{uF,uV} F T` and
  `MirabolicProductMinus.RightPhiShortExact.{uF,uV} F T`, the `Ψ⁻` and `Φ⁻`
  clauses of BZ77 Proposition 4.13(c);
- `LeftMixedProductDerivativeIso.{uF,uV} F T` and
  `LeftMixedProductDerivativeVanishing.{uF,uV} F T`, BZ77 Corollary 4.14(a);
- `Mirabolic.MinusExactnessStatement.{uF, max uF uV} F T`, exactness of the
  actual unnormalized and normalized `Ψ⁻` and `Φ⁻`. Only its last two clauses
  (normalized `Ψ⁻` and `Φ⁻`) are used. It is used at the carrier universe
  `max uF uV` of the right mixed product.

This module does not prove any of these hypotheses, and it does not establish
the target proposition by itself. It is an intermediate unit of task
`3231134e`. The planned target proof module
`Langlands.Representation.Derivative.RightMixedProductDerivativeFiltrationProof`
is not part of this unit. It will supply each hypothesis from an independently
published proof and add the `k = 0` case from the published
`Langlands.Derivative.rightMixedProductDerivativeFiltration_zero`. When this
unit was submitted, minus exactness was already published as
`Langlands.Derivative.Mirabolic.minusExactness`. The proofs of the 4.13(c)
clauses (task `6cd54f76`) and of 4.14(a) (task `7e19f753`) were not yet
published.

The entry theorem is

```lean
theorem Langlands.Derivative.RightMixedDerivative.filtration_pos
    (hPsi : MirabolicProductMinus.RightPsiCompatibility.{uF, uV} F T)
    (hSE : MirabolicProductMinus.RightPhiShortExact.{uF, uV} F T)
    (hLI : LeftMixedProductDerivativeIso.{uF, uV} F T)
    (hLV : LeftMixedProductDerivativeVanishing.{uF, uV} F T)
    (hE : Mirabolic.MinusExactnessStatement.{uF, max uF uV} F T)
    (k r d : ℕ) (hd : 0 < d ∧ d ≤ (k + 1 + r) + 1) :
    ∃ e : Fin (rightMixedDerivativeIndices (k + 1) r d).card ≃
        RightMixedDerivativeIndex (k + 1) r d,
      IsGluedFrom (rightMixedDerivativeSource.{uF, uV} T ψ (k + 1) r d hd)
        (fun i => rightMixedDerivativePiece T ψ (k + 1) r d (e i))
```

It holds for every prime `p`, `F : PadicField.{uF} p`, `T : F.TopologicalData`
and unitary additive character `ψ`. The two universes `uF` and `uV` stay
independent. Its body is exactly the body of the published statement at
`GL` rank `k + 1`.

## Source

BZ77, source `bernstein-zelevinsky-1977-induced-i`, printed p.458 (one-based PDF
page 19). Corollary 4.14(b) says that for `τ` on `P_m` and `ρ` on `G_k`, the
derivative `(τ × ρ)^(d)` is glued from the representations
`τ^(j) × ρ^(d-j)`. The printed proof derives (b) from (a) and 4.13(c). The
published statement makes this precise. The source is
`rightMixedDerivativeSource T ψ K r d hd`, which is the actual order-`d`
derivative `mirabolicDerivativeOfOrder T ψ (K + r) d hd` of
`T.rightMixedProductFunctor K r`, viewed in `Rep`. The grades are
`rightMixedDerivativePiece T ψ K r d x`, one for each `x = (j, t)` in the finite
type `RightMixedDerivativeIndex K r d`. That type contains exactly the pairs with
`1 ≤ j ≤ r + 1`, `t ≤ K` and `j + t = d`. Each grade is
`B^(j) × A^(t)`, the binary normalized product of the order-`j` mirabolic
derivative and the order-`t` `GL` derivative, followed by the rank cast
`rightMixedDerivativeIndices_rank`. In the source, the convention
`τ^(j) = 0` for `j > m` and `ρ^(t) = 0` for `t > k` is what removes the
infeasible pairs. The published index family omits those pairs instead, and the
proof below matches this by showing that the corresponding quotient terms are
zero.

## Proof outline

Write `K = k + 1`. The theorem follows from

```lean
theorem glued_pos ... (k : ℕ) : ∀ (r d : ℕ) (hd : 0 < d ∧ d ≤ (k + 1 + r) + 1),
    IsGluedFromFamily (rightMixedDerivativeSource T ψ (k + 1) r d hd)
      (rightMixedDerivativePiece T ψ (k + 1) r d)
```

where `IsGluedFromFamily` (module `Langlands.Representation.Filtration.GluedFamily`)
is gluing from a family indexed by a finite type, in some enumeration.
`filtration_pos` unpacks it with `IsGluedFromFamily.exists_equiv`, using
`Fintype.card_coe` to identify the cardinality of the subtype
`RightMixedDerivativeIndex` with `(rightMixedDerivativeIndices _ r d).card`.

`glued_pos` is proved by induction on the mirabolic rank `r`, for all orders
`d` at once. In each rank it splits into `d = 1` and `d = e + 2`.

### Order one (`glued_one`)

Every index type of order one has exactly one element, `(1, 0)`
(`indexOneUnique`). The order-one mirabolic derivative is `Ψ⁻`
(`mirabolicDerivativeOfOrder_one`), and the `GL` derivative of order zero is the
identity functor by definition. Hence `source_one_eq` and `piece_one_eq` are
equalities of functors that rewrite the source as
`T.rightMixedProductFunctor K r ⋙ Ψ⁻ ⋙ toRep` and the only grade as
`(Ψ⁻ × 𝟭) ⋙ binaryNormalizedProduct r K ⋙ cast ⋙ toRep`.
`RightPsiCompatibility` gives a natural isomorphism between the two smooth
functors. Whiskering it with `SmoothRep.toRep` and applying
`IsGluedFromFamily.of_iso_unique` gives the one-step gluing.

### The order recursion

For `d = e + 2`, the proof peels one `Φ⁻` off the derivative. By definition,
`mirabolicDerivativeOfOrder T ψ N i` is a mirabolic rank cast followed by
`phiMinusIterate` (`i - 1` copies of `Φ⁻`) and then `Ψ⁻`. The lemmas
`derivative_succ_eq` and `phiMinus_derivative_eq` state

```text
D_(N+1)^(i+1) = Φ⁻_N ⋙ D_N^(i) ⋙ (GL rank cast)
```

as an equality of functors. Each one is proved by first generalizing the ranks
inside the casts to variables, then substituting the defining equalities. After
that every rank cast is the identity cast and both sides agree definitionally.
`restrictionDerivative_eq` uses the same method to identify restriction to the
mirabolic subgroup followed by `D_k^(i)` with the `GL` derivative of order `i`
on `GL_(k+1)`. The lemmas `derivative_transport` and `castDerivativeCast_eq`
move mirabolic rank casts across a derivative of fixed order. `pieceShift_aux`
moves the casts inside a binary product.

Applying the recursion to the right mixed product (`source_succ_eq`):

```text
source (K, r, e+2) = rightPhiProduct T ψ k r ⋙ D_(k+r)^(e+1) ⋙ cast ⋙ toRep,
```

where `rightPhiProduct T ψ k r = Φ⁻(τ × ρ)` is the middle term of 4.13(c), with
the cast `(k+1)+r = k+r+1` already built in.

### The quotient term (`quotientIso`, `quotient_subsingleton`)

The last term of 4.13(c) is
`rightPhiQuotient T k R = (Ψ⁻τ) × (ρ|P_(k+1))`, a left mixed product with
`GL_R` factor `Ψ⁻τ` (for `R = 0` this is `GL_0`, with its carrier kept in full)
and mirabolic factor `ρ|P_(k+1)` (`generalLinearRestriction T k`).

- If `e + 1 ≤ k + 1`, `LeftMixedProductDerivativeIso` at
  `(ψ, R, k, e+1)` gives
  `(Ψ⁻τ × ρ|P)^(e+1) ≅ Ψ⁻τ × (ρ|P)^(e+1)`. Then `quotient_eq₂` (using
  `restrictionDerivative_eq` and `mirabolicDerivativeOfOrder_one`) identifies the
  right side with the grade at index `(1, e + 1)` (`quotientIndex`):
  `τ^(1) × ρ^(e+1)`, since `τ^(1) = Ψ⁻τ` and `(ρ|P)^(e+1) = ρ^(e+1)`.
  `quotient_eq₁` moves the rank cast `R + k = k + R` of `rightPhiQuotient` across
  the derivative. `quotientIso` composes these equalities (as `eqToIso`) with
  the whiskered isomorphism.
- If `e + 1 > k + 1`, `LeftMixedProductDerivativeVanishing` says that the
  order-`(e+1)` derivative of `Ψ⁻τ × ρ|P_(k+1)` has zero carrier.
  `derivativeCast_subsingleton` carries this through the rank casts. In this
  case the index `(1, e + 1)` is not feasible.

### Mirabolic rank zero (`glued_zero`)

For `r = 0` and `d = e + 2`, the only feasible index is `(1, e + 1)`
(`indexZeroUnique`), and `e + 1 ≤ k + 1` follows from the bound on `d`. The
published theorem `MirabolicProductMinus.rightPhiBoundary` (module
`MirabolicProductMinusRightBoundary`, BZ77 4.13(c) at `m = 1` with `P_0 = ∅`)
gives `rightPhiProduct T ψ k 0 ≅ rightPhiQuotient T k 0`. Whiskering it with
`D_k^(e+1) ⋙ cast ⋙ toRep` and composing with `source_succ_eq` and
`quotientIso` gives a natural isomorphism from the source to the only grade.
No exactness is used in this case.

### Positive mirabolic rank (`glued_succ`)

For mirabolic rank `r + 1` and `d = e + 2`, `RightPhiShortExact` gives natural
transformations

```text
i : rightPhiSubobject T ψ k r ⟶ rightPhiProduct T ψ k (r+1),
q : rightPhiProduct T ψ k (r+1) ⟶ rightPhiQuotient T k (r+1)
```

whose actual linear maps are injective, exact in the middle and surjective at
every pair `(τ, ρ)`. That is BZ77's sequence
`0 → (Φ⁻τ) × ρ → Φ⁻(τ × ρ) → (Ψ⁻τ) × (ρ|P) → 0`. The proof whiskers `i` and `q`
by `J ⋙ toRep`, where `J = D_(k+r+1)^(e+1) ⋙ cast`. The whiskered maps are still
short exact, because `J` maps short exact sequences to short exact sequences:

- `LevelCalculus.mapsShortExact_mirabolicDerivativeOfOrder` composes the `Ψ⁻` clause of
  `hE` with the `Φ⁻` clause of `hE`, iterated by `mapsShortExact_phiMinusIterate`;
- `mapsShortExact_mirabolicRankCast` and `mapsShortExact_generalLinearRankCast`
  handle the rank casts. These are identities after substitution.

The underlying linear map of the whiskered component is definitionally
`SmoothRep.hom (J.map (i.app X))`. This is the map controlled by
`MapsShortExactIntertwiners`.

- Subobject. `sub_eq` rewrites the whiskered subobject as
  `(Φ⁻ × 𝟭) ⋙ source (K, r, e+1) ⋙ cast`. The induction hypothesis at rank `r`
  and order `e + 1`, transported by `glued_rankCast` and
  `IsGluedFromFamily.precomp`, glues it from the precomposed grades
  `(Φ⁻ × 𝟭) ⋙ (B^(j) × A^(t)) ⋙ cast`. `pieceShift_eq`, which uses
  `phiMinus_derivative_eq` (`Φ⁻ ⋙ D_r^(j) = D_(r+1)^(j+1) ⋙ cast`), identifies
  each of these with the grade `B^(j+1) × A^(t)` of the source at rank `r + 1`
  and order `e + 2`. This is the index shift `(j, t) ↦ (j + 1, t)`.
- Quotient. The quotient is glued from the family indexed by
  `PLift (e + 1 ≤ k + 1)`. When the inequality holds, that family has one
  element, the grade `(1, e + 1)`, and `quotientIso` applies. Otherwise the
  family is empty and `quotient_subsingleton` applies with
  `IsGluedFromFamily.of_isEmpty`.
- Splice. `IsGluedFromFamily.splice` combines the two along the whiskered short
  exact sequence. The index map
  `spliceIndexEquiv K r e : Index K r (e+1) ⊕ PLift (e + 1 ≤ K) ≃ Index K (r+1) (e+2)`
  sends `(j, t)` to `(j + 1, t)` and the right summand to `(1, e + 1)`. It is a
  bijection (`spliceIndexFun_bijective`): an index at rank `r + 1` with first
  coordinate `j ≥ 2` comes from `(j - 1, t)`, and one with `j = 1` must be
  `(1, e + 1)`, which is feasible exactly when `e + 1 ≤ K`. Finally
  `source_succ_eq` identifies the middle term with the source.

The proof does not change the grades. Every feasible pair occurs exactly once,
including grades that are zero or isomorphic to one another.

## Implementation notes

All comparisons of composite functors are stated as equalities and turned into
isomorphisms with `eqToIso`. Each is proved after the ranks inside the casts
have been generalized to variables. Both `binaryNormalizedProductFunctor` and
`mirabolicDerivativeOfOrder` contain case splits and casts on their rank
arguments, so direct definitional unfolding at composite rank expressions is
not used. The index helpers `indexOneUnique`, `quotientIndex` and
`indexZeroUnique` are reducible, so that rewriting with them is possible.

## Imports and dependencies

Direct imports:

- `Langlands.Representation.Derivative.RightMixedProductDerivativeFiltrationStatement`
  (target definitions);
- `Langlands.Representation.Derivative.MirabolicProductMinusCompatibilityStatement`
  (4.13(b,c) proposition definitions and `rightPhiProduct`, `rightPhiSubobject`,
  `rightPhiQuotient`);
- `Langlands.Representation.Derivative.MirabolicProductMinusRightBoundary`
  (published proof of `RightPhiBoundary`, used for `r = 0`);
- `Langlands.Representation.Derivative.MixedProductDerivativeStatement`
  (4.14(a) proposition definitions);
- `Langlands.Representation.Derivative.LevelCalculus`
  (published identity/composition and conditional derivative exactness laws,
  reusing `ShortExactFunctorLaws` and the unchanged exactness proposition);
- `Langlands.Representation.Filtration.GluedFamily`.

Mathematically, the only theorem used beyond generic category theory, generic
filtration infrastructure and definitional unfolding is `rightPhiBoundary`.
Everything else enters through the five hypotheses above. The remaining
imported lemmas are bookkeeping about definitions:
`mirabolicDerivativeOfOrder_one` and `mirabolic_rank_eq_of_order`
(`Derivative.Homogeneity`), `rank_eq_of_succ_le` (`Derivative.Iteration`), and
the index lemmas `mem_rightMixedDerivativeIndices`,
`rightMixedDerivativeIndices_left_bound`, `rightMixedDerivativeIndices_right_le`
and `rightMixedDerivativeIndices_rank` from the target statement module.

The identity, composition, mirabolic rank-cast, iterated-minus and derivative
exactness helpers are reused from `LevelCalculus`; the duplicate declarations
in the submitted `RightMixedDerivative` namespace have been removed.
