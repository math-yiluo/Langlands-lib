# Big-cell gluing from commutator relations of the positive cell factors

This internal derived criterion sharpens the gluing criterion of
`Langlands.GroupScheme.Reductive.LocalSplitPositiveLawGluing`. That criterion asks
that every law `P(w) · u_a(c) = P(z)` of the positive cell factor of `G` hold in `H`.
Here `P(w) = ∏ₖ u_{pos k}(w k)` is the ordered product of the positive cell factors
and `a` is a simple root. This module replaces that hypothesis with one about
commutators of two positive cell factors only. For every pair of positions `k < l`,
each expression of the commutator of the factors at `k` and `l` as a product of
positive cell factors of `G` must also hold in `H`. The positive roots are
enumerated by increasing height. The base ring is arbitrary and may have
nilpotents. The negative simple relations remain as a hypothesis, unchanged.

The module also proves, without hypotheses on `H`, where such commutators are
supported. Over every commutative ring, the commutator of the positive cell factors
at positions `k` and `l` has zero coordinates at every position `p` with
`⟨ch (pos p), ν⟩ < ⟨ch (pos k), ν⟩ + ⟨ch (pos l), ν⟩`. This is the integral form of
the statement that the commutator of two positive root groups lies in the product of
the root groups of the roots `i·α + j·β` with `i, j ≥ 1`.

## Statement

`LocalSplitCommutatorLawIsomorphismStatement.{u}` concerns:

- a commutative ring `R`, a finite type `I` with decidable equality, and a type `J`,
  all in universe `u`;
- reductive group schemes `G`, `H` over `Spec R`, with instance binders `IsAffineHom`
  for their structure morphisms;
- coordinate split tori `i : T_I → G` and `i' : T_I → H`, both maximal on every
  residue-field fibre (`IsFibrewiseMaximalTorus`);
- one coordinate root datum `P : RootDatum J (I → ℤ) (I → ℤ)` that is a fibrewise
  root datum (`IsFibrewiseRootDatumOf`) for `i` in `G` and for `i'` in `H`;
- a base `b` of `P` and a choice `W` of a `SimpleWord P b α` for every root `α`, such
  that for every simple root `a` the word `W a` has starting root `a` and the empty
  list of reflections;
- families `u : J → (𝔾ₐ ⟶ G)` and `u' : J → (𝔾ₐ ⟶ H)`. For every simple root `a`,
  `u a` is a root parametrization of `i` for `P.root a`, and `rootWeylPoint P u a`
  is a Weyl point of `i` acting by `P.reflection a`. The same holds for `u'` and
  `i'`;
- enumerations `neg : Fin m ≃ {α // ¬ b.IsPos α}` and `pos : Fin n ≃ {α // b.IsPos α}`
  of the non-positive and the positive roots. The heights `b.height (pos p)` must be
  monotone in `p`.

Write `u_W = weylFamily P W u` and `u'_W = weylFamily P W u'`. Let
`Ω = cellMap i u_W neg pos` and `Ω' = cellMap i' u'_W neg pos`. For a family `v`, a test
object `Z`, positions `k`, `l` and global functions `x`, `y` on `Z`, let
`posComm v pos Z k l x y = (v_k(x) · v_l(y))⁻¹ · (v_l(y) · v_k(x))`, where `v_k = v (pos k)`.
The two hypotheses concern every commutative local ring `A : Type u` with separably
closed residue field and every structure map `s : Spec A → Spec R`:

- **commutator relations:** for all positions `k < l`, all global functions `x`, `y`
  and all coordinate vectors `e : Fin n → Γ(Spec A, ⊤)`, if
  `posComm u_W pos (Spec A) k l x y = P(e)` in `G`, then
  `posComm u'_W pos (Spec A) k l x y = P'(e)` in `H`. Here `P` and `P'` are the ordered
  products of the positive cell factors of `u_W` and `u'_W`;
- **negative simple relations:** for every simple root `a` and all cell-source points
  `x`, `y` over `s`, if `Ω(x) · u_{-a}(-1) = Ω(y)`, then `Ω'(x) · u'_{-a}(-1) = Ω'(y)`,
  where `u_{-a}` means `u (P.reflectionPerm a a)`.

The conclusion is an isomorphism `ψ : G ≅ H` with `Ω ≫ ψ = Ω'`. The module proves
this proposition at full universe as `localSplitCommutatorLawIsomorphism`.

The namespace `LocalSplitCell` also contains:

- `prod_ofFn_split`: in a monoid, `∏ₗ f l` splits at a position `k` as
  `(∏_{l<k} f l) · f k · (∏_{l>k} f l)`, with the omitted factors replaced by `1`;
- `PosGood u u' pos Z g h`: right multiplication by `g` keeps products `P(w)` over `Z`
  in the form `P(z)`, and every law `P(w) · g = P(z)` of `G` gives
  `P'(w) · h = P'(z)` in `H`. `PosGood.one` (given uniqueness of the coordinates in
  `G`), `PosGood.mul` and `PosGood.prod_ofFn` show closure under products;
- `posComm` and `orderedProduct_mul_rootPoint_eq`: the decomposition
  `P(w) · u_k(x) = P(v) · ∏_{l>k} (u_l(w l) · posComm k l x (w l))`, where `v` agrees
  with `w` before `k`, equals `w k + x` at `k`, and is zero after `k`;
- `posGood_rootPoint`: over a fixed test object, let the coordinates in `G` be
  unique, let right multiplication by every positive cell factor preserve the form
  `P(z)`, and for `k < l` let the commutator coordinates vanish up to position `k`
  and transfer to `H`. Then `(u_k(x), u'_k(x))` is positive-good for every position
  `k` and every `x`;
- `exists_eq_X_mul_C_X_mul`: a polynomial in `B[S][T]` vanishing at `T = 0` and at
  `S = 0` is divisible by `S · T`;
- `comp_posComm`, `posComm_zero_left`, `posComm_zero_right`,
  `torus_mul_posComm_mul_inv`, `exists_orderedProduct_mul_rootPoint_eq_pos_of_ring`,
  `exists_posComm_eq_ring`, `posComm_specHom` and `coord_eq_of_orderedProduct_eq`:
  naturality of commutators, their triviality when one argument is zero, their
  conjugation by torus points, and their coordinates over rings;
- `posComm_coord_eq_zero`: the support statement above, for any family with a torus
  equivariance, any enumerations whose cell map is an open immersion, and a
  cocharacter `ν` pairing negatively with the characters of `neg` and positively
  with those of `pos`. `posComm_coord_eq_zero_of_monotone` specializes it to
  positions `p ≤ k` when the pairings with `ν` are monotone along `pos`;
- `CommutatorRelations` and `positiveLawRelations_of_commutatorRelations`: the
  commutator hypothesis above implies the hypothesis `PositiveLawRelations` of the
  imported `LocalSplitPositiveLawGluing`.

## Proof

**Laws from commutators.** Fix a test object `Z` and argue by downward induction on
the position `k`. By `prod_ofFn_split`, `P(w) = A · u_k(w k) · T` with `A` the product
before `k` and `T` the product after `k`. Then
`P(w) · u_k(x) = A · u_k(w k + x) · u_k(x)⁻¹ T u_k(x)`. The conjugate `u_k(x)⁻¹ T u_k(x)`
is the product over `l > k` of `u_k(x)⁻¹ u_l(w l) u_k(x) = u_l(w l) · posComm k l x (w l)`.
Since `u_l(0) = 1` (imported `rootPoint_zero`), `A · u_k(w k + x) = P(v)`. Each commutator
is a product of root points, so by the existence hypothesis it equals `P(e)` for some
`e` (`exists_posComm_eq`). The commutator hypothesis gives the same `e` in `H`, and
the support hypothesis gives `e p = 0` for `p ≤ k`. Hence every factor of
`posComm k l x (w l) = ∏_p u_p(e p)` is either `1` or a factor at a position after `k`.
By induction these factors are positive-good, and by closure under products so are
`posComm` and the whole product over `l > k`. The same decomposition holds in `H`
with the same coordinates. So a law `P(w) · u_k(x) = P(z)` in `G` becomes
`P(v) · X = P(z)`, transfers to `P'(v) · X' = P'(z)`, and gives
`P'(w) · u'_k(x) = P'(z)`.

**Support of commutators.** Let `dk`, `dl`, `dp` be the pairings of `ch (pos k)`,
`ch (pos l)`, `ch (pos p)` with `ν`, and assume `dp < dk + dl`. Write `x`, `y` and the
coordinates `e` of the commutator over `Spec B` as elements of `B`.

1. Over `B[S][T]`, the commutator of `u_k(S x)` and `u_l(T y)` has coordinates
   `h q` (`exists_posComm_eq_ring`, from the imported
   `exists_orderedProduct_eq_pos_of_ring`).
2. At `T = 0` and at `S = 0` the commutator is `1 = P(0)`. Pull back along the ring
   maps `T ↦ 0` and `S ↦ 0` (`posComm_specHom`) and compare coordinates
   (`coord_eq_of_orderedProduct_eq`). So `h p` vanishes on both axes and
   `h p = T · S · r` (`exists_eq_X_mul_C_X_mul`, from Mathlib's
   `Polynomial.ker_mapRingHom` and `Polynomial.ker_evalRingHom`).
3. Pull back along `σ : B[S][T] → B[U]`, `S ↦ U^dk`, `T ↦ U^dl`. The commutator of
   `u_k(U^dk x)` and `u_l(U^dl y)` has coordinates `σ (h q)`, and
   `σ (h p) = U^(dl + dk) · σ r`.
4. Over the Laurent polynomials `B[U, U⁻¹]`, `U` is a unit, and `ν(U)` is the torus
   point with coordinates `U^(ν j)`. Its characters are `U^dk`, `U^dl` and `U^dp`
   (imported `torusChar_cocharPoint_of_eq`). Conjugating the commutator of `u_k(x)`
   and `u_l(y)` by `ν(U)` gives the commutator of `u_k(U^dk x)` and `u_l(U^dl y)`
   (`torus_mul_posComm_mul_inv`). Conjugating `P(e)` multiplies its `p`-th coordinate
   by `U^dp` (imported `torus_mul_orderedProduct_mul_inv`). Comparing coordinates and
   using injectivity of Mathlib's `Polynomial.toLaurent` gives
   `σ (h p) = U^dp · e p` in `B[U]`.
5. The coefficient of `U^dp` is `e p` on the right and `0` on the left, since
   `dp < dl + dk`. So `e p = 0`.

**Weyl families.** By the imported `isRootParametrization_weylFamily`, the Weyl family
`u_W` consists of root parametrizations for all roots. So it is torus equivariant with
characters `P.root α`, and its cell map is an open immersion (imported
`LocalSplitBigCell.isOpenImmersion_cellMap`). The imported
`exists_coPairing_eq_height` gives `d > 0` and `ν` with `⟨P.root α, ν⟩ = d · height α`.
So `ν` is negative on the non-positive roots and positive on the positive ones, and
monotone heights give monotone pairings. Uniqueness of coordinates is the imported
`orderedProduct_pos_injective`, and existence is the imported local
`exists_orderedProduct_mul_rootPoint_eq_pos`. For a simple root `a`, the trivial word
gives `u_W a = u a`, and `a = pos k` for `k = pos.symm a`. So `posGood_rootPoint` gives
`PositiveLawRelations`. The proposition follows from the imported
`localSplitPositiveLawIsomorphism`.

## Provenance and scope

This is an internal derived criterion for the Isomorphism Theorem over an arbitrary
local ring. It follows the strategy of the proofs of the Isomorphism and Isogeny
Theorems. There, the group law of the product of the positive root groups is
described by commutation relations, and the structure constants of these relations
are shown to depend only on the pinned root datum (B. Conrad, *Reductive group
schemes*, in *Autour des schémas en groupes*, Panoramas et Synthèses 42–43, 2014,
Proposition 5.1.14, Proposition 5.1.16 and Lemma 6.2.8; SGA 3, Exp. XXIII,
3.1–3.4). The support statement is an integral form of the shape of the commutator
formula (Conrad, (5.1.5) in Proposition 5.1.14). There it is proved over a general
base using the closed subgroups `U_Ψ` and weight considerations. Here it is proved
directly by the torus-scaling argument above. The induction deriving the laws from
commutators is likewise an explicit construction of this module.

The criterion does not verify the commutator relations or the negative simple
relations for any pair of groups. Verifying the commutator relations amounts to
showing that the structure constants of the two Weyl families agree (Conrad,
Lemma 6.2.8), which this module does not do. The criterion does not construct
Weyl-normalized simple-root data, and it does not prove the local split Isomorphism
Theorem.
