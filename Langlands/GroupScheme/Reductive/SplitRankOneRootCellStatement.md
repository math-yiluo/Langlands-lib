# Root groups, open cell and the rank-one relation

Author: Worker 1388.

Module `Langlands.GroupScheme.Reductive.SplitRankOneRootCellStatement`, declaration
`Langlands.GroupScheme.SplitRankOneRootCellStatement` (a `Prop`, universe `u`). The
module states the proposition and proves nothing. Its proof is open.

## The statement

Let `k : Type u` be a field, `G` a group scheme over `Spec k` with
`IsConnectedReductive G`, and `T` a commutative group scheme over `Spec k` with
`IsSplitTorus T.toGrp`. Let `i : T.toGrp ⟶ G` satisfy `IsMaximalTorus i`, and let
`P : RootDatum J (characterLattice T) (cocharacterLattice T)` satisfy
`IsRootDatumOf i P`. Assume that no two roots `α, β ∈ roots i` are linearly
independent over `ℤ`, so `G` has semisimple rank at most one. Then for every `r : J`,
with `α = P.root r` and `α^∨ = P.coroot r`, there are homomorphisms

`xp xm : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G`

from the additive group `𝔾ₐ` such that the following five clauses hold. In them `Z` is
any object of `Over (Spec k)`, points are morphisms in `Over (Spec k)`, and the
coordinate of a point `a : Z ⟶ 𝔾ₐ` is
`(VectorGroup.coordinates (CommRingCat.of k) 1 Z a).toAdd 0 ∈ Γ(Z.left, ⊤)`, written `X`
for `a` and `Y` for `b` below.

1. **Weight `α` on `xp`.** For all points `t : Z ⟶ T.X` and `a : Z ⟶ 𝔾ₐ`,
   `(t ≫ i) * (a ≫ xp) * (t ≫ i)⁻¹ = VectorGroup.weightPointAction α Z t a ≫ xp`. The
   right side is `xp` applied to the point with coordinate `α(t) X`.
2. **Weight `-α` on `xm`.** The same with `xm` and `-α`.
3. **Open cell.** The underlying morphism of schemes of
   `Dynamic.tripleCellMultiplication xm i xp`, the map `(Y, t, X) ↦ xm(Y) t xp(X)` from
   `𝔾ₐ × T × 𝔾ₐ` to `G`, is an open immersion. Its image is the open cell `Ω`.
4. **When `xp(X) xm(Y)` lies in the cell.** For all points `a b : Z ⟶ 𝔾ₐ`, some
   `c : Z ⟶ 𝔾ₐ × T × 𝔾ₐ` satisfies `c ≫ tripleCellMultiplication = xp(a) xm(b)` if and
   only if `1 + X Y` is a unit of `Γ(Z.left, ⊤)`.
5. **The rank-one relation.** For all points `a b a' b' : Z ⟶ 𝔾ₐ` and every unit `u`
   with `u = 1 + X Y`, if the coordinates of `a'` and `b'` are `u⁻¹ X` and `u⁻¹ Y`, then
   `xp(a) xm(b) = xm(b') · α^∨(u) · xp(a')`. Here `α^∨(u)` is the point
   `(Gm.pointsEquiv _ Z).symm u ≫ (CommGroupScheme.groupHom α^∨).hom.hom ≫ i.hom.hom`.

Clauses 3 and 4 refer to the same morphism. Lean writes `xp.hom.hom` and `i.hom.hom`
for the underlying morphisms of `xp` and `i`.

## Source

Brian Conrad, *Reductive group schemes* (Autour des schémas en groupes, 2014;
literature `conrad-2014-reductive-group-schemes`), over the base `S = Spec k`:

- **Theorem 4.1.4** (PDF p.110): for a split maximal torus `T` and a root `a` there is a
  unique homomorphism `exp_a : W(g_a) → G` that induces the canonical inclusion
  `g_a ↪ g` on Lie algebras and intertwines conjugation by `T` on `G` with `a`-scaling
  on `W(g_a)`. Moreover `(X', t, X) ↦ exp_{-a}(X') t exp_a(X)` is an isomorphism from
  `W(g_{-a}) × T × W(g_a)` onto an open subscheme `Ω_a` of `Z_G(T_a)`. The condition
  on Lie algebras is needed for uniqueness: rescaling the coordinate of `W(g_a)` gives
  other `T`-equivariant homomorphisms, for example `x ↦ [[1, cx], [0, 1]]` into `SL₂`
  for any nonzero constant `c`. The proposition below only asks for existence, so it
  does not fix this normalization (see "What is left out").
- **Remark 4.2.4** (PDF p.119): a parametrization `p_a : 𝔾ₐ ≃ U_a` intertwining the
  `T`-action with `t.x = a(t) x` is the same as a trivializing section of `g_a`.
- **Theorem 4.2.6** (PDF p.120-121), with the paragraph on linked parametrizations
  after it (PDF p.121): if `G` has semisimple rank one, then
  `exp_a(X) exp_{-a}(Y)` lies in `Ω_a` if and only if `1 + XY` is a unit, and then
  `exp_a(X) exp_{-a}(Y) = exp_{-a}(Y/(1+XY)) a^∨(1+XY) exp_a(X/(1+XY))` (4.2.1).
  This is SGA 3, Exp. XX, 2.1. For `SL₂` it is the calculation of Example 4.2.5
  (PDF p.119-120).

The proposition takes `xp = p_a` and `xm = p_{-a}` for linked parametrizations. They
exist because `g_{±a}` are one-dimensional over the field `k`, and for linked
parametrizations the pairing `XY` of Theorem 4.2.6 is the product of coordinates.
Clauses 1-2 are the `T`-equivariance in Theorem 4.1.4 and Remark 4.2.4. Clause 3 is the
open immersion (4.1.1), and clauses 4-5 are parts 1 and 2 of Theorem 4.2.6.

Three points of the translation need comment.

- **The cell is open in `G`.** Conrad's `Ω_a` is open in `Z_G(T_a)`. If `roots i` is
  nonempty, the hypothesis leaves only the roots `±a` (the root system of a reductive
  group is reduced), so `G` has semisimple rank one. Then `Z_G(T_a) = G`, which is the
  reduction at the start of the proof of Theorem 4.1.4 (PDF p.116). If `roots i` is
  empty, then `J` is empty, because `Set.range P.root = roots i`, and the statement holds
  trivially.
- **The coroot is `P.coroot r`.** `IsRootDatumOf i P` asks that `P.reflection r` be
  induced by a `k`-point normalizing `T`. That reflection sends `α` to `-α`, so this
  point acts nontrivially on `T`. In semisimple rank one the Weyl group has order two,
  and its nontrivial element is Conrad's reflection `s_a : χ ↦ χ - ⟨χ, a^∨⟩ a`
  (Corollary 5.1.11, PDF p.142, realizes it by `n_a = w_a(X_a)`). So
  `⟨χ, P.coroot r⟩ α = ⟨χ, a^∨⟩ α` for every character `χ`. The pairing is perfect, so
  `P.coroot r` is the coroot `a^∨` of Theorem 4.2.6.
- **What is left out.** The proposition omits the uniqueness assertions and the
  Lie-algebra normalization of `exp_a`, the closed immersion and semidirect-product
  claims of Theorem 4.1.4, and the identities
  `a ∘ a^∨ = 2` and perfect duality of Theorem 4.2.6.

## Use

`Reductive.SplitRankOneRootCellReduction` proves that this proposition implies
`SplitRankOneCommonTorusIsomorphismStatement`. The proposition and its reduction were
written for task `de20c777-ce5f-4764-be9b-a09f5e0aca68`.
