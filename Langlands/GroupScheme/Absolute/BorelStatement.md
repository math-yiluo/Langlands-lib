# Borel subgroups, maximal tori and parabolic subgroups over a field: statements

Worker 1234.

This module states or imports the main structure theorems about the notions defined in
`Langlands.GroupScheme.Absolute.Borel`: Borel subgroups, parabolic subgroups,
Borel pairs and regular cocharacters. It states theorems only. Each statement is a
`Prop`-valued definition, and none of them is proved here. Statements 1–6 are
general theorems of the literature. Statement 7 is the `GL_N` case, which this
task proves separately.

Throughout, `k : Type u` is a field and `S = Spec (CommRingCat.of k)`. Group
schemes are `Langlands.GroupScheme S`. For a group scheme `G`, write `G(k)` for
the group `Over.mk (𝟙 S) ⟶ G.X` of points of `G` over `S`. A closed subgroup is
a homomorphism `i : H ⟶ G` with the published `IsClosedSubgroup i`, which says
that the underlying morphism of schemes is a closed immersion. Inner
automorphisms are the published `G.innerIso g : G ≅ G` for `g ∈ G(k)`, which acts
on points by `x ↦ g x g⁻¹`. The dynamic subgroup functors `P(χ)` and `U(χ)` of a
cocharacter `χ : 𝔾_m ⟶ G` are the published `Dynamic.parabolic χ` and
`Dynamic.unipotent χ`. They are defined by limits at `0` of the orbit maps
`t ↦ χ(t) g χ(t)⁻¹`. A closed subgroup `i` represents a subgroup functor `F`
(`F.IsRepresentedBy i`, published) when `i` is a monomorphism with
`SubgroupFunctor.range i = F`.

`λ` is a Lean keyword, so cocharacters `𝔾_m ⟶ G` are written `χ`, and
cocharacters of a torus `T` (elements of `cocharacterLattice T`) are written `ν`.

## Sources

Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`
(printed page = PDF page − 16):

- the sentence after Definition 17.6, Example 17.7, Theorem 17.9(b) and Theorem
  17.10, printed p.354 (PDF 370): existence of Borel subgroups, the Borel
  subgroups of `GL_V`, and conjugacy of Borel subgroups and of maximal tori.
  Section 17b, where these appear, assumes that `G` is a connected group
  variety over an algebraically closed field.
- Theorem 17.48, printed p.367 (PDF 383): the normalizer theorem.
- Definition 21.26, Proposition 21.29, Proposition 21.31 and Theorem 21.32,
  printed pp.433–434 (PDF 449–450): regular cocharacters, `P(λ)` for regular
  `λ` is a Borel subgroup, Weyl chambers, and Borel subgroups containing `T`.
  Section 21d, where these appear, assumes that `(G, T)` is a split reductive
  group over `k`.
- Theorem 25.1, printed p.544 (PDF 560): the parabolic subgroups of a reductive
  group are the `P(λ)`.

Conrad, Gabber, Prasad, *Pseudo-reductive groups*, 2nd ed. (2015), source ID
`conrad-gabber-prasad-2015-pseudo-reductive`, Proposition 2.1.8(3), printed
p.53 (PDF 79): the opposite open cell.

Conrad, *Reductive group schemes* (2014), source ID
`conrad-2014-reductive-group-schemes`, Theorem 4.1.7(4), pp.112–113 (PDF
112–113): the opposite open cell for smooth affine groups.

## 1. `BorelConjugacyStatement`

For every field `k` with `IsAlgClosed k` and every group scheme `G` over `S`
with `Smooth G.X.hom`, `IsAffineHom G.X.hom` and `ConnectedSpace G.X.left`:

- there are a group scheme `B` and a homomorphism `i : B ⟶ G` with
  `IsBorelSubgroup i`;
- for any `i : B ⟶ G` and `i' : B' ⟶ G` with `IsBorelSubgroup i` and
  `IsBorelSubgroup i'`, there are `g ∈ G(k)` and an isomorphism `φ : B ≅ B'`
  with `i ≫ (G.innerIso g).hom = φ.hom ≫ i'`.

Source: Milne, Theorem 17.9(b): any two Borel subgroups of `G` are conjugate by
an element of `G(k)`. Existence is the remark after Definition 17.6: every
connected solvable subgroup variety of largest possible dimension is a Borel
subgroup.

**Derived.** Milne states conjugacy as an equality `B' = gBg⁻¹` of
subgroups. Here closed subgroups are homomorphisms, so conjugacy says that the
composite of `i` with the inner automorphism by `g` agrees with `i'` up to an
isomorphism `φ` of the sources.

## 2. `MaximalTorusConjugacyStatement`

For every field `k` with `IsAlgClosed k`, every `G` as in statement 1, all
commutative group schemes `T` and `T'` over `S`, and all `j : T.toGrp ⟶ G` and
`j' : T'.toGrp ⟶ G` with `IsMaximalTorus j` and `IsMaximalTorus j'` (published),
there are `g ∈ G(k)` and an isomorphism `φ : T ≅ T'` of commutative group schemes
with `j ≫ (G.innerIso g).hom = CommGroupScheme.groupHom φ.hom ≫ j'`.

Source: Milne, Theorem 17.10: any two maximal tori in `G` are conjugate by an
element of `G(k)`. **Derived**: the isomorphism form of conjugacy, as in
statement 1.

## 3. `BorelNormalizerStatement`

For every field `k` with `IsAlgClosed k`, every `G` as in statement 1, and every
`i : B ⟶ G` with `IsBorelSubgroup i`: let `H ⊆ G(k)` be the image of `B(k)`
under `i`, the subgroup `(SubgroupFunctor.range i).carrier (Over.mk (𝟙 S))`.
Then `Subgroup.normalizer H = H` in the group `G(k)`.

Source: Milne, Theorem 17.48: `B = N_G(B)`. **Derived**: this is the `k`-point
form of the theorem, as the contract asks. Milne's statement is an equality of
algebraic subgroups. Over an algebraically closed field, `N_G(B)(k)` consists of
the `g ∈ G(k)` with `gBg⁻¹ = B`. A smooth closed subgroup is determined by its
`k`-points, so `N_G(B)(k)` is the normalizer of `B(k)` in `G(k)`. Milne's
theorem gives `N_G(B)(k) = B(k)`. This derivation is not formalized.

## 4. `ParabolicDynamicStatement`

For every field `k`, every `G` with `IsConnectedReductive G` (published), and
every closed subgroup `i : P ⟶ G`: `IsParabolicSubgroup i` holds if and only if
there is a cocharacter `χ : (Gm S).toGrp ⟶ G`, defined over `k`, with
`SubgroupFunctor.range i = Dynamic.parabolic χ`.

`IsConnectedReductive G` contains smoothness, affineness and connectedness of
`G`, so the standing assumptions hold.

Source: Milne, Theorem 25.1: for a reductive group `G` over `k` and a cocharacter
`λ` of `G`, `P(λ)` is a parabolic subgroup of `G`, and every parabolic subgroup
of `G` is of this form. **Derived**: the range formulation. Milne identifies
subgroups with the `P(λ)`. Here a closed subgroup `i` is identified with `P(χ)`
when its range, the subgroup functor of points factoring through `i`, equals
`Dynamic.parabolic χ`. Parabolicity is the derived definition
`IsParabolicSubgroup` of `Langlands.GroupScheme.Absolute.Borel`, from Milne
Theorem 17.16.

## 5. `RegularCocharacterBorelStatement`

For every field `k`, every `G` with `hG : IsConnectedReductive G`, every
commutative group scheme `T` with `IsSplitTorus T.toGrp` (published), and every
`j : T.toGrp ⟶ G` with `IsMaximalTorus j`, the following three statements hold.
Write `P(ν ≫ j)` for `Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j)`. The
roots `roots j` and regularity need `IsAffineHom G.X.hom`, which is taken from
`hG`.

- For every `ν : cocharacterLattice T` with `IsRegularCocharacter j ν`, every
  closed subgroup `i : B ⟶ G` representing `P(ν ≫ j)` has `IsBorelSubgroup i`.
- For all regular `ν` and `ν'`: `P(ν ≫ j) = P(ν' ≫ j)` if and only if, for
  every `α ∈ roots j`, `0 < latticePairing T α ν ↔ 0 < latticePairing T α ν'`.
- For every `i : B ⟶ G` with `IsBorelSubgroup i` and every `f : T.toGrp ⟶ B`
  with `f ≫ i = j`, there is a regular `ν` such that `i` represents
  `P(ν ≫ j)`.

Sources: Milne, Proposition 21.29 (`P(λ)` is a Borel subgroup containing `T`
for regular `λ`), Proposition 21.31 (`P(λ) = P(λ')` if and only if `λ` and `λ'`
lie in the same Weyl chamber) and Theorem 21.32 (every Borel subgroup containing
`T` is `P(λ)` for some regular `λ`).

**Derived** reformulations:

- *Representability form.* Milne's subgroups `P(λ)` are algebraic subgroups.
  Here the first and third parts speak of closed subgroups representing the
  subgroup functor `P(ν ≫ j)`. The first part is conditional on a representing
  closed subgroup; the representability of `P(χ)` (Conrad, Theorem 4.1.7(1)) is
  a separate result.
- *Same Weyl chamber.* For regular `ν` and `ν'` all pairings with roots are
  nonzero. The Weyl chambers are the connected components of the complement of
  the root hyperplanes, so `ν` and `ν'` lie in the same chamber exactly when
  `⟨α, ν⟩` and `⟨α, ν'⟩` have the same sign for every root `α`. This is how
  Milne's proof of Proposition 21.31 uses the condition. The sign condition is
  written `0 < ⟨α, ν⟩ ↔ 0 < ⟨α, ν'⟩`.
- *Borel subgroups over a non-closed field.* Milne works with Borel subgroups of
  `G_{k̄}`, and `IsBorelSubgroup` asks for maximality among closed subgroups over
  `k`. For split `(G, T)` the two agree on the subgroups in question. If
  `B_{k̄}` is a Borel subgroup of `G_{k̄}` and `B ⊆ B'` with `B'` smooth,
  connected and solvable over `k`, then `B'_{k̄}` is smooth, connected (it has a
  rational point) and solvable, so `B_{k̄} = B'_{k̄}`, and `B = B'` by descent.
  Conversely, let `B` be maximal over `k` and contain `T`. Then `B_{k̄}` lies in
  a Borel subgroup of `G_{k̄}` containing `T_{k̄}`, which is `P(ν)` for a regular
  `ν ∈ X_*(T_{k̄}) = X_*(T)`. Containment of closed subschemes descends, so
  `B ⊆ P(ν)`, and maximality gives `B = P(ν)`. These arguments are not
  formalized.

## 6. `OppositeCellStatement`

The opposite-open-cell statement is imported from
[`OppositeCellStatement`](OppositeCellStatement.md). Its declaration name,
universe, hypotheses and body are unchanged. The separate module lets the
open-cell, connectedness and generic-centralizer proofs be imported without
the classification statements collected here.

## 7. `GeneralLinearBorelStatement`

For every field `k`, every `N : ℕ` and every `e : Fin N → ℤ` with
`StrictAnti e`, write `R = CommRingCat.of k`. Then:

- `IsBorelSubgroup (GeneralLinear.blockParabolicHom (Fin N) R e)`. The published
  block parabolic subgroup scheme of `e` consists of the matrices `g` with
  `g_{ab} = 0` when `e a < e b`. As `e` is strictly decreasing, these are the
  upper triangular matrices.
- `IsBorelPair (GeneralLinear.blockParabolicHom (Fin N) R e)
  (GeneralLinear.diagonalTorus (Fin N) R)`. So the published diagonal torus is a
  maximal torus that factors through the upper triangular subgroup.
- `(Dynamic.parabolic (GeneralLinear.diagonalCocharacter (Fin N) R e)).IsRepresentedBy
  (GeneralLinear.blockParabolicHom (Fin N) R e)`. The published diagonal
  cocharacter of `e` is `t ↦ diag(t^{e 0}, …, t^{e (N-1)})`.
- `IsRegularCocharacter (GeneralLinear.diagonalTorus (Fin N) R) ν` for
  `ν = (splitTorus.cocharacterLatticeEquiv k (ULift (Fin N))).symm
  (fun a => e a.down)`, the cocharacter of the diagonal torus with coordinates
  `e`.

Sources: Milne, Example 17.7 (the Borel subgroups of `GL_V` are the conjugates
of the upper triangular group `T_n`) and Proposition 21.29 (`P(λ)` is a Borel
subgroup for regular `λ`). **Derived**: Milne's Example 17.7 is over an
algebraically closed field. Over a general `k`, the statement uses
`IsBorelSubgroup`, with maximality over `k`, and the representability form of
`P(λ)`.
