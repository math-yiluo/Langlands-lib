# Orbit-dimension strata of unipotent actions and their quotient spaces

Author: Worker 105.

`UnipotentOrbitQuotientStatement` states Example 5.5 of Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), printed p.16. The
registered source is `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. The module only
states the example's claims and contains no proof. The topological claim is false as
Conrad states it. Statement (3) therefore assumes that the quotient is locally
separated; the section "Correction" below gives a counterexample to the uncorrected
claim.

Conrad's Example 5.5 reads, in part: "Let `G` be a unipotent algebraic group over a
henselian valued field `k` of characteristic 0 (such as a `p`-adic field; i.e., a finite
extension of `Q_p`) and `V` a reduced `k`-scheme of finite type equipped with a
`G`-action […]. For `d ≥ 0` let `V_d ⊂ V` denote the reduced locally closed subscheme of
points whose `G`-orbit has dimension `d`. (This is locally closed due to applying
semicontinuity of fiber dimension to the action map `G × V → V`.) The universal action
map `G × V_d → V_d × V_d` defined by `(g, v) ↦ (g.v, v)` is flat over the diagonal […].
Thus, by [Del2, Prop. 3.11] there is a finitely presented algebraic space `X` over `k`
and a faithfully flat map `V_d → X` that identifies `X` with the fppf sheaf quotient of
`V_d` by its `G`-action, so we denote `X` as `V_d/G`. […] The topological space
`(V_d/G)(k)` is locally Hausdorff and locally compact (and locally totally
disconnected)." Section 5 works throughout with quasi-separated algebraic spaces
(printed p.13).

## Objects

Throughout, `S` is a scheme, `G : GroupScheme S` is a group object in schemes over `S`
(`Langlands/GroupScheme/Basic.lean`), `V : Over S` is a scheme over `S`, and
`a : SchemeAction G V` is an action of `G` on `V` (`Langlands/GroupScheme/SchemeAction.lean`):
a morphism `a.hom : G × V ⟶ V` over `S` satisfying the unit and associativity axioms.
Products are the cartesian products in schemes over `S`, i.e. fibre products over `S`.

- `IsFlat f`, for a transformation `f : F ⟶ G` of presheaves on schemes over `S`, says
  that `f` is representable by actual schemes and every base change of `f` along a
  scheme's point is a flat morphism of schemes. It is the flat analogue of `IsEtale` and
  `IsSurjective` in `Langlands/AlgebraicGeometry/AlgebraicSpace/Basic.lean`, defined in
  the same way through Mathlib's `MorphismProperty.relative`.
- The action graph is `lift a.hom (snd G.X V) : G × V ⟶ V × V`, the morphism
  `(g, v) ↦ (g.v, v)` of the source. Its base change along the diagonal
  `lift (𝟙 V) (𝟙 V) : V ⟶ V × V` is the stabilizer scheme
  `{(g, v) | g.v = v}`, with the projection `σ` to `V`.
- `IsStabilizerFlat a` says that `σ` is flat. This is Conrad's "flat over the diagonal":
  the base change of the action graph along the diagonal is flat over `V`.
- `HasOrbitDimension a v d`, for a point `v` of `V` and `d : ℕ`, says that the
  topological Krull dimension of `G` equals `d` plus the topological Krull dimension of
  the fibre `σ⁻¹(v)` (Mathlib's `Scheme.Hom.fiber`), the stabilizer of `v` as a scheme
  over the residue field `κ(v)`.
- `IsFppfActionQuotient a π`, for an fppf sheaf `Q` and a map
  `π : h_V ⟶ Q` of fppf sheaves from the sheaf represented by `V`, says that `π`
  coequalizes the two maps `h_{G × V} ⇉ h_V` induced by `a.hom` and the projection, and
  that the resulting cofork is a colimit in fppf sheaves. Since `h_{G × V} = h_G × h_V`
  and `G` is a group, the presheaf coequalizer is `T ↦ V(T)/G(T)`, so `Q` is the fppf
  sheafification of the presheaf quotient: Conrad's "fppf sheaf quotient of `V_d` by
  its `G`-action".
- For a nontrivially normed field `K` (Conrad's valued field `k`):
  `IsUnipotentAlgebraicGroup K G` says that `G → Spec K` is affine and locally of finite
  type and that `G` is unipotent in the sense of `IsUnipotent`
  (`Langlands/GroupScheme/Reductive/Basic.lean`: every nonzero finite-dimensional
  matrix representation has a nonzero fixed vector). This is the definition recalled in
  J. S. Milne, *Algebraic Groups* (2022 corrected reprint, source
  `milne-2022-algebraic-groups`, SHA-256
  `f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`), Chapter 14,
  printed p.280 (from 6.45), where algebraic groups are affine (Chapter 14 opening,
  printed p.279: "Recall that all algebraic groups are affine over a base field `k`").
  The Library's `IsUnipotent` does not include affineness, so it is assumed
  separately.
- `IsReducedFiniteType K V` says that `V` is reduced and that `V → Spec K` is locally of
  finite type and quasi-compact, i.e. of finite type.
- `IsHenselianValuedField K` (`HenselianEtalePointStatement.lean`) is Conrad's
  henselian condition: the absolute value of `K` extends uniquely to every algebraic
  extension.
- `HasLocallyHausdorffRationalPoints K X`, for an algebraic space `X` over `Spec K`,
  equips `X(K)` (`RingPoints K X K`) with `etaleChartTopology K X`, the topology of
  Conrad's Proposition 5.4 (`EtaleChartTopology.lean`), and says: every `x ∈ X(K)` has
  an open neighbourhood `W` that is Hausdorff, locally compact if `K` is locally
  compact, and totally disconnected if the norm of `K` is ultrametric
  (Mathlib's `IsUltrametricDist`).
- `IsLocallySeparated X` (`HenselianSpacePointTopologyStatement.lean`, introduced for
  the corrected Proposition 5.4) says that the diagonal `X → X × X` is a representable
  immersion. This is the Stacks Project's local separatedness (source
  `stacks-algebraic-spaces-chapter-ed88ff78-2026-11-05`, SHA-256
  `49a75fa582cbeafadb9e1fbbdce130e5b8971322a2c0048d777e8a97f0d0fcf5`, Algebraic
  Spaces, Definition 13.2, Tag 02X5, part (2): "We say `F` is locally separated over
  `S` if `∆` is an immersion").
- `IsQuasiSeparated X` (`RingPoints.lean`) and `FinitePresentationOverRing K X`
  (`SpaceWeilRestriction.lean`, an étale surjective atlas locally of finite presentation
  and quasi-compact over `Spec K`) together say that `X` is quasi-separated and finitely
  presented over `K`, as explained in `SpaceWeilRestriction.md`.

## The statements

All three statements assume: `K : Type u` is a nontrivially normed field with
`IsHenselianValuedField K` and characteristic zero, `G` is a group scheme over `Spec K`
with `IsUnipotentAlgebraicGroup K G`, `V` is a scheme over `Spec K` with
`IsReducedFiniteType K V`, `a : SchemeAction G V` and `d : ℕ`.

1. `UnipotentOrbitStratumLocallyClosedStatement`: the set
   `{v | HasOrbitDimension a v d}` of points of `V` whose orbit has dimension `d` is
   locally closed (Mathlib's `IsLocallyClosed`).
2. `UnipotentOrbitStratumQuotientStatement`: let `Z` be a reduced scheme over `Spec K`
   and `i : Z ⟶ V` an immersion whose image is `{v | HasOrbitDimension a v d}`. Then
   there is an action `b` of `G` on `Z` with `b.hom ≫ i = (G ◁ i) ≫ a.hom` (the action
   restricts to `Z` and `i` is equivariant) such that `IsStabilizerFlat b`, and there are
   an algebraic space `X` over `Spec K` and a map `π : h_Z ⟶ X` of fppf sheaves with
   `IsFppfActionQuotient b π`, `IsQuasiSeparated X`, `FinitePresentationOverRing K X`,
   `IsFlat π` and `IsSurjective π`.
3. `UnipotentOrbitQuotientPointTopologyStatement`: with `Z` and `i` as in (2), for every
   action `b` of `G` on `Z` making `i` equivariant, every algebraic space `X` over
   `Spec K` and every `π : h_Z ⟶ X` with `IsFppfActionQuotient b π`, if `X` is locally
   separated (`IsLocallySeparated X`), then the rational points satisfy
   `HasLocallyHausdorffRationalPoints K X`.

`UnipotentOrbitQuotientStatement` is the conjunction of (1), (2) and (3).

## Relation to the source and derived content

- **The stratum `V_d`.** Conrad's `V_d` is "the reduced locally closed subscheme of
  points whose `G`-orbit has dimension `d`". The orbit dimension of a point is not
  defined in the Library, so it is formalized through the stabilizer: for a point `v`
  with residue field `κ(v)`, the orbit of the corresponding `κ(v)`-point under
  `G_{κ(v)}` has dimension `dim G − dim Stab_v`. This is derived from Milne,
  *Algebraic Groups*: for a rational point `o`, the orbit map of a reduced group (here
  `G` is smooth, being an affine algebraic group in characteristic 0, Cartier's
  Theorem 3.23, printed p.71) is faithfully flat onto the orbit `O_o`
  (Proposition 7.4(b), printed p.139); when the scheme acted on is separated the orbit
  is the quotient `G/G_o` by the stabilizer `G_o` (Proposition 7.12, printed p.142; the
  quotient exists by Theorem 5.28, printed p.105), and
  `dim G = dim G_o + dim G/G_o` (Proposition 5.23, printed p.104). Without
  separatedness the same count follows from the faithfully flat orbit map
  `G → O_o`, whose fibres are torsors under `G_o`, by the dimension formula for flat
  morphisms of schemes of finite type over a field; this extension is not taken from a
  cited source and is not formalized. Dimensions of schemes of finite type over a field
  are invariant under field extension, so `dim G_{κ(v)} = dim G`. Dimensions are
  Mathlib's `topologicalKrullDim` with values in `WithBot ℕ∞`.
- **The subscheme structure.** Conrad uses the reduced subscheme structure on the
  locally closed set. Statements (2) and (3) quantify over every reduced `Z` with an
  immersion `i : Z ⟶ V` onto the stratum; any two such are uniquely isomorphic over
  `V`, so this is the source's `V_d` without choosing a construction.
- **The restricted action.** Conrad writes the action map `G × V_d → V_d × V_d` without
  saying that the action restricts; statement (2) asserts the restricted action `b`
  with `i` equivariant.
- **Flatness over the diagonal.** Formalized as flatness of the stabilizer scheme over
  `Z` (`IsStabilizerFlat b`), the base change of the action graph along the diagonal.
- **The quotient.** Conrad's "finitely presented algebraic space `X` over `k`" is read
  with his quasi-separatedness convention, so (2) asserts both `IsQuasiSeparated X`
  and `FinitePresentationOverRing K X`. "Faithfully flat" is `IsFlat π ∧ IsSurjective π`
  for the representable map `π` (algebraic spaces have representable diagonal, so maps
  from schemes are representable). "Identifies `X` with the fppf sheaf quotient" is
  `IsFppfActionQuotient b π`.
- **The topology, corrected.** Conrad asserts that `(V_d/G)(k)` is locally Hausdorff,
  locally compact and locally totally disconnected. For a henselian valued field that is
  not locally compact (for example the algebraic closure of `Q` in `Q_p`), or that is
  archimedean (`R` and `C` are henselian), the trivial group acting on the affine line
  gives `V_0/G = A^1` with `(V_0/G)(k) = k`, which is then not locally compact,
  respectively not totally disconnected. Statement (3) therefore asserts local
  compactness when `K` is locally compact and local total disconnectedness when the norm
  of `K` is ultrametric, matching Conrad's parenthetical "such as a `p`-adic field".
  Statement (3) is stated for every fppf quotient `X`; quotients are unique up to
  unique isomorphism of fppf sheaves. All three properties are asserted only for
  locally separated `X`; see the next section.
- Also derived here: the names of all declarations, and the conjunction.

## Correction: the quotient must be locally separated

Conrad's assertion that `(V_d/G)(k)` is locally Hausdorff is false in general.
Statement (3) assumes `IsLocallySeparated X`. The same hypothesis corrects Conrad's
Proposition 5.4; see `HenselianSpacePointTopologyStatement.md`.

**Why the corrected claim holds.** Conrad gives no argument for the topological claim.
It rests on Proposition 5.4, whose corrected form covers quasi-separated, locally
separated spaces locally of finite type. By (2), every fppf quotient `X` is
isomorphic to a quasi-separated space of finite presentation. For such `X`, if it is
also locally separated, the corrected Proposition 5.4 makes every étale chart
`U(K) → X(K)` from a scheme a local homeomorphism. Every `K`-point of `X` lifts to
`U(K)` for some affine scheme `U` of finite type étale over `X` (Conrad, printed p.15,
citing Knutson II, Thm. 6.4). So every point of `X(K)` has an open neighbourhood
homeomorphic to an open subset of `U(K)`, which is a closed subset of some `K^n`. Such a
set is Hausdorff, locally compact when `K` is, and totally disconnected when the norm
is ultrametric. This derivation is not formalized here.

**Counterexample to the uncorrected claim.** The following construction was made for
this module; it is not taken from a source. It is a variant of the Stacks Project's
Example 14.1 (Tag 02Z1, same source as above), which glues `x` to `-x` on the
punctured affine line. Let `K` be a henselian valued field of characteristic zero, for
example `Q_p` or `R`.

1. *The space `X₂`.* Let `U = A²_K` with coordinates `(x, y)`, let `W = {xy ≠ 0}`, and
   let `ι(x, y) = (-x, y)`, a free involution of `W`. Let `R = Δ ⊔ Γ → U × U`, where `Δ`
   is the diagonal and `Γ = {(w, ι(w)) | w ∈ W}`. Both projections `R → U` are étale and
   `R` is an equivalence relation. So `X₂ = U/R` is an algebraic space with étale
   surjection `φ : U → X₂` and `U ×_{X₂} U = R` (Stacks Theorem 10.5, Tag 02WW; source
   `stacks-etale-equivalence-relations-2026-11-01`, directory SHA-256
   `df1ecbfa63c5e31cf736d9ea79dd262976c3098fd9b36f2dd32668d44bf75420`). As in
   Example 14.1, `R` is quasi-compact (two affine components), so `X₂` is
   quasi-separated, and `X₂` is of finite type over `K`. Informally, `X₂` is the plane
   folded by `x ↦ -x` away from the two axes. The `x`-axis is not folded, so its two
   halves become non-separated from each other.
2. *`X₂(K)` is not locally Hausdorff.* The chart `φ` is an étale map from a scheme of
   finite type, so `φ_K : K² → X₂(K)` is continuous for `etaleChartTopology`. Fix
   `x₀ ∈ K` with `x₀ ≠ 0`, and let `p± = φ(±x₀, 0)`. These two points are distinct. A
   common image would give a `K`-point of `U ×_{X₂} U = R` over
   `((x₀, 0), (-x₀, 0))`, but this pair is not in `Δ` (since `2x₀ ≠ 0`) and not in `Γ`
   (since `x₀ · 0 = 0`). The points `p+` and `p-` have no disjoint neighbourhoods. Let
   `N±` be open neighbourhoods of `p±`. Then `φ_K⁻¹(N±)` is an open neighbourhood of
   `(±x₀, 0)` in `K²`, so for small `y ≠ 0` it contains `(±x₀, y)`. Since
   `((x₀, y), (-x₀, y)) ∈ Γ(K)`, the point `φ(x₀, y) = φ(-x₀, y)` lies in `N+ ∩ N-`. Now
   let `O` be any open neighbourhood of `φ(0, 0)`. Its preimage under `φ_K` is a
   neighbourhood of `(0, 0)`, so it contains `(±x₀, 0)` for small `x₀ ≠ 0`. Then `O`
   contains both points `p±`. Open subsets of `O` are open in `X₂(K)`, so `p+` and `p-`
   have no disjoint neighbourhoods in `O`, and `O` is not Hausdorff. So
   `HasLocallyHausdorffRationalPoints K X₂` fails.
3. *`X₂` is a quotient `V/G_a` as in Example 5.5.* Let `Ũ = A³_K` with coordinates
   `(x, y, t)`, let `W̃ = {xy ≠ 0}`, and let `σ(x, y, t) = (-x, y, t + 1/(xy))` on `W̃`.
   This is again a free involution: `σ(σ(x, y, t)) = (x, y, t + 1/(xy) - 1/(xy))`. Let
   `R̃ = Δ ⊔ Γ_σ` and `V = Ũ/R̃`. The additive group `G_a` acts on `Ũ` by translating
   `t`. This action commutes with `σ`, so it descends to an action `a` of `G_a` on `V`.
   The projection `Ũ → U`, `(x, y, t) ↦ (x, y)`, carries `σ` to `ι` and `R̃` to `R`.
   The square formed by the second projections `R̃ → Ũ` and `R → U` is cartesian: a pair
   `(ι(w), w) ∈ Γ` together with a lift `w̃` of `w` lifts uniquely to `(σ(w̃), w̃)`. By
   Stacks Lemma 39.20.7 (Tag 07S3, same source), the square formed by `Ũ → V` and
   `U → X₂` is then cartesian. So the pullback of `V → X₂` along the étale cover `φ`
   is the trivial torsor `U × G_a → U`. Hence `V → X₂` is a `G_a`-torsor, and `X₂` is
   the fppf sheaf quotient of `V` by `G_a`: `IsFppfActionQuotient a π` holds for the
   induced map `π : h_V ⟶ X₂`. The torsor isomorphism `G_a × V ≅ V ×_{X₂} V` makes the
   stabilizer scheme the identity section, whose fibres are points of dimension `0`,
   while `dim G_a = 1`. So every point of `V` has orbit dimension `1`, `V_1 = V`, and
   one may take `Z = V`, `i = 𝟙` and `b = a`. The group `G_a` is a unipotent algebraic
   group.
4. *`V` is a reduced scheme of finite type over `K`.* The étale surjection `Ũ → V`
   from a smooth scheme of finite type shows that `V` is reduced, locally of finite type
   and quasi-compact. To see that `V` is a scheme, put `q = xyt + 1/2`. On `W̃` one has
   `q ∘ σ = -q`, so the open set `{q ≠ 0} ⊂ Ũ` is stable under `R̃`. Consider the
   morphism
   `F : {q ≠ 0} → M = A³ ∖ {rsg = 1}`, `(x, y, t) ↦ (r, s, g) = (x/q, y, t(q + 1/2)/q)`.
   It is invariant under `σ`, and `1 - rsg = 1/(4q²)`. Its Jacobian determinant is
   `1/(2q³)`, so `F` is étale. The geometric fibres of `F` are exactly the classes of
   `R̃`. Over a point with `rs ≠ 0`, the two roots `±q` of `4q²(1 - rsg) = 1` give the
   preimages `(rq, s, (q - 1/2)/(rqs))`, which are exchanged by `σ`. Over a point with
   `rs = 0`, only `q = 1/2` is possible, and the unique preimage `(r/2, s, g/2)` has
   `xy = 0`. In particular `F` is surjective. The restriction of `R̃` to `{q ≠ 0}` maps
   to `{q ≠ 0} ×_M {q ≠ 0}` by a monomorphism between schemes étale over `{q ≠ 0}` that
   is bijective on geometric points, hence by an isomorphism. By Stacks Lemma 39.20.3
   (Tag 03C5, same source), the open subspace of `V` with preimage `{q ≠ 0}` is the
   scheme `M`. The rest of `V` is the image of `{q = 0}`, which lies in `W̃` because
   `q = 0` forces `xyt = -1/2`. The open subspace of `V` with preimage `W̃` is the
   quotient of the affine scheme `W̃` by the free action of `Z/2` generated by `σ`, which
   is the affine scheme `Spec O(W̃)^σ`. So `V` is covered by two open subspaces that are
   schemes, and `V` is a scheme.

So `K`, `G = G_a`, `V`, `a`, `d = 1`, `Z = V`, `i = 𝟙`, `b = a`, `X = X₂` and `π`
satisfy every hypothesis of the uncorrected statement (3), but its conclusion fails.
The space `X₂` is not locally separated, as the corrected statement requires: the base
change `R → U × U` of the diagonal of `X₂` along `φ × φ` is not an immersion, since
`Δ` is open in `R` while points of `Γ` accumulate on `Δ` at `((0, y), (0, y))`,
`y ≠ 0`. The counterexample is not formalized here.

## Not stated here

- "Generally `V_d/G` is highly non-separated."
- The example of the coadjoint representation `V = Lie(G)^*` and the remark on sheaf
  theory on `(V_d/G)(k)` and smooth representations of `G(k)`; these are motivation.
- The justification of flatness through `exp(ker B)` for the differentiated map
  `B : g × V → Tan_{V/k}` of constant rank over `V_d`, and the appeal to [Del2,
  Prop. 3.11]: these are proof material.
