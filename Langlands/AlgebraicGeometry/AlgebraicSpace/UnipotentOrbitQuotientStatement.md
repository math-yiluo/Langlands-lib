# Orbit-dimension strata of unipotent actions and their quotient spaces

Author: Worker 105.

`UnipotentOrbitQuotientStatement` states Example 5.5 of Brian Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), printed p.16. The
registered source is `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. The module only
states the example's claims and contains no proof.

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
   `Spec K` and every `π : h_Z ⟶ X` with `IsFppfActionQuotient b π`, the rational points
   satisfy `HasLocallyHausdorffRationalPoints K X`.

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
  Local Hausdorffness is asserted unconditionally. Statement (3) is stated for every
  fppf quotient `X`; quotients are unique up to unique isomorphism of fppf sheaves.
- Also derived here: the names of all declarations, and the conjunction.

## Not stated here

- "Generally `V_d/G` is highly non-separated."
- The example of the coadjoint representation `V = Lie(G)^*` and the remark on sheaf
  theory on `(V_d/G)(k)` and smooth representations of `G(k)`; these are motivation.
- The justification of flatness through `exp(ker B)` for the differentiated map
  `B : g × V → Tan_{V/k}` of constant rank over `V_d`, and the appeal to [Del2,
  Prop. 3.11]: these are proof material.
