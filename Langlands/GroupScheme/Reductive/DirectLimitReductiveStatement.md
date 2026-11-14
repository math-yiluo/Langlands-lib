# Statement: reductivity and semisimplicity over a direct limit of rings

Worker 75.

`Langlands.GroupScheme.DirectLimitReductiveStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other
definitions, theorems or axioms. It imports
[`Reductive.IdentityComponentLocus`](IdentityComponentLocus.md), which provides
`identityComponentReductiveLocus`, and [`Reductive.Semisimple`](Semisimple.md), which
provides `IsSemisimple`. Through these imports it also uses:

- `IsReductive`, `IsConnectedReductive`, `geometricPoint` and `geometricFiber` from
  [`Reductive.Basic`](Basic.md);
- `identityComponent` from [`IdentityComponent`](../IdentityComponent.md);
- `GroupScheme` and the base-change functor `GroupScheme.baseChange` from
  `Langlands.AbelianScheme.GroupScheme`. `GroupScheme S` is `Grp (Over S)`, and the
  underlying morphism of `(GroupScheme.baseChange f).obj H` is
  `pullback.snd H.X.hom f`.

It states Conrad's Corollary 3.1.11: reductivity and semisimplicity, both of a group
scheme and of the identity components of its geometric fibres, descend along a direct
limit of rings.

## Statement and quantifiers

The proposition quantifies over:

- a type `ι : Type u` with a preorder in which every two elements have a common upper
  bound (`IsDirected ι (· ≤ ·)`). This is Conrad's directed index set;
- a functor `A : ι ⥤ CommRingCat.{u}` from the preorder category of `ι`. This is the
  directed system of rings: for `i ≤ j` the transition map is
  `A.map (homOfLE h) : A i ⟶ A j`, and functoriality is the compatibility of the
  transition maps;
- a cocone `c` over `A` together with a proof of `IsColimit c`. The vertex `c.pt` is
  Conrad's direct limit `A = lim→ Aᵢ`, and `c.ι.app i : A i ⟶ c.pt` are the canonical
  maps. Every colimit cocone is uniquely isomorphic to every other one, so this covers
  every presentation of the direct limit;
- an index `i₀ : ι` and a group scheme `G₀ : GroupScheme (Spec (A i₀))` with the
  instances `Smooth G₀.X.hom` and `IsAffineHom G₀.X.hom`. This is Conrad's smooth affine
  `A_{i₀}`-group `G_{i₀}`.

The proposition then introduces local abbreviations:

- `Gi i h`, for `i : ι` and `h : i₀ ≤ i`: the base change of `G₀` along
  `Spec (A i) ⟶ Spec (A i₀)`, the morphism induced by the transition map. This is
  Conrad's `Gᵢ = G_{i₀} ⊗_{A_{i₀}} Aᵢ`;
- `G`: the base change of `G₀` along `Spec c.pt ⟶ Spec (A i₀)`, induced by
  `c.ι.app i₀`. This is Conrad's `G = G_{i₀} ⊗_{A_{i₀}} A`;
- local instances saying that `Gi i h` and `G` are smooth and affine over their bases.
  They are the base-change instances of Mathlib for `pullback.snd`, and they are needed
  to form `identityComponentReductiveLocus`;
- `Eventually p`, for a predicate `p i h` on the indices `i ≥ i₀`: there is `i₁ ≥ i₀`
  such that `p i h` holds for every `i ≥ i₀` with `i₁ ≤ i`. This is Conrad's "for all
  sufficiently large `i > i₀`";
- `SemisimpleFibres H`, for a smooth affine group scheme `H` over a scheme `S`: for
  every point `s` of `S`, the identity component of the geometric fibre `H_{s̄}` is
  semisimple (`IsSemisimple`).

## Conclusion

The conclusion is the conjunction of four equivalences.

1. `identityComponentReductiveLocus G = Set.univ` if and only if eventually
   `identityComponentReductiveLocus (Gi i h) = Set.univ`. For a smooth affine group `H`
   over `S`, `identityComponentReductiveLocus H` is the set of points `s` of `S` such that
   the identity component of the geometric fibre `H_{s̄}` is connected reductive
   (`IsConnectedReductive`).
2. `IsReductive G` if and only if eventually `IsReductive (Gi i h)`. `IsReductive H`
   means that `H` is smooth and affine over the base and that every geometric fibre is
   a smooth connected affine group with trivial unipotent radical.
3. `SemisimpleFibres G` if and only if eventually `SemisimpleFibres (Gi i h)`.
4. `G` is reductive and all its geometric fibres are semisimple if and only if
   eventually `Gi i h` is reductive and all its geometric fibres are semisimple.
   `IsSemisimple` for a group over a field means connected reductive
   (`IsConnectedReductive`) with finite scheme-theoretic centre (`HasFiniteCenter`).

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014. It is registered as `conrad-2014-reductive-group-schemes`,
file `Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the printed page numbers.

- Corollary 3.1.11, p.88: "Let {Aᵢ} be a directed system of rings with direct limit A,
  and G_{i₀} a smooth affine A_{i₀}-group for some i₀. For all i > i₀ define
  Gᵢ = G_{i₀} ⊗_{A_{i₀}} Aᵢ and G = G_{i₀} ⊗_{A_{i₀}} A. The fibers of G⁰ → Spec A are
  reductive if and only if the fibers of Gᵢ⁰ → Spec Aᵢ are reductive for all
  sufficiently large i > i₀, and G is a reductive A-group if and only if Gᵢ is a
  reductive Aᵢ-group for all sufficiently large i > i₀. The same holds for
  semisimplicity." The proof is on p.89.
- Definition 3.1.1, p.81: "A reductive S-group is a smooth S-affine group scheme G → S
  such that the geometric fibers G_s̄ are connected reductive groups. A semisimple
  S-group is a reductive S-group whose geometric fibers are semisimple."
- Proposition 3.1.9(1), p.85: "There is an open U around s in S such that G⁰_u is
  reductive for all u ∈ U. The same holds for semisimplicity." The proof of
  Corollary 3.1.11 uses it to see that the loci in clauses 1 and 3 are open.

## Derivation from the source

- **Direct limit.** A directed system of rings is a functor from a directed preorder to
  rings, and its direct limit is its colimit. Conrad does not say whether the index set
  is a preorder or a partial order; a preorder is the more general reading.
- **Indices.** Conrad defines `Gᵢ` for `i > i₀`, which for a directed system is read as
  `i ≥ i₀`. The proposition defines `Gi i h` for every `i ≥ i₀`. Including `i = i₀`
  changes nothing, since every conclusion is about all sufficiently large `i`.
- **Clause 1.** `G⁰` is the open subgroup of `G` whose fibre over `s` is the identity
  component `(G_s)⁰`. A fibre over a field is reductive when its geometric fibre is
  connected reductive (Definition 3.1.1 and the remark after it). The identity component
  commutes with extension of the ground field for groups locally of finite type, so
  "the fibres of `G⁰` are reductive" says that for every `s` the identity component of
  the geometric fibre `G_{s̄}` is connected reductive. That is
  `identityComponentReductiveLocus G = Set.univ`. The same holds for each `Gᵢ`.
- **Clause 2** is the second assertion of Corollary 3.1.11, with Conrad's reductive
  `S`-group encoded by the Library's `IsReductive`.
- **Clause 3** is "the same holds for semisimplicity" applied to the first assertion: the
  identity components of the geometric fibres of `G` are semisimple if and only if this
  holds for `Gᵢ` for all large `i`. This is also the reading in Conrad's proof, where
  `Uᵢ` is "the locus of points at which the geometric fiber of Gᵢ⁰ is reductive (resp.
  semisimple)".
- **Clause 4** is "the same holds for semisimplicity" applied to the second assertion.
  A semisimple `S`-group is a reductive `S`-group with semisimple geometric fibres
  (Definition 3.1.1). The Library has no separate predicate for semisimple group
  schemes over a general base, so the definition is written out. This is the encoding
  used by other relative semisimple statements of the Library, for example
  `RelativeDerivedGroupStatement` in
  [`Reductive.RelativeDerivedGroupStatement`](RelativeDerivedGroupStatement.md).
- **Semisimple groups over a field.** `IsSemisimple` asks for a connected reductive
  group with finite scheme-theoretic centre. Over an algebraically closed field, a
  connected reductive group is semisimple exactly when its centre is finite.

## Scope

All objects are in universe `u`. The proposition does not state:

- the openness of the loci (Proposition 3.1.9(1));
- the descent of geometric connectedness of the fibres that is used in Conrad's proof
  ([EGA IV₃, 9.7.7(ii) and 8.3.4]);
- its uses in reductions to Noetherian bases, such as Proposition 3.1.12.

## Relation to the Library

- `IdentityComponentReductiveLocusOpenStatement` in
  [`Reductive.IdentityComponentLocus`](IdentityComponentLocus.md) is Proposition
  3.1.9(1) for reductivity. Conrad's proof of Corollary 3.1.11 uses it; the semisimple
  analogue is not stated in that module.
- `GenericReductivitySpreadingStatement` in
  [`Reductive.GenericSpreadingStatement`](GenericSpreadingStatement.md) spreads
  reductivity from the generic fibre over a Noetherian domain to a principal open.

This module proves none of these relations.
