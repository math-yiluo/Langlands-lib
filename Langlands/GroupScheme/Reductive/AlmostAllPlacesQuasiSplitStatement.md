# Statement: quasi-splitness and torsor points at almost all places

Worker 75.

`Langlands.GroupScheme.AlmostAllPlacesQuasiSplitStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It uses:

- `IsConnectedReductive` from [`Reductive.Basic`](Basic.md): a group scheme over
  `Spec k` that is smooth, affine and connected, and whose base change to an algebraic
  closure of `k` has trivial unipotent radical.
- `IsQuasiSplit` from [`Reductive.QuasiSplit`](QuasiSplit.md): `IsConnectedReductive`
  together with a field-defined subgroup `i : B ⟶ G` with `IsGeometricBorelSubgroup i`,
  that is, a Borel subgroup over the base field whose base change to the algebraic
  closure is again a Borel subgroup.
- `FinitePlace F` and `FiniteCompletion F v` from
  [`Global.Adelic`](../../Global/Adelic.md). `FinitePlace F` is Mathlib's
  `IsDedekindDomain.HeightOneSpectrum (𝓞 F)`, the nonzero prime ideals of the ring of
  integers, which index the non-archimedean places of `F`. `FiniteCompletion F v` is
  Mathlib's `v.adicCompletion F`, the completion `F_v` of `F` for the `v`-adic
  valuation, with its `F`-algebra structure.
- `RingPoint F X A` from
  [`PointTopology.ProductRingPoints`](../../AlgebraicGeometry/PointTopology/ProductRingPoints.md):
  the morphisms `Spec A ⟶ X` over `Spec F`, that is, the actual `A`-valued points of a
  scheme `X` over `Spec F`.
- `GroupScheme.baseChange f` from
  [`AbelianScheme.GroupScheme`](../../AbelianScheme/GroupScheme.md): the pullback of
  group schemes along a morphism of base schemes `f`.
- Mathlib's `ModObj G.X X` (a left action of the group object `G.X` on `X` in the
  cartesian monoidal category `Over (Spec F)`) and its shear morphism
  `ModObj.leftSMul G.X X : G.X ⊗ X ⟶ X ⊗ X`, `(g, x) ↦ (g • x, x)`.

## Statement

Let `F : Type u` be a number field and `G` a group scheme over `Spec F` with
`IsConnectedReductive G`. Then:

1. **Quasi-splitness.** For all but finitely many `v : FinitePlace F` (the filter
   `Filter.cofinite`), the base change of `G` along
   `Spec.map (CommRingCat.ofHom (algebraMap F (FiniteCompletion F v)))` satisfies
   `IsQuasiSplit`.
2. **Torsors.** Let `X` be a scheme over `Spec F` with an action `ModObj G.X X` such that
   `X.hom` is flat, surjective and quasi-compact, and the shear `ModObj.leftSMul G.X X`
   is an isomorphism. Then for all but finitely many `v : FinitePlace F` the type
   `RingPoint F X (FiniteCompletion F v)` is nonempty.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014. It is registered as `conrad-2014-reductive-group-schemes`,
file `Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the printed page numbers.

- Exercise 5.5.3, pp.182–183: "Let R be Dedekind with fraction field K, and G a
  connected reductive K-group. […] (iii) Using (i) and (ii), show that if G is a
  connected reductive group over a global field F then G_{F_v} is quasi-split for all but
  finitely many places v of F. Likewise show that any G-torsor over F admits an
  F_v-point for all but finitely many v." The omitted passage states parts (i) and (ii).
- Definition 5.2.10, p.157 (cited in the exercise): "A Borel subgroup of a reductive
  group scheme G → S is a parabolic subgroup P ⊂ G such that P_s is a Borel subgroup of
  G_s for all s ∈ S. A reductive group G → S is quasi-split over S if it admits a Borel
  subgroup scheme over S." Over the spectrum of a field this means having a Borel
  subgroup defined over that field.

Conrad leaves the exercise to the reader; the notes contain no proof of it. The hint
is to spread `G` out to a reductive group scheme over a dense open subscheme of
`Spec 𝓞_F` (part (i)) and to pass from the quasi-split special fibre over a finite
residue field to the generic fibre over the henselian local ring `𝓞_{F_v}` (part (ii)).
This is explanation only.

## Derivation from the source

- **Global field.** Conrad allows any global field. The statement treats number fields
  only, because the Library's places and completions (`FinitePlace`, `FiniteCompletion`
  in `Global.Adelic`) exist only for number fields. Global function fields are not
  covered.
- **Places.** A number field has finitely many archimedean places. "All but finitely
  many places" is therefore the same as "all but finitely many non-archimedean places",
  and both clauses quantify over `FinitePlace F` with the filter `Filter.cofinite`.
  The non-archimedean places of `F` correspond bijectively to the nonzero primes of
  `𝓞_F`, and `FiniteCompletion F v` is the completion at that place.
- **`G_{F_v}`.** This is the actual base change of `G` along
  `Spec F_v → Spec F`. Quasi-split means having a Borel `F_v`-subgroup. Over a field
  that need not be algebraically closed, a Borel subgroup is a subgroup that becomes a
  Borel subgroup over an algebraic closure, which is `IsGeometricBorelSubgroup`.
  `IsQuasiSplit` packages this with `IsConnectedReductive` of the base change. The
  latter holds for every field extension, so it adds no condition beyond Conrad's.
- **Torsors.** The torsor clause uses the encoding of
  [`FiniteFieldTorsorPointStatement`](../FiniteFieldTorsorPointStatement.md): an actual
  left action whose structure map is an fpqc cover and whose shear is an isomorphism.
  Its Markdown explains why these conditions describe torsors under a smooth affine group
  over a field, through faithfully flat descent. Since `G` is smooth and affine, such a
  torsor is smooth and affine over `F`, so this agrees with Conrad's fppf or étale
  torsors. An `F_v`-point of `X` is a morphism `Spec F_v → X` over `Spec F`, which is
  `RingPoint F X (FiniteCompletion F v)`.
- **Order of quantifiers.** In clause 2 the finite exceptional set may depend on the
  torsor `X`, as in Conrad ("any G-torsor … admits an F_v-point for all but finitely
  many v").

## Scope

The proposition does not state:

- parts (i) and (ii) of Exercise 5.5.3. Part (i) is covered in substance by
  `GenericReductivitySpreadingStatement` (see below). Part (ii) is a separate statement;
- the case of global function fields;
- the pointer to Exercise 7.3.5 on the analogous property of being split.

## Relation to the Library

- `GenericReductivitySpreadingStatement` in
  [`Reductive.GenericSpreadingStatement`](GenericSpreadingStatement.md) gives the
  spreading of reductivity used in part (i) of the exercise. The construction
  `reductiveModelData` in
  [`IntegralModel.ArithmeticReductiveSpreading`](../IntegralModel/ArithmeticReductiveSpreading.md)
  produces a reductive model of `G` over a ring of `S`-integers of a number field.
- `HenselianFiniteResidueQuasiSplitStatement` in
  [`RelativeLevi.HenselianQuasiSplitStatement`](../RelativeLevi/HenselianQuasiSplitStatement.md)
  states that reductive groups over a henselian local ring with finite residue field are
  quasi-split in the relative sense, which is the input for the local step.
- `FiniteFieldTorsorPointStatement` in
  [`FiniteFieldTorsorPointStatement`](../FiniteFieldTorsorPointStatement.md) states
  Lang's theorem for torsors over finite fields, the input for the torsor clause.

This module proves none of these relations.
