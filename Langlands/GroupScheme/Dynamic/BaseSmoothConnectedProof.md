# Dynamic subgroups over any base scheme are smooth with connected fibres: proof

Worker 285, using the recovered proof and documentation of Worker 3483.
The Lean proof is unchanged from that draft.

`Langlands.GroupScheme.dynamicBaseSmoothConnected.{u}` proves the proposition
`Langlands.GroupScheme.DynamicBaseSmoothConnectedStatement.{u}` (module
`Langlands.GroupScheme.Dynamic.BaseSmoothConnectedStatement`). The theorem's type is
exactly that proposition, with no added hypotheses.

## The statement

Over every scheme `S`, for a group scheme `G` over `S` with smooth affine structure
morphism, a cocharacter `χ` and a homomorphism `j : H ⟶ G`: if `j` represents `U_G(χ)`,
then `H` is smooth over `S` with geometrically connected fibres; if `j` represents
`P_G(χ)` or `Z_G(χ)`, then `H` is smooth over `S`, and has geometrically connected fibres
when `G` does. This is Conrad, *Reductive group schemes* (2014), Theorem 4.1.7(2) and the
smoothness assertion of 4.1.7(4), for conjugation actions, in the version over any base
scheme stated after Example 4.1.9; the statement's Markdown gives the quotations and the
correspondence.

## Helper lemmas

Namespace `Langlands.GroupScheme.DynamicBaseSmoothConnected`, for group schemes `G`, `H`
over `S`. Here `GroupScheme.baseChange y` is base change along a morphism `y : T ⟶ S`,
whose underlying structure morphism is `pullback.snd G.X.hom y`.

- `smooth_baseChange` and `isAffineHom_baseChange`: base changes of `G` along any
  `y : T ⟶ S` are smooth, respectively affine, since `Smooth` and `IsAffineHom` are
  stable under base change (`MorphismProperty.pullback_snd` for `IsAffineHom`).
- `smooth_of_baseChange`: if the base change of `H` along every morphism
  `y : Spec R ⟶ S` from the spectrum of a commutative ring `R : Type u` is smooth, then
  `H.X.hom` is smooth. This is Mathlib's `IsZariskiLocalAtTarget.of_openCover` for
  `Smooth`, applied to the affine open cover `S.affineOpenCover.openCover`; the morphism
  of the cover on its `i`-th component is `pullback.snd H.X.hom (S.affineOpenCover.f i)`,
  the base change of `H` along the chart `Spec (S.affineOpenCover.X i) ⟶ S`.
- `geometricallyConnected_of_baseChange`: if the base change of `H` along every
  field-valued point `y : Spec K ⟶ S` is a connected space, then
  `GeometricallyConnected H.X.hom`. This is Mathlib's
  `geometrically_iff_of_isClosedUnderIsomorphisms` for the property `ConnectedSpace`.
- `connectedSpace_baseChange`: conversely, if `GeometricallyConnected G.X.hom`, the base
  change of `G` along every field-valued point is connected (the same Mathlib lemma
  applied to `GeometricallyConnected.geometrically_connectedSpace`).

The module sets `backward.isDefEq.respectTransparency false`, as Mathlib's
`Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber` does around its own use of
`IsZariskiLocalAtTarget` for `Smooth`; without it the instance
`IsZariskiLocalAtTarget @Smooth` is not found.

## The proof

Fix a clause and its hypothesis `hj`, for instance `(Dynamic.unipotent χ).IsRepresentedBy j`.
For a morphism `y : T ⟶ S`:

1. `hj.baseChange y` (`SubgroupFunctor.IsRepresentedBy.baseChange`): the base-changed
   homomorphism `j_T` represents the base change of the subgroup functor, here
   `(Dynamic.unipotent χ).baseChange y`.
2. `Dynamic.unipotent_baseChange` (respectively `Dynamic.parabolic_baseChange`,
   `Dynamic.centralizer_baseChange`) rewrites this functor as the dynamic subgroup of the
   base-changed cocharacter `Dynamic.baseChangeCocharacter y χ` of `G_T`.

Smoothness. By `smooth_of_baseChange` it suffices to treat `y : Spec R ⟶ S`. Then `G_R`
is a group scheme over `Spec R` with smooth affine structure morphism, and the published
theorem `dynamicSmooth_ring R G_R (Dynamic.baseChangeCocharacter y χ) H_R j_R` gives the
smoothness of `H_R` from steps 1–2.

Connectedness. By `geometricallyConnected_of_baseChange` it suffices to treat a field
point `y : Spec K ⟶ S`. Then `G_K` is smooth and affine over the field `K`, so the
published field case `dynamicConnected` (`DynamicConnectedStatement`) applies to `G_K`,
the cocharacter `Dynamic.baseChangeCocharacter y χ` and `j_K`. For `U_G(χ)` it gives
`ConnectedSpace` of `H_K` directly. For `P_G(χ)` and `Z_G(χ)` it needs `G_K` connected,
which `connectedSpace_baseChange` provides from the hypothesis
`GeometricallyConnected G.X.hom`.

## Published inputs

- `dynamicSmooth_ring`, module `Langlands.GroupScheme.Dynamic.SmoothOverRing`.
- `dynamicConnected : DynamicConnectedStatement`, module
  `Langlands.GroupScheme.Dynamic.ConnectedProof`.
- `Dynamic.baseChangeCocharacter`, `Dynamic.unipotent_baseChange`,
  `Dynamic.parabolic_baseChange` and `Dynamic.centralizer_baseChange`, module
  `Langlands.GroupScheme.Dynamic.BaseChange`.
- `SubgroupFunctor.IsRepresentedBy.baseChange`, module
  `Langlands.GroupScheme.SubgroupBaseChange`.
- Mathlib: `IsZariskiLocalAtTarget.of_openCover`, `Scheme.affineOpenCover`,
  `MorphismProperty.pullback_snd`, `GeometricallyConnected`,
  `geometrically_iff_of_isClosedUnderIsomorphisms`.

## Relation to the literature

Conrad says that the theorem "adapts to work over any base scheme S" without spelling
out the argument. The proof here is the evident reduction: smoothness is local on the
base and is supplied over affine opens by the published ring case, and connectedness of
fibres is a statement about field-valued points, supplied by the published field case.
