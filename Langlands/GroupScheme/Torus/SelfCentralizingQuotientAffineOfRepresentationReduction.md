# Reducing the affine normalizer quotient to three statements

This module defines the conjugacy-orbit morphism
`Langlands.GroupScheme.SelfCentralizingQuotientAffineReduction.conjugacyOrbit` and proves
`Langlands.GroupScheme.SelfCentralizingQuotientAffineReduction.selfCentralizingQuotientAffineOfRepresentation_of`.
The theorem derives `Langlands.GroupScheme.SelfCentralizingQuotientAffineOfRepresentationStatement`
from three premise statements, which it takes as hypotheses:

- `hGL : Langlands.GroupScheme.TorusSubgroupModuli.GeneralLinearAffineSumStatement`.
  The scheme of closed subtori of `GL_n` over `Spec R` is a disjoint union of
  affine opens.
- `hIm : Langlands.GroupScheme.RelativeTorusImageFactorizationStatement`. A
  homomorphism from a torus into an affine group of finite presentation is a
  flat, surjective map onto a torus `D`, locally of finite presentation,
  followed by a closed subgroup inclusion `D ⟶ G`.
- `hCl : Langlands.GroupScheme.SelfCentralizingConjugacyClosedEmbeddingStatement`.
  Over `Spec R`, the map `g ↦ ρ(g) D ρ(g)⁻¹` into the subtori of `GL_m` factors
  through the quotient `p : G ⟶ Y` as a closed immersion.

The theorem is the target `SelfCentralizingQuotientAffineOfRepresentationStatement`,
conditional on these three hypotheses. The module adds no other geometric
input. It uses only Library results on base change, Mathlib's locality of
affine morphisms, and the finite-union lemma for disjoint affine opens.

## The conjugacy-orbit morphism

Let `L` be a group scheme over `S`. Let `j : K ⟶ L_M` be a universal family of
closed subtori of `L` (`TorusSubgroupModuli.IsUniversal j`) with parameter
scheme `M`, and let `e : D ⟶ L` be a closed torus. For an `X`-valued point
`r : X ⟶ L.X`, `SubgroupFunctor.conjugateFamily e r` is the family
`x ↦ r(x) D r(x)⁻¹` over `X`. Its range is a closed subtorus of `L_X`. This uses
`SubgroupFunctor.isClosedSubgroup_conjugatePullback` and `IsTorus.baseChange`,
and `TorusSubgroupModuli.isAdmissible_range` turns the two facts into
admissibility. `conjugacyOrbit j huni e hD he r : X ⟶ M` is the classifying
morphism, chosen from the unique-existence clause of `huni` with
`Classical.choose`. `evaluate_conjugacyOrbit` states the defining property:
`TorusSubgroupModuli.evaluate j (conjugacyOrbit j huni e hD he r)` is
`SubgroupFunctor.range (SubgroupFunctor.conjugateFamily e r)`. By uniqueness,
this is the only morphism with that property. The special case `r = 𝟙 L.X` is
`TorusSubgroupModuli.torusOrbit` in
`Langlands.GroupScheme.Torus.SelfCentralizingConjugacyQuotientReduction`. Here
`r` may be any point, because the reduction uses `L = GL_m` and `r = ρ`.

## The proof

The module has three auxiliary theorems and the main theorem.

**`isAffine_of_isAffineHom_of_disjointAffineCover`.** Let `φ : Y ⟶ M` be an
affine morphism from a quasi-compact scheme. Let `U : J → M.Opens` be pairwise
disjoint affine opens with supremum `⊤`. Then `Y` is affine. The image of `φ`
is compact and so lies in finitely many `U k`, indexed by a finset `s`
(`IsCompact.elim_finite_subcover`). Mathlib's `IsAffineOpen.biSup_of_disjoint`
shows that `V = ⨆ k ∈ s, U k` is an affine open. Its preimage under `φ` is `⊤`,
and it is affine by `IsAffineOpen.preimage`. Finally `Scheme.topIso` identifies
`⊤` with `Y`.

**`isAffineHom_of_spec`.** This is the case of an affine base `Spec R` with a
global representation `ρ : G ⟶ GL_m` with central kernel.

1. `hIm`, applied to `t ≫ ρ`, gives the image torus `e : D ⟶ GL_m` and
   `π : T ⟶ D` with `π ≫ e = t ≫ ρ`. It needs `GL_m` to be affine
   (`GeneralLinear.isAffineHom_groupScheme`) and smooth
   (`GeneralLinear.smoothStatement`), hence locally of finite presentation.
2. `TorusSubgroupModuli.smoothTorusSubgroupRepresentability` gives a universal
   family `j` of closed subtori of `GL_m`, with parameter scheme `M`.
3. `f = conjugacyOrbit j huni e hD he ρ.hom.hom : G.X ⟶ M`. It satisfies
   `evaluate j f = range (conjugateFamily e ρ.hom.hom)` by
   `evaluate_conjugacyOrbit`.
4. `hCl` gives `φ : Y ⟶ M` whose underlying morphism is a closed immersion, hence
   affine. `hGL` gives the disjoint affine opens of `M.left`.
5. `G.X.left` is quasi-compact, because `G.X.hom` is quasi-compact over the
   affine `Spec R`. So `Y.left`, the image under the continuous surjection
   `p.left`, is compact (`Function.Surjective.compactSpace`). The first lemma
   makes `Y.left` affine, and a morphism between affine schemes is affine.

**`isAffineHom_pullback_of_openImmersion`.** Let `i : Spec R ⟶ S` be an open
immersion with a representation `ρ` of `G_R = (GroupScheme.baseChange i).obj G`
with central kernel. Then `pullback.snd Y.hom i` is affine. The proof transfers
every hypothesis to `G_R`, `t_R = (GroupScheme.baseChange i).map t` and
`p_R = (Over.pullback i).map p`, and then applies `isAffineHom_of_spec`.

- Smoothness, separatedness and quasi-compactness pass to the pullback
  `pullback.snd G.X.hom i`.
- Residue-field fibres are handled with
  `ExtensionReduction.residueFiberBaseChangeIso`. That isomorphism identifies
  the fibre of `G_R` at `s` with a base change of the fibre of `G` at `i s`.
  Connectedness is
  `ExtensionReduction.connectedSpace_residueFiber_baseChange_iff`. Affineness
  passes through the base change and then through the isomorphism, using
  `Over.w`.
- The torus `T_R` comes from `IsTorus.baseChange`, and closedness of `t_R`
  from `IsClosedSubgroup.baseChange`. Self-centralization comes from
  `IsRepresentedBy.baseChange` together with `torusCentralizer_baseChange`.
- Fibrewise maximality is not transported from `t`. The Library's
  `IsFibrewiseMaximalTorus.baseChange` needs an affine ambient group, which is
  not available here. Instead each residue-field fibre of `t_R` is shown to be
  self-centralizing, by `torusCentralizer_baseChange` and
  `SubgroupFunctor.range_baseChangeHom`. It is a torus over that field by
  `RelativeTorus.IsTorus.isTorus`. So it is a maximal torus by
  `isMaximalTorus_of_torusCentralizer_eq`.
- Flatness, surjectivity and local finite presentation of `p_R.left` come from
  `MorphismProperty.overPullbackMap`.
- The coset condition for `p_R` is transported through the adjunction
  `Over.mapPullbackAdj i`, as in `HomogeneousQuotient.baseChange`. The test
  points of `G_R` correspond to points of `G` by the multiplicative equivalence
  `baseChangePointsEquiv`, and `mem_torusNormalizer_baseChange_iff` identifies
  the two normalizers.

**`selfCentralizingQuotientAffineOfRepresentation_of`.** The representation
hypothesis is unpacked with `choose`, giving for each point `s` an affine open
`i s : Spec (R s) ⟶ S` containing `s`. The ranges of the `i s` cover `S`.
`IsZariskiLocalAtTarget.of_iSup_eq_top` reduces affineness of `Y.hom` to its
restrictions to these opens. `morphismRestrictOpensRange` identifies each
restriction with `pullback.snd Y.hom (i s)`, which is affine by the previous
theorem. The fibrewise-maximality hypothesis of the statement is not used. It
is recovered on each affine open from self-centralization, as explained above.
