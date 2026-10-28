# Ampleness of the actual `𝒪(1)` on projective space

`Langlands.AlgebraicGeometry.ProjectiveSpaceTwistOneAmpleStatement.{u}` is a
universe-polymorphic definition of type `Prop`. This module states the result
and supplies no proof.

Worker 712 implemented this pair. Worker 404 supplied the specification, the
source selection and the reuse boundaries in the task contract.

## Exact statement

The checked declaration, in namespace `Langlands.AlgebraicGeometry` with
`_root_.AlgebraicGeometry` open, is

```lean
def ProjectiveSpaceTwistOneAmpleStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ),
    ∃ M : Langlands.AlgebraicGeometry.Picard.LineBundle (ProjectiveSpace R n),
      M.obj = twistOne R n ∧ M.IsAmple
```

Its type is `Prop`, with the single universe parameter `u`. The body is
literally the proposition displayed in the task contract. A private check
compiled the identification `Iff.rfl` between the declaration and that text.

The module imports only `Langlands.AlgebraicGeometry.ProjectiveSpace.TwistOne`
and `Langlands.AlgebraicGeometry.Picard.Ample`. It uses their declarations
unchanged and changes no imported Lean/Markdown pair.

## The clauses

The proposition quantifies over every commutative ring `R : Type u` and every
`n : ℕ`. There is no other hypothesis.

- `ProjectiveSpace R n` is the published polynomial projective space
  `Proj (projectiveSpaceGrading R n)`, the Proj of
  `MvPolynomial (Fin (n + 1)) R` with its total-degree grading.
- `twistOne R n : (ProjectiveSpace R n).Modules` is the published actual
  twisting sheaf `𝒪(1) = S(1)~`. Its sections are the locally homogeneous
  fractions `a / b` with `deg a = deg b + 1` (see
  `Langlands/AlgebraicGeometry/ProjectiveSpace/TwistOne.md`).
- `Langlands.AlgebraicGeometry.Picard.LineBundle X` is the published full
  subcategory of actual `X.Modules` that satisfy `IsLocallyFreeRankOne`:
  every point has an open neighbourhood on which the actual restriction is
  isomorphic to the structure sheaf. A term `M` is a pair of a module
  `M.obj` and a proof of this property.
- `M.obj = twistOne R n` is an equality of objects of
  `(ProjectiveSpace R n).Modules`. It fixes the underlying module to the
  actual `S(1)~`. The proposition is therefore not the existence of some
  unspecified ample bundle.
- `M.IsAmple` is the published `LineBundle.IsAmple`, unchanged.

### Why an existential bundle

`twistOne R n` is a bare module. It is not yet bundled as a `LineBundle`,
because its local rank one is a separate proof obligation. A bundle `M` with
`M.obj = twistOne R n` exists exactly when
`IsLocallyFreeRankOne (twistOne R n)` holds: the witness is the pair of
`twistOne R n` and such a proof, and conversely `M.property` transported
along the equality is such a proof. `LineBundle.IsAmple` depends only on
the underlying module. So the statement says that `twistOne R n` is locally
free of rank one and that, so bundled, it is ample. The existential carries
the local-rank-one proof. It introduces no unproved bundled definition and no
certificate premise.

### The ample convention

For a line bundle `L` on a scheme `Y`, `L.IsAmple` is

```text
CompactSpace Y ∧ ∀ y : Y, ∃ n : ℕ, 1 ≤ n ∧ ∃ s : L.powSections n,
  y ∈ L.sectionOpen s ∧ IsAffineOpen (L.sectionOpen s).
```

`L.powSections n` is the type of global sections of the actual sheafified,
right-associated tensor power `Langlands.Scheme.Modules.tensorPow L.obj n`.
The open `L.sectionOpen s` is
`Langlands.SchemeModule.trivializationOpen (tensorPow L.obj n) s`. This is the
union of all opens on which the morphism from the structure sheaf sending `1`
to `s` restricts to an isomorphism, the largest such open. The **whole**
generation open must be affine. See
`Langlands/AlgebraicGeometry/Picard/Ample.md` for these definitions.

### Degenerate cases

The statement includes the zero ring and `n = 0`. For the zero ring the
polynomial ring is zero, so `ProjectiveSpace R n` has empty underlying space.
Then compactness holds, the condition on points is vacuous, and local rank one
holds vacuously. For `n = 0` there is a single coordinate `X 0`. No field,
Noetherian, positive-dimension, rank-one, coordinate-cover, tensor, residue,
projectivity, model, existing ample-sheaf or compatibility premise occurs.

## Source correspondence and derivation

The statement is derived from the following passages. It is not a verbatim
source statement.

- Registered original `stacks-projective-space-twists-morphisms-2026-10-26`,
  file `01MM.html` (Stacks Section 27.10): Lemma 27.10.2 and its proof,
  Lemma 27.10.3 and its proof, and Lemma 27.10.5 and its proof. File
  `01ND.html` (Section 27.13): Definition 27.13.2 and Lemma 27.13.3 with its
  proof.
- Registered original `stacks-invertible-picard-ampleness-2026-10-21`, file
  `01PS.html`: Definition 28.27.1. File `01CY.html`: Lemma 17.25.10 and its
  proof.

Definition 28.27.1 calls an invertible `𝒪_X`-module `ℒ` ample if `X` is
quasi-compact and every `x ∈ X` lies in `X_s` for some `n ≥ 1` and some
`s ∈ Γ(X, ℒ^{⊗ n})` with `X_s` affine. The Library's `LineBundle.IsAmple` has
the same shape. Stacks defines `X_s` by residue nonvanishing,
`s ∉ 𝔪_x ℒ_x` (Lemma 17.25.10). The Library uses instead the largest open on
which `s : 𝒪 → ℒ^{⊗ n}` is an isomorphism. For an invertible module these
agree: Lemma 17.25.10 shows that `s` is an isomorphism on `X_s`, and
conversely a generator near `x` is a basis of the stalk, so it is not in
`𝔪_x ℒ_x`. In the Library, `Ample.lean` proves
`coe_trivializationOpen_eq_nonvanishingLocus` under the hypothesis
`LineBundleResidueOpenComparison`. The published theorem
`Langlands.SchemeModule.lineBundleResidueOpenComparison`, in
`Langlands.AlgebraicGeometry.Modules.SectionResidueComparison`, proves that
hypothesis. This statement does not use the residue formulation.

The derivation, which the proof successor is expected to formalize, is the
following.

1. **Bundling.** Lemma 27.10.2, for `f = X i` of degree one, trivializes
   `𝒪(1)` on `D₊(X i)` by multiplication by `X i`. Lemma 27.10.3 then gives
   invertibility under the degree-one coordinate cover. In the Library this
   is clause 2 of the published statement
   `ProjectiveSpaceTwistOneLocalFramesStatement` in
   `Langlands.AlgebraicGeometry.ProjectiveSpace.TwistOneLocalFramesStatement`.
   Its proof bundles `twistOne R n` as the witness `M`, which makes
   `M.obj = twistOne R n` hold by `rfl`.
2. **Compactness.** Lemma 27.13.3 covers projective space by the `n + 1`
   affine opens `D₊(X i)`, so it is quasi-compact. In the Library this is
   clause 3 of `ProjectiveSpaceCoordinateCoverStatement`, proved by the
   published `projectiveSpaceCoordinateCover` in
   `Langlands.AlgebraicGeometry.ProjectiveSpace.CoordinateCoverProof`. Its
   proof is for every commutative ring, not only over `ℤ`.
3. **A coordinate open through each point.** Clause 2 of the same
   coordinate-cover statement says that the opens `D₊(X i)` have supremum
   `⊤`. So every point `x` lies in some `D₊(X i)`.
4. **The section of a positive power.** Take `n = 1` and the coordinate
   section `X i = twistOneCoordinate R n i`, the image of `X i ∈ S_1` under
   Equation 27.10.1.3. `LineBundle.IsAmple` asks for a section of
   `tensorPow (twistOne R n) 1`, which unfolds definitionally to
   `tensorObj (twistOne R n) (structureSheaf _)`. This is the actual sheafified
   tensor product with the structure sheaf, not the raw module. The section is
   transported through the actual right unitor
   `tensorRightUnitor (twistOne R n) : tensorPow (twistOne R n) 1 ≅ twistOne R n`,
   as `(tensorRightUnitor (twistOne R n)).inv.app ⊤ (twistOneCoordinate R n i)`.
   The published `Langlands.SchemeModule.trivializationOpen_mapIso`, in
   `Langlands.AlgebraicGeometry.Picard.AmpleIsoProof`, says that a module
   isomorphism preserves the whole generation open of a section. So the
   generation open of the transported section equals
   `trivializationOpen (twistOne R n) (twistOneCoordinate R n i)`.
5. **The whole generation open.** Lemma 27.10.5, with Stacks' `d = 1`,
   `n = 1` and `f = X i`, gives `W_s = D₊(X i) ∩ W`. Here `W = W_1` is the
   local-invertibility open of Lemma 27.10.4. For polynomial projective
   space it is the whole space, since the `D₊(X i)` cover it and on each the
   twists are trivial (step 1). So the whole generation open of `X i` is
   `D₊(X i)`. In the Library this is the separate statement
   `ProjectiveSpaceCoordinateGenerationOpenStatement` in
   `Langlands.AlgebraicGeometry.ProjectiveSpace.CoordinateGenerationOpenStatement`.
   That statement asserts equality in the lattice of opens, not only
   containment.
6. **Affineness.** By steps 4 and 5, the generation open of the transported
   section is `D₊(X i)`. It contains `x` by step 3 and is affine by clause 1
   of the coordinate-cover statement. This is the required section.

A private check compiled this assembly as a conditional theorem. Its only
hypotheses were local rank one of `twistOne R n` and the whole generation-open
equality, and it used the published `projectiveSpaceCoordinateCover`. The
check is evidence of feasibility only. It is not a proof of this statement,
and those hypotheses are not premises of the statement.

The retained comment threads were read. The comments on Section 27.10 concern
a cross-reference to (27.9.0.2), a typo in the proof of Lemma 27.10.4, and a
compatibility remark about (27.10.1.5). The comments on Section 27.13 concern
notation and cross-references between Definition 27.13.2 and Lemma 27.13.3.
The two comments on Definition 28.27.1 add the reference EGA II, Definition
4.5.3. The comments on Lemma 17.25.10 fix typos in its proof and suggest a
slogan. The snapshot of `01PS.html` reports five further comments on Section
28.27 but does not retain their text. None of the retained comments changes
the passages used here.

## Owners and remaining obligations

This unit is a prerequisite of the arbitrary-field ample-existence route
coordinated by Worker 404. The exact proof of this statement must reuse,
after their publication, the following owners. It must not keep them as outer
hypotheses or duplicate them.

- The local-frame workflow (task `5b16e18e-acbd-4449-8966-975c52bbee25`).
  Its statement `ProjectiveSpaceTwistOneLocalFramesStatement` is published,
  and its exact proof successor supplies local rank one.
- The whole-coordinate-generation-open workflow (task
  `4b81eafb-03e2-4a09-b57d-af7d8ee3c8b7`). It owns
  `ProjectiveSpaceCoordinateGenerationOpenStatement` and its proof successor.
- The published coordinate-cover proof `projectiveSpaceCoordinateCover`.
- The published section/isomorphism transport
  `trivializationOpen_mapIso` and the right unitor `tensorRightUnitor`.

## Not claimed

This module states only the proposition above. It does not state or prove:

- any comparison `𝒪(1)^{⊗ m} ≅ 𝒪(m)` or any property of twists other than
  degree one;
- ampleness of a pullback along a closed immersion (an existing downstream
  owner), projectivity of abelian varieties, field descent, or any
  group-scheme ample-existence result;
- the identification `Γ(D₊(f), 𝒪(1)) = S(1)_(f)` or any chart isomorphism of
  `D₊(X i)` with affine space.
