# Coordinate frames and local rank one of `𝒪(1)` on projective space

`ProjectiveSpaceTwistOneLocalFramesStatement` is a universe-polymorphic proposition, with level `u`, in namespace `Langlands.AlgebraicGeometry`. It is a statement target only. This module proves neither of its clauses.

## Exact statement

For every commutative ring `R : Type u` and every `n : ℕ`, the proposition asserts the conjunction of two properties of the actual twisting sheaf `twistOne R n = 𝒪(1)` on `ProjectiveSpace R n`:

1. `∀ i : Fin (n + 1), Langlands.SchemeModule.TrivializesOn (twistOne R n) (twistOneCoordinate R n i) (projectiveSpaceCoordinateOpen R n i)`. For each `i`, the coordinate section `X i` trivializes `𝒪(1)` on the coordinate open `D₊(X i)`.
2. `Langlands.AlgebraicGeometry.Picard.IsLocallyFreeRankOne (twistOne R n)`. The sheaf `𝒪(1)` is locally isomorphic to the structure sheaf.

All imported definitions are used unchanged:

- `twistOne`, `twistOneCoordinate` and `projectiveSpaceCoordinateOpen` come from `Langlands.AlgebraicGeometry.ProjectiveSpace.TwistOne` and `Langlands.AlgebraicGeometry.ProjectiveSpace`;
- `TrivializesOn` comes from `Langlands.AlgebraicGeometry.Modules.SectionLocus`;
- `IsLocallyFreeRankOne` comes from `Langlands.AlgebraicGeometry.Picard.LineBundle`.

There is no hypothesis on `R` or `n`. In particular the statement covers the zero ring, where `ProjectiveSpace R n` has empty underlying space, and `n = 0`, where there is a single coordinate `X 0`. No local-triviality, sheaf-comparison, coordinate-cover, field, Noetherian, nontriviality, positive-dimension, rank-one, projectivity or ampleness premise occurs.

### Clause 1: the coordinate `X i` is a frame on `D₊(X i)`

For a sheaf of modules `M` on a scheme `X` and a global section `s : Γ(M, ⊤)`, `Langlands.SchemeModule.sectionHom M s : structureModule X ⟶ M` is the morphism from the structure sheaf that sends `1` to `s`. It is obtained by Mathlib's `SheafOfModules.unitHomEquiv` from the compatible family of restrictions of `s`. Over an open `V`, it sends a function `g` to `g • s|_V`. `TrivializesOn M s U` says that the image of this morphism under the restriction functor `Scheme.Modules.restrictFunctor U.ι` is an isomorphism of sheaves of modules on the open subscheme `U`.

Here `M = twistOne R n`, `s = twistOneCoordinate R n i` is the global section `X i / 1`, and `U = projectiveSpaceCoordinateOpen R n i` is Mathlib's Proj basic open `D₊(X i)` of the degree-one variable `X i`. So clause 1 says that, on `D₊(X i)`, the map `𝒪 → 𝒪(1)`, `g ↦ g · X i`, is an isomorphism. The trivializing section is fixed to be `X i`, not an unspecified local basis.

### Clause 2: local rank one

`IsLocallyFreeRankOne M` is the published definition: every point `x` has an open neighbourhood `U` with an isomorphism `M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf`, using the actual restriction of sheaves of modules. It is not tensor-invertibility. With this clause the sheaf `twistOne R n` can later be bundled as a `Picard.LineBundle`, but this statement does no bundling.

## How the published sheaf realizes `𝒪(1)`

`twistOne R n` is `projTwistingSheaf (projectiveSpaceGrading R n) 1`, the actual sheaf `S(1)~` for `S = MvPolynomial (Fin (n + 1)) R` with total-degree grading. Its sections over an open are functions with values in the localizations `S_𝔭` at the points that are locally a single fraction `a / b`. Here `b` is homogeneous and nonvanishing on the open, and `deg a = deg b + 1`. At a point `𝔭`, each value is an element of the homogeneous localization `S(1)_(𝔭)`, viewed inside `S_𝔭`. Stacks Lemma 27.8.4(5) gives `S(1)_(𝔭)` as the stalk of `S(1)~`. The paired Markdown of `TwistOne` explains this, and records that the comparison with Stacks' `M~` is not formalized.

For this statement no such comparison is needed: both clauses are about the published sheaf itself. The intended local inverse divides by `X i` on `D₊(X i)`. A local section `a / b` of `𝒪(1)` with `deg a = deg b + 1` goes to the degree-zero fraction `a / (b X i)`, a section of the structure sheaf of `Proj`, and multiplying back by `X i / 1` returns `a / b`. Any formal local-description comparison used in a proof, for example identifying sections over `D₊(X i)` with `S(1)_(X i)`, is a proof obligation of the proof task. It is not an assumption of this statement.

## Source correspondence

The source is the registered original `stacks-projective-space-twists-morphisms-2026-10-26`, file `01MM.html` (Stacks Section 27.10, tag 01MM).

- **Clause 1** is Lemma 27.10.2 for the polynomial ring `S`, the degree-one element `f = X i` and the twist `𝒪_X(1)` (the source's `d = 1` and `n = 1`). The lemma states that `𝒪_X(nd)|_{D₊(f)}` is trivial. Its proof says that the graded `S`-module map `S → S(nd)`, `x ↦ f^n x`, becomes an isomorphism after inverting `f`, which gives `S_(f) ≅ S(nd)_(f)` and so `𝒪_{D₊(f)} ≅ 𝒪_X(nd)|_{D₊(f)}`. For `nd = 1` this map is multiplication by `f = X i`, so the trivialization sends `1` to the section `X i / 1`. This is the image of `X i ∈ S_1` under Equation 27.10.1.3 and equals `twistOneCoordinate R n i`. Clause 1 is the statement that this specific morphism is an isomorphism. The other assertions of Lemma 27.10.2, about the multiplication maps (27.10.1.1), (27.10.1.2) and (27.10.1.5), are not stated here.
- **Clause 2** is the invertibility of `𝒪_X(1)` in Lemma 27.10.3, specialized to degree one. The lemma assumes that `X` is covered by the standard opens `D₊(f)` with `f ∈ S_1`, and its proof applies Lemma 27.10.2 on each of them. For the polynomial ring this cover is given by the coordinate opens `D₊(X i)`. File `01ND.html`, Lemma 27.13.3 (tag 01NG), records this cover for projective space over `ℤ`, and Definition 27.13.2 gives the conventions. Its proof, that the irrelevant ideal is generated by the variables, works over any commutative ring `R`, as the published `ProjectiveSpaceCoordinateCoverStatement` explains. The tensor isomorphisms `𝒪_X(1)^{⊗ n} ≅ 𝒪_X(n)` and the isomorphisms of (27.10.1.1), (27.10.1.2) and (27.10.1.5) in Lemma 27.10.3 are not stated here.

Stacks uses "invertible" in the sense of Definition 17.25.1 (tensor-invertible), and "trivial" there means isomorphic to `𝒪_X`. These are in the registered original `stacks-local-freeness-invertibility-sections-2026-10-21`, file `01CR.html` (Section 17.25). By Lemma 17.25.4, on a locally ringed space such as a scheme, invertible is the same as locally free of rank one. Clause 2 uses the Library's local definition, "locally isomorphic to the structure sheaf", which is what the proof of Lemma 27.10.3 provides directly: `𝒪_X(1)` is trivial on each `D₊(X i)`. So no comparison with tensor-invertibility is stated or needed.

The retained comment threads were read. The comments on Section 27.10 concern a cross-reference to (27.9.0.2), a typo in the proof of Lemma 27.10.4, and a compatibility remark about (27.10.1.5). The comments on Section 27.13 concern notation and cross-references between Definition 27.13.2 and Lemma 27.13.3. Section 17.25 has no comments. None of them changes Lemmas 27.10.2, 27.10.3, 27.13.3 or Definition 17.25.1.

## Relation between the clauses

Clause 2 is a consequence of clause 1 together with the published coordinate-cover theorem `projectiveSpaceCoordinateCover` in `Langlands.AlgebraicGeometry.ProjectiveSpace.CoordinateCoverProof`, which proves `ProjectiveSpaceCoordinateCoverStatement`. Its second clause says that the opens `D₊(X i)` have supremum `⊤`. Every point then lies in some `D₊(X i)`. Clause 1 gives an isomorphism from the restriction of the structure module to the restriction of `𝒪(1)` there. Mathlib's `Scheme.Modules.restrictUnitIso` identifies the restriction of the structure module with the structure sheaf of the open. The task keeps both clauses in one statement so that one proof can establish them together. Including clause 2 adds no new premise.

## Role and remaining obligations

This statement supplies the local frames of `𝒪(1)` for the arbitrary-field ample-existence route coordinated by Worker 404. It does not state any of the following:

- that the generation (local-isomorphism) open of `X i` equals `D₊(X i)`;
- any bundling of `twistOne R n` as a `Picard.LineBundle`;
- any tensor comparison `𝒪(1)^{⊗ m} ≅ 𝒪(m)`, or properties of twists other than `d = 1`;
- the identification `Γ(D₊(f), 𝒪(1)) = S(1)_(f)` of Lemma 27.8.4;
- ampleness, or any chart isomorphism of `D₊(X i)` with affine space.

Those are separate successors. The proof of this proposition is the obligation of a separate exact-target proof task, which should reuse `projectiveSpaceCoordinateCover` for the cover rather than redo the irrelevant-ideal argument.
