# The whole generation opens of the coordinate sections of `𝒪(1)`

`ProjectiveSpaceCoordinateGenerationOpenStatement` is a universe-polymorphic proposition with level `u`. It is a statement target only. This module proves none of its content.

## Exact statement

For every commutative ring `R : Type u`, every `n : ℕ` and every `i : Fin (n + 1)`, the proposition asserts the equality

```text
Langlands.SchemeModule.trivializationOpen (twistOne R n) (twistOneCoordinate R n i)
  = projectiveSpaceCoordinateOpen R n i
```

in the lattice `(ProjectiveSpace R n).Opens` of opens of the scheme. Its ingredients are imported unchanged:

- `ProjectiveSpace R n` is the Library's actual polynomial Proj `Proj (projectiveSpaceGrading R n)` of `MvPolynomial (Fin (n + 1)) R` with the total-degree grading.
- `twistOne R n` is the actual degree-one twisting sheaf `𝒪(1) = S(1)~` from `Langlands.AlgebraicGeometry.ProjectiveSpace.TwistOne`. It is the sheaf of locally homogeneous degree-one fractions, not a line bundle assumed to have properties.
- `twistOneCoordinate R n i : Γ(twistOne R n, ⊤)` is the global section `X i / 1`. It is the image of the degree-one variable `X i` under Stacks Equation 27.10.1.3.
- `Langlands.SchemeModule.trivializationOpen M s`, from `Langlands.AlgebraicGeometry.Modules.SectionLocus`, is `sSup {U | TrivializesOn M s U}`. Here `TrivializesOn M s U` says that the restriction to `U` of `sectionHom M s : structureModule X ⟶ M` is an isomorphism. `sectionHom M s` is the morphism of modules `𝒪 → M` sending `1` to `s`. The trivialization open is therefore the union of all opens on which `𝒪 → 𝒪(1)`, `1 ↦ X i`, restricts to an isomorphism. The Library's `Langlands.AlgebraicGeometry.Picard.Ample` calls this open the generation locus of the section. Its `IsAmple` uses the generation loci `sectionOpen s = trivializationOpen (tensorPow L.obj n) s` of sections of tensor powers. This statement concerns `twistOne R n` itself, not a tensor power `tensorPow _ 1`, and it asserts no comparison between the two.
- `projectiveSpaceCoordinateOpen R n i` is the coordinate open `D₊(X i)`, Mathlib's `Proj.basicOpen` of the degree-one variable `MvPolynomial.X i`.

The equality says that the whole generation open of `X i / 1` is exactly `D₊(X i)`. It contains two inclusions. First, `D₊(X i)` lies in the generation open, so the section trivializes `𝒪(1)` on `D₊(X i)`. Second, the generation open contains no point outside `D₊(X i)`. The second inclusion is required: an inclusion `D₊(X i) ≤ trivializationOpen …`, or trivialization on some smaller opens, would not state this proposition.

## Hypotheses and edge cases

There are no hypotheses on `R`, `n` or `i`, and the universe `u` is arbitrary. In particular:

- For the zero ring, `ProjectiveSpace R n` has empty underlying space. Both sides are then the unique open of the empty scheme.
- For `n = 0` there is a single coordinate `X 0`. The statement then says that `X 0 / 1` generates `𝒪(1)` on all of `D₊(X 0)`, which is the whole space.

The proposition has no rank-one, local-frame, field, Noetherian, residue-comparison, coordinate-cover, projectivity or ampleness premise. It does not mention `LineBundle`, residue fields or tensor powers.

## Source correspondence

The source is the registered original `stacks-projective-space-twists-morphisms-2026-10-26`, file `01MM.html` (Stacks Section 27.10, tag 01MM).

- Definition 27.10.1 defines the twist `𝒪_X(m) = S(m)~` on `X = Proj(S)`. (The source writes `n` for the twist degree; here `n` is the dimension.) Equation 27.10.1.3 maps `S` to the global sections of the twists. The Library's `twistOne` and `twistOneCoordinate` are these constructions for `S = R[X_0, …, X_n]`, twist degree `1` and the element `X i ∈ S_1`.
- Lemma 27.10.2 says that `𝒪_X(md)` is trivial on `D₊(f)` for `f` homogeneous of degree `d > 0`, by multiplication by `f^m`. With `f = X i` and `d = 1`, this is the trivialization of `𝒪(1)` on `D₊(X i)` by `X i`.
- Lemma 27.10.3 concludes that `𝒪_X(1)` is invertible when `X` is covered by the standard opens `D₊(f)` with `f ∈ S_1`. Polynomial projective space is so covered by the coordinate opens. This is Lemma 27.13.3 (tag 01NG) in `01ND.html` of the same original. The Library states this cover as `ProjectiveSpaceCoordinateCoverStatement` and proves it as `projectiveSpaceCoordinateCover`.
- Lemma 27.10.4 defines the open `W = W_d` where the twists `𝒪_X(dm)` are invertible and the multiplication maps are isomorphisms. It identifies `W_d` with the union of the opens `D₊(gh)`, where `g, h` are homogeneous and `deg g = deg h + d`. For `d = 1`, taking `g = X j` and `h = 1` gives every `D₊(X j)`. By the coordinate cover, `W_1` is the whole space.
- Lemma 27.10.5 says the following. Let `d ≥ 1`, let `m ≥ 1` (the source's `n`) and let `f ∈ S_{md}` with image section `s` of `𝒪_W(md)`. Then `W_s = D₊(f) ∩ W`. With `d = 1`, `m = 1`, `f = X i` and `W` the whole space, this is `X_s = D₊(X i)` for `s = X i / 1`.

The locus `X_s` in Lemma 27.10.5 is defined in the registered original `stacks-invertible-picard-ampleness-2026-10-21`, file `01CY.html` (Stacks Lemma 17.25.10, tag 01CY). For an invertible module `ℒ` on a locally ringed space and a section `s`, `X_s` is the set of points `x` where the image of `s` does not lie in `𝔪_x ℒ_x`. The lemma proves that `X_s` is open and that `s : 𝒪_{X_s} → ℒ|_{X_s}` is an isomorphism. Conversely, if `s : 𝒪_U → ℒ|_U` is an isomorphism on an open `U`, then each stalk `s_x` with `x ∈ U` is a basis of `ℒ_x`, so it is not in `𝔪_x ℒ_x`. So for an invertible module, `X_s` is the largest open on which `𝒪 → ℒ`, `1 ↦ s`, is an isomorphism. That is the Library's `trivializationOpen`. The published theorem `Langlands.SchemeModule.lineBundleResidueOpenComparison` in `Langlands.AlgebraicGeometry.Modules.SectionResidueComparison` formalizes this identification: `nonvanishingLocus L.obj s = trivializationOpen L.obj s` for every `L : LineBundle X`.

This proposition is therefore the source's `X_s = D₊(X i)` for `s = X i / 1`, stated for the Library's generation open rather than the residue nonvanishing locus. Using the residue comparison requires `twistOne R n` to be a line bundle. That fact is the second clause of the separate local-frame statement `ProjectiveSpaceTwistOneLocalFramesStatement`. The proposition stated here assumes neither the comparison nor local freeness. These are routes for the proof, not premises.

The retained comment threads were read. On Section 27.10, comment #8507 (fixed in #9110) corrects a cross-reference to Equation 27.9.0.2. Comment #9887 (fixed in #10428) corrects a typo in the proof of Lemma 27.10.4. Comment #10886 (answered in #11074, text left unchanged) suggests a compatibility remark about Equation 27.10.1.5. None changes the statements of Lemmas 27.10.2 to 27.10.5 or Definition 27.10.1. The comments on Lemma 17.25.10 are two fixed typos in its proof (#2443/#2486 and #4898/#5175) and a suggested slogan (#2594). None changes the definition of `X_s` or the lemma's statement. The comments on Definition 28.27.1 (#2689/#2716) add the EGA II 4.5.3 reference.

## Role and what is not claimed

A later ampleness proof uses this proposition. Stacks Definition 28.27.1 (tag 01PS in `01PS.html` of the second original) and the Library's ampleness definition need the whole generation open of a section to be affine, not just some affine neighbourhood inside it. With this equality, the whole generation open of `X i / 1` is `D₊(X i)`. That open is affine by the published coordinate-cover proof, and these opens cover the space.

This module asserts none of the following:

- a proof of the equality;
- that `twistOne R n` is a `LineBundle`, or any new `LineBundle` construction;
- the local-frame statement;
- an identification `Γ(D₊(f), 𝒪(1)) = S(1)_(f)` or a description of stalks;
- tensor comparisons `𝒪(1)^{⊗ m} ≅ 𝒪(m)`;
- ampleness or projectivity.

## Expected proof obligations

A separate exact-target `lean.proof@1` task proves the whole proposition, with no added outer hypotheses. That proof should reuse existing owners rather than restate or duplicate them:

- the published coordinate-cover proof `projectiveSpaceCoordinateCover`;
- the proof successor of the local-frame statement `ProjectiveSpaceTwistOneLocalFramesStatement` (task `5b16e18e-acbd-4449-8966-975c52bbee25`), whose first clause gives trivialization of `X i / 1` on `D₊(X i)`;
- the published general section-locus and residue infrastructure in `Langlands.AlgebraicGeometry.Modules.SectionLocusComparison` and `Langlands.AlgebraicGeometry.Modules.SectionResidueComparison`.

There are two natural routes. The direct route works as follows:

- The inclusion `D₊(X i) ≤ trivializationOpen` follows from the local-frame clause and `maximalTrivialization`.
- For the reverse inclusion, take a point `x ∈ D₊(X j)` with `X i ∈ x`. In the stalk, `X i / 1 = (X i / X j)(X j / 1)`, and `X i / X j` lies in the maximal ideal. Since `𝒪(1)_x` is free of rank one with basis `X j / 1`, Nakayama's lemma shows that the stalk map `𝒪_x → 𝒪(1)_x` is not surjective, and `x` is not a stalk frame. By `isStalkFrame_of_mem_trivializationOpen`, `x` is not in the trivialization open.

The residue route identifies the generation open with the residue nonvanishing locus. It does so by `lineBundleResidueOpenComparison`, using the rank-one clause of the local-frame proof. It then computes that locus to be `D₊(X i)`, as in the proof of Lemma 27.10.5.
