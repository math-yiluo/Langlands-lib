# Proof: coordinate frames and local rank one of `𝒪(1)` on projective space

`Langlands.AlgebraicGeometry.projectiveSpaceTwistOneLocalFrames` proves exactly the published
proposition `ProjectiveSpaceTwistOneLocalFramesStatement.{u}` from
`Langlands.AlgebraicGeometry.ProjectiveSpace.TwistOneLocalFramesStatement`:

```lean
theorem projectiveSpaceTwistOneLocalFrames : ProjectiveSpaceTwistOneLocalFramesStatement.{u}
```

The proposition says that for every commutative ring `R : Type u` and every `n : ℕ`:

1. for each `i : Fin (n + 1)`, `TrivializesOn (twistOne R n) (twistOneCoordinate R n i)
   (projectiveSpaceCoordinateOpen R n i)`. In words, the morphism `sectionHom`, the morphism
   `𝒪 → 𝒪(1)` sending `1` to the coordinate section `X i / 1`, becomes an isomorphism after
   restriction to the coordinate open `D₊(X i)`;
2. `Picard.IsLocallyFreeRankOne (twistOne R n)`: every point has an open neighbourhood `U`
   with an isomorphism from the restriction of `𝒪(1)` to `U` onto the structure sheaf of
   `U`.

The theorem has no hypotheses on `R` or `n`, so the zero ring and `n = 0` are included. The
statement pair and every imported declaration are unchanged. The module imports the
statement module, `Langlands.AlgebraicGeometry.ProjectiveSpace.CoordinateCoverProof` (for the
coordinate cover) and `Langlands.AlgebraicGeometry.Picard.LineBundleDescent` (for the existing
`Langlands.SchemeModule.LineBundleDescent.sectionHom_app`). It declares no instances. Like
`Langlands.AlgebraicGeometry.ProjectiveSpace.TwistOne` and Mathlib's Proj structure sheaf,
it sets `backward.isDefEq.respectTransparency.types false`.

## Implemented proof

Clause 1 is proved in more generality, inside namespace `Langlands.AlgebraicGeometry.ProjTwist`.
The general setting is any `ℕ`-graded ring `𝒜`, any `d : ℕ`, any `f ∈ 𝒜 d` and any open `U`
contained in `D₊(f) = Proj.basicOpen 𝒜 f`. There the section `f / 1` of
`projTwistingSheaf 𝒜 d` trivializes the sheaf. The proof shows directly that, on every open
`W ≤ D₊(f)`, multiplication by the restricted section `f / 1` is a bijection from sections of
the structure sheaf to sections of `𝒪(d)`. Recall that a section of `𝒪(d)` over `W` is a
function sending each point `x` to an element of the localization `A_x` at its homogeneous
prime, and that it is locally a fraction `a / b` with `b` homogeneous of some degree `j` and
nonvanishing, and `a` of degree `j + d`. Structure-sheaf sections act pointwise through
`HomogeneousLocalization.val`.

Pointwise lemmas:

- `isUnit_mk_one`: at a point `x` with `f ∉ x`, the fraction `f / 1` is a unit of
  `A_x`. It is the image of the element `f` of the prime complement, so
  `IsLocalization.map_units` applies.
- `val_mul_mk_one_injective`: hence `y ↦ y.val * (f / 1)` is injective on the homogeneous
  localization at such a point. This uses `IsUnit.mul_left_injective` and
  `HomogeneousLocalization.val_injective`.
- `val_mk_mul_mk_one`: for `a ∈ 𝒜 (j + d)` and `b ∈ 𝒜 j`, the degree-zero fraction
  `a / (b f)` times `f / 1` equals `a / b` in `A_x`. This is a computation with
  `Localization.mk_mul` and `Localization.mk_eq_mk_iff`.
- `exists_val_mul_eq`: for a section `t` of `𝒪(d)` over `W ≤ D₊(f)` and a point `x ∈ W`,
  some element `y` of the homogeneous localization at `x` satisfies
  `y.val * (f / 1) = t x`. Write `t` near `x` as `a / b`. Then `y = a / (b f)` works, since
  `b f` is nonvanishing at `x` because both `b` and `f` are.

Division by `f`:

- `divBySection hf hW t` is the structure-sheaf section over `W` whose value at `x` is the
  element chosen by `exists_val_mul_eq` (via `Classical.choose`). To show that it is a section,
  take a neighbourhood `V` of `x` on which `t = a / b`. On `V` the chosen value equals the
  single degree-zero fraction `a / (b f)`: both have the same product with `f / 1`
  (`choose_spec`, the local formula for `t`, and `val_mk_mul_mk_one`), so they agree by
  `val_mul_mk_one_injective`. This is the local inverse `a / b ↦ a / (b f)` of Stacks
  Lemma 27.10.2.
- `bijective_smul_restrict_section hf hW`: for `W ≤ D₊(f)`, the map
  `g ↦ g • (f / 1)|_W` from `Γ(Proj 𝒜, W)` to `Γ(projTwistingSheaf 𝒜 d, W)` is bijective.
  The value of `g • (f / 1)|_W` at `x` is by definition `(g x).val * (f / 1)`. Injectivity
  compares values pointwise and applies `val_mul_mk_one_injective`. For surjectivity,
  `divBySection hf hW t` is a preimage of `t`; the pointwise equality is exactly the
  `choose_spec` of `exists_val_mul_eq`.

From sections to the restricted morphism:

- The existing `Langlands.SchemeModule.LineBundleDescent.sectionHom_app` holds for any scheme `X`, any
  `M : X.Modules`, any global section `s` and any open `U`. It says that
  `(sectionHom M s).app U g = g • s|_U`. The proof applies `Scheme.Modules.Hom.app_smul` to
  `g • 1` and rewrites the value at `1` with the Library lemma
  `Langlands.SchemeModule.sectionHom_app_one`. In the structure module `g • 1 = g * 1 = g`.
- `trivializesOn_projTwistingSheafSection hf hU`: for `U ≤ D₊(f)`, the section `f / 1`
  trivializes `projTwistingSheaf 𝒜 d` on `U`. After unfolding `TrivializesOn`,
  `Scheme.Modules.Hom.isIso_iff_isIso_app` reduces the claim to every open `V` of the open
  subscheme `U`, and `ConcreteCategory.isIso_iff_bijective` reduces it to bijectivity. The
  component at `V` of the restricted morphism is, definitionally, the component of
  `sectionHom` at the image `U.ι ''ᵁ V`. By `LineBundleDescent.sectionHom_app` it is the map
  `g ↦ g • (f / 1)|_{U.ι ''ᵁ V}`. Since `U.ι ''ᵁ V ≤ U ≤ D₊(f)` (`Scheme.Opens.ι_image_le`),
  `bijective_smul_restrict_section` applies.

Clause 2, with assembly:

- `Langlands.AlgebraicGeometry.isLocallyFreeRankOne_twistOne_of_coordinateFrames R n h`
  derives `Picard.IsLocallyFreeRankOne (twistOne R n)` from the coordinate-frame hypotheses
  `h`. This lemma was contributed by Worker 311. For a point `x`, the second conjunct of the
  published `projectiveSpaceCoordinateCover R n` gives
  `⨆ i, projectiveSpaceCoordinateOpen R n i = ⊤`, so `TopologicalSpace.Opens.mem_iSup`
  chooses `i` with `x ∈ D₊(X i)`. Hypothesis `h i` makes the restricted `sectionHom` an
  isomorphism `φ`. Then `(asIso φ).symm ≪≫ Scheme.Modules.restrictUnitIso U.ι` is the
  required isomorphism from the restriction of `twistOne R n` to
  `SheafOfModules.unit U.toScheme.ringCatSheaf`. Here Mathlib's `restrictUnitIso` identifies
  the restricted structure module, which is `structureModule` by definition, with the
  structure sheaf of the open.
- `projectiveSpaceTwistOneLocalFrames` introduces `R`, its instance and `n`. It obtains clause 1
  for each `i` from `trivializesOn_projTwistingSheafSection` with `𝒜 =
  projectiveSpaceGrading R n`, `d = 1`, `f = X i`, degree proof `projectiveSpace_X_mem R n i`
  and `U = D₊(X i)` (`le_rfl`); this matches `twistOne` and `twistOneCoordinate` by their
  definitions. Clause 2 then follows from the previous lemma.

## Provenance

The mathematics is Stacks Project Lemma 27.10.2 (tag 01MS) and Lemma 27.10.3 (tag 01MT),
in the registered snapshot `stacks-projective-space-twists-morphisms-2026-10-26`, file
`01MM.html`. Lemma 27.10.2 says that `𝒪_X(nd)` is trivial on `D₊(f)` for `f` of degree
`d > 0`, because multiplication by `f^n` becomes an isomorphism after inverting `f`. The
Lean proof treats the case `n = 1` for the published sheaf `S(d)~` of locally homogeneous
fractions. Rather than identifying sections over `D₊(f)` with `S(d)_(f)`, it checks
bijectivity of multiplication by `f / 1` directly on the sections over every open inside
`D₊(f)`, with the explicit local inverse `a / b ↦ a / (b f)`. That argument does not use
`d > 0`. Lemma 27.10.3 deduces invertibility of `𝒪_X(1)` from a cover by the opens
`D₊(f)` with `f` of degree one. Here that cover is the published coordinate cover by the
`D₊(X i)`, and "trivial" is read through `Scheme.Modules.restrictUnitIso`, as in Stacks
Definition 17.25.1 (tag 01CS; file `01CR.html` of the registered snapshot
`stacks-local-freeness-invertibility-sections-2026-10-21`).

Authors: Worker 974 (coordinate trivialization and assembly into this module) and Worker 311
(`isLocallyFreeRankOne_twistOne_of_coordinateFrames`).
