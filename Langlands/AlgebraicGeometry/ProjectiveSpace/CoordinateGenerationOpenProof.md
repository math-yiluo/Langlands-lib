# Proof: the whole generation opens of the coordinate sections of `𝒪(1)`

`Langlands.AlgebraicGeometry.projectiveSpaceCoordinateGenerationOpen` proves exactly the
published proposition `ProjectiveSpaceCoordinateGenerationOpenStatement.{u}` from
`Langlands.AlgebraicGeometry.ProjectiveSpace.CoordinateGenerationOpenStatement`:

```lean
theorem projectiveSpaceCoordinateGenerationOpen :
    ProjectiveSpaceCoordinateGenerationOpenStatement.{u}
```

The proposition says the following. Let `R : Type u` be any commutative ring, `n : ℕ` and
`i : Fin (n + 1)`. Then

```text
Langlands.SchemeModule.trivializationOpen (twistOne R n) (twistOneCoordinate R n i)
  = projectiveSpaceCoordinateOpen R n i
```

holds as an equality of opens of `ProjectiveSpace R n`. The left side is the union of all opens
on which `sectionHom`, the morphism `𝒪 → 𝒪(1)` sending `1` to `X i / 1`, restricts to an
isomorphism. The right side is the coordinate open `D₊(X i)`. The theorem has no hypotheses on
`R`, `n` or `i`, so the zero ring and `n = 0` are included, and it proves both inclusions. The
statement pair and every imported declaration are unchanged.

The module imports the statement module and the published local-frame proof
`Langlands.AlgebraicGeometry.ProjectiveSpace.TwistOneLocalFramesProof`. Through that import
it also uses the published coordinate cover lemma `iSup_projectiveSpaceCoordinateOpen`
(module `CoordinateCoverProof`), the section-locus comparison `maximalTrivialization` (module
`Langlands.AlgebraicGeometry.Modules.SectionLocusComparison`), the lemmas
`Langlands.SchemeModule.LineBundleDescent.trivializesOn_iff_bijective` and
`Langlands.SchemeModule.LineBundleDescent.sectionHom_app` (module
`Langlands.AlgebraicGeometry.Picard.LineBundleDescent`), and the pointwise lemma
`ProjTwist.isUnit_mk_one` of the local-frame proof. It declares no instances or definitions.
Like `TwistOne` and the local-frame proof, it sets
`backward.isDefEq.respectTransparency.types false`.

## Implemented proof

The proof has one auxiliary lemma for the reverse inclusion and the final theorem.

`trivializationOpen_twistOneCoordinate_le R n i` proves
`trivializationOpen (twistOne R n) (twistOneCoordinate R n i) ≤ projectiveSpaceCoordinateOpen R n i`.
The argument does not use stalks.

1. Let `x` be a point of the trivialization open. Since that open is defined as
   `sSup {U | TrivializesOn … U}`, `TopologicalSpace.Opens.mem_sSup` gives an open `V` with
   `x ∈ V` on which `X i / 1` trivializes `𝒪(1)`.
2. The second conjunct of the published coordinate cover, `iSup_projectiveSpaceCoordinateOpen`,
   says that the opens `D₊(X j)` cover the space. So `TopologicalSpace.Opens.mem_iSup` gives
   some `j` with `x ∈ D₊(X j)`, that is `X j ∉ x`.
3. By `LineBundleDescent.trivializesOn_iff_bijective`, the trivialization on `V` makes the
   component `(sectionHom (twistOne R n) (X i / 1)).app V` bijective. By
   `LineBundleDescent.sectionHom_app` this component is `g ↦ g • (X i / 1)|_V` on
   `Γ(ProjectiveSpace R n, V)`. Its surjectivity gives a structure-sheaf section `g` over `V`
   with `g • (X i / 1)|_V = (X j / 1)|_V`.
4. A section of `twistOne R n` over `V` is a function sending each point to the localization
   of the coordinate ring at its homogeneous prime. A structure-sheaf section acts pointwise
   through `HomogeneousLocalization.val`. Evaluating the equality of step 3 at `x` therefore
   gives `(g x).val * (X i / 1) = X j / 1` in this localization `A_x`.
5. Since `X j ∉ x`, the element `X j / 1` is a unit of `A_x` (`ProjTwist.isUnit_mk_one`).
   By `isUnit_of_mul_isUnit_right`, `X i / 1` is then a unit of `A_x`. Rewriting `X i / 1` as
   the image of `X i` under `algebraMap` (`Localization.mk_one_eq_algebraMap`),
   `IsLocalization.AtPrime.isUnit_to_map_iff` shows that `X i` lies in the complement of the
   prime of `x`. This is the condition `x ∈ Proj.basicOpen _ (X i) = D₊(X i)`, by definition.

`projectiveSpaceCoordinateGenerationOpen` introduces `R`, its instance, `n` and `i` and proves
the equality by `le_antisymm`.

- The inclusion of the trivialization open in `D₊(X i)` is the lemma above.
- The inclusion `D₊(X i) ≤ trivializationOpen …` uses the first clause of the published
  local-frame proof, `(projectiveSpaceTwistOneLocalFrames R n).1 i`, which is
  `TrivializesOn (twistOne R n) (twistOneCoordinate R n i) (projectiveSpaceCoordinateOpen R n i)`.
  The published `Langlands.SchemeModule.maximalTrivialization`
  (`TrivializesOn M s U ↔ U ≤ trivializationOpen M s`) turns it into the inclusion.

The local-frame proof and the coordinate cover are only imported and applied. They are not
reproved, restated or taken as hypotheses. The second clause of the local-frame proof (local
rank one) and the residue comparison theorems are not needed by this route.

Inspection of the theorem with `lean_check` reports level parameter `u` and only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The mathematics is Stacks Project Lemma 27.10.5 (tag 01MV) in the registered snapshot
`stacks-projective-space-twists-morphisms-2026-10-26`, file `01MM.html`, with `d = 1`,
`n = 1` (the source's twist multiple), `f = X i` and `W = W_1` the whole space. The lemma says
`W_s = D₊(f) ∩ W`. Here `X_s` is identified with the Library's `trivializationOpen`, as the
statement Markdown explains. Stacks proves the lemma by writing the restriction of `s` on a
standard open as a function times a generator of the twist there, and by identifying `W_s` on
that open with the principal open of the function. The Lean proof uses the same
factorization in a different form. On a trivializing open, the section `X j / 1`, which
generates at `x`, is a multiple of `X i / 1`. Evaluating at `x` makes `X i / 1` a unit of the
local ring of the coordinate ring at `x`. The Lean proof works with sections over opens and
their pointwise values, not with stalks or residue fields, so no stalk description of `𝒪(1)`
and no Nakayama argument is needed. The inclusion `D₊(X i) ≤ X_s` is Stacks Lemma 27.10.2
(tag 01MS) in the same file, formalized in the published local-frame proof.

Author: Worker 974.
