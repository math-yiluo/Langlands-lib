# Degree-one comparisons for actual projective evaluation

This is derived infrastructure for projective evaluation. It combines the
published relative-linear-system degree-one comparison with actual evaluated
frame sections, their restriction law, and the coherent projective-frame
transition comparison. Its provenance is these internal constructions and
proved pullback-coordinate identities; it asserts no additional theorem from
external literature.

Fix schemes `X` and `S` in an arbitrary common universe `u`, a morphism
`p : X → S`, a module sheaf `M` on `S`, a line bundle `L` on `X`, and an
actual module-sheaf morphism `ev : M → p_* L`. For a local frame `e` of
rank `n + 1` on `U`, an open `W ≤ U`, and pointwise generation by its actual
evaluated sections on `p⁻¹W`, `localEvaluationTwistIso` is the actual module
isomorphism

`localEvaluationMap(e,W)^* O(1) ≅ evaluationLineBundle(p,L,W)`.

It is the published `relativeLinearSystemTwistIso` for those sections and
the actual restricted base morphism. Its coordinate theorem carries every
pulled-back homogeneous coordinate to the corresponding evaluated frame
section. `localEvaluationTwistIso_unique` proves that any module morphism
with these equations is its hom: the pulled-back coordinate sections generate,
so they detect equality. `localEvaluationTwistIso_linearChange` carries
arbitrary linear combinations of projective coordinates to the same linear
combinations of the evaluated frame sections, with scalars transported
through the genuine base morphisms. The coefficients are any linear map over
the global function ring of `W`; invertibility is not required for this law.

For square coherence, `LinearSystem.PullbackSquareCompatible` is the explicit
proposition for a commuting square `p' ≫ b = a ≫ p`, with modules `M,N,M',N'`
on its four schemes and morphisms

- `δ : p^* M → N` and `α : p'^* M' → N'`;
- `β : b^* M → M'` and `γ : a^* N → N'`.

It states

`p'^*(β) ≫ α = squarePullbackIso.hom ≫ a^*(δ) ≫ γ`.

The lemma `.eq` exposes that equation. The generic theorem
`pullback_comparison_square_between` proves it when `M` is locally free of
rank one, its given coordinate sections have trivialization opens covering
the scheme, and the two composite morphisms have the same value on each
successively pulled-back coordinate. The proof pulls the coordinate cover
back along `b` and `p'`, applies equality detection by generating sections,
and uses the canonical square comparison's section formula. No isomorphism
or local-freeness premise on the other three modules is required.

Now assume `M` is locally free of rank `n + 1` and
`hs : FrameEvaluationGenerates p L ev n`. In namespace `EvaluationTwist`,
`localMap` and `localIso` specialize the actual evaluation map and degree-one
comparison to the chosen frame on each frame open. For `U ≤ V`,
`localMap_chartMap` proves that evaluation on `U` followed by the full
projective chart transition equals the inverse-image-open inclusion followed
by evaluation on `V`. It cancels the target chart open immersion and uses
the actual evaluation chart restriction theorem.

`localIso_chartTwistIso_coordinate` computes the coordinate value after
pulling back the full projective transition comparison and applying the
local evaluation comparison on `U`. The transition's coordinate formula
is the actual dual-frame change. The proved linear-combination law and the
actual evaluated-section frame-change law identify the result with the
section obtained by evaluating the frame on `V` over `p⁻¹U`.

`localIso_restrict_coordinate` computes the other route: first apply the
local comparison on `V`, pull back along `p⁻¹U → p⁻¹V`, and apply the
canonical `openPullbackIso` for restriction of `L`. The local coordinate
formula and the actual evaluated-section restriction theorem give exactly
the same evaluated section over `p⁻¹U`.

`localSquare_criterion` specializes the generic square criterion to these
actual four schemes and modules while retaining arbitrary module maps.
Finally, `localIso_compatible` applies this criterion to the actual two
local degree-one comparisons, the actual projective `chartTwistIso`, and
the canonical `openPullbackIso`. The two preceding coordinate calculations
supply its premise. Consequently the local comparisons satisfy the full
square equation, including frame change and both canonical pullback
comparisons; their compatibility is proved from evaluation.

This unit proves local comparisons and their transition compatibility.
Generation remains an explicit hypothesis. It does not yet glue a global
isomorphism for the pullback of `FrameBundle.twistOne`, prove frame-choice or
tensor-line independence, establish a cubic embedding, or prove the host
large-level representability statement. No affine, noetherian, abelian-scheme,
universal-family or representability premise occurs in this construction.
