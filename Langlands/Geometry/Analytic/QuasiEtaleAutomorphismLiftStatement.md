# Statement: lifts of near-identity automorphisms to compact quasi-étale spaces

This module states, as a proposition, the existence half of Berkovich's Key
Lemma 7.2 for one cartesian square. Let `f : U → X` be quasi-étale with `U`
compact. Then every automorphism of `X` that is close enough to the identity
is covered by an endomorphism of `U` that is close to the identity. The
statement is not proved here. Together with the Library's rigidity of
quasi-étale morphisms with compact source (`isRigid_of_quasiEtale`), it
implies the Library proposition `QuasiEtaleActionLiftStatement`. That
deduction is in `ActionLiftFromAutomorphismLifts` and in the final proof
`quasiEtaleActionLift` (module `QuasiEtaleActionLiftProof`).

## Original sources

Berkovich, *Vanishing cycles for formal schemes*, Invent. Math. 115 (1994),
registered as `berkovich-1994-vanishing-cycles-formal-schemes`, SHA256
`f4f7bc00cc46a0a5f72a69d7bbb220bce1d3ed9fd465aeda629f37dfc054bed1`.

- §7, printed p.560 / PDF p.22: "As in §6, all the analytic spaces considered
  are assumed to be Hausdorff."
- Key Lemma 7.2, printed p.560 / PDF p.22: "Let X be an analytic space, and
  let f : U → X be a quasi-étale morphism with compact U. Then there exists
  ε₀ ∈ 𝔈(U) with the following property. For any ε ≤ ε₀ there exists
  δ ∈ 𝔈(X) such that, for any cartesian (resp. commutative) diagram (∗) and
  any morphism φ′ : Y → X with d(φ, φ′) < δ, there exists a unique morphism
  ψ′ : V → U with d(ψ, ψ′) < ε for which the following diagram is also
  cartesian (resp. commutative)". The square (∗) has `φ : Y → X` on top,
  `ψ : V → U` on the bottom, and vertical maps `g : V → Y` and `f : U → X`.
  The square (∗′) is the same with `φ′` and `ψ′` in place of `φ` and `ψ`.
- §6, printed pp.557–558 / PDF pp.19–20: the set `𝔈(X)`, the relation
  `d(φ, ψ) < ε`, the order `δ ≤ ε`, and the subgroups `G_ε(X)` of the
  automorphism group. These passages are quoted in the Library's
  `Langlands/Geometry/Analytic/ContinuousAnalyticAction.md`, which transcribes
  them as `TestTriple`, `IsNear` and `nearIdentity`.

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*
(unfinished manuscript, 1995–1996), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`
(folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`), §1.4,
printed p.7. This passage uses the Key Lemma in exactly this way: "Recall that
the Key Lemma 7.2 from [Ber3] implies that given a quasi-étale morphism U → X
with compact U there exist ε ∈ 𝔈(X), δ ∈ 𝔈(U) and a unique continuous
homomorphism 𝒢_ε(X) → 𝒢_δ(U) such that the morphism U → X commutes with the
action of 𝒢_ε(X)."

## The statement

All names are in the namespace `Langlands.Analytic.SaturatedAtlasPresentation`.
`QuasiEtaleAutomorphismLiftStatement K` is defined for a complete ultrametric
normed field `K` and has universe parameters `u` (the field) and `v`. It is
the following proposition.

For all analytic spaces `X`, `U` of `LocalizedCategory.{u, v, v}` and every
morphism `f : U ⟶ X`, suppose that:

- the underlying space of `X` is Hausdorff,
- `f` is quasi-étale (`quasiEtale f`), and
- `U` is compact (`IsCompactSpace U`: compact and Hausdorff).

Then for every finite set `E` of test triples of `U` there is a finite set
`D` of test triples of `X` with the following property. Let `σ : Aut X`
satisfy `σ ∈ nearIdentity τ` for every `τ ∈ D`. Then there is a morphism
`ψ : U ⟶ U` such that

- `ψ ≫ f = f ≫ σ.hom`, that is, `f ∘ ψ = σ ∘ f`, and
- `IsNear τ ψ (𝟙 U)` holds for every `τ ∈ E`.

## Correspondence with the source

This is the existence part of Key Lemma 7.2 for the cartesian square (∗) with
`Y = X`, `φ = 1_X`, `V = U`, `g = f` and `ψ = 1_U`. That square is cartesian
because `U` is the fibre product of `f` and `1_X`. Take `φ′ = σ`. Then
(∗′) commutes exactly when `f ∘ ψ′ = σ ∘ f`. The proposition keeps the
commutativity and the closeness of `ψ′` to `1_U`. It drops two things:

- uniqueness of `ψ′`, which the Library proves separately as
  `isRigid_of_quasiEtale`;
- cartesianness of (∗′). The deduction of the action-lift statement does not
  need it, because invertibility of the lifts follows from uniqueness.

The quantifiers are matched as follows.

1. **From `E` to an element of `𝔈(U)`.** A test triple of `U` consists of a
   chart of the saturated presentation (an affinoid domain of `U`), a function
   on it and a positive bound. So `E` defines an element `ε_E ∈ 𝔈(U)` with the
   following property: `d(ψ, ψ′) < ε_E` exactly when `IsNear τ ψ ψ′` for all
   `τ ∈ E` (`ContinuousAnalyticAction.md`). Let `ε` be the infimum of `ε₀` and
   `ε_E`, that is, the union of the two families. Then `ε ≤ ε₀` and `ε ≤ ε_E`.
2. **From `δ` to `D`.** The Key Lemma gives `δ ∈ 𝔈(X)` for `ε`. Berkovich's
   remark on p.558 gives `δ′ ≤ δ` defined by finitely many triples `(W, h, t)`
   with `W` an affinoid domain of `X`. The chart refinement argument in
   `ContinuousAnalyticAction.md` ("Provenance of choice 1") replaces each such
   triple by finitely many triples on charts. Their conjunction implies
   `d(·,·) < (W, h, t)`. This argument does not need `X` to be compact,
   because `δ′` has finitely many members and each `W` is compact. Let `D` be
   the finite set of all these chart triples.
3. **Conclusion.** Suppose `σ ∈ nearIdentity τ` for all `τ ∈ D`, that is,
   `IsNear τ σ.hom (𝟙 X)`. Then `d(1_X, σ) < δ` by symmetry of the relation.
   The Key Lemma gives `ψ′` with `f ∘ ψ′ = σ ∘ f` and `d(1_U, ψ′) < ε ≤ ε_E`.
   Hence `IsNear τ ψ′ (𝟙 U)` holds for all `τ ∈ E`.

Conventions:

- **Hausdorff spaces.** Berkovich assumes all spaces in §§6–7 are Hausdorff.
  Here `Y = X` and `V = U`, so it suffices to assume that `X` is Hausdorff and
  `U` is compact Hausdorff.
- **`K`-linear morphisms.** The morphisms of `LocalizedCategory` are
  `K`-morphisms, and `Aut X` is Berkovich's `G_K(X)`. The Key Lemma allows
  arbitrary morphisms of analytic spaces. If `σ` is `K`-linear, the lift `ψ′`
  is `K`-linear too: `f ∘ ψ′ = σ ∘ f` with `f` and `σ` `K`-linear forces the
  field homomorphism underlying `ψ′` to be the identity of `K`.

## Provenance of the shape

The Key Lemma is specialised to automorphisms near the identity because that
is exactly what the Library's `QuasiEtaleActionLiftStatement` needs. The
derivation is in `ActionLiftFromAutomorphismLifts`, theorem
`nonempty_actionLift_of_automorphismLift`. The general commutative and
cartesian forms, with arbitrary `Y`, `V`, `φ` and `ψ`, are not stated here.
A proof of this proposition along Berkovich's §7 will pass through such a
general form internally, because the induction of Lemma 7.5 does not preserve
the special case.

## Scope

Only the proposition is defined. Not provided here:

- its proof (Berkovich 1994 §7, Steps 1–3 with Lemmas 7.3–7.5);
- the uniqueness half and the cartesian conclusion of the Key Lemma;
- Berkovich's sets `𝔈(X)` themselves.
