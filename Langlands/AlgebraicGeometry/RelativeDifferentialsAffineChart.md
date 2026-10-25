# Affine-chart comparison for the actual relative differential sheaf

Let `f : X ⟶ S` be any morphism of schemes, let `hU : IsAffineOpen U` and
`hV : IsAffineOpen V`, and suppose `e : V ≤ f ⁻¹ᵁ U`. Set
`R = Γ(S, U)`, `A = Γ(X, V)`, and `φ = f.appLE U V e : R ⟶ A`.
Every algebraic differential module and basis below uses the algebra structure
`φ.hom.toAlgebra`. The definition `relativeDifferentialsAffineChartIso` constructs
an isomorphism in `V.toScheme.Modules`:

```text
(relativeDifferentials f).restrict V.ι
  ≅ (pullback hV.isoSpec.hom).obj (tilde (ModuleCat.of A (KaehlerDifferential R A))).
```

Its target is the previously defined `relativeDifferentialsAffineChartModel f hV e`.
Its source is the restriction of the existing sheafification-based differential
sheaf. The construction preserves `relativeDifferentials` and
`relativeDifferentialsDerivation`. All declarations in this module are in
`Langlands.Scheme`. There are no smoothness, reducedness, finite type, nonzero-ring,
nonemptiness, or additional invertibility hypotheses.

Write `g = hV.fromSpec : Spec A ⟶ X`, `b = hU.fromSpec : Spec R ⟶ S`,
`q = hV.isoSpec.hom : V.toScheme ⟶ Spec A`, and `f′ = Spec.map φ`.
The canonical chart square satisfies `g ≫ f = f′ ≫ b`.
The instance `relativeDifferentialsAffineChartSquareMap_isIso` applies the
published open-immersion locality theorem
`relativeDifferentialsOpenImmersionIsIso` to this square; both `g` and `b`
are open immersions. Thus the existing chart-square map
`g* relativeDifferentials f ⟶ relativeDifferentials f′` is invertible.
The instance `relativeDifferentialsAffineChartFromModelMap_isIso` applies
`relativeDifferentialsSpecMapIsIso R A` and preservation of isomorphisms by
`pullback q`. It proves invertibility of the existing map from the chart model
to `q* relativeDifferentials f′`.

The comparison composes `relativeDifferentialsAffineChartPullbackIso`,
the pullback of the isomorphism furnished by the chart-square map, and the
inverse of the isomorphism furnished by the model map. The first factor is
the existing composite of restriction-to-pullback, `q ≫ g = V.ι`, and
pullback-composition isomorphisms. In the following diagram all objects
and arrows are module sheaves on `V.toScheme`:

```text
Ω(X/S).restrict V.ι  ──chartIso.hom──▶  q* tilde(Ω(A/R))
          │                                  │
          │ ToSpecMap                        │ FromModelMap
          ▼                                  ▼
       q* Ω(Spec A/Spec R) ═══════════ q* Ω(Spec A/Spec R)
```

The lemma `relativeDifferentialsAffineChartIso_fac` proves commutativity:
`chartIso.hom ≫ FromModelMap = ToSpecMap`. Its proof simplifies the
composite and the inverse identities. The lemma
`relativeDifferentialsAffineChartIso_inv_fac` gives the inverse equation
`chartIso.inv ≫ ToSpecMap = FromModelMap`. The lemma
`relativeDifferentialsAffineChartIso_hom_unique` proves that the forward
factorization uniquely determines the chart morphism, by cancelling the
invertible `FromModelMap`.

These equations retain compatibility with the universal derivation through
the already published canonical maps. More precisely,
`relativeDifferentialsAffineChartSquareMap_adjoint_app` states, for every
open `W` of `X` and every `a : Γ(X, W)`, that the pullback–pushforward adjoint
of the chart-square map sends `d(a)` to `d(g.app W a)`.
The map underlying `FromModelMap` satisfies
`relativeDifferentialsSpecMap_app_toOpen_D`: on every open of `Spec A`,
it sends `tilde.toOpen(D(a))`, for `a : A`, to the actual differential of
the restricted global section corresponding to `a`. The chart isomorphism
is the unique map fitting the factorization through these two
derivation-compatible comparisons and the canonical pullback transports.
The new lemmas express this compatibility as morphism equations; this module
does not add a separate evaluation formula for arbitrary sections on a
chart open.

Given an algebraic basis
`B : Module.Basis ι A (KaehlerDifferential R A)`,
`relativeDifferentialsAffineChartBasisIso` composes the chart isomorphism
with the published model basis isomorphism to give
`(relativeDifferentials f).restrict V.ι ≅ SheafOfModules.free ι`.
The model basis isomorphism uses `B.repr.toModuleIso`, the tilde functor,
`tildeFinsupp`, and `SheafOfModules.pullbackObjFreeIso`.
The definition `relativeDifferentialsAffineChartBasisSections` transports
the canonical free generating sections along the inverse basis isomorphism
using `GeneratingSections.ofEpi`. The instance
`relativeDifferentialsAffineChartBasisSections_isIso` proves that their
associated free-sheaf map `π` is an isomorphism: unfolding `ofEpi_π` and
`free.generatingSections_π` reduces this to the inverse basis isomorphism.
These constructions allow any index type `ι : Type u`. When `[Finite ι]`,
`relativeDifferentialsAffineChartBasisSections_finite` supplies
`IsFiniteType` for these generating sections. Thus a finite algebraic basis
gives actual finite local basis data for the restricted sheaf.

The geometric source is the Stacks Project, Morphisms §29.33 (tag 01UM),
Definition 29.33.1 and Lemmas 29.33.3–5, in registered source
`stacks-relative-differentials-internal-hom-2026-10-21`, folder SHA256
`9c075370ba97d8876785c5486425c6c661765e747452c026583f4dc51f1e1133`.
Lemma 29.33.3 identifies the restricted differential sheaf for open subschemes.
Lemma 29.33.4 relates derivations on spectra to algebraic derivations, and
Lemma 29.33.5 literally compares the affine section module with algebraic
Kähler differentials, compatibly with the derivations.
The sheaf-level chart isomorphism here is a derived construction from the
published locality and Spec comparison proofs, using Mathlib's affine-chart
and module pullback infrastructure. It is not a literal transcription of
the section-module statement. The factorization, uniqueness, and basis
transport are internal consequences of these constructions. No
quasi-coherence assumption on the actual differential sheaf is used.
