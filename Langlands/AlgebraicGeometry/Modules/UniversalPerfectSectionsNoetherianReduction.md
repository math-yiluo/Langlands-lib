# Reduction of universal perfect sections to noetherian bases

Module `Langlands.AlgebraicGeometry.Modules.UniversalPerfectSectionsNoetherianReduction`,
namespace `Langlands.AlgebraicGeometry.Modules`, universe `u`. The interface (the statement
body, the theorem name and the order of its three hypotheses) was fixed by Worker 958 for the
proof task of `UniversalPerfectSectionsStatement` (task
`5056e5fc-5861-489e-adae-be84a23164c5`). The Lean proof is by Worker 975.

`IsUniversalPerfectSectionsRepresentative f M K` is the published predicate on
`K : CochainComplex (ModuleCat R) ℤ` for `f : X ⟶ Spec R` and `M : X.Modules`. It says that
`K` is bounded with finite projective terms, computes the derived `R`-module sections of `M`,
and that for every ring map `φ : R ⟶ T` its degreewise base change computes the derived
`T`-module sections of the pullback of `M` to `pullback f (Spec.map φ)`. `Picard.LineBundle X`
is the published type of line bundles on `X`, with underlying module `L.obj` and proof
`L.property : IsLocallyFreeRankOne L.obj`.

## Definition

```lean
def UniversalPerfectSectionsNoetherianReductionStatement : Prop :=
  NoetherianApproximation.IsProperSubalgebraDescentStatement.{u} →
  NoetherianApproximation.LineBundleSubalgebraDescentStatement.{u} →
  NoetherianUniversalPerfectSectionsStatement.{u} →
  UniversalPerfectSectionsStatement.{u}
```

Three propositions together imply the published `UniversalPerfectSectionsStatement.{u}`:
- `IsProperSubalgebraDescentStatement`: properness descends to a finitely generated
  subalgebra over a noetherian ring.
- `LineBundleSubalgebraDescentStatement`: a line bundle on a base change to `Spec A` comes from
  a finitely generated subalgebra.
- `NoetherianUniversalPerfectSectionsStatement`: `UniversalPerfectSectionsStatement` for
  noetherian bases.

The published `UniversalPerfectSectionsStatement` asks, for every commutative ring `R`, every
smooth proper `f : X ⟶ Spec R` and every line bundle `L` on `X`, for a complex `K` with
`IsUniversalPerfectSectionsRepresentative f L.obj K`.

The statement only records an implication. It does not assert any of the three hypotheses.
The published `NoetherianApproximation.isProperSubalgebraDescent` and
`NoetherianApproximation.lineBundleSubalgebraDescent` prove the first two.

## Main result

```lean
theorem universalPerfectSectionsNoetherianReduction :
    UniversalPerfectSectionsNoetherianReductionStatement.{u}
```

So `UniversalPerfectSectionsStatement.{u}` follows from the noetherian case once
`isProperSubalgebraDescent` and `lineBundleSubalgebraDescent` are supplied for the first two
hypotheses.

## Auxiliary results

The following theorems are in namespace `NoetherianReduction`:

- `isNoetherianRing_of_fg`: a finitely generated subalgebra `T` over a noetherian ring is a
  noetherian ring.
- `iff_pullback_snd_of_isPullback`: for a property `P` of morphisms stable under base change,
  and a pullback square `IsPullback a f g ψ`, `P f` holds exactly when `P` holds for
  `pullback.snd g ψ`. The descent statements are phrased with Mathlib's chosen pullback; this
  moves between it and an arbitrary pullback square.
- `exists_isPullback_subalgebra` and `exists_isPullback_subalgebra'`: let `T` be a ring with
  `[Algebra T A]`, `T'` a `T`-subalgebra of `A`, and let `X` be the base change of
  `g : Y ⟶ Spec T` along `Spec A ⟶ Spec T`. Then `X` is the base change, along
  `Spec A ⟶ Spec T'`, of the base change `Y'` of `Y` to `Spec T'`. The unprimed version uses
  `Y' = pullback g (Spec.map (algebraMap T T'))` and gives the map `X ⟶ Y'` explicitly through
  its two projections. The primed version leaves `Y'` abstract.
- `exists_rep_of_finitePresentation`, `exists_rep_of_smooth`, `exists_rep_of_isSeparated` and
  `exists_rep_of_isProper` are the stages of the reduction (see Proof). Each works over an
  arbitrary noetherian ring `T` with `[Algebra T A]`. It assumes a morphism to `Spec T` whose
  base change to `Spec A` is the given smooth proper `f : X ⟶ Spec A`, with progressively more
  properties. It concludes that a representative for `f` and `L.obj` exists.
- `exists_isUniversalPerfectSectionsRepresentative`: the conclusion of
  `UniversalPerfectSectionsStatement` over `CommRingCat.of A`, for any commutative ring `A`
  and the three hypotheses.

## Provenance

Derived. This is the noetherian-approximation step in the proof of Stacks Project, Derived
Categories of Schemes, `lemma-base-change-tensor-perfect`. See `perfect.tex` at git commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`, lines 7396–7441, in the registered source
`stacks-perfect-complexes-a04446e5`. That lemma gives the published 0B91 and Remark 0A1I as
special cases. They are the sources of `UniversalPerfectSectionsStatement`. Its proof
proceeds as follows:
- Write `R` as a filtered colimit of noetherian rings `R_i`.
- Descend `X` to a scheme of finite presentation over some `R_i` (Limits, tag 01ZM).
- Descend the module and its flatness and proper support.
- Apply the noetherian case.
- Use base change.

The present proof follows that outline. The steps differ in four ways:
- **Colimit.** The colimit is the directed union of the finitely generated subalgebras of `A`
  over its prime subring.
- **Descent steps.** The flatness and support conditions on a line bundle are replaced by
  descending smoothness (Limits, tag 0C0C) and properness (tag 081F) of the morphism, and the
  line bundle itself (tag 0B8W). Separatedness (tag 01ZQ) is descended first because the
  properness descent requires it. These are the published `NoetherianApproximation`
  propositions, whose Markdown cites `limits.tex` in the registered source
  `stacks-limits-of-schemes-a04446e5`.
- **Base change.** The base-change property is the published
  `universalPerfectSectionsScalarTower` together with the published
  `universalPerfectSectionsIsoTransport`.
- **Proof structure.** The stage lemmas and pullback pastings are internal.

## Proof

- `isNoetherianRing_of_fg`: `Subalgebra.fg_iff_finiteType` and
  `Algebra.FiniteType.isNoetherianRing` (Hilbert's basis theorem).
- `iff_pullback_snd_of_isPullback`: `IsPullback.isoPullback_hom_snd` writes `f` as an
  isomorphism followed by `pullback.snd g ψ`. A property stable under base change respects
  isomorphisms (`cancel_left_of_respectsIso`).
- `exists_isPullback_subalgebra`: the square from `X` to `Y'` is a pullback by
  `IsPullback.of_right`. It pastes onto the chosen pullback square of `g` and
  `Spec T' ⟶ Spec T`, and the composite square is the given one, because
  `Spec A ⟶ Spec T' ⟶ Spec T` is `Spec A ⟶ Spec T` (`IsScalarTower.algebraMap_eq`).
- `exists_rep_of_isProper`, for `T` noetherian and `f₄ : X₄ ⟶ Spec T` smooth and proper with
  base change `f`:
  - Line-bundle descent gives a finitely generated `T`-subalgebra `T₅` of `A`, a line bundle
    `M₀` on `X₅ = pullback f₄ (Spec T₅ ⟶ Spec T)` and, for every map `X ⟶ X₅` over `X₄` and
    `Spec T₅`, an isomorphism between the pullback of `M₀` and `L.obj`.
  - `T₅` is noetherian, and `X₅ ⟶ Spec T₅` is smooth and proper by base change. The noetherian
    case gives a representative `K₀` for `M₀`.
  - `universalPerfectSectionsScalarTower` with `T₅ ⟶ A` shows that the base change of `K₀`
    represents the pullback of `M₀` to `pullback (X₅ ⟶ Spec T₅) (Spec A ⟶ Spec T₅)`.
  - By `exists_isPullback_subalgebra`, `X` is isomorphic to that pullback over `Spec A`
    (`IsPullback.isoPullback`). Under this isomorphism the pulled-back `M₀` corresponds to
    `L.obj`, by the descended isomorphism and `Scheme.Modules.pullbackComp`.
  - `universalPerfectSectionsIsoTransport` gives a representative for `f` and `L.obj`.
- `exists_rep_of_isSeparated`: `f` is proper, so the base change of `f₃` to `Spec A` is proper
  (`iff_pullback_snd_of_isPullback`). Properness descent (the hypothesis) gives a finitely
  generated `T₄`. `exists_isPullback_subalgebra'` gives `f₄ : X₄ ⟶ Spec T₄` with base change
  `f`. It is proper by the descent, and smooth by base change. Then apply
  `exists_rep_of_isProper` over `T₄`.
- `exists_rep_of_smooth`: in the same way, separatedness descent
  (`isSeparatedSubalgebraDescent`) gives `T₃` and a separated, smooth, quasi-compact `f₃`.
  Then apply `exists_rep_of_isSeparated` over `T₃`.
- `exists_rep_of_finitePresentation`: in the same way, smoothness descent
  (`smoothSubalgebraDescent`) gives `T₂` and a smooth, quasi-compact, quasi-separated `f₂`.
  Then apply `exists_rep_of_smooth` over `T₂`.
- `exists_isUniversalPerfectSectionsRepresentative`: the prime subring
  `⊥ : Subalgebra ℤ A` is a finitely generated `ℤ`-algebra (`Subalgebra.fg_bot`), hence
  noetherian. `f` is smooth and proper, hence quasi-compact, quasi-separated and locally of
  finite presentation. Scheme descent (`schemeSubalgebraDescent` with `A₀ = ⊥`) gives a
  finitely generated `⊥`-subalgebra `T₁` and `f₁ : X₁ ⟶ Spec T₁` with base change `f`. Then
  apply `exists_rep_of_finitePresentation` over `T₁`.
- `universalPerfectSectionsNoetherianReduction`: the previous theorem with `A = R`. Here
  `CommRingCat.of R` is definitionally `R`.

Each stage takes an abstract noetherian ring `T` rather than a subalgebra of a subalgebra. In
a single proof, instance search failed to find `CommRing` on the third nested subalgebra. So
each stage hands its subalgebra `↥T'` to the next one as the ring `T`.
