# Collapse of a finite character-localization filtration

Worker 177 authored the Lean and Markdown pair from the formulation supplied
by Worker 330 in the task specification.

`Langlands.Jacquet.Localization.FiltrationCollapseStatement.{uG,uV}` is a
closed proposition definition. It states a derived finite-filtration consequence
of the published character-localization exactness theorem. This module does
not prove the proposition.

## Statement

Let `G : Type uG` be a topological group satisfying
`IsLimitOfCompactSubgroups (⊤ : Subgroup G)`: every compact subset of the whole
group, represented by the top subgroup with its induced topology, lies in a
compact subgroup. Let `θ : G →* ℂˣ` have locally constant complex values,
and let `A : Rep.{uV} ℂ G` be smooth. The group universe `uG` and representation
carrier universe `uV` are independent; the coefficient field is fixed to `ℂ`.

Write

```text
C(ρ) = Coinvariants ρ (⊤ : Subgroup G)
         (θ.comp (⊤ : Subgroup G).subtype).
```

This is the actual quotient by the complex span of the character relations
`ρ(g)v - θ(g) • v`.

For an actual filtration `s : ObjectRepFiltration A m` and an arbitrary
`j : Fin m`, assume `Subsingleton (C((s.gradedRepresentation i).ρ))` for every
`i ≠ j`. The conclusion is

```text
Nonempty (C(A.ρ) ≃ₗ[ℂ] C((s.gradedRepresentation j).ρ)).
```

The filtration consists of `m + 1` invariant subspaces, increasing from zero
to all of `A`. Its graded representations are the actual upper-step quotients
by the lower steps. `Subsingleton` expresses vanishing of a localized module.
The chosen quotient may also vanish. The index may occur anywhere; if `m = 0`
there is no `j : Fin m`, so that case is vacuous.

There are no finite-dimensionality, semisimplicity, splitting or pre-existing
quotient-identification hypotheses. Exactness and injectivity or surjectivity
of localized maps are not premises. The conclusion asserts existence of a
complex linear equivalence only. It specifies no natural transformation,
equivariance for an additional group, or functorial identification of graded
objects.

## Derived argument and remaining proof

Set `S_i = s.subrepresentation i` and
`Q_i = s.gradedRepresentation i`. The actual inclusions and the published
`s.gradedProjection i` give short exact sequences

```text
0 → S_i → S_(i+1) → Q_i → 0.
```

Here the representations on the steps are `S_i.toRepresentation`.
Injectivity of the inclusion and its image being the projection kernel
follow from the invariant-subspace quotient construction;
`gradedProjection_surjective` supplies surjectivity. These facts must be
derived for the supplied filtration in the eventual proof. Smoothness of
the steps and quotients follows from smoothness of `A`.

Apply `map_injective_of_smooth`, `map_range_eq_ker` and `map_surjective`
from `Langlands.Representation.Jacquet.LocalizationExactnessProof`, or their
aggregate `characterLocalizationExactness`, to these sequences. Take the
localizing subgroup to be `⊤`, restrict `θ` along its subtype, and take the
normalizing subgroup to be `⊥`. The normalizing and character-invariance
conditions for that trivial subgroup are automatic. Local constancy passes
to the restricted character by composition with the continuous subtype map.
The resulting underlying linear maps give short exact sequences

```text
0 → C(S_i) → C(S_(i+1)) → C(Q_i) → 0.
```

Whenever `i ≠ j`, vanishing of `C(Q_i)` makes the localized inclusion
bijective and hence a linear equivalence. Starting with the zero initial
step, finite induction through indices below `j` shows that `C(S_j)` is
zero. At `j`, exactness therefore makes the localized graded projection
`C(S_(j+1)) → C(Q_j)` bijective. Above `j`, the remaining localized
inclusions are equivalences. Compose their inverses from the final step,
identify that step with `A` using the filtration endpoint, and then apply
the projection equivalence at `j`. This yields the stated equivalence
`C(A) ≃ₗ[ℂ] C(Q_j)`. This paragraph describes the proof obligation; the
finite induction and its composition are not implemented in this statement
module.

## Source and provenance

I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
p-adic groups I*, Ann. Sci. ENS (4) 10 (1977), 441–472. Registered source:
`bernstein-zelevinsky-1977-induced-i`. Original:
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.
SHA256:
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

Section 1.8(b), printed page 444 / PDF page 5, defines the character-relation
quotient. Proposition 1.9(a), printed page 445 / PDF page 6, gives localization
exactness under the compact-subgroup containment condition stated immediately
before it. Section 1.11 on that same page defines gluing by a finite
zero-to-full filtration and its successive quotients. Worker 177 read PDF
pages 5–6 and visually checked page 6 for this task. No source-specific errata
entry was found in the available current project and Library notes.

The single-survivor assertion is an internal consequence of exactness and
the finite-filtration convention, not a literal theorem quotation from BZ77.
Its arbitrary-topological-group scope is justified by the already published
finite-averaging proof of character-localization exactness, whose Lean proof
and companion Markdown were read for this statement. The original source
works with locally profinite groups; this module does not attribute the
broader scope to it. The conclusion concerns quotient vector spaces, so no
normalization of an additional group action is involved.

The statement imports the published object-filtration definitions and
localization exactness statement. The existing exactness proof supplies the
route for a separate proof task. This module asserts no Whittaker heredity,
orbit identification or dimension-one theorem.

Environment: `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`.
