# Parabolic induction preserves normalized-exponent temperedness

Author: Worker 6. Module `Langlands.Representation.Exponents.LeviInductionNormalizedTemperedStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`. Statement `LeviInductionNormalizedTemperedStatement : Prop`; nothing is proved here.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VII.2.2, Lemma, printed p.227 / PDF p.233, with its proof on printed pp.227–228 / PDF pp.233–234. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The lemma says: let `P = MN` be a parabolic subgroup of `G` and `(σ, E)` a tempered representation of `M`; then `i_P^G(σ, E)` is tempered.

This is a **derived** formulation, because temperedness is the published derived predicate `IsNormalizedExponentTempered` (see "Temperedness" below). Otherwise the statement follows the lemma.

## Statement

The statement quantifies over a field `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`, so every nonarchimedean local field of any characteristic, and over a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`. It installs `hG.isAffineHom` and the canonical topology `RationalPointFamily.pointTopology` on `rationalPoints G`, and assumes `[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]` for that topology, as in the published temperedness predicate. It then quantifies over every actual rational parabolic `p : P ⟶ G` with `hp : IsParabolicSubgroup p`, every rational Levi `l : M ⟶ P` with `hl : IsRationalLeviSubgroup l`, and every matching geometric unipotent radical `r : U ⟶ P` with `hr` and `hmul : IsIso (subgroupMultiplication l r)`.

For these data it installs on `rationalPoints M`

- the affine instance `hl.isConnectedReductive.isAffineHom`, from the connected reductivity of the Levi recorded in `IsRationalLeviSubgroup`;
- the canonical topology `leviPointTopology l hl`;
- local compactness and the nonarchimedean-group property, from `leviPoints_locallyCompactSpace p l hp hl` and `leviPoints_nonarchimedeanGroup p l hp hl`.

Then, for every `σ : SmoothRep.{0, u, v} ℂ (rationalPoints M)` with an arbitrary carrier universe `v`, it asserts that `IsNormalizedExponentTempered hl.isConnectedReductive σ` implies `IsNormalizedExponentTempered hG ((leviInductionFunctor p l r hp hr hl hmul).obj σ)`.

## The objects

- `leviInductionFunctor p l r hp hr hl hmul` is Renard's normalized parabolic induction `i_P^G` (VI.1.2, printed pp.135–136 / PDF pp.141–142), applied to representations of `M(F)`. It pulls `σ` back along the inverse of the published isomorphism `leviPointsEquiv p l hp hl : M(F) ≃ₜ* pointImage (l ≫ p)` and applies the published `inductionFunctor` from the literal Levi image. The induced representation lies in carrier universe `max u v`, as for the published induction functor.
- `IsNormalizedExponentTempered hl.isConnectedReductive σ` is the published temperedness predicate for the connected reductive group `M`, with the canonical topology on `M(F)`. Its parabolics, Levi subgroups and split components are those of `M`, as group schemes over `k` with maps into `M`. This is Renard's temperedness of a representation of `M`.
- `IsNormalizedExponentTempered hG _` is the same predicate for `G`.

## Temperedness

The published predicate `IsNormalizedExponentTempered` is a derived formulation of the definition at the start of VII.2.1 (printed p.227 / PDF p.233). It requires admissibility. It also requires, for every actual rational parabolic, rational Levi and split component, that a compatible root presentation exist and that every normalized Jacquet exponent have its `q^(-s)` real part in the closed root cone `pres.nonnegCone` of every compatible presentation. The predicate's own Markdown records why the `q^(-s)` real part is used instead of the raw-log parameter that V.3.20 also writes. This statement uses the predicate unchanged on both sides.

## Faithfulness notes

- The lemma is stated for every parabolic `P = MN`. The statement quantifies over every actual rational parabolic with a rational Levi and a matching radical, not only standard ones.
- The source's `σ` is any tempered representation of `M`. Temperedness includes admissibility, so no further hypothesis is added. No irreducibility, finite length or finite-dimensionality is assumed.
- The local-compactness and nonarchimedean-group instances of `G(F)` are hypotheses, as in the published temperedness predicate. Those of `M(F)` are derived from them, not assumed.

## Remaining obligations

The proof is a separate obligation. The source proof reduces to standard parabolics `Q = LU` and uses the geometric lemma VI.5.1, the Weyl-group representatives `W_{L,M}` of (V.4.6.1) and the lemma of VII.1.1. A proof of this statement also needs three more things. First, normalized induction must preserve admissibility. Second, `IsNormalizedExponentTempered` on `G(F)` requires a compatible presentation for every actual parabolic triple of `G`, which is a separate structural obligation. Third, the transport between `M(F)` and the Levi image must be matched with the parabolic data of `M` used by the hypothesis. None of these is asserted here.

## Provenance

This is a derived statement of the Lemma of VII.2.2 for the represented-parabolic interface. Temperedness on both sides is the published normalized-exponent predicate. The representation of `M` is a representation of `M(F)`, linked to the Levi image of the parabolic by the published `leviPointsEquiv`.
