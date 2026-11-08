# Flat, unramified and étale quasifinite morphisms through full-recognition pair systems

Author: Worker 36.

This module defines Berkovich's flat, unramified and étale morphisms, at a
point and globally, for strong maps of local-domain enlargements. The
definitions use the finite morphisms of `FullRecognitionFiniteMorphisms` and
the pointwise conditions on affinoid maps of `AffinoidPointwiseEtale`. The
module proves that the recognized affinoid subsets inside any neighborhood of
a point form a finite family whose union is again a neighborhood. It then
shows that the finite étale morphisms of `FullRecognitionFiniteMorphisms` are
étale in this sense, so the identity is étale.

## Original source and derived provenance

The source is Berkovich, *Étale cohomology for non-Archimedean analytic spaces*
(1993), registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The relevant original passages are:

- Definition 3.1.1, printed p.54 / PDF p.51: finiteness at a point and
  quasifinite morphisms (formalized in `FullRecognitionFiniteMorphisms`);
- Proposition 3.2.3, printed p.58 / PDF p.55. For a finite morphism
  `φ : Y → X`, `y ∈ Y` and `x = φ(y)`, the following are equivalent:
  "a) there exist affinoid domains `V_1, …, V_n ⊂ X` such that
  `x ∈ V_1 ∩ … ∩ V_n`, `V_1 ∪ … ∪ V_n` is a neighborhood of `x` and
  `φ⁻¹(V_i) → V_i` are flat at `y`; b) for any affinoid domain `x ∈ V ⊂ X`,
  `φ⁻¹(V) → V` is flat at `y`";
- Definition 3.2.5, printed p.59 / PDF p.56: a quasifinite morphism `φ` "is
  said to be flat at a point `y ∈ Y` if there exist open neighborhoods `𝒱` of
  `y` and `𝒰` of `φ(y)` such that `φ` induces a finite morphism `𝒱 → 𝒰` that
  possesses the equivalent properties of Proposition 3.2.3; `φ` is said to be
  flat if it is flat at all points of `Y`";
- Definition 3.3.4, printed p.63 / PDF p.60: a quasifinite morphism is
  unramified if `Ω_{Y/X} = 0`, étale if it is unramified and flat, and
  unramified (resp. étale) at `y` if some open neighborhood of `y` is
  unramified (resp. étale) over `X`;
- Proposition 3.3.7(a)⇔(b), printed p.63 / PDF p.60: a quasifinite morphism
  is unramified at `y` if and only if the support of `Ω_{Y/X}` does not
  contain `y`; §1.3, printed p.25 / PDF p.22: a point lies in the support of a
  coherent sheaf if it lies in the support of its restriction to some (and
  therefore any) affinoid domain containing it.

`IsFlatAt` transcribes Definition 3.2.5 with property (a) of Proposition
3.2.3. The affinoid domains are the recognized subsets of the full
recognition, as in `FullRecognitionFiniteMorphisms`. Flatness of a finite
morphism of affinoid spaces at `y` is `BoundedAlgHom.IsFlatAtPoint`, the
characterization of Proposition 3.2.1 (see `AffinoidPointwiseEtale`).

`IsUnramifiedAt` uses Proposition 3.3.7(b) instead of the open-neighborhood
form of Definition 3.3.4. It asks for the same finite affinoid pieces as
`IsFlatAt`, on which `y` lies outside the support of the module of
differentials (`BoundedAlgHom.IsUnramifiedAtPoint`). Berkovich's sheaf
`Ω_{Y/X}` is not formalized. The identification of its restriction to these
pieces with the algebraic module of differentials is Lemma 3.3.5 and its proof,
and is not proved here.

`IsEtaleAt` asks for an open neighborhood of `y` at every point of which `g`
is unramified and flat. Definition 3.3.4 asks instead that the induced
morphism from the neighborhood be étale. The two agree because flatness and
unramifiedness at a point depend only on neighborhoods of the point, by
Berkovich's Lemma 3.1.2. That lemma is not formalized, and this definition is
derived.

## Neighborhoods of recognized subsets

Let `a` be an indexed affinoid atlas on `X`, `x ∈ X` and `U` a neighborhood
of `x`. `IndexedAffinoidAtlas.exists_finite_recognized_nhds_subset` gives a
finite set `I` of recognized subsets of the full recognition (recognized
subsets of `a.saturatedAtlas`), each containing `x` and contained in `U`, whose
union is a neighborhood of `x`.

1. The chart family of `a` is a net, so finitely many chart ranges `σ` contain
   `x` and have union a neighborhood of `x`.
2. For a chart `i` in `σ` with `x = chart i s`, the preimage of `U` is a
   neighborhood of `s`. The Library's `RationalChart.exists_rational_neighborhood`
   gives a rational chart `d` of the chart algebra whose locus is a
   neighborhood of `s` inside that preimage. The local domain `(i, d.toDomain)`
   has the recognized subset `recognizedLocalDomain`, with locus
   `chart i '' d.locus`. This locus contains `x` and lies in `U`.
3. The chart is an embedding, so there is a neighborhood `t_i` of `x` with
   `t_i ∩ range (chart i) ⊆ chart i '' d.locus`.
4. The intersection of the finitely many `t_i`, intersected with the union of
   the chart ranges in `σ`, is a neighborhood of `x` contained in the union of
   the chosen recognized subsets. The family is finite as a dependent image of
   `σ`.

## Definitions

Let `A`, `B` be presentations and
`g : StrongHom A.saturatedPresentation B.saturatedPresentation`, with
full-recognition pair system `P`. Let `Q` be a property of a bounded algebra
map together with a point of the spectrum of its target.

`HasFinitePiecesAt Q g y` asks for:

- open `V ∋ y` and open `U` with `IsFiniteOver g V U`;
- a finite set `I` of recognized target subsets, each contained in `U` and
  containing `g(y)`, whose union is a neighborhood of `g(y)`;
- for every `W ∈ I`, every recognized source subset `V'` with
  `V'.locus = V ∩ g⁻¹(W.locus)`, every admissibility proof `h`, and every
  spectrum point `s` of `V'` with `V'.chart s = y`, the property
  `Q (P(V', W, h)) s`.

`IsFiniteOver g V U` supplies such a `V'` for each `W`. A recognized subset is
determined by its locus, so `V'` is unique. Since `y ∈ V` and `g(y) ∈ W`, the
point `y` lies in `V'.locus`, the range of `V'.chart`, so the point `s`
exists.

- `IsFlatAt g y` is `HasFinitePiecesAt` with `IsFlatAtPoint`;
  `IsFlat g` asks for it at every point.
- `IsUnramifiedAt g y` is `HasFinitePiecesAt` with `IsUnramifiedAtPoint`;
  `IsUnramified g` asks for it at every point.
- `IsEtale g` is `IsUnramified g ∧ IsFlat g`.
- `IsEtaleAt g y` asks for an open `V ∋ y` such that `g` is unramified and
  flat at every point of `V`.

## Results

- `HasFinitePiecesAt.isFiniteAt` forgets the pieces. Hence flatness,
  unramifiedness and étaleness at a point imply finiteness at the point
  (`IsFlatAt.isFiniteAt`, `IsUnramifiedAt.isFiniteAt`,
  `IsEtaleAt.isFiniteAt`). Flat, unramified and étale morphisms are
  quasifinite (`IsFlat.isQuasifinite`, `IsUnramified.isQuasifinite`,
  `IsEtale.isQuasifinite`).
- `HasFinitePiecesAt.mono` weakens the pointwise property.
- `IsEtaleAt.isUnramifiedAt` and `IsEtaleAt.isFlatAt` evaluate the
  neighborhood condition at the point itself.
- `isEtale_iff_forall_isEtaleAt`: `g` is étale if and only if it is étale at
  every point. One direction uses the whole space as the neighborhood.
- `hasFinitePiecesAt_of_isFiniteOver`: let `V`, `U` be open with
  `IsFiniteOver g V U`, and suppose that every induced affinoid map over a
  recognized `W ⊆ U` has the property `Q` at every point. Then
  `HasFinitePiecesAt Q g y` holds for every `y ∈ V`. The neighborhood theorem
  applied to `U`, a neighborhood of `g(y)`, supplies the pieces.
- `IsLocallyFiniteEtaleAt.isEtaleAt`: the locally finite étale condition of
  `FullRecognitionFiniteMorphisms` implies étaleness at the point. Its affinoid
  maps are algebraically finite étale. By `AffinoidPointwiseEtale` they are
  flat and unramified at every point. A given `V'` agrees with the recognized
  subset supplied by `IsFiniteEtaleOver`, since both have the same locus.
- `IsFiniteEtale.isEtale` (with `V = U` the whole spaces) and `isEtale_id`, by
  `isFiniteEtale_id` of `FullRecognitionFiniteMorphisms`.

## Scope

No Hausdorffness, nontrivial valuation or strictness is assumed. The
following remain further work: Lemma 3.1.2, that the neighborhoods in finiteness at a point
can be chosen arbitrarily small, and with it the composition and base-change
laws for flat, unramified and étale morphisms (Corollaries 3.2.6 and 3.3.8);
local isomorphisms and open immersions as étale morphisms; fiber products;
the local-ring definitions of flatness and the sheaf `Ω_{Y/X}`; the étale and
quasi-étale sites; and the Harris specializations.
