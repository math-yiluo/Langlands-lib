# Flat, unramified and étale morphisms over all affinoid pieces, and their composition

Author: Worker 36.

This module defines flatness, unramifiedness and étaleness at a point through
property (b) of Berkovich's Proposition 3.2.3. The pointwise condition is
required for every affinoid piece over every recognized target subset
containing the image point. It shows that these conditions imply the
finite-family versions of `FullRecognitionEtaleMorphisms`, and that the
identity and the locally finite étale morphisms satisfy them. It proves
Berkovich's composition results: flat, unramified and étale morphisms compose.

## Original source and derived provenance

The source is Berkovich, *Étale cohomology for non-Archimedean analytic spaces*
(1993), registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
The relevant original passages are:

- Proposition 3.2.3, printed p.58 / PDF p.55. For a finite morphism `φ`,
  `y ∈ Y` and `x = φ(y)`, the following are equivalent: "a) there exist
  affinoid domains `V₁, …, Vₙ ⊂ X` such that `x ∈ V₁ ∩ … ∩ Vₙ`,
  `V₁ ∪ … ∪ Vₙ` is a neighborhood of `x` and `φ⁻¹(Vᵢ) → Vᵢ` are flat at `y`;
  b) for any affinoid domain `x ∈ V ⊂ X`, `φ⁻¹(V) → V` is flat at `y`";
- Definition 3.2.5, printed p.59 / PDF p.56: flatness at a point means there
  are open neighborhoods `𝒱` of `y` and `𝒰` of `φ(y)` such that `φ` induces a
  finite morphism `𝒱 → 𝒰` "that possesses the equivalent properties of
  Proposition 3.2.3";
- Corollary 3.2.6, printed p.59 / PDF p.56: "Flat quasifinite morphisms are
  preserved under compositions, under any base change functor, and under any
  ground field extension functor";
- Definition 3.3.4 and Proposition 3.3.7, printed p.63 / PDF p.60:
  unramified and étale morphisms, and unramifiedness at `y` as `y` lying
  outside the support of `Ω_{Y/X}`;
- Corollary 3.3.8, printed p.63 / PDF p.60: "Unramified (resp. étale)
  morphisms are preserved under compositions, under any base change functor,
  and under any ground field extension functor."

`IsFlatAtAllPieces` transcribes Definition 3.2.5 with property (b), and
`IsUnramifiedAtAllPieces` uses the same pieces with the pointwise condition of
Proposition 3.3.7. Unit `FullRecognitionEtaleMorphisms` used property (a)
instead. Berkovich proves the two equivalent (Proposition 3.2.3). Here only
the implication (b) ⇒ (a) is proved; the converse uses Berkovich's Lemma 3.2.4
and ground field extension and is not formalized. The composition theorems are
the composition parts of Corollaries 3.2.6 and 3.3.8 for the (b) forms. Base
change and ground field extension are not treated. All proofs are derived.

## Definitions

Let `g : StrongHom A.saturatedPresentation B.saturatedPresentation`, with
full-recognition pair system `P`. Let `Q` be a property of a bounded algebra
map together with a point of the spectrum of its target.

`HasAllPiecesAt Q g y` asks for open `V ∋ y` and open `U` with
`IsFiniteOver g V U`, such that for every recognized target subset `W ⊆ U`
containing `g(y)`, every recognized source subset `V'` with
`V'.locus = V ∩ g⁻¹(W.locus)`, every admissibility proof `h`, and every point
`s` of the spectrum of `V'` with `V'.chart s = y`, the property
`Q (P(V', W, h)) s` holds.

- `IsFlatAtAllPieces g y` uses `IsFlatAtPoint`.
- `IsUnramifiedAtAllPieces g y` uses `IsUnramifiedAtPoint`.
- `IsEtaleAtAllPieces g y` asks for an open `V ∋ y` such that `g` is
  unramified and flat over all pieces at every point of `V`.
- `IsEtaleAllPieces g` asks for this at every point.

## Comparison and basic examples

- `HasAllPiecesAt.hasFinitePiecesAt`: (b) implies (a). The neighborhood basis
  `exists_finite_recognized_nhds_subset` supplies finitely many recognized
  subsets of `U` containing `g(y)` with union a neighborhood. Hence
  `IsFlatAtAllPieces.isFlatAt`, `IsUnramifiedAtAllPieces.isUnramifiedAt`,
  `IsEtaleAtAllPieces.isEtaleAt` and `IsEtaleAllPieces.isEtale` relate these
  notions to those of `FullRecognitionEtaleMorphisms`.
- `hasAllPiecesAt_of_isFiniteOver`: if every piece of a finite morphism
  between open sets has `Q` at every point, then `Q` holds over all pieces at
  every point of the source.
- `IsLocallyFiniteEtaleAt.isEtaleAtAllPieces`, `IsFiniteEtale.isEtaleAllPieces`
  and `isEtaleAllPieces_id`: the algebraically finite étale affinoid maps are
  étale at every point (`AffinoidPointwiseEtale`).

## Composition

`HasAllPiecesAt.comp` is the general composition theorem. Let `Q` compose
along maps of finite type: if `f` has `Q` at `z` and `f'` has `Q` at the image
of `z`, then `f ∘ f'` has `Q` at `z`. Let `Q` also hold for flat surjective maps
at every point. Let `g` have `Q` over all pieces at `y` (neighborhoods `V`,
`U`), and let `g'` have `Q` over all pieces at `g(y)` (neighborhoods `U₂`,
`T₂`). Then the saturated composite has `Q` over all pieces at `y`.

1. Lemma 3.1.2 (`IsFiniteOver.exists_small` of
   `FiniteMorphismSmallNeighborhoods`) gives open `U₃ ⊆ U ∩ U₂` containing
   `g(y)` and `T₃ ⊆ T₂` with `g'` finite from `U₃` to `T₃`. Restricting the
   target of `g` to `U₃` and composing gives a finite morphism from
   `V ∩ g⁻¹(U₃)` to `T₃`.
2. Let `Z ⊆ T₃` be recognized and contain the image of `y`. The new piece
   `Q₃` of `g'` over `Z` has locus `U₃ ∩ g'⁻¹(Z)`, which is the old piece `Q₂`
   (locus `U₂ ∩ g'⁻¹(Z)`) cut by the open set `U₃`. By `ClopenPieceLocalization`
   the restriction from `Q₂` to `Q₃` is flat, surjective and finite. The
   restriction law of the pair system writes the map of `Q₃` as this
   restriction composed with the map of `Q₂`.
3. The piece of `g` over the recognized subset `Q₃ ⊆ U`, which contains
   `g(y)`, has the same locus as the given composite piece, so the two are
   equal. The composition law of pair systems (`fullRecognitionPairs_comp`)
   writes the composite map as the map of `g` over `Q₃` followed by the map of
   `g'` over `Z`.
4. The chart equations identify the intermediate points: the image of `s`
   under the first map is the point of `Q₃` over `g(y)`, and its image under
   the restriction is the point of `Q₂` over `g(y)`. The hypotheses then apply,
   and the two composition steps conclude.

Specializations:

- `IsFlatAtAllPieces.comp`, from `IsFlatAtPoint.comp` and flatness of flat
  maps at points;
- `IsUnramifiedAtAllPieces.comp`, from `IsUnramifiedAtPoint.comp` (maps of
  finite type: finite Banach maps and surjective restrictions are finite) and
  formal unramifiedness of surjective maps;
- `IsEtaleAtAllPieces.comp`, on the intersection of the source neighborhood of
  `g` with the preimage of that of `g'`; and `IsEtaleAllPieces.comp`.

## Scope

No Hausdorffness, nontrivial valuation or strictness is assumed. The following
remain further work: the implication (a) ⇒ (b) of Proposition 3.2.3; base
change and ground field extension; fibre products; and the étale,
quasi-étale and equivariant sites.
