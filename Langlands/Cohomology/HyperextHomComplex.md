# The abutment of the hyperext spectral sequence as cohomology of a Hom complex

Author: Worker 61. Built on the Library modules
`Langlands.Cohomology.HyperextSpectralSequence` (`hyperextSpectralObject`,
`abutmentIso`) and `Langlands.Cohomology.HyperextSecondPage` (the additive
equivalences `precompAddEquiv` and `postcompAddEquiv`), and on Mathlib's Hom
complexes (`CochainComplex.HomComplex`, `Cochain.toSingleEquiv`,
`HomComplex.homologyAddEquiv`, `CohomologyClass.homAddEquiv`), K-projective
complexes (`IsKProjective.Qh_map_bijective`, `isKProjective_of_projective`)
and derived categories.

For a cochain complex `P` and an object `W` of an abelian category, the
module defines the complex of abelian groups `Hom(P^{-•}, W)` and shows
that, when `P` is K-projective, its cohomology in degree `n` is the group of
morphisms from `P` to `W[n]` in the derived category. That group is the
intended abutment, in total degree `n`, of the hyperext spectral sequence of
`Langlands.Cohomology.HyperextSpectralSequence` for `P` and `W` placed in
degree `0`. So the abutment can be computed from an explicit complex of
projective objects, as in Harris's construction of his spectral sequences.

## The complex `Hom(P^{-•}, W)`

Section `HomObj` takes a preadditive category `C` (objects in `Type u`,
morphisms in `Type v`), a cochain complex `P : CochainComplex C ℤ` and an
object `W : C`.

| Declaration | Meaning |
| --- | --- |
| `homObjComplex P W` | The cochain complex of abelian groups (in `AddCommGrpCat.{v}`, indexed by `ℤ`) with the group `P.X (-n) ⟶ W` in degree `n`. The differential from degree `i` to degree `j` sends `f` to `P.d (-j) (-i) ≫ f`; for `j = i + 1` this is precomposition with the differential `P^{-i-1} ⟶ P^{-i}`. No signs are introduced. |
| `sign n` | The unit `(-1)^{n(n+1)/2}` of `ℤ`, defined as `(n * (n + 1) / 2).negOnePow` (the product `n * (n + 1)` is even, so the integer division is exact). |
| `sign_succ n` | `sign (n + 1) = sign n * (n + 1).negOnePow`. |
| `negOnePow_mul_sign_succ n` | `(n + 1).negOnePow * sign (n + 1) = sign n`. |

The remaining declarations of this section also assume that `C` has a zero
object, so that `W₀ = (CochainComplex.singleFunctor C 0).obj W`, the complex
with `W` in degree `0` and zero elsewhere, is defined.

| Declaration | Meaning |
| --- | --- |
| `cochainAddEquiv P W n` | The additive equivalence from Mathlib's group of cochains `Cochain P W₀ n` to `P.X (-n) ⟶ W`: Mathlib's `Cochain.toSingleEquiv` (the component of the cochain from degree `-n` to degree `0`), followed by multiplication by `sign n`. |
| `cochainAddEquiv_toSingleMk` | `cochainAddEquiv P W n` sends the cochain `Cochain.toSingleMk f _` built from `f : P.X (-n) ⟶ W` to `sign n • f`. |
| `homComplexSingleIso P W` | An isomorphism of cochain complexes from Mathlib's Hom complex `HomComplex P W₀` to `homObjComplex P W`, whose component in degree `n` is `cochainAddEquiv P W n`. |

Why the sign: by Mathlib's `Cochain.δ_toSingleMk`, the differential of
`HomComplex P W₀` from degree `n` to degree `n + 1` sends
`Cochain.toSingleMk f _` to `(-1)^{n+1} • Cochain.toSingleMk (P.d (-(n + 1)) (-n) ≫ f) _`.
The components `cochainAddEquiv` commute with the differentials because
`(-1)^{n+1} · sign (n + 1) = sign n` (`negOnePow_mul_sign_succ`); the proof
of `homComplexSingleIso` checks this on cochains of the form
`Cochain.toSingleMk f _`, which are all cochains
(`Cochain.toSingleMk_surjective`).

## Comparison with the derived category

Section `Derived` takes an abelian category `C` (objects in `Type u`,
morphisms in `Type v`) with `HasDerivedCategory.{w} C`, so that morphisms of
`DerivedCategory C` lie in `Type w`. `Q` is the localization functor from
cochain complexes to the derived category, `Qh` the induced functor on the
homotopy category, `W₀` is as above, and
`DerivedCategory.singleFunctor C 0` places an object in degree `0` in the
derived category. A complex `P` is K-projective (`P.IsKProjective`) when every
morphism from `P` to an acyclic complex is homotopic to zero.

| Declaration | Statement |
| --- | --- |
| `cohomologyClassAddEquiv P L n` | For cochain complexes `P`, `L` with `P` K-projective, an additive equivalence `CohomologyClass P L n ≃+ (Q.obj P ⟶ (Q.obj L)⟦n⟧)`. |
| `homComplexHomologyAddEquiv P L n` | For `P` K-projective, `(HomComplex P L).homology n ≃+ (Q.obj P ⟶ (Q.obj L)⟦n⟧)`. |
| `homObjHomologyAddEquiv P W n` | For `P` K-projective, `(homObjComplex P W).homology n ≃+ (Q.obj P ⟶ ((DerivedCategory.singleFunctor C 0).obj W)⟦n⟧)`. |
| `abutmentAddEquiv P W n` | For `P` K-projective, the term in degree `n` of `hyperextSpectralObject TStructure.t (Q.obj P) ((DerivedCategory.singleFunctor C 0).obj W)` at the arrow `⊥ ⟶ ⊤` of `EInt` is additively equivalent to `(homObjComplex P W).homology n`. |
| `homObjHomologyAddEquivOfProjective P W n d` | `homObjHomologyAddEquiv P W n` for a complex `P` that is strictly bounded above by `d` (`P.IsStrictlyLE d`) and has projective terms (`∀ k, Projective (P.X k)`). |

Construction of `cohomologyClassAddEquiv P L n`, as a composite of additive
equivalences:

1. Mathlib's `CohomologyClass.homAddEquiv`, from cohomology classes of
   degree `n` of `HomComplex P L` to morphisms `P ⟶ L⟦n⟧` in the homotopy
   category;
2. the map induced by `Qh` on these morphisms, bijective because `P` is
   K-projective (Mathlib's `IsKProjective.Qh_map_bijective`); it is additive
   because `Qh` is an additive functor;
3. precomposition with the inverse of the component at `P` of Mathlib's
   `quotientCompQhIso C`, which identifies `Qh` applied to the image of `P`
   in the homotopy category with `Q.obj P`;
4. postcomposition with the component at `L⟦n⟧` of `quotientCompQhIso C`,
   followed by the component at `L` of `Q.commShiftIso n`, the identification
   `Q.obj (L⟦n⟧) ≅ (Q.obj L)⟦n⟧`.

Mathlib's `CohomologyClass.equivOfIsKProjective` is a similar bijection, onto
`SmallShiftedHom` rather than onto morphisms of the derived category, and is
not stated to be additive.

`homComplexHomologyAddEquiv` composes Mathlib's
`HomComplex.homologyAddEquiv` (cohomology of `HomComplex P L` in degree `n`
equals `CohomologyClass P L n`) with `cohomologyClassAddEquiv`.

`homObjHomologyAddEquiv P W n` is the inverse of the map on cohomology in
degree `n` induced by `homComplexSingleIso P W`, followed by
`homComplexHomologyAddEquiv P W₀ n`. Here `Q.obj W₀` is definitionally
`(DerivedCategory.singleFunctor C 0).obj W`, since Mathlib defines
`DerivedCategory.singleFunctors C` by composing
`CochainComplex.singleFunctors C` with `Q`.

`abutmentAddEquiv P W n` is `abutmentIso` of
`Langlands.Cohomology.HyperextSpectralSequence` (which identifies the term
with `Q.obj P ⟶ ((DerivedCategory.singleFunctor C 0).obj W)⟦n⟧` by
definition), followed by the inverse of `homObjHomologyAddEquiv P W n`.

`homObjHomologyAddEquivOfProjective` uses Mathlib's
`isKProjective_of_projective`: a cochain complex strictly bounded above with
projective terms is K-projective.

The equivalences depend on the sign convention of `homComplexSingleIso` and
on the identifications of steps 3 and 4. No compatibility with the
differentials, edge maps or filtration of the spectral sequence is claimed.

## Provenance and interpretation

Harris constructs his spectral sequences by computing compactly supported
cohomology with a complex of smooth projective modules and then taking `Hom`
into the coefficient module term by term. The passages below were read by
Worker 61 in the rendered page scans.

- Harris, *Supercuspidal representations in the cohomology of Drinfel'd
  upper half spaces; elaboration of Carayol's program*, Invent. Math. 129
  (1997), 75-119 (source `harris-1997-drinfeld-cohomology`), proof of Lemma
  6, printed p.94 (one-based PDF page 20). Harris takes the double complex

  (7) `C^{i,j}(S_N) = Hom_{GJ}(Z^{-i,2(n-1)-j}(n-1), 𝒜(G𝒥, C^p)^+)`,

  with `Z^{•,•}` as in Harris's (6), and continues:
  "Recalling that `𝒫^•` is a complex of projective objects in the category of
  smooth `Q_ℓ[GJ]`-modules, and bearing in mind (5), we thus see that (7) can
  be rewritten

  `Rf_*(Q_ℓ) ⥲ RHom_{smooth GJ-modules}(Rp_!(Q_ℓ)(n-1), 𝒜(G𝒥, C^p)^+)`".
- Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
  J. Math. Kyoto Univ. 39-2 (1999), 299-318 (source
  `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`), proof of
  Proposition 4.4, printed p.310 (one-based PDF page 12), on the spectral
  sequence (4.4.1): "This spectral sequence is constructed just as in the
  proof of Lemma 6 of [H1]. There the main step is to show that
  `H_c^•(M̌_N, O_m)` can be calculated by a complex of smooth projective
  `GJ`-modules over `Q_ℓ`." (`[H1]` is Harris 1997, and the printed text says
  "over `Q_ℓ`" here.)

The step formalized here is the generic part of this argument: for a
K-projective complex `P` (for example a bounded above complex of projective
objects), `RHom(P, W)` in degree `n`, that is `Hom(P, W[n])` in the derived
category, is the cohomology in degree `n` of the explicit complex
`Hom(P^{-•}, W)`. The statements and proofs are ours, assembled from Mathlib
and the Library; the identification itself is standard.

Specialization (explanation only). In Harris's situation `C` would be the
category of smooth representations of `GJ` with coefficients `O_m` or `Q_ℓ`,
`W` the coefficient module, and `P` a bounded above complex of projective
smooth representations computing compactly supported cohomology up to the
shift and Tate twist of Harris's duality argument. None of this is formalized:
no complex of Harris's compactly induced modules is defined, no such module is
shown to be projective (Harris uses [Vi, 5.9 (d)] and banality or projective
resolutions for this), Harris's double complex and its simple complex are not
treated, and no derived category instance for the Library's smooth
representation categories is fixed here.

## Scope

- Only the second argument placed in degree `0` is treated by
  `homObjComplex`; `homComplexHomologyAddEquiv` allows any complex `L`.
- All equivalences are additive. No linearity over a coefficient ring and no
  naturality in `P`, `L` or `W` is stated.
- `HasDerivedCategory.{w} C` is a hypothesis; the results hold for each such
  instance.
- Convergence of the hyperext spectral sequence is not proved;
  `abutmentAddEquiv` only identifies the intended abutment.

Source registrations: Harris 1997, `harris-1997-drinfeld-cohomology`, SHA-256
`aea284b917442459028b710dbfd9ae537631490504f3bc6d54a1e76ee697e0d9`, printed
p.94 read in the rendered page scan; Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`, printed
p.310 read in the rendered page scan.

Dependencies: `Langlands.Cohomology.HyperextSecondPage` (which imports
`Langlands.Cohomology.HyperextSpectralSequence`) and Mathlib
(`Mathlib.Algebra.Homology.DerivedCategory.KProjective`,
`Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology`,
`Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle`), pinned to Lean
4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
