# The centralizer of a diagonalizable subgroup is open in its normalizer

Module: `Langlands.GroupScheme.Torus.DiagonalizableCentralizerOpen`.

## Main results

Let `R` be a commutative ring and `Λ` a finitely generated abelian group (`[AddGroup.FG Λ]`).
`Λ` may have torsion. Write `D(Λ) = Diagonalizable.groupScheme R Λ` for the diagonalizable
group scheme over `Spec R`.

- `Langlands.GroupScheme.diagonalizableCentralizer_isOpenImmersion_of_iso`: take group schemes
  `G H N C` over `Spec R`, a homomorphism `i : H ⟶ G` whose underlying morphism of schemes is
  a monomorphism (`[Mono i.hom.hom.left]`), and an isomorphism `e : H ≅ D(Λ)`. Let `n : N ⟶ G`
  represent the all-test normalizer `(SubgroupFunctor.range i).normalizer`, and let `c : C ⟶ N`
  represent the preimage `((SubgroupFunctor.range i).centralizer).comap n` of the all-test
  centralizer. Then `c.hom.hom.left` is an open immersion.
- `Langlands.GroupScheme.diagonalizableCentralizer_isOpenImmersion_of_mono`: the same
  conclusion for a homomorphism `i : D(Λ) ⟶ G` itself, with an explicit hypothesis
  `Mono i.hom.hom.left`. Here the normalizer is written `torusNormalizer i`, which is
  `(range i).normalizer` by definition. The centralizer is written `torusCentralizer i`, which
  equals `(range i).centralizer` by `torusCentralizer_eq_centralizer_range`.
- `Langlands.GroupScheme.diagonalizableCentralizer_isOpenImmersion_field`: the special case
  `R = k` a field (`Spec (CommRingCat.of k)`). Its binders are in the order `k, M, G, N, C, i,
  hi, n, c, hn, hc`, the order of the body of `DiagonalizableCentralizerOpenProperty`, the
  split-case input of the reduction `MultiplicativeTypeCentralizerOpenReduction` toward
  `MultiplicativeTypeCentralizerOpenStatement` (Milne, *Algebraic Groups*, 12.40). This module
  does not import that reduction.

No finiteness, smoothness, reducedness or affineness of `G`, `N` or `C` is assumed. The
represented subgroups are subgroup functors on all test schemes over `Spec R`
(`SubgroupFunctor.IsRepresentedBy`).

## Definitions

All of the following are in the namespace `Langlands.GroupScheme.DiagonalizableConjugation`.

- `Chars Λ X` is the group `Multiplicative Λ →* Γ(X, ⊤)ˣ` of characters with values in the
  global units of a scheme `X`. `charsRestrict f` restricts characters along a morphism of
  schemes `f`. `characterPointsEquiv_comp` says that the Library identification
  `Diagonalizable.characterPointsEquiv` of points of `D(Λ)` with characters is natural.
- `gens Λ` is a chosen finite generating set of `Λ`, and `chars_ext` says that characters that
  agree on `gens Λ` are equal.
- `charPoint i e V x` is the point of `G` over `V` coming from the point of `H ≅ D(Λ)` with
  character `x`.
- For a point `g : U ⟶ G.X` of the normalizer (`hg`) and `a : V ⟶ U`, `conjChars e hg a x` is
  the character of the conjugate `(a ≫ g) * charPoint x * (a ≫ g)⁻¹`. It exists by
  normalization and is unique because `charPoint` is injective (`charPoint_injective`).
  It is multiplicative (`conjChars_mul`), natural (`conjChars_naturality`), and depends only on
  the underlying morphism of schemes (`conjChars_congr`).
- `ActsTrivially e hg a` means that `conjChars` is the identity over every test scheme over
  `V`. `actsTrivially_iff` shows that this is exactly membership of `a ≫ g` in
  `(range i).centralizer`.
- Charts. For a chart `ρ : Over.mk s ⟶ U` with `s : Spec R' ⟶ Spec R`, define
  `chartHom ρ W` and `chartPoint ρ β`. For a generator `ν`, `chartUnits e hg ρ ν :
  NaturalUnits R' Λ` is the natural family of units
  `x ↦ conjChars (chartHom ρ W) (character of x) (ofAdd ν)` on the points of `D_{R'}(Λ)`.
  Its universal value in `R'[Λ]` is grouplike (`NaturalUnits.isGrouplike_value`), so its
  coefficients are idempotent (`isIdempotentElem_chartCoeff`).
- `ActsAtPoint e hg x` means that conjugation acts trivially over the residue field of
  `x ∈ U`, and `centralizerLocus e hg : U.left.Opens` is the set of such points.

## Proof

The Lean proof follows the Library's split-torus argument
(`Langlands.GroupScheme.TorusConjugation` in `Rational/TorusNormalizerRigidity` and
`Torus/CentralizerOpenInNormalizer`). It replaces the coordinate tori `𝔾ₘ^I` and exponent
matrices with characters of `Λ` and the coefficients at the generators.

1. Algebra (`app_eq_of_coeff`, `coeff_eq_one_of_app`). Let `c : NaturalUnits R Λ`. If the
   coefficient of `m` in `c.value` becomes `1` in `Γ(U)`, then `c` is evaluation at `m` on
   every point over `U`: the other coefficients are killed because grouplike coefficients are
   orthogonal idempotents. Conversely, if `c` is evaluation at `m` at the universal character
   over `A[Λ]`, then that coefficient is `1` in `A` (`lift_of_eq_mapRingHom`).
2. Charts (`actsTrivially_chartHom`, `actsTrivially_chartPoint_iff`,
   `actsTrivially_chart_iff`). Conjugation through `chartPoint ρ β` is trivial iff
   `β (coeff_ν (chartUnits ρ ν)) = 1` for every `ν ∈ gens Λ`. For one direction, test on
   `Spec B[Λ]` with its universal character and apply step 1. For the other, use step 1
   together with `chars_ext`, transporting the coefficient condition along
   `Scheme.ΓSpecIso_inv_naturality`.
3. Points (`actsTrivially_overHom_iff`, `actsAtPoint_chart_iff`). Every field-valued point
   factors through a residue field, and field maps are injective. So at a point
   `p ∈ Spec R'` of a chart, triviality holds iff each idempotent coefficient lies outside `p`
   (`TorusConjugation.algebraMap_residueField_eq_one_iff`).
4. Openness (`isOpen_actsAtPoint`). On each affine chart the locus is the finite intersection
   `⋂_{ν ∈ gens Λ} D(coeff_ν)` of basic opens. This is the only place where finite generation
   of `Λ` is used. Torsion in `Λ` causes no difficulty.
5. Pointwise criterion (`actsTrivially_iff_forall_actsAtPoint`,
   `range_subset_centralizerLocus_iff`). Conjugation restricted along `a` is trivial iff it is
   trivial at every point of the image of `a`. For the reverse direction, reduce to affine
   tests (`actsTrivially_of_forall_affine`, by gluing on an affine open cover). An idempotent
   lying in no maximal ideal is `1`. So a morphism factors through `centralizerLocus` iff its
   composite with `g` lies in the centralizer.
6. Main theorem. Apply this to the universal point `g = n` of the represented normalizer.
   `c` factors through the open `centralizerLocus`, and the inclusion of that open into `N`
   factors through `c` because `c` represents the centralizer preimage. Hence `C` is
   isomorphic to the open subscheme and `c` is an open immersion.

## Provenance

Internal. These are supporting results for the task proving
`MultiplicativeTypeCentralizerOpenStatement` (Milne, *Algebraic Groups*, Corollary 12.40),
restricted to the split diagonalizable case. The argument adapts the published Library
argument for split tori to arbitrary finitely generated character groups. It introduces no
new external mathematical assertion.
