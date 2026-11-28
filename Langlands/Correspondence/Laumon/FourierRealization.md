# The arithmetic Fourier transform on the affine line over a finite field

This module builds the Fourier–Deligne transform of Laumon 1987, Définition (1.2.1.1), p. 141, in
rank one over a finite base field, as a functor on arithmetic bounded constructible
`ℚ̄_ℓ`-complexes, and states the properties of it that Laumon §2 uses: its comparison with the
ambient condensed transform of weil-conjectures, its form over the compactified target
((2.3.2.1)(iii), p. 160, and (2.3.3.1)(iii), p. 161), its comparison with the Weil transform on the
geometric fibre ((1.2.2.9), p. 144, and (2.4.2), pp. 162–163), its fibres at rational points
((1.2.2.1)–(1.2.2.2), pp. 141–142), its compatibility with finite extension of the constant field
((1.2.2.9), p. 144), the composite kernel ((1.2.2.1)–(1.2.2.3), pp. 141–143,
and (1.2.3.1), p. 144) and the inversion formula (Corollaire (1.2.2.3), p. 143; (2.5.6), p. 169).
The module defines the objects and states the eight propositions; it proves none of them.

Printed page numbers refer to Laumon, *Transformation de Fourier, constantes d'équations
fonctionnelles et conjecture de Weil*, Publ. Math. IHÉS 65 (1987).

## Setting and normalization

Throughout, `k` is a finite field (`[Field k] [Fintype k]`) of characteristic `p`, `ℓ` is a prime
with `ringChar k ≠ ℓ`, `E = PadicAlgCl ℓ` and `ψ : AddChar k E` is an additive character. The
coefficient ring of the arithmetic complexes is weil-conjectures' condensed ring
`Λ = Profinite.padicAlgClRingObj ℓ` (`ℚ̲̄_ℓ`), and `Dᵇc(X)⟦Λ⟧` is its bounded constructible derived
category on the pro-étale site of a `k`-scheme `X`. The definitions take an arbitrary `ψ`; the
statements that need it assume `ψ ≠ 1`. The character Laumon fixes in (0.2), p. 134, is
`Langlands.Henniart.Laumon.fourierCharacter k ℓ` of the module `Traits`, which is nontrivial by
`fourierCharacter_ne_one`; Laumon writes `ψ` for both directions of the transform, as here.

The line `A = 𝔸¹_k` and its dual `A'` are both weil-conjectures' `AlgebraicGeometry.affineLine k`
(the affine space `𝔸(PUnit; Spec k)`), with coordinates `x` and `x'`; `A × A'` is its
`affinePlane k` (the fibre product `𝔸¹ ×_k 𝔸¹`), with the projections `pr = affinePlane.fst` and
`pr' = affinePlane.snd`. The kernel is the arithmetic Artin–Schreier sheaf `Lψ(xx')` of the
pairing; the shift is `[1]`, the relative dimension (Laumon (1.2.1.1) with `r = 1`). Tate twists
are those of weil-conjectures (`tateTwistDerived`, `boundedConstructibleTateTwist` on the
arithmetic side, `WeilComplex.tateTwist` on the Weil side); Laumon's `(−1)` is the twist by
`-1`. Weil structures are those of weil-conjectures, defined with the geometric Frobenius; for
`q = #k` the geometric Frobenius acts on `E(1)` by `q⁻¹` and on `E(−1)` by `q`
(weil-conjectures' `WeilSheaf.cyclotomicUnit_eq` and `WeilSheaf.tateTwistSheaf_one`), the
normalization fixed in §1 of the note `notes/henniart/laumon-local-fourier-weil-conjectures-design.md`.

## The transform

- `fourierLine k`, `fourierPlane k` are `A` and `A × A'` as objects of `Over (Spec k)`, with the
  instances `LocallyOfFiniteType`, `QuasiCompact` and `IsSeparated` for their structure
  morphisms; `fourierFirstProjection k` and `fourierSecondProjection k` are `pr` and `pr'` as
  morphisms over `k`.
- `fourierPlaneIsoRelativeLine k : A × A' ≅ 𝔸¹_{A'}` is the inverse of the isomorphism given by
  the cartesian square `AffineSpace.isPullback_map` (relative affine line over `A'` as the base
  change of `𝔸¹_k` along `A' → Spec k`).
- `fourierProjectionCompactification k` is the compactification `A × A' ↪ D × A' → A'` of `pr'`:
  weil-conjectures' `affineTraceLineCompactification A'` (the standard chart of the projective
  line `ℙ¹_{A'} = D × A'` over `A'`), precomposed with `fourierPlaneIsoRelativeLine k` by
  `Compactification.precomp` and transported to `pr'` by `Compactification.copy`.
- `condensedFourierCharacter k ℓ ψ` is `ψ` followed by the constant global sections
  `Profinite.PadicAlgCl.constRingHom ℓ : E → Γ(Λ)`. The theorems `prime_ne_ringChar` and
  `isUnit_ringChar_condensed` record that `ℓ ≠ p` and that `p` is invertible in `Γ(Λ)`; they are the
  hypotheses of the kernel finiteness theorem below.
- `arithmeticFourierKernel k ℓ ψ` is `Lψ(xx')` in degree `0`: weil-conjectures'
  `condensedFourierKernel` (the Artin–Schreier sheaf `condensedArtinSchreierSheafOf` of the standard
  pairing `AffineSpace.stdPairing`), bundled as an object of `Dᵇc(A × A')⟦Λ⟧` by the proved
  `condensedFourierKernel_boundedConstructible`.
- `boundedConstructibleArithmeticFourier k ℓ ψ : Dᵇc(A)⟦Λ⟧ ⥤ Dᵇc(A')⟦Λ⟧` is
  `K ↦ Rpr'_!(pr^*K ⊗ Lψ(xx'))[1]`: the bounded constructible pullback
  `boundedConstructibleUpperStar` along `pr`, the tensor product of the monoidal category
  `Dᵇc(A × A')⟦Λ⟧` with the kernel, the compact support pushforward
  `boundedConstructibleLowerShriekOfCompactification` for `fourierProjectionCompactification k`,
  and the shift of the triangulated subcategory `Dᵇc(A')⟦Λ⟧`. Every step is an operation on
  bounded constructible complexes that weil-conjectures constructs, so the functor needs no
  unproved property to be formed.
- `ambientArithmeticFourier k ℓ ψ` is weil-conjectures' `condensedFieldFourierTransform` on the whole
  derived category of `Λ`-modules on `A`, for `condensedFourierCharacter k ℓ ψ` and the same
  compactification.

**`ArithmeticFourierRestrictionStatement`** (Laumon (1.2.1.1), p. 141, and (2.3.3.1), p. 161). For
every finite field `k`, prime `ℓ ≠ char k` and character `ψ`: (1) the ambient transform carries
every bounded constructible complex to a bounded constructible complex; (2)
`boundedConstructibleArithmeticFourier k ℓ ψ` followed by the inclusion of `Dᵇc(A')⟦Λ⟧` is
isomorphic, as a functor, to the inclusion followed by the ambient transform; (3) for every open
immersion `j : U ↪ A` of separated `k`-schemes of finite type, the transform of `j_! K`, with
`j_!` the bounded constructible extension by zero `boundedConstructibleOpenImmersionLowerShriek`,
is naturally isomorphic to the ambient transform of the ambient compact support pushforward
`rightDerivedLowerShriekOfCompactification` for `Compactification.ofIsOpenImmersion j` (the
factorization of `j` with identity proper part). The ambient transform uses for the kernel the
structure morphism `pr ≫ (A → Spec k) ≫ Spec(id_k)`, the transform here the structure morphism
`pr ≫ (A → Spec k)` of `affinePlane k`; the two kernels are the same sheaf after the identification
`Spec(id_k) = id`, which is part of what (2) asserts.

## The compactified target

- `fourierBase k` is `Spec k` over itself; `fourierDualCompletion k` is the projective line
  `D' = ℙ¹_k` (weil-conjectures' `Scheme.overProjectiveLine`); `fourierDualChart k : A' ↪ D'` is the
  chart `ProjectiveLine.affineChart`, `x' ↦ [x' : 1]`, whose complement is the point `∞'`.
- `fourierCompletionChart k : D × A' ↪ D × D'` is the open immersion of projective lines induced
  by `fourierDualChart k` (`Scheme.overProjectiveLineMap`); it is an open immersion as the base change
  of one (`Scheme.isPullback_overProjectiveLineMap`). Its source is the scheme of
  `fourierProjectionCompactification k`.
- `fourierKernelZeroExtension k ℓ ψ` is `K ↦ B_K`, the complex `pr^*K ⊗ Lψ(xx')` extended by zero
  along `A × A' ↪ D × A'`; `extendedFourierKernel k ℓ ψ` is `K ↦ B̄_K`, its extension by zero to
  `D × D'`. These are Laumon's `j_! (pr^*K ⊗ Lψ(xx'))` on the compactified product in
  (2.3.2.1)(iii), p. 160, and (2.3.3.1), p. 161. By construction the transform is
  `Rq_* B_K [1]` for the proper projection `q : D × A' → A'`.

**`ArithmeticFourierCompactifiedTargetStatement`** (Laumon (2.3.2.1)(iii), p. 160, and
(2.3.3.1)(iii), p. 161). With `q̄ : D × D' → D'` the proper projection (`overProjectiveLineProj`,
pushforward `boundedConstructibleLowerStarOfIsProper`), `Rq̄_* B̄_K [1]` restricted to `A'` along
`fourierDualChart k` is naturally isomorphic to the transform of `K`, and `Rq̄_* B̄_K [1]` is
naturally isomorphic to the extension by zero of the transform of `K` along `A' ↪ D'`.
Mathematically, the first assertion is base change along the open immersion `A' ↪ D'`, and the
second says moreover that the stalk at `∞'` vanishes, since `B̄_K` vanishes on `D × {∞'}` and
`q̄` is proper.

## Comparison with the Weil transform

- `weilRealization k ℓ X : Dᵇc(X)⟦Λ⟧ ⥤ WeilComplex k ℓ X` uses
  `WeilComplex.finiteBaseNativeDescent` for a separated `k`-scheme `X` of finite type. It pulls
  back to the geometric fibre `X ⊗ k̄` with its canonical Frobenius structure.
  `WeilComplex.finiteBaseNativeDescentComparison` identifies its image under the derived
  coefficient equivalence `ProEtaleWeilSheaf.derivedEquivCondensed` with the derived functor of
  `geometricFiberWeilLowerStar`. In this condensed model, the Weil structure on a sheaf `M`
  is an isomorphism `(Fr⁻¹)_* M ≅ M`. The geometric carrier of the pullback is bounded
  constructible by `CondensedRing.boundedConstructible_geometricFiberWeilLowerStar`.
- `weilInversionTarget k ℓ` is `(−1) ⋙ [−2] ⋙ a^* ⋙ [1] ⋙ [1]` on Weil complexes of the line, the
  target of weil-conjectures' Weil inversion `nonempty_iso_fourierTransform_comp_self`, and
  `commIsoTwice e : (F ⋙ F) ⋙ R ≅ R ⋙ (G ⋙ G)` is a comparison `e : F ⋙ R ≅ R ⋙ G` applied twice.
- `linearFunction k a` is the function `x ↦ a x` on the line.

**`ArithmeticArtinSchreierWeilComparisonStatement`** (Laumon (1.1.3.2), p. 139, (1.1.3.6), p. 140,
and (1.2.1.1), p. 141). For every `a ∈ k`, the pullback to `A ⊗ k̄` with its Frobenius structure of
the arithmetic Artin–Schreier sheaf `Lψ(ax)` (`condensedArtinSchreierSheafOf` for
`linearFunction k a`) is isomorphic, as a condensed Weil object, to `ProEtaleWeilSheaf.toCondensed`
of the Weil Artin–Schreier sheaf `AlgebraicGeometry.artinSchreier ψ a`. Both are the image of the
projector `q⁻¹ ∑_c ψ(-c) σ_c` on the pushforward of the coefficients along `u ↦ u^q − u`, `σ_c` the
pullback along the translation `u ↦ u + c`, pulled back along `x ↦ a x`.

**`ArithmeticFourierWeilComparisonStatement`** (Laumon (1.2.1.1), p. 141, (1.2.2.9), p. 144, and
(2.4.2), pp. 162–163). Write `R_A` and `R_U` for the realizations on the line and on an open
subscheme. There are natural isomorphisms `e : FTψ ⋙ R_A ≅ R_A ⋙ fourierTransform ψ` and
`s : [1] ⋙ R_A ≅ R_A ⋙ [1]`. For each quasi-compact open immersion `j : U ↪ A` of separated
`k`-schemes of finite type, there is `z : j_! ⋙ R_A ≅ R_U ⋙ Rj_!`, where `Rj_!` is the Weil
extension by zero `WeilComplex.derivedLowerShriek`. The isomorphism
`c : j_! ⋙ [1] ⋙ FTψ ⋙ R_A ≅ R_U ⋙ Rj_! ⋙ [1] ⋙ fourierTransform ψ` on shifted zero extensions
`j_! K[1]` is the composite of three natural isomorphisms. It applies `e` after `j_! ⋙ [1]`, then
`s` between `j_!` and the Weil transform, then `z` before the Weil shift and transform.

Each comparison is in Weil complexes and respects their Frobenius structures. Pullback to the
geometric fibre commutes with the pullback, the tensor product with the Artin–Schreier kernel,
and the compact support pushforward and shift that form the transform. The kernel comparison
uses the same torsor projector as the comparison of the Artin–Schreier lines. The compact
support comparison uses proper base change, given in the condensed model by
`CondensedRing.boundedConstructibleLowerShriekOfCompactificationGeometricFiberWeilIso`.

## Fibres and finite base change

- `fourierLineStructure k : A → Spec k`; `rationalPointHom k a` and `fourierRationalPoint k a` are
  the rational point `a : Spec k → A'`; `fibreInclusionHom k a` and `fourierFibreInclusion k a` are
  `x ↦ (x, a)`, `A → A × A'`, a morphism over `k` by `fibreInclusionHom_over`.
- `fourierFibreKernel k ℓ ψ a` is the derived pullback of `Lψ(xx')` along `x ↦ (x, a)`.
- `fourierLineCompactCohomology k ℓ` is `RΓ_c(A_k̄, −)` with its arithmetic structure: the bounded
  constructible compact support pushforward along `A → Spec k` for the compactification
  `A ⊂ D` of `affineTraceLineCompactification (Spec k)`, with values in `Dᵇc(Spec k)⟦Λ⟧`.
- `fourierNegation k` is `a(x) = −x`, weil-conjectures' `affineLine.neg`; `fourierLineBaseChange k k₁`
  is `𝔸¹_{k₁} → 𝔸¹_k` for a field extension `k ⊂ k₁`; `schemeUpperStar ℓ f` is the derived pullback
  on bounded constructible complexes along an arbitrary morphism of schemes, which weil-conjectures
  proves preserves bounded constructible complexes
  (`boundedConstructible_leftDerivedUpperStar_obj_of_scheme`).

**`ArithmeticFourierFibreStatement`** (Laumon (1.2.2.1)–(1.2.2.2), pp. 141–142, and (1.2.2.9),
p. 144). For a rational point `a ∈ k` of `A'`: (1) the restriction of `FTψ(K)` to `a` is
naturally isomorphic to `RΓ_c(A_k̄, K ⊗ L_a)[1]` with its arithmetic structure, where `L_a` is
`fourierFibreKernel k ℓ ψ a`; (2) `L_a` is isomorphic to the Artin–Schreier sheaf `Lψ(ax)` placed in
degree `0`; (3) at the origin `L_0` is the unit, so the fibre at `0'` is `RΓ_c(A_k̄, K)[1]`. This is
proper base change for the compactified projection along the point `a`, and the rigidification
(1.1.3.1) of the Artin–Schreier sheaf at the origin.

**`FourierCommutesWithFiniteBaseChangeStatement`** (Laumon (1.2.2.9), p. 144: the formation of
the transform commutes with every base change; Proposition (1.2.3.5), pp. 145–146, is the related
formula for compactly supported direct images). For a finite extension `k ⊂ k₁` of finite fields (with `ℓ ≠ char k₁`, which is
automatic), pulling back along `𝔸¹_{k₁} → 𝔸¹_k` carries the transform over `k` for `ψ` to the
transform over `k₁` for `ψ ∘ Tr_{k₁/k}`, naturally in the input. The character changes because the
pullback of the Artin–Schreier sheaf of `ψ` for the covering `u^q − u` is the Artin–Schreier sheaf of
`ψ ∘ Tr_{k₁/k}` for the covering `u^{q₁} − u` (Laumon (1.1.3.3), p. 139, with `J = 𝔾_a`).

## The composite kernel and inversion

- `fourierTriple k` is `A × A' × A''`, weil-conjectures' `affineTripleProduct k`, with the
  projections `fourierTripleProj₁₂`, `fourierTripleProj₂₃` (over `k` by `fourierTripleProj₂₃_over`)
  and `fourierTripleProj₁₃` onto the planes of `(x, x')`, `(x', x'')` and `(x, x'')`;
  `fourierAntidiagonal k` is `x ↦ (x, −x)`, weil-conjectures' `affineLine.antidiagonal`, a closed
  immersion.

**`ArithmeticFourierKernelCohomologyStatement`** (Laumon (1.2.2.1)–(1.2.2.3), pp. 141–143, and
(1.2.3.1), p. 144). For `ψ ≠ 1`, the convolution
`Rp₁₃!(p₁₂^* Lψ(xx') ⊗ p₂₃^* Lψ(x'x''))` (compact support pushforward
`boundedConstructibleLowerShriek` for the compactification chosen by weil-conjectures) is isomorphic
to the pushforward along the antidiagonal of `E(−1)[−2]` (`boundedConstructibleTateTwist ℓ A (-1)
(-2)`), as arithmetic complexes. This is Laumon's computation `Rpr'_! Lψ(⟨e', e''+e⟩) =
σ_* E(−1)[−2]` in the proof of (1.2.2.1) and Proposition (1.2.2.2) for `E = A`; the Weil-complex form
is weil-conjectures' proved `nonempty_iso_kernelConvolution_fourierKernel`.

**`ArithmeticFourierInversionStatement`** (Laumon Théorème (1.2.2.1) and Corollaire (1.2.2.3),
pp. 141–143; (2.5.6), p. 169). For `ψ ≠ 1`:

1. `FTψ ∘ FTψ` is naturally isomorphic, as a functor on `Dᵇc(A)⟦Λ⟧`, to `K ↦ a^*K ⊗ E(−1)` with
   `a(x) = −x`. The isomorphism is one of arithmetic complexes, i.e. it respects the action of
   `Gal(k̄/k)`, which is what Laumon §2 needs for the local Galois representations. Laumon's
   normalization (0.2): the shifts `[1][1]` of the two transforms cancel the shift `[−2]` of the
   composite kernel.
2. With `R = weilRealization k ℓ A`, there is a natural isomorphism
   `ρ : (a^* ⋙ (− ⊗ E(−1))) ⋙ R ≅ R ⋙ weilInversionTarget k ℓ`. The comparison comes from
   pullback along `a`, realization of the arithmetic Tate line, and cancellation of the Weil
   shifts `[−2]`, `[1]`, `[1]`. For that `ρ`, each comparison
   `e : FTψ ⋙ R ≅ R ⋙ fourierTransform ψ` and each Weil inversion
   `β : fourierTransform ψ ⋙ fourierTransform ψ ≅ weilInversionTarget k ℓ` admit an arithmetic
   inversion `α` satisfying the equality

   `R(α) ≫ ρ = (e applied twice, commIsoTwice e) ≫ R(β)`

   of natural isomorphisms `(FTψ ⋙ FTψ) ⋙ R ≅ R ⋙ weilInversionTarget k ℓ`.
   Weil-conjectures' `nonempty_iso_fourierTransform_comp_self` supplies a Weil inversion.

The comparison lifts through full faithfulness of Weil realization on bounded constructible
complexes. BBD (5.1.2.5), printed p. 124, gives the exact sequences
`0 → Hom^{i−1}(K, L)_F → Hom^i(K₀, L₀) → Hom^i(K, L)^F → 0` for complexes `K₀, L₀` on `X₀` with
geometric fibres `K, L`. The Weil sequences have the same end terms because the continuous
cohomology of `Ẑ` and the cohomology of `ℤ` with coefficients in a finite-dimensional ℓ-adic
representation agree in degrees `0` and `1`. The preimage of
`commIsoTwice e ≫ R(β) ≫ ρ⁻¹` under realization gives `α`.

## External declarations and their axioms

Every declaration of weil-conjectures (commit `a25955cde4f85f67bef3149a6efc3efe20c22132`) and of
Mathlib used by this module was checked with `#print axioms` in the pinned environment and depends
only on `propext`, `Classical.choice` and `Quot.sound`: `affineLine`, `affineSpacePair`
(`affinePlane`), `affinePlane.fst`, `affinePlane.snd`, `AffineSpace.stdPairing`,
`AffineSpace.isPullback_map`, `AffineSpace.homOfVector`, `AffineSpace.map`,
`affineTraceLineCompactification`, `Compactification.precomp`, `Compactification.copy`,
`Compactification.ofIsOpenImmersion`, `Compactification.overObj`, `Compactification.overI`,
`Profinite.padicAlgClRingObj`, `Profinite.PadicAlgCl.constRingHom`,
`ProEtale.condensedFourierKernel`, `CondensedRing.condensedFourierKernel_boundedConstructible`,
`ProEtale.condensedFieldFourierTransform`, `ProEtale.condensedArtinSchreierSheafOf`,
`ProEtale.boundedConstructible`, `CondensedRing.isMonoidal_boundedConstructible`,
`ProEtale.isTriangulated_boundedConstructible_padicAlgClRingObj`,
`CondensedRing.boundedConstructibleUpperStar`,
`CondensedRing.boundedConstructibleLowerShriekOfCompactification`,
`CondensedRing.boundedConstructibleLowerShriek`,
`CondensedRing.boundedConstructibleOpenImmersionLowerShriek`,
`CondensedRing.boundedConstructibleLowerStarOfIsProper`,
`CondensedRing.boundedConstructibleTateTwist`,
`CondensedRing.rightDerivedLowerShriekOfCompactification`, `CondensedRing.upperStar`,
`CondensedRing.boundedConstructible_leftDerivedUpperStar_obj_of_scheme`,
`Scheme.overProjectiveLine`, `Scheme.overProjectiveLineProj`, `Scheme.overProjectiveLineMap`,
`Scheme.isPullback_overProjectiveLineMap`, `ProjectiveLine.affineChart`,
`ProjectiveLine.affineChart_over`, `CondensedRing.geometricFiberWeilLowerStar`,
`ProEtaleWeilSheaf.derivedEquivCondensed`, `ProEtaleWeilSheaf.toCondensed`, `WeilComplex`,
`WeilSheaf`, `WeilSheaf.objectProperty`, `artinSchreier`, `fourierTransform`,
`WeilComplex.finiteBaseNativeDescent`, `WeilComplex.derivedLowerShriek`, `WeilComplex.tateTwist`,
`WeilComplex.upperStar`, `affineLine.neg`, `affineLine.antidiagonal`, `affineTripleProduct`,
`affineTripleProduct.proj₁₂`, `affineTripleProduct.proj₂₃`, `affineTripleProduct.proj₁₃`,
`ProEtale.condensedRingObj`, `ProEtale.BoundedConstructible` (the category `Dᵇc(X)⟦Λ⟧`) and
`Scheme.Hom.geometricGaloisFrobenius` (all in the namespace `AlgebraicGeometry`), and
`CategoryTheory.Functor.leftDerivedFunctor`, `CategoryTheory.Functor.mapDerivedCategory` and
`CategoryTheory.MonObj.Γ`. Mathlib's `AffineSpace.homOfVector_over` and `Scheme.ΓSpecIso` have
the same axioms. The results cited in the explanations also depend only on `propext`,
`Classical.choice` and `Quot.sound`. These are `WeilComplex.finiteBaseNativeDescentComparison`,
`CondensedRing.boundedConstructible_geometricFiberWeilLowerStar`,
`WeilSheaf.cyclotomicUnit_eq`, `WeilSheaf.tateTwistSheaf_one`,
`nonempty_iso_kernelConvolution_fourierKernel`, `nonempty_iso_fourierTransform_comp_self` and
`CondensedRing.boundedConstructibleLowerShriekOfCompactificationGeometricFiberWeilIso`. Every
declaration of this module has the same three axioms.

Two global instances of weil-conjectures are removed in this file with `attribute [-instance]`:
the monoidal structure `CategoryTheory.sfbRegularAbMonoidal` on abelian sheaves, for which
`Profinite.padicAlgClRingObj ℓ` is not a ring object, and the derived category instance
`WeilConjectures.CompletedCoefficientPushforward.hasDerived`, whose morphisms lie in a different
universe from the derived categories of the six operations. With them removed, the instances found
are the ones the imported operations are stated with.
