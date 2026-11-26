# Étale descent, étale-local lifting and connected fibres of the normalized CM classes

The module `Langlands.Shimura.PEL.HarrisTaylorCMNormalQuotientPremiseStatements`
states three properties of the normalized Harris CM class presheaves
`(smallLevelClassPresheafTower …).obj U` at sufficiently small levels. It
supplies no proof of any of them. The module
`Langlands.Shimura.PEL.HarrisTaylorCMNormalQuotientReduction` derives
`CMQuasiProjectiveNormalQuotientStatement` from these three statements and
`Langlands.AlgebraicGeometry.FiniteFreeQuasiProjectiveQuotientStatement`.

## Common data

All three propositions take the same parameters as
`CMQuasiProjectiveNormalQuotientStatement`: the universe-zero number fields
`E`, `F`, `L`, the algebra `A`, the central simple unitary datum `D`, the
embedding `τ₀`, the Harris signature charts `C` on
`harrisCMSection E (algebraMap L F) τ₀`, and the named prerequisites
`preservation`, `composition`, `unitCoherence`, `associativity`, `comparison`,
`symmetry`, `stability`, `square`, `universality`, `dualityNaturality`,
`polarizationStability`, `compatibility`, `h` and `htor`. They are parameters
of the definitions, not assertions.

Write `DisBases` for `ComponentwiseAdmissibleCMBaseCategory D C …`, the full
subcategory of schemes over `Spec F` whose underlying scheme is locally
noetherian and whose connected components satisfy `AdmissibleCMBase`, with all
morphisms over `Spec F`. Write `M_U` for
`(smallLevelClassPresheafTower …).obj U : DisBasesᵒᵖ ⥤ Type 1`, the presheaf
of normalized joint classes at the small level `U : SmallCMLevel D`. A test
morphism `f : T ⟶ S` in `DisBases` has underlying scheme morphism
`f.hom.left`. For small levels `U' ≤ U`, the forgetting transition is
`(smallLevelClassPresheafTower …).map (smallCMInclusion D hle)`, a natural
transformation `M_U' ⟶ M_U`. When `U'` is normal in `U`, an element `g` of
`U` acts on `M_U'` by `(smallLevelClassPresheafTower …).map
(smallCMNormalInverseArrow D U U' hle g)`, inverse right translation of the
level orbit by `g` (the transporter with element `g⁻¹`).

## `CMSmallLevelEtaleSheafStatement`

For every small level `U`, every test `S`, every index type `J : Type`, every
family of tests `T : J → DisBases` and every family of test morphisms
`f i : T i ⟶ S` such that

- each `(f i).hom.left` is étale, and
- every point of `S` is the image of a point of some `T i`,

the presheaf `M_U` satisfies the sheaf condition
`Presieve.IsSheafFor M_U (Presieve.ofArrows T f)`. Every compatible family of
classes on the `T i` is the restriction of exactly one class on `S`.
Compatibility is Mathlib's: for any test `Z` with morphisms `a : Z ⟶ T i` and
`b : Z ⟶ T j` satisfying `a ≫ f i = b ≫ f j`, the two pullbacks to `Z` agree.

So `M_U`, restricted to the admissible tests, is a sheaf for the étale
topology. Covers by open subschemes, finite étale surjections and their
combinations are such families.

## `CMSublevelEtaleLiftStatement`

For small levels `U' ≤ U` (no normality is assumed), every test `S` and every
class `c` in `M_U(S)`, there are a test `S₁`, a test morphism `p : S₁ ⟶ S`
whose underlying scheme morphism is étale and surjective, and a class `c₁` in
`M_U'(S₁)` whose image under the forgetting transition is the pullback
`M_U.map p.op c`. Every class at the coarser level lifts to the finer level
étale locally.

## `CMNormalSublevelConnectedFibreStatement`

For small levels `U' ≤ U` with `U'.obj.subgroup.subgroupOf U.obj.subgroup`
normal, every test `T` whose underlying scheme is connected, and classes
`c₁ c₂` in `M_U'(T)` with the same image in `M_U(T)` under the forgetting
transition, there is `g : U.obj.subgroup` with
`(smallLevelClassPresheafTower …).map (smallCMNormalInverseArrow D U U' hle g)`
sending `c₁` to `c₂`. On connected tests the fibres of the forgetting
transition are orbits of the residual action.

## Sources and provenance

The three propositions are internal to the Library. They are stated for an
arbitrary central simple unitary datum `D` with the Harris signature charts
`C`, for the Library presheaf `M_U` of normalized classes at every small level
`U` of the finite-adelic points, on the admissible tests, and without
assuming that `M_U` is representable. They are motivated by consequences of
representability and of the level coverings for the moduli problems of the
following sources, whose hypotheses are narrower.

Harris and Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), source `harris-taylor-2001-geometry-cohomology-simple-shimura`,
SHA-256 `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`,
III.1, printed pp.90–91 (PDF pp.98–99). Page 90 defines the functor `X_U` on
locally noetherian `F`-schemes as the product over connected components; page
91 defines it on connected bases by quadruples `(A, λ, i, η̄)` up to isogeny,
with `η̄` a `π₁(S, s)`-invariant `U`-orbit of isomorphisms of adelic Tate
modules, and asserts that for sufficiently small `U` the functor is
represented by a smooth projective scheme `X_U`, that `X_V ⟶ X_U` is finite
étale for `V ⊂ U`, and that it is Galois with group `U/V` when `V` is normal
in `U`. These assertions are made under the running assumptions of the book:
the opening of Chapter III (printed p.89, PDF p.97) uses the notation of I.7,
and I.7 (printed p.51, PDF p.59) takes `E` imaginary quadratic with `p` split,
`F = E F⁺` and `B` a division algebra over `F` with `B^op ≅ B ⊗_{E,c} E`,
split at the chosen place `w` and subject to further local conditions.

Kottwitz, *Points on some Shimura varieties over finite fields*, J. Amer.
Math. Soc. 5 (1992), source `kottwitz-1992-points-shimura-finite-fields`,
SHA-256 `c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`,
§5, printed pp.389–391 (PDF pp.17–19), and §6, printed p.392 (PDF p.20). Its
moduli problem lives over `O_E ⊗ Z_(p)` for the reflex field `E`: abelian
schemes up to prime-to-`p` isogeny with an action of a `Z_(p)`-order of `B`,
polarization, determinant condition and level structure of type `K^p` for a
compact open subgroup of the prime-to-`p` finite-adelic points, with `B ⊗ Q_p`
a product of matrix algebras over unramified extensions of `Q_p`. Page 391
asserts representability by a quasi-projective scheme `S_{K^p}` for
sufficiently small `K^p`; page 392 gives the étale coverings
`S_{K'^p} ⟶ S_{K^p}`, Galois with group `K^p/K'^p` when `K'^p` is normal in
`K^p`, for levels small enough that the objects have no nontrivial
automorphisms.

For the moduli functors of these sources the three properties are standard
consequences of these assertions. A representable functor is a sheaf for the
étale topology, the analogue of the first proposition. Base change of the
finite étale surjective covering `X_V ⟶ X_U` along the morphism classifying a
point at level `U` lifts that point to level `V` after an étale surjective
base change, the analogue of the second. The covering being Galois with group
`U/V` means that two points at level `V` over the same point at level `U` on
a connected base differ by one element of `U`, the analogue of the third.
This file does not compare `M_U` with the moduli functors of the sources.
Harris and Taylor use full finite-adelic levels under the division-algebra
and local hypotheses of I.7. Kottwitz uses prime-to-`p` levels for the
integral PEL moduli problem of §5. Proofs of the propositions for `M_U` need
étale descent for the normalized polarized classes and the orbit description
of level structures.
