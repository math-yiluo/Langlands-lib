# Restriction-compatible perfect models from universal perfect models

Module `Langlands.AlgebraicGeometry.Modules.RestrictionPerfectModelsReduction`
defines universal perfect models of derived sections of a line bundle. It
proves that if every line bundle on every smooth proper family over an affine
base has one, then `RestrictionPerfectModelsStatement.{u}` holds. The module
locally selects Mathlib's `HasDerivedCategory.standard`, as the statement does.

Notation: `Q = DerivedCategory.Q`, and for `f : X ⟶ Spec R` and an
`𝒪_X`-module `M`,
`RΓ_R(X, M) = (DerivedPlus.derivedComplex (relativeGlobalSections f) ⋙ DerivedCategory.Plus.ι).obj M`.
`K ⊗ T` is `(ModuleComplex.baseChange φ.hom).obj K`, termwise extension of
scalars along `φ : R ⟶ T`.

## `UniversalPerfectModel`

For `R : CommRingCat.{u}`, `X : Scheme.{u}`, `f : X ⟶ Spec R` and
`L : Picard.LineBundle X`, the proposition `UniversalPerfectModel f L` asserts
that there exist

- a cochain complex `K : CochainComplex (ModuleCat.{u} R) ℤ` with
  `ModuleComplex.IsStrictlyPerfect K` (bounded, with finite projective terms),
  together with the proof `hK` of this; and
- a morphism `a : Q.obj K ⟶ RΓ_R(X, L.obj)` in the derived category,

such that `a` is an isomorphism, and for every `T : CommRingCat.{u}`,
`φ : R ⟶ T`, scheme `X'`, and morphisms `p : X' ⟶ X`, `f' : X' ⟶ Spec T` with
`hp : IsPullback p f' f (Spec.map φ)`, the morphism
`DerivedSections.perfectModelBaseChange hp L hK a : Q.obj (K ⊗ T) ⟶ RΓ_T(X', p^* L.obj)`
is an isomorphism.

`perfectModelBaseChange hp L hK a` is the published construction in
`Langlands.AlgebraicGeometry.Modules.PerfectModelRestriction`: the `T`-linear
adjunct, under the perfect-source scalar-extension equivalence
`ModuleComplex.perfectScalarDerivedTargetHomEquiv`, of
`a ≫ derivedBaseChangeMapLineBundle hp L`. So it is the canonical map
`K ⊗ T → RΓ_T(X', p^* L)` induced by `a` and derived base change. The point of
the definition is that one derived isomorphism `a` makes all of these
canonical maps invertible. The isomorphisms are not arbitrary objectwise
choices.

## `exists_chainMap_of_isStrictlyPerfect`

For strictly perfect `K` and any complex `K'` of `R`-modules, every derived
morphism `x : Q.obj K ⟶ Q.obj K'` equals `Q.map ψ` for some chain map
`ψ : K ⟶ K'`.

Proof: `K` is K-projective (`ModuleComplex.isKProjective_of_isStrictlyPerfect`).
The published bijection `kProjectiveDerivedHomEquiv K K'` from homotopy classes
of maps to derived morphisms gives a homotopy class `y` with image `x`. The
quotient functor to the homotopy category is full, so `y` is the class of an
actual chain map `ψ`. The simp lemma `kProjectiveDerivedHomEquiv_quotient_map`
then gives `Q.map ψ = x`.

## `restrictionPerfectModels_of_universalPerfectModel`

Hypothesis `H`: for every `R`, `X` and `f : X ⟶ Spec R` with `Smooth f` and
`IsProper f`, and every line bundle `L` on `X`, `UniversalPerfectModel f L`
holds. Conclusion: `RestrictionPerfectModelsStatement.{u}`.

Proof. Fix `R, X, f, L` and take `K, hK, a` from `H`.

1. The isomorphisms `α` of the statement are
   `asIso (perfectModelBaseChange hp L hK a)`, one for each pullback square `hp`.
2. Let `g : Y ⟶ X` be a closed immersion with `Smooth (g ≫ f)`. The composite
   `g ≫ f` is proper, so `H` gives a universal perfect model `K', hK', a'` of
   the pulled-back line bundle `(LineBundle.pullback g).obj L` over `g ≫ f`.
   Its underlying sheaf is `(Scheme.Modules.pullback g).obj L.obj`.
3. Write `e` for the isomorphism `a'`. By `exists_chainMap_of_isStrictlyPerfect`,
   the derived morphism `a ≫ derivedRestrictionMap g f L.obj ≫ e⁻¹` is `Q.map ψ`
   for a chain map `ψ : K ⟶ K'`. Hence
   `Q.map ψ ≫ a' = a ≫ derivedRestrictionMap g f L.obj`.
   Here `derivedRestrictionMap` is the published derived restriction map along
   a closed immersion: the image of the adjunction unit `M ⟶ g_* g^* M`,
   followed by the inverse of the derived pushforward comparison.
4. The isomorphisms `β` of the statement are
   `asIso (perfectModelRestrictionBaseChange hp hq L hK' a')` for squares
   `hp : IsPullback p f' f (Spec.map φ)` and `hq : IsPullback q g' g p`. This
   published map is the base change of `a'` along the pasted square
   `hq.paste_vert hp`, followed by the canonical isomorphisms
   `RΓ_T(Y', q^* g^* L) ≅ RΓ_T(Y', g'^* p^* L) ≅ RΓ_T(X', g'_* g'^* p^* L)`.
   By the published `isIso_perfectModelRestrictionBaseChange_iff` it is an
   isomorphism, because the base change of `a'` along the pasted square is one
   by universality of `a'`.
5. The commuting square of the statement is exactly the published theorem
   `perfectModelBaseChange_restriction hp hq L hK hK' ψ a a' h`, applied to the
   identity `h` from step 3.

## Provenance

Internal. The definition and the reduction were written for the proof task
`e969f1c2-7aa6-4731-abaa-2f7455f32265`
(`Langlands.AlgebraicGeometry.Picard.FibreFrameLiftingStatement`). They package
the "map `E → Eᵢ` in `D(𝒪_S)` whose formation commutes with change of base"
used in the proofs of Stacks Project Lemmas 0BF1 and 0BF2
(`more-morphisms.tex`, commit `a04446e57ec1fbc252a871afcec7752fb2807b14`,
lines 9453–9619), as recorded in `RestrictionPerfectModelsStatement.md`. That
source is context only: the Lean argument here is the categorical one above,
built from the published constructions `perfectModelBaseChange`,
`perfectModelRestrictionBaseChange`, `isIso_perfectModelRestrictionBaseChange_iff`,
`perfectModelBaseChange_restriction`, `derivedRestrictionMap` and
`kProjectiveDerivedHomEquiv`.

## Scope

The module does not prove that universal perfect models exist; that is
`universalPerfectModel` in `RestrictionPerfectModelsProof`. The hypothesis `H`
requires them for all smooth proper families, because the reduction applies it
both to `f` and to `g ≫ f`.
