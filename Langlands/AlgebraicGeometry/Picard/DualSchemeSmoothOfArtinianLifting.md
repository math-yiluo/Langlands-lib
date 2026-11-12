# Smoothness of the chosen dual from Artinian lifting of Picard-zero families

This module proves that the statement
`PicardZeroArtinianLiftingStatement.{u}` implies smoothness of the chosen dual
`dualScheme A hA` over noetherian affine bases. It is a conditional reduction.
It does **not** prove the lifting statement, and it does not prove smoothness
outright.

## Main theorems

```lean
theorem Langlands.AbelianScheme.dualScheme_smooth_of_picardZeroArtinianLifting
    (lifting : PicardZeroArtinianLiftingStatement.{u}) {R : Type u} [CommRing R]
    [IsNoetherianRing R] (A : AbelianScheme (Spec (CommRingCat.of R)))
    (hA : HasDualScheme A) : Smooth (dualScheme A hA).hom

theorem Langlands.AbelianScheme.finiteType_dualScheme_smooth_of_picardZeroArtinianLifting
    (lifting : PicardZeroArtinianLiftingStatement.{u}) (R : Type u) [CommRing R]
    [Algebra.FiniteType ℤ R] (A : AbelianScheme (Spec (CommRingCat.of R)))
    (hA : HasDualScheme A) : Smooth (dualScheme A hA).hom
```

`HasDualScheme A` is the Library's existence of an actual universal Picard-zero
family, and `dualScheme A hA` its chosen parameter scheme over `Spec R`
(module `DualScheme`). The lifting statement enters only as the explicit
hypothesis `lifting`. Both theorems use only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

The second theorem is the first for `R` of finite type over `ℤ`. Such an `R` is
noetherian by `Algebra.FiniteType.isNoetherianRing ℤ R`. Its form matches the
quantifiers of `FiniteTypeDualSchemeGeometryStatement`, whose smoothness part it
supplies once the lifting statement is proved.

## Proof of `dualScheme_smooth_of_picardZeroArtinianLifting`

Write `D = dualScheme A hA` and `g = D.hom : D.left ⟶ Spec R`.

1. `g` is locally of finite type by the published
   `dualScheme_locallyOfFiniteType A hA` (module
   `DualSchemeSubalgebraFactorization`), and `Spec R` is locally noetherian by
   Mathlib's instance for noetherian rings. So the Library criterion
   `ArtinianLiftingSmooth.smooth_of_liftsArtinian` applies, and it suffices to
   prove `LiftsArtinian g`.
2. Take a lifting problem: local Artinian `B'`, `B`, a surjection
   `φ : B' →+* B` with `maximalIdeal B' * ker φ = ⊥`, `α : Spec B ⟶ D.left`
   and `β : Spec B' ⟶ Spec R` with `α ≫ g = Spec φ ≫ β`. (The criterion's
   finite-type hypothesis on the residue point of `α` is not needed.)
3. In `Over (Spec R)` put `T = Over.mk (Spec φ ≫ β)`, `T' = Over.mk β`,
   `ι = Over.homMk (Spec φ) : T ⟶ T'` and `a = Over.homMk α : T ⟶ D`.
   Let `M` be the actual rigidified pullback of the Poincaré family
   `poincareFamily A hA` along `a`. It is Picard-zero by the published
   `picardZeroPullback` and the Picard-zero part of
   `poincareFamily_universal A hA`.
4. `lifting` applied to `S = Spec R`, `A`, `φ`, `β` and `M` gives a Picard-zero
   rigidified family `M'` over `T'` and an isomorphism `e` from its pullback
   along `ι` to `M`.
5. Let `c = dualClassify A hA T' ⟨classOf M', hM'⟩ : T' ⟶ D`. Then
   `γ = c.left : Spec B' ⟶ D.left` satisfies `γ ≫ g = β` by `Over.w c`.
6. It remains to show `Spec φ ≫ γ = α`, which is the `left` component of
   `ι ≫ c = a`.
   - `a = dualClassify A hA T ⟨classOf M, hM⟩` by `dualClassify_unique`: the
     classifying map of the Poincaré family sends `a` to the class of its own
     pullback, which is `classOf M` by definition.
   - By the published `dualClassify_pullback` (with the published
     `RigidifiedModule.pullbackCoherence` and `picardZeroPullback`),
     `ι ≫ c` is `dualClassify A hA T` applied to the pullback along `ι` of the
     class of `M'`. That pullback is the class of the pullback of `M'`, which
     equals `classOf M` by `Quotient.sound` applied to `e`.

So `γ` solves the lifting problem.

## Provenance

Derived. The argument is the standard one: a scheme representing a formally
smooth functor is formally smooth, and with local finite type over a locally
noetherian base this gives smoothness. Here it is carried out with the Library's
actual representability (`dualClassify`, `dualClassify_unique`,
`dualClassify_pullback`) and its Artinian smoothness criterion. The lifting
statement records Faltings–Chai, *Degeneration of Abelian Varieties*, Chapter I,
Remark 1.5(c), printed p.2 (PDF p.14), in its Artinian case; see
`PicardZeroArtinianLiftingStatement.md`. No source theorem is formalized here
beyond this deduction.
