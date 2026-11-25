/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.TensorInvertible
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift
public import WeilConjectures.SixFunctors.Etale.Derived.InvertiblePullback
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure

/-!
# Co-projection for a closed immersion

For a closed immersion `i : Z ⟶ X`, an invertible tensor factor passes through `Ri^!` at the
cost of restricting it: `Ri^! (K ⊗^L L) ≅ Ri^! K ⊗^L Li^* L` (blueprint `sk-lem-coprojection`).
This is the input that moves twists through the exceptional inverse image of a zero section in
the model purity (`WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace`) and in purity
for regular closed immersions (`WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion`).

The co-projection is formal: both `Ri^! (- ⊗^L L)` and `Ri^! (-) ⊗^L Li^* L` are right
adjoints, of `Ri_!(-) ⊗^L L⁻¹` and of `Ri_!(- ⊗^L Li^* L⁻¹)`, which the projection formula at
the dualizable object `L⁻¹` identifies. The argument works for any `i` admitting a
compactification.

## Main statements

- `AlgebraicGeometry.Etale.derivedTensorRightCompRightDerivedUpperShriekIso`: the co-projection
  `Rf^! (- ⊗^L L) ≅ Rf^! (-) ⊗^L Lf^* L` for `L` invertible (blueprint `lem-pur-coprojection`).
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_derivedTensor_of_isInvertible`:
  the subsection statement `sk-lem-coprojection`.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_derivedTensor_shiftTateObject`:
  the case of the Tate twists, `Ri^! (K ⊗^L Λ(m)[2m]) ≅ Ri^! K ⊗^L Λ(m)[2m]`
  (blueprint `lem-pur-immersion-twist`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section General

universe u'

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- The co-projection `Rf^! (K ⊗ᴸ L) ≅ Rf^! K ⊗ᴸ Lf^* L`, natural in `K ∈ D(Y_ét)`, for an
object `L` of `D(Y_ét)` with a two-sided tensor inverse `M` (`e : M ⊗ᴸ L ≅ 𝟙_`,
`e' : L ⊗ᴸ M ≅ 𝟙_`).

Both sides are right adjoints, of `Rf_!(-) ⊗ᴸ M` and of `Rf_!(- ⊗ᴸ Lf^* M)` respectively. The
object `M` is dualizable, so the projection formula identifies these two left adjoints
(`AlgebraicGeometry.Etale.hasProjectionFormula_of_isDualizable`), and the co-projection is the
induced isomorphism of right adjoints
(`CategoryTheory.Adjunction.tensorRightCompIsoOfTensorIso`). -/
noncomputable def derivedTensorRightCompRightDerivedUpperShriekIsoOfTensorIso
    (L M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (e : ((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj M).obj L ≅ 𝟙_ _)
    (e' : ((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj L).obj M ≅ 𝟙_ _) :
    derivedTensorRight (ModuleCat.{u + 1} Λ) Y L ⋙ R(f)^![Λ] ≅
      R(f)^![Λ] ⋙ derivedTensorRight (ModuleCat.{u + 1} Λ) X ((L((f)^*[ModuleCat.{u + 1} Λ])).obj L)
          :=
  letI := leftDerivedUpperStarMonoidal (ModuleCat.{u + 1} Λ) f
  have : ∀ K, IsIso ((((flipFunctor _ _ _).map (projectionMap (ModuleCat.{u + 1} Λ) f)).app M).app
      K) :=
    fun K ↦ hasProjectionFormula_of_isDualizable (ModuleCat.{u + 1} Λ) f K
        (isDualizable_of_tensorIso e e')
  have := NatIso.isIso_of_isIso_app (((flipFunctor _ _ _).map (projectionMap (ModuleCat.{u + 1} Λ)
      f)).app M)
  (rightDerivedUpperShriekAdjunction Λ f).tensorRightCompIsoOfTensorIso (L((f)^*[ModuleCat.{u + 1}
      Λ])) e e'
    (asIso (((flipFunctor _ _ _).map (projectionMap (ModuleCat.{u + 1} Λ) f)).app M))

end General

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {X Z : Scheme.{u}}

section Coprojection

variable {Y : Scheme.{u}}

omit [HasTateTwist Λ] in
/-- Blueprint `lem-pur-coprojection`: Co-projection for a closed immersion

For a morphism `f : X ⟶ Y` admitting a compactification and an object `L` of `D(Y_ét, Λ)` with
a two-sided tensor inverse `M` (`e : M ⊗^L L ≅ Λ_Y`, `e' : L ⊗^L M ≅ Λ_Y`), the co-projection

`Rf^! (K ⊗^L L) ≅ Rf^! K ⊗^L Lf^* L`

is an isomorphism natural in `K ∈ D(Y_ét, Λ)`. Both sides are right adjoints:
`(- ⊗^L L) ⋙ Rf^!` of `Rf_! ⋙ (- ⊗^L M)`, and `Rf^! ⋙ (- ⊗^L Lf^* L)` of
`(- ⊗^L Lf^* M) ⋙ Rf_!`, since tensoring with an invertible object is an equivalence and `Lf^*`
is monoidal. The projection formula at the dualizable object `M`
identifies the two left adjoints, so the right adjoints agree; this is the Yoneda argument of
the blueprint.

The blueprint states this for a closed immersion `f`, where `Rf_! = Rf_*`; the argument does
not use that `f` is a closed immersion. -/
noncomputable def derivedTensorRightCompRightDerivedUpperShriekIso (f : X ⟶ Y)
    [HasCompactification f]
    (L M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (e : ((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj M).obj L ≅ constantComplex Λ Y)
    (e' : ((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj L).obj M ≅ constantComplex Λ Y) :
    derivedTensorRight (ModuleCat.{u + 1} Λ) Y L ⋙ R(f)^![Λ] ≅
      R(f)^![Λ] ⋙
        derivedTensorRight (ModuleCat.{u + 1} Λ) X ((L((f)^*[ModuleCat.{u + 1} Λ])).obj L) :=
  derivedTensorRightCompRightDerivedUpperShriekIsoOfTensorIso _ f L M e e'

end Coprojection

omit [HasTateTwist Λ] in
/-- Blueprint `sk-lem-coprojection`: Co-projection for a closed immersion

For a closed immersion `i : Z ⟶ X`, a complex `K ∈ D^b_{ctf}(X, Λ)` and an object `L` of
`D^b_{ctf}(X, Λ)` that is *invertible*, the canonical co-projection

`Ri^! (K ⊗^L L) ≅ Ri^! K ⊗^L Li^* L`

is an isomorphism: an invertible tensor factor passes through `i^!` at the cost of restricting
it. Testing against an arbitrary `A ∈ D^b_{ctf}(Z, Λ)` and using `Ri_! = Ri_*`, the projection
formula for `Ri_*` and invertibility of `L`, the two Hom-functors agree naturally in `A`, so
Yoneda gives the isomorphism. Here it is the component at `K` of the co-projection
`AlgebraicGeometry.Etale.derivedTensorRightCompRightDerivedUpperShriekIso`
(blueprint `lem-pur-coprojection`), which needs neither that `i` is a closed immersion nor that
`K` and `L` lie in `D^b_{ctf}`.

Taking `L = Λ_X(m)[2m]`, whose restriction is `Λ_Z(m)[2m]`, this reads
`Ri^!(K(m)[2m]) ≅ (Ri^! K)(m)[2m]`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_derivedTensor_shiftTateObject`);
taking `L = Lf^* B` for `B` invertible on `Y` and `f' = f ∘ i` it reads
`Ri^!(K ⊗ Lf^* B) ≅ Ri^! K ⊗ Lf'^* B`
(`nonempty_iso_rightDerivedUpperShriek_derivedTensor_leftDerivedUpperStar`);
the diagonal identity is
`nonempty_iso_rightDerivedUpperShriek_derivedTensor_leftDerivedUpperStar_pair`.
-/
theorem nonempty_iso_rightDerivedUpperShriek_derivedTensor_of_isInvertible
    (i : Z ⟶ X) [IsClosedImmersion i] [HasCompactification i]
    (K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (_hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K)
    (_hLctf : DerivedCategory.boundedConstructibleFiniteTor Λ X L)
    (hL : DerivedCategory.isInvertible Λ X L) :
    Nonempty ((rightDerivedUpperShriek Λ i).obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj L) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) Z).obj
          ((rightDerivedUpperShriek Λ i).obj K)).obj
        ((L((i)^*[ModuleCat.{u + 1} Λ])).obj L)) :=
  have ⟨M, ⟨e'⟩, ⟨e⟩⟩ := hL
  ⟨(derivedTensorRightCompRightDerivedUpperShriekIso Λ i L M e e').app K⟩

section Consequences

variable {Y W : Scheme.{u}}

omit [HasTateTwist Λ] in
/-- Blueprint `sk-lem-coprojection`, invertible factor pulled back from the base: for
`i : Z ⟶ X`, `f : X ⟶ Y`, `K ∈ D(X_ét, Λ)` and `B` invertible on `Y`,

`Ri^! (K ⊗^L Lf^* B) ≅ Ri^! K ⊗^L L(i ≫ f)^* B`.

This is the co-projection for the invertible object `L = Lf^* B`, followed by
`Li^* Lf^* B ≅ L(i ≫ f)^* B`. -/
theorem nonempty_iso_rightDerivedUpperShriek_derivedTensor_leftDerivedUpperStar (i : Z ⟶ X)
    [HasCompactification i] (f : X ⟶ Y)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {B : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hB : DerivedCategory.isInvertible Λ Y B) :
    Nonempty ((R(i)^![Λ]).obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj
          ((L((f)^*[ModuleCat.{u + 1} Λ])).obj B)) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) Z).obj ((R(i)^![Λ]).obj K)).obj
        ((L((i ≫ f)^*[ModuleCat.{u + 1} Λ])).obj B)) :=
  have ⟨M, ⟨e'⟩, ⟨e⟩⟩ := hB.leftDerivedUpperStar f
  ⟨(derivedTensorRightCompRightDerivedUpperShriekIso Λ i _ M e e').app K ≪≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) Z).obj _).mapIso
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) i f).app B).symm⟩

omit [HasTateTwist Λ] in
/-- Blueprint `sk-lem-coprojection`, two invertible factors: for `i : Z ⟶ W` and `L₁`, `L₂`
invertible on `W`, applying the co-projection twice (to `L₁ ⊗^L L₂ ≅ (Λ_W ⊗^L L₁) ⊗^L L₂`)
gives

`Ri^! (L₁ ⊗^L L₂) ≅ (Ri^! Λ_W ⊗^L Li^* L₁) ⊗^L Li^* L₂`. -/
theorem nonempty_iso_rightDerivedUpperShriek_derivedTensor_of_isInvertible_of_isInvertible
    (i : Z ⟶ W) [HasCompactification i]
    {L₁ L₂ : _root_.DerivedCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (h₁ : DerivedCategory.isInvertible Λ W L₁) (h₂ : DerivedCategory.isInvertible Λ W L₂) :
    Nonempty ((R(i)^![Λ]).obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) W).obj L₁).obj L₂) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) Z).obj
          (((derivedTensor (ModuleCat.{u + 1} Λ) Z).obj
              ((R(i)^![Λ]).obj (constantComplex Λ W))).obj
            ((L((i)^*[ModuleCat.{u + 1} Λ])).obj L₁))).obj
        ((L((i)^*[ModuleCat.{u + 1} Λ])).obj L₂)) :=
  have ⟨M₁, ⟨e₁'⟩, ⟨e₁⟩⟩ := h₁
  have ⟨M₂, ⟨e₂'⟩, ⟨e₂⟩⟩ := h₂
  ⟨(R(i)^![Λ]).mapIso
      (((derivedTensor (ModuleCat.{u + 1} Λ) W).mapIso
        (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) W L₁).symm).app L₂) ≪≫
    (derivedTensorRightCompRightDerivedUpperShriekIso Λ i L₂ M₂ e₂ e₂').app _ ≪≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) Z).mapIso
      ((derivedTensorRightCompRightDerivedUpperShriekIso Λ i L₁ M₁ e₁ e₁').app _)).app _⟩

omit [HasTateTwist Λ] in
/-- Blueprint `sk-lem-coprojection`, the diagonal identity: for `Δ : X ⟶ W` and
`p₁, p₂ : W ⟶ X` (in the blueprint, the diagonal of `X ⟶ Y` and the two projections of
`W = X ×_Y X`) and `ω` invertible on `X`,

`RΔ^! (Lp₁^* ω ⊗^L Lp₂^* ω) ≅ (RΔ^! Λ_W ⊗^L LΔ^* Lp₁^* ω) ⊗^L LΔ^* Lp₂^* ω`.

The objects `Lp₁^* ω` and `Lp₂^* ω` are invertible as pullbacks of an invertible object. -/
theorem nonempty_iso_rightDerivedUpperShriek_derivedTensor_leftDerivedUpperStar_pair
    (Δ : X ⟶ W) [HasCompactification Δ] (p₁ p₂ : W ⟶ X)
    {ω : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hω : DerivedCategory.isInvertible Λ X ω) :
    Nonempty ((R(Δ)^![Λ]).obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) W).obj
            ((L((p₁)^*[ModuleCat.{u + 1} Λ])).obj ω)).obj
          ((L((p₂)^*[ModuleCat.{u + 1} Λ])).obj ω)) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
          (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
              ((R(Δ)^![Λ]).obj (constantComplex Λ W))).obj
            ((L((Δ)^*[ModuleCat.{u + 1} Λ])).obj ((L((p₁)^*[ModuleCat.{u + 1} Λ])).obj ω)))).obj
        ((L((Δ)^*[ModuleCat.{u + 1} Λ])).obj ((L((p₂)^*[ModuleCat.{u + 1} Λ])).obj ω))) :=
  nonempty_iso_rightDerivedUpperShriek_derivedTensor_of_isInvertible_of_isInvertible Λ Δ
    (hω.leftDerivedUpperStar p₁) (hω.leftDerivedUpperStar p₂)

end Consequences

/-- Blueprint `lem-pur-immersion-twist`: The co-projection for the twist

For `i : Z ⟶ X` admitting a compactification (in the blueprint: a closed immersion of separated
finite-type `k`-schemes), `K ∈ D(X_ét, Λ)` and `m ∈ ℤ`,

`Ri^! (K ⊗^L Λ_X(m)[2m]) ≅ Ri^! K ⊗^L Λ_Z(m)[2m]`.

This is the co-projection `AlgebraicGeometry.Etale.derivedTensorRightCompRightDerivedUpperShriekIso`
(blueprint `lem-pur-coprojection`) for the invertible object `L = Λ_X(m)[2m]`, followed by the
identification `Li^* (Λ_X(m)[2m]) ≅ Λ_Z(m)[2m]` of the Tate twist datum. -/
theorem nonempty_iso_rightDerivedUpperShriek_derivedTensor_shiftTateObject (i : Z ⟶ X)
    [HasCompactification i] [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Z]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (m : ℤ) :
    Nonempty ((R(i)^![Λ]).obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj ((tateObject Λ X m)⟦2 * m⟧)) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) Z).obj ((R(i)^![Λ]).obj K)).obj
        ((tateObject Λ Z m)⟦2 * m⟧)) :=
  have ⟨M, ⟨e'⟩, ⟨e⟩⟩ := (isInvertible_tateObject Λ X m).shift (2 * m)
  ⟨(derivedTensorRightCompRightDerivedUpperShriekIso Λ i _ M e e').app K ≪≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) Z).obj _).mapIso
      (leftDerivedUpperStarTateShiftIso Λ i m)⟩

end Etale

end AlgebraicGeometry
