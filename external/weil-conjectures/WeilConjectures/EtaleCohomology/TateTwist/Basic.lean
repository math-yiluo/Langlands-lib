/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.SixFunctors.Etale.Derived.InvertibleSheafPowers
public import WeilConjectures.SixFunctors.Etale.Derived.PullbackIntTensorFamily
public import WeilConjectures.SixFunctors.Etale.Derived.InvertibleRestriction
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.ConstructibleSheaf.Monoidal

/-!
# The Tate twists

Let `Λ` be a commutative ring of positive characteristic `n`. This file constructs the Tate
twists `Λ_X(m)`, `m ∈ ℤ`, of the blueprint (`definition-tate-twists`) on every scheme
`X` on which `n` is invertible, and shows that they form a Tate twist datum
(`AlgebraicGeometry.Etale.HasTateTwist`) for the coefficient ring `Λ`.

## Construction

On the universal base `S = Spec ℤ[1/n]` (`AlgebraicGeometry.invertibleExponentBase`) the Tate
sheaf `Λ_S(1) = μₙ ⊗ Λ` (`AlgebraicGeometry.Etale.tateSheaf`) becomes the constant sheaf `Λ` on
the étale cover `V ⟶ S` adjoining a primitive `n`-th root of unity
(`AlgebraicGeometry.Etale.tateCover`), so its dual is a tensor inverse
(`AlgebraicGeometry.Etale.tateSheafTensorInverse`). Its integer tensor powers in `D(S_ét, Λ)` form
a coherent family `Λ_S(m)` (`AlgebraicGeometry.Etale.tateIntTensorFamily`): `Λ_S(m)` is the
`m`-th tensor power of `Λ_S(1)` for `m ≥ 0` and of its dual for `m < 0`, placed in degree zero.
On a scheme `X` on which `n` is invertible, `Λ_X(m)` is the derived pullback of `Λ_S(m)` along
the unique morphism `X ⟶ S` (`AlgebraicGeometry.Etale.tateTwistObject`); all compatibilities
between the twists of different schemes are then those of the derived pullbacks. On the other
schemes, which play no role, `Λ_X(m)` is defined to be `Λ_X`.

## Main definitions

- `AlgebraicGeometry.Etale.tateTwistObject`: the twisting objects `Λ_X(m)`.
- `AlgebraicGeometry.Etale.hasTateTwist`: the Tate twist datum.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The characteristic of `Λ` is invertible in `ℤ[1/n]`. -/
lemma isUnit_ringChar_invertibleExponentRing :
    IsUnit ((ringChar Λ : ℕ) : InvertibleExponentRing.{u} Λ) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (ringChar Λ : ℤ))
    (ringChar Λ : ℤ)
  let φ : Localization.Away (ringChar Λ : ℤ) →+* InvertibleExponentRing.{u} Λ :=
    ULift.ringEquiv.symm.toRingHom
  simpa using h.map φ

/-- The ring `ℤ[1/n][ζ]` of the cover `V` of `Spec ℤ[1/n]` adjoining a primitive `n`-th root of
unity. -/
noncomputable abbrev tateCoverRing : CommRingCat.{u} :=
  .of (PrimitiveRootsAlgebra (InvertibleExponentRing.{u} Λ) (ringChar Λ))

/-- The étale cover `V ⟶ Spec ℤ[1/n]` adjoining a primitive `n`-th root of unity, `n` being the
characteristic of `Λ`. -/
noncomputable abbrev tateCover : Spec (tateCoverRing Λ) ⟶ invertibleExponentBase.{u} Λ :=
  primitiveRootsCover _ _

variable [NeZero (ringChar Λ)]

instance etale_tateCover : Etale (tateCover Λ) :=
  etale_primitiveRootsCover _ _ (NeZero.ne _) (isUnit_ringChar_invertibleExponentRing Λ)

omit [NeZero (ringChar Λ)] in
lemma surjective_tateCover : Function.Surjective (tateCover Λ).base :=
  surjective_primitiveRootsCover _ _ (isUnit_ringChar_invertibleExponentRing Λ)

/-- The primitive root of unity `ζ` on the cover `V`. -/
noncomputable def tateCoverZeta : Γ(Spec (tateCoverRing Λ), ⊤)ˣ :=
  ((PrimitiveRootsAlgebra.isUnit_zeta _ _ (Nat.pos_of_ne_zero (NeZero.ne _))).map
    (Scheme.ΓSpecIso (tateCoverRing Λ)).inv.hom).unit

lemma tateCoverZeta_pow : tateCoverZeta Λ ^ ringChar Λ = 1 := by
  ext
  simp only [tateCoverZeta, Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one,
    ← map_pow, PrimitiveRootsAlgebra.zeta_pow, map_one]

lemma isUnit_tateCoverZeta_pow_sub {i j : ℕ} (hi : i < ringChar Λ) (hj : j < ringChar Λ)
    (hij : i ≠ j) :
    IsUnit (((tateCoverZeta Λ : _) : Γ(Spec (tateCoverRing Λ), ⊤)) ^ i -
      ((tateCoverZeta Λ : _) : Γ(Spec (tateCoverRing Λ), ⊤)) ^ j) := by
  simpa [tateCoverZeta, ← map_pow, ← map_sub] using
    (PrimitiveRootsAlgebra.isUnit_zeta_pow_sub_zeta_pow _ _ hi hj hij).map
      (Scheme.ΓSpecIso (tateCoverRing Λ)).inv.hom

/-- The Tate sheaf of `Spec ℤ[1/n]` becomes the constant sheaf `Λ` on the cover `V`. -/
noncomputable def upperStarTateCoverTateSheafIso :
    (tateCover Λ)^*[ModuleCat.{u + 1} Λ].obj (tateSheaf Λ (invertibleExponentBase.{u} Λ)) ≅
      𝟙_ _ :=
  asIso (upperStarTateSheafToTateSheaf Λ (tateCover Λ)) ≪≫
    tateSheafIsoConstantSheaf _ (tateCoverZeta Λ) (tateCoverZeta_pow Λ)
      (fun _ hi _ hj hij ↦ isUnit_tateCoverZeta_pow_sub Λ hi hj hij)

/-- The dual of the Tate sheaf of `Spec ℤ[1/n]` is a tensor inverse: the Tate sheaf is trivial
on the étale cover `V`. -/
noncomputable def tateSheafTensorInverse :
    TensorInverse (tateSheaf Λ (invertibleExponentBase.{u} Λ)) :=
  tensorInverseOfUpperStarIso (ModuleCat.{u + 1} Λ) (fun _ : Unit ↦ tateCover Λ)
    (by rw [Set.iUnion_const]; exact Set.range_eq_univ.2 (surjective_tateCover Λ)) _
    (fun _ ↦ upperStarTateCoverTateSheafIso Λ)

/-- The coherent family of the Tate twists `Λ_S(m)` on `S = Spec ℤ[1/n]`: the integer tensor
powers of the Tate sheaf `Λ_S(1)`, placed in degree zero. -/
noncomputable def tateIntTensorFamily :=
  (tateSheafTensorInverse Λ).singleFunctor.intTensorFamily


open Classical in
/-- Blueprint `definition-tate-twists`: Coefficient Tate twists.

The Tate twisting object `Λ_X(m) ∈ D(X_ét, Λ)`: on a scheme `X` on which the characteristic `n`
of `Λ` is invertible, the derived pullback of `Λ_S(m)`
(`AlgebraicGeometry.Etale.tateIntTensorFamily`) along the unique morphism `X ⟶ S = Spec ℤ[1/n]`.
It is the sheaf `(μₙ ⊗ Λ)^{⊗ m}` for `m ≥ 0`, and its dual `Hom((μₙ ⊗ Λ)^{⊗ -m}, Λ)` for
`m < 0`, placed in degree zero. On the other schemes it is `Λ_X`. -/
noncomputable def tateTwistObject (X : Scheme.{u}) (m : ℤ) :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  if h : HasInvertibleExponent Λ X then
    haveI := h
    (pullbackIntTensorFamily (ModuleCat.{u + 1} Λ) (tateIntTensorFamily Λ)
      (toInvertibleExponentBase (Λ := Λ) X)).obj m
  else constantComplex Λ X

lemma tateTwistObject_eq (X : Scheme.{u}) [HasInvertibleExponent Λ X] :
    tateTwistObject Λ X = (pullbackIntTensorFamily (ModuleCat.{u + 1} Λ) (tateIntTensorFamily Λ)
      (toInvertibleExponentBase (Λ := Λ) X)).obj :=
  funext fun _ ↦ dite_eq_left _

/-- The coherent family of the Tate twists `Λ_X(m)` on a scheme `X` on which the characteristic
of `Λ` is invertible. -/
noncomputable def tateTwistIntTensorFamily (X : Scheme.{u}) [HasInvertibleExponent Λ X] :=
  (pullbackIntTensorFamily (ModuleCat.{u + 1} Λ) (tateIntTensorFamily Λ)
    (toInvertibleExponentBase (Λ := Λ) X)).copy (tateTwistObject Λ X) (tateTwistObject_eq Λ X)

section Fields

variable (X : Scheme.{u}) [HasInvertibleExponent Λ X]

/-- `Λ_X(0) ≅ Λ_X`. -/
noncomputable def tateTwistObjectZeroIso : tateTwistObject Λ X 0 ≅ constantComplex Λ X :=
  (tateTwistIntTensorFamily Λ X).zeroIso

/-- `Λ_X(m) ⊗ᴸ Λ_X(m') ≅ Λ_X(m + m')`. -/
noncomputable def tateTwistObjectAddIso (m m' : ℤ) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (tateTwistObject Λ X m)).obj
      (tateTwistObject Λ X m') ≅ tateTwistObject Λ X (m + m') :=
  (tateTwistIntTensorFamily Λ X).derivedTensorAddIso m m'

lemma isInvertible_tateTwistObject (m : ℤ) :
    DerivedCategory.isInvertible Λ X (tateTwistObject Λ X m) :=
  (tateTwistIntTensorFamily Λ X).exists_derivedTensor_iso m

lemma tateTwistObjectAddIso_zero_left (m : ℤ) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).map (tateTwistObjectZeroIso Λ X).hom).app
        (tateTwistObject Λ X m) ≫ (derivedTensorLeftUnitor _ X (tateTwistObject Λ X m)).hom =
      (tateTwistObjectAddIso Λ X 0 m).hom ≫ eqToHom (by rw [zero_add]) :=
  (tateTwistIntTensorFamily Λ X).derivedTensor_zero_left m

lemma tateTwistObjectAddIso_zero_right (m : ℤ) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (tateTwistObject Λ X m)).map
        (tateTwistObjectZeroIso Λ X).hom ≫
        (derivedTensorRightUnitor _ X (tateTwistObject Λ X m)).hom =
      (tateTwistObjectAddIso Λ X m 0).hom ≫ eqToHom (by rw [add_zero]) :=
  (tateTwistIntTensorFamily Λ X).derivedTensor_zero_right m

lemma tateTwistObjectAddIso_assoc (a b c : ℤ) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).map (tateTwistObjectAddIso Λ X a b).hom).app
        (tateTwistObject Λ X c) ≫ (tateTwistObjectAddIso Λ X (a + b) c).hom =
      (derivedTensorAssociator _ X (tateTwistObject Λ X a) (tateTwistObject Λ X b)
          (tateTwistObject Λ X c)).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (tateTwistObject Λ X a)).map
          (tateTwistObjectAddIso Λ X b c).hom ≫ (tateTwistObjectAddIso Λ X a (b + c)).hom ≫
            eqToHom (by rw [add_assoc]) :=
  (tateTwistIntTensorFamily Λ X).derivedTensor_assoc a b c

end Fields

section Pullback

variable {X Y Z : Scheme.{u}} [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y]

/-- The identification `Lf^* Λ_Y(m) ≅ Λ_X(m)` of the Tate twists, through the composition
isomorphism of the derived pullbacks along `X ⟶ Y ⟶ S`. -/
noncomputable def leftDerivedUpperStarTateTwistObjectIso (f : X ⟶ Y) (m : ℤ) :
    L((f)^*[ModuleCat.{u + 1} Λ]).obj (tateTwistObject Λ Y m) ≅ tateTwistObject Λ X m :=
  pullbackIntTensorFamilyCopyIso _ _ (tateTwistObject Λ X) (tateTwistObject Λ Y) f
    (toInvertibleExponentBase X) (toInvertibleExponentBase Y)
    (comp_toInvertibleExponentBase f).symm (tateTwistObject_eq Λ X) (tateTwistObject_eq Λ Y) m

lemma leftDerivedUpperStarTateTwistObjectIso_comp [HasInvertibleExponent Λ Z] (f : X ⟶ Y)
    (g : Y ⟶ Z) (m : ℤ) :
    leftDerivedUpperStarTateTwistObjectIso Λ (f ≫ g) m =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f g).app (tateTwistObject Λ Z m) ≪≫
        (L((f)^*[ModuleCat.{u + 1} Λ])).mapIso (leftDerivedUpperStarTateTwistObjectIso Λ g m) ≪≫
          leftDerivedUpperStarTateTwistObjectIso Λ f m :=
  pullbackIntTensorFamilyCopyIso_comp _ _ (tateTwistObject Λ X) (tateTwistObject Λ Y)
    (tateTwistObject Λ Z) f g (toInvertibleExponentBase X) (toInvertibleExponentBase Y)
    (toInvertibleExponentBase Z) (comp_toInvertibleExponentBase (f ≫ g)).symm
    (comp_toInvertibleExponentBase g).symm (comp_toInvertibleExponentBase f).symm
    (tateTwistObject_eq Λ X) (tateTwistObject_eq Λ Y) (tateTwistObject_eq Λ Z) m

lemma leftDerivedUpperStar_map_tateTwistObjectAddIso (f : X ⟶ Y) (m m' : ℤ) :
    (L((f)^*[ModuleCat.{u + 1} Λ])).map (tateTwistObjectAddIso Λ Y m m').hom ≫
        (leftDerivedUpperStarTateTwistObjectIso Λ f (m + m')).hom =
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) f _ _).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) X).map
          (leftDerivedUpperStarTateTwistObjectIso Λ f m).hom).app _ ≫
          ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (tateTwistObject Λ X m)).map
            (leftDerivedUpperStarTateTwistObjectIso Λ f m').hom ≫
            (tateTwistObjectAddIso Λ X m m').hom :=
  map_addIso_pullbackIntTensorFamilyCopyIso _ _ (tateTwistObject Λ X) (tateTwistObject Λ Y) f
    (toInvertibleExponentBase X) (toInvertibleExponentBase Y)
    (comp_toInvertibleExponentBase f).symm (tateTwistObject_eq Λ X) (tateTwistObject_eq Λ Y)
    m m'

end Pullback

section Sheaf

variable (X : Scheme.{u}) [HasInvertibleExponent Λ X]

/-- The sheaf `(μₙ ⊗ Λ)^{⊗ m}` on `X` (for `m < 0`, the `-m`-th tensor power of the dual of
`μₙ ⊗ Λ`): the pullback of the integer tensor powers of the Tate sheaf of `S = Spec ℤ[1/n]`. -/
noncomputable def tateTwistSheaf (m : ℤ) : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  (toInvertibleExponentBase (Λ := Λ) X)^*[ModuleCat.{u + 1} Λ].obj
    ((tateSheafTensorInverse Λ).zpow m)

/-- The Tate twist `Λ_X(m)` is the sheaf `(μₙ ⊗ Λ)^{⊗ m}` placed in degree zero. -/
noncomputable def tateTwistObjectIsoSingleFunctor (m : ℤ) :
    tateTwistObject Λ X m ≅
      (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj
        (tateTwistSheaf Λ X m) :=
  eqToIso (congrFun (tateTwistObject_eq Λ X) m) ≪≫
    L((toInvertibleExponentBase (Λ := Λ) X)^*[ModuleCat.{u + 1} Λ]).mapIso
      ((tateSheafTensorInverse Λ).zpowSingleFunctorIso m) ≪≫
    (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} Λ)
      (toInvertibleExponentBase (Λ := Λ) X)).app _

/-- The étale cover `X ×_S V ⟶ X` adjoining a primitive `n`-th root of unity. -/
noncomputable abbrev tateCoverOf :
    pullback (toInvertibleExponentBase (Λ := Λ) X) (tateCover Λ) ⟶ X :=
  pullback.fst _ _

omit [NeZero (ringChar Λ)] in
lemma surjective_tateCoverOf : Function.Surjective (tateCoverOf Λ X).base := by
  intro x
  obtain ⟨v, hv⟩ := surjective_tateCover Λ (toInvertibleExponentBase (Λ := Λ) X x)
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x v hv.symm
  exact ⟨z, hz⟩

/-- The sheaf `(μₙ ⊗ Λ)^{⊗ m}` is trivial on the cover `X ×_S V`. -/
noncomputable def upperStarTateCoverOfTateTwistSheafIso (m : ℤ) :
    (tateCoverOf Λ X)^*[ModuleCat.{u + 1} Λ].obj (tateTwistSheaf Λ X m) ≅ 𝟙_ _ :=
  ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) (tateCoverOf Λ X)
      (toInvertibleExponentBase (Λ := Λ) X)
      (pullback.snd _ _ ≫ tateCover Λ) pullback.condition.symm).app _).symm ≪≫
    (Etale.upperStarComp (ModuleCat.{u + 1} Λ) (pullback.snd _ _) (tateCover Λ) _ rfl).app _ ≪≫
    (pullback.snd (toInvertibleExponentBase (Λ := Λ) X) (tateCover Λ))^*[ModuleCat.{u + 1} Λ].mapIso
      ((tateSheafTensorInverse Λ).zpowMapIsoUnit ((tateCover Λ)^*[ModuleCat.{u + 1} Λ])
        (upperStarTateCoverTateSheafIso Λ) m) ≪≫
    (Functor.Monoidal.εIso _).symm

/-- The stalks of `(μₙ ⊗ Λ)^{⊗ m}` at the geometric points are free of rank one. -/
noncomputable def sheafFiberTateTwistSheafIso (m : ℤ) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X) :
    (pointSmallEtale s).sheafFiber.obj (tateTwistSheaf Λ X m) ≅ ModuleCat.of Λ Λ := by
  have hlift := exists_comp_primitiveRootsCover_eq _ _ (isUnit_ringChar_invertibleExponentRing Λ)
    (s ≫ toInvertibleExponentBase (Λ := Λ) X)
  let t₀ := hlift.choose
  let t := pullback.lift s t₀ hlift.choose_spec.symm
  have ht : t ≫ tateCoverOf Λ X = s := pullback.lift_fst _ _ _
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  exact eqToIso (by rw [ht]) ≪≫
    ((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) (tateCoverOf Λ X) t).app _).symm ≪≫
    (pointSmallEtale t).sheafFiber.mapIso (upperStarTateCoverOfTateTwistSheafIso Λ X m) ≪≫
    (pointSmallEtale t).sheafFiberConstantSheafIso (ModuleCat.of Λ Λ)

/-- The sheaf `(μₙ ⊗ Λ)^{⊗ m}` is finite locally constant: it is trivial on the étale cover
`X ×_S V`, and its stalks are free of rank one. -/
lemma isFiniteLocallyConstantSheaf_tateTwistSheaf (m : ℤ) :
    IsFiniteLocallyConstantSheaf (tateTwistSheaf Λ X m) where
  toIsLocallyConstantSheaf := by
    let 𝒰 : Cover.{u} etalePrecoverage X := Cover.mkOfCovers PUnit (fun _ ↦ _)
      (fun _ ↦ tateCoverOf Λ X) (fun x ↦ ⟨⟨⟩, surjective_tateCoverOf Λ X x⟩)
      (fun _ ↦ inferInstance)
    have : ∀ i, IsLocallyConstantSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj
        (tateTwistSheaf Λ X m)) := fun _ ↦
      have : IsLocallyConstantSheaf (𝟙_ (Sheaf (pullback (toInvertibleExponentBase (Λ := Λ) X)
          (tateCover Λ)).smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
        (isFiniteLocallyConstantSheaf_constantSheaf
          (𝟙_ (ModuleCat.{u + 1} Λ))).toIsLocallyConstantSheaf
      IsLocallyConstantSheaf.of_iso (upperStarTateCoverOfTateTwistSheafIso Λ X m).symm
    exact IsLocallyConstantSheaf.of_cover 𝒰 _
  toIsFiniteSheaf := ⟨fun _ _ _ s ↦ ((ModuleCat.isFinitelyGenerated_iff _).2
    (inferInstanceAs (Module.Finite Λ Λ))).of_iso (sheafFiberTateTwistSheafIso Λ X m s).symm⟩

/-- The sheaf `(μₙ ⊗ Λ)^{⊗ m}` is flat: `(μₙ ⊗ Λ)^{⊗ -m}` is a tensor inverse. -/
lemma flat_tateTwistSheaf (m : ℤ) : ObjectProperty.flat (tateTwistSheaf Λ X m) :=
  ObjectProperty.flat_of_tensorIso (Y := tateTwistSheaf Λ X (-m))
    (Functor.Monoidal.μIso _ _ _ ≪≫
      (toInvertibleExponentBase (Λ := Λ) X)^*[ModuleCat.{u + 1} Λ].mapIso
        ((tateSheafTensorInverse Λ).intTensorFamily.addIso m (-m) ≪≫
          eqToIso (congrArg (tateSheafTensorInverse Λ).zpow (add_neg_cancel m))) ≪≫
      (Functor.Monoidal.εIso _).symm)

/-- Every Tate twist `Λ_X(m)` lies in `D^b_{ctf}(X, Λ)`: it is a finite locally constant flat
sheaf placed in degree zero. -/
lemma boundedConstructibleFiniteTor_tateTwistObject (m : ℤ) :
    DerivedCategory.boundedConstructibleFiniteTor Λ X (tateTwistObject Λ X m) := by
  have := isFiniteLocallyConstantSheaf_tateTwistSheaf Λ X m
  have : IsConstructibleSheaf (tateTwistSheaf Λ X m) :=
    IsFiniteLocallyConstantSheaf.isConstructibleSheaf ‹_›
  refine ⟨(Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X).prop_of_iso
      (tateTwistObjectIsoSingleFunctor Λ X m).symm
      (Etale.DerivedCategory.boundedConstructible_singleFunctor_obj _ 0),
    (Etale.DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} Λ) X).prop_of_iso
      (tateTwistObjectIsoSingleFunctor Λ X m).symm
      ⟨0, 0, _root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
        (flat_tateTwistSheaf Λ X m)⟩⟩

/-- Every Tate twist `Λ_X(m)` is a locally constant sheaf of rank one placed in degree zero. -/
lemma exists_isLocallyConstantSheaf_tateTwistObject (m : ℤ) :
    ∃ L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ), IsLocallyConstantSheaf L ∧
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
        Nonempty ((pointSmallEtale s).sheafFiber.obj L ≅ ModuleCat.of Λ Λ)) ∧
      Nonempty (tateTwistObject Λ X m ≅ (DerivedCategory.singleFunctor _ 0).obj L) :=
  ⟨tateTwistSheaf Λ X m,
    (isFiniteLocallyConstantSheaf_tateTwistSheaf Λ X m).toIsLocallyConstantSheaf,
    fun _ _ _ s ↦ ⟨sheafFiberTateTwistSheafIso Λ X m s⟩, ⟨tateTwistObjectIsoSingleFunctor Λ X m⟩⟩

end Sheaf

/-- Blueprint `definition-tate-twists`: Coefficient Tate twists.

The genuine Tate twist datum of a commutative ring `Λ` of positive characteristic `n`:
`Λ_X(m) = (μₙ ⊗ Λ)^{⊗ m}` on the schemes `X` on which `n` is invertible
(`AlgebraicGeometry.Etale.tateTwistObject`), with the identifications coming from the derived
pullbacks along the morphisms to `Spec ℤ[1/n]`. -/
noncomputable instance hasTateTwist : HasTateTwist Λ where
  twistObject := tateTwistObject Λ
  twistObjectZeroIso X _ := tateTwistObjectZeroIso Λ X
  twistObjectAddIso X _ := tateTwistObjectAddIso Λ X
  leftDerivedUpperStarTwistObjectIso f := leftDerivedUpperStarTateTwistObjectIso Λ f
  isInvertible_twistObject X _ := isInvertible_tateTwistObject Λ X
  boundedConstructibleFiniteTor_twistObject X _ := boundedConstructibleFiniteTor_tateTwistObject Λ X
  exists_isLocallyConstantSheaf_twistObject X _ :=
    exists_isLocallyConstantSheaf_tateTwistObject Λ X
  twistObjectAddIso_zero_left X _ := tateTwistObjectAddIso_zero_left Λ X
  twistObjectAddIso_zero_right X _ := tateTwistObjectAddIso_zero_right Λ X
  twistObjectAddIso_assoc X _ := tateTwistObjectAddIso_assoc Λ X
  leftDerivedUpperStarTwistObjectIso_comp f g := leftDerivedUpperStarTateTwistObjectIso_comp Λ f g
  leftDerivedUpperStar_map_twistObjectAddIso f := leftDerivedUpperStar_map_tateTwistObjectAddIso Λ f

end Etale

end AlgebraicGeometry
