/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.ForgetCohomologyVanishing
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.TraceFormula.CurveLocal.StrictLocalVanishing

/-!
# Higher cohomology of the affine line over a strictly henselian local ring

Let `R` be a strictly henselian local ring, `Λ` a finite coefficient ring whose exponent is
invertible on `S = Spec R`, `p : 𝔸¹_S ⟶ S` the affine line and `M` a locally constant sheaf of
`Λ`-modules on `S`. This file reduces the vanishing of `Hᵠ(𝔸¹_R, p^* M)` for `q ≥ 2`
(SGA 4 XV 2.1–2.2, Fu, *Étale cohomology theory*, 7.4, Milne, *Étale cohomology*, VI.4) to the
vanishing of the higher direct images `Rᵠp_*(p^* M)`
(`AlgebraicGeometry.Etale.isZero_cohomology_affineLine_of_isZero_higherDirectImage`).

## The argument

The global sections functor of the strictly local scheme `S` is exact and computes the stalk at
the closed geometric point `t` of `S`. Hence the Leray isomorphism `RΓ(𝔸¹_S, -) ≅ RΓ(S, Rp_* -)`
identifies `Hᵠ(𝔸¹_S, F)` with `Γ(S, Rᵠp_* F)`, which vanishes as soon as the stalk of `Rᵠp_* F`
at `t` does (`AlgebraicGeometry.Etale.subsingleton_H_of_isZero_sheafFiber_higherDirectImage`).
This reduces the statement to the vanishing of the higher direct images `Rᵠp_*(p^* M)` for
`q ≥ 2`, the sheaf form of SGA 4 XV 2.2 in degrees `≥ 2`, which is taken as a hypothesis.

Note that the vanishing of `Rᵠp_* G` for `q ≥ 2` fails for general (non locally constant)
torsion sheaves `G` on `𝔸¹_S` over a base of positive dimension: the relative affine vanishing
theorem only bounds `Rᵠp_*` by the dimension of `𝔸¹_S`, not by the relative dimension (compare
`AlgebraicGeometry.Etale.isZero_sheafFiber_higherDirectImage_of_isAffineHom`, Stacks 0F0X).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The cohomology `Hᵠ(X, G)` of a sheaf of `Λ`-modules placed in degree `0`, computed in
`D(Λ)`, vanishes if and only if the cohomology of the underlying abelian sheaf does
(Stacks 03FD). -/
theorem isZero_cohomology_singleFunctor_iff_subsingleton_H (X : Scheme.{u})
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    IsZero ((cohomology (ModuleCat.{u + 1} Λ) X q).obj
      ((DerivedCategory.singleFunctor _ 0).obj G)) ↔
      Subsingleton (Sheaf.H ((sheafForget₂ Λ X).obj G) q) := by
  obtain ⟨e⟩ := Scheme.nonempty_etaleModuleCohomology_forgetIso X Λ q
  obtain ⟨e'⟩ := Scheme.nonempty_sheafH_extDerivedIso X q
  refine ModuleCat.isZero_iff_subsingleton.trans ((AddCommGrpCat.isZero_iff_subsingleton
    (G := (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj _)).symm.trans
    (Iff.trans ?_ (AddCommGrpCat.isZero_iff_subsingleton
      (G := (Sheaf.functorH X.smallEtaleTopology q).obj ((sheafForget₂ Λ X).obj G)))))
  exact ⟨fun h ↦ h.of_iso (e'.app _ ≪≫ (e.app G).symm),
    fun h ↦ h.of_iso (e.app G ≪≫ (e'.app _).symm)⟩

/-- **Cohomology over a strictly local base through the stalk of the higher direct image.**
Let `f : X ⟶ T` be a morphism to a scheme `T ≅ Spec R` with `R` strictly henselian local, `t` a
geometric point of `T` over the closed point and `F` a sheaf of `Λ`-modules on `X`. If the stalk
at `t` of `Rᵠf_* F` vanishes, then so does `Hᵠ(X, F)`.

Indeed, by the Leray isomorphism `RΓ(X, -) ≅ RΓ(T, Rf_* -)` and the exactness of the global
sections functor of `T`, `Hᵠ(X, F) = Γ(T, Rᵠf_* F)`, and a sheaf on `T` with vanishing stalk at
`t` has vanishing global sections. -/
theorem subsingleton_H_of_isZero_sheafFiber_higherDirectImage {R : Type u} [CommRing R]
    [IsStrictlyHenselianLocalRing R] {X T : Scheme.{u}} (f : X ⟶ T) (e : T ≅ Spec (.of R))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (ht : (t ≫ e.hom) (IsLocalRing.closedPoint Ω) = IsLocalRing.closedPoint R)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ)
    (hF : IsZero ((pointSmallEtale t).sheafFiber.obj (higherDirectImage Λ f q F))) :
    Subsingleton (Sheaf.H ((sheafForget₂ Λ X).obj F) q) := by
  rw [← isZero_cohomology_singleFunctor_iff_subsingleton_H]
  have := preservesFiniteColimits_Γ_of_iso_isStrictlyHenselianLocalRing (Λ := Λ) e
  let K := (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj
    F
  let L := ((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctor.obj K
  have hL : IsZero ((pointSmallEtale t).sheafFiber.obj
      ((DerivedCategory.homologyFunctor _ q).obj L)) :=
    hF.of_iso ((pointSmallEtale t).sheafFiber.mapIso
      ((DerivedCategory.homologyFunctor _ q).mapIso
        (((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusCompatibility.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)).symm))
  have hΓ : IsZero ((Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      ((DerivedCategory.homologyFunctor _ q).obj L)) :=
    IsZero.of_iso (isZero_obj_of_isZero_sheafFiber e t ht _ hL)
      ((Sheaf.ΓNatIsoSheafSections _ _
        (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)).app _)
  exact hΓ.of_iso ((DerivedCategory.homologyFunctor _ q).mapIso
      ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ f).app K).symm ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso
      ((Sheaf.Γ T.smallEtaleTopology _).rightDerivedFunctorIsoMapDerivedCategory.app L) ≪≫
    (((Sheaf.Γ T.smallEtaleTopology _).mapDerivedCategoryHomologyFunctorIso q).app L).symm)

/-- **The affine line over a strictly henselian local ring has no cohomology in degrees `≥ 2`**
with locally constant coefficients from the base: for `R` strictly henselian local, `Λ` a finite
ring whose exponent is invertible on `Spec R` and `M` a locally constant sheaf of `Λ`-modules on
`Spec R`, `Hᵠ(𝔸¹_R, p^* M) = 0` for `q ≥ 2` (SGA 4 XV 2.1–2.2).

It is `Γ(Spec R, Rᵠp_*(p^* M))`
(`AlgebraicGeometry.Etale.subsingleton_H_of_isZero_sheafFiber_higherDirectImage`), and
as soon as `Rᵠp_*(p^* M) = 0` (SGA 4 XV 2.2; this vanishing is the hypothesis `hM`). -/
theorem subsingleton_H_affineLine_of_isZero_higherDirectImage
    {R : Type u} [CommRing R]
    [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    [HasInvertibleExponent Λ (Spec (.of R))]
    (M : Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsLocallyConstantSheaf M] (q : ℕ)
    (hM : IsZero (higherDirectImage Λ (𝔸(ULift.{u} (Fin 1); Spec (.of R)) ↘ Spec (.of R)) q
      ((𝔸(ULift.{u} (Fin 1); Spec (.of R)) ↘ Spec (.of R))^*[ModuleCat.{u + 1} Λ].obj M))) :
    Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((𝔸(ULift.{u} (Fin 1); Spec (.of R)) ↘ Spec (.of R))^*[ModuleCat.{u + 1} Λ].obj M)) q) := by
  have : IsStrictlyHenselianLocalRing R := { isSepClosed_residueField := inferInstance }
  refine subsingleton_H_of_isZero_sheafFiber_higherDirectImage Λ
    (𝔸(ULift.{u} (Fin 1); Spec (.of R)) ↘ Spec (.of R)) (Iso.refl _)
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ?_ _ q ?_
  · simp only [Iso.refl_hom, Category.comp_id]
    have : IsLocalHom (CommRingCat.ofHom (IsLocalRing.residue R)).hom := by
      rw [CommRingCat.hom_ofHom]
      infer_instance
    exact Spec_closedPoint
  · exact Functor.map_isZero _ hM

/-- **The affine line over a strictly henselian local ring has no cohomology in degrees `≥ 2`**,
as the vanishing of the abelian group `Hᵠ(𝔸¹_R, p^* M)`; see
`AlgebraicGeometry.Etale.subsingleton_H_affineLine_of_isZero_higherDirectImage`. -/
theorem isZero_cohomology_affineLine_of_isZero_higherDirectImage
    {R : Type u} [CommRing R]
    [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    [HasInvertibleExponent Λ (Spec (.of R))]
    (M : Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsLocallyConstantSheaf M] (q : ℕ)
    (hM : IsZero (higherDirectImage Λ (𝔸(ULift.{u} (Fin 1); Spec (.of R)) ↘ Spec (.of R)) q
      ((𝔸(ULift.{u} (Fin 1); Spec (.of R)) ↘ Spec (.of R))^*[ModuleCat.{u + 1} Λ].obj M))) :
    IsZero (AddCommGrpCat.of (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((𝔸(ULift.{u} (Fin 1); Spec (.of R)) ↘ Spec (.of R))^*[ModuleCat.{u + 1} Λ].obj M)) q)) :=
  have := subsingleton_H_affineLine_of_isZero_higherDirectImage Λ M q hM
  AddCommGrpCat.isZero_of_subsingleton _

end Etale

end AlgebraicGeometry
