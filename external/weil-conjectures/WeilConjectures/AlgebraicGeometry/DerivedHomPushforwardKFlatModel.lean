/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
import WeilConjectures.AlgebraicGeometry.DerivedInternalHomPullbackAdjunction
import WeilConjectures.Algebra.Homology.KFlatPullback
import WeilConjectures.Algebra.Homology.KInjectiveHomComplex

/-! # K-flat model for internal Hom into a derived direct image

Source: Stacks Project, Cohomology, Tags 08I3, 08DH, 06YS and 079P.
(blueprint: lem-pc-derived-hom-pushforward-kflat-model). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem model_same_localization
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [(Scheme.Modules.tensorPullback i).Additive]
    (P : CochainComplex Y.Modules ℤ) (J : CochainComplex Z.Modules ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := Y.sheaf) P) (hJ : J.IsKInjective) :
    let F := (Scheme.Modules.pushforward i).mapHomologicalComplex (.up ℤ)
    let T := ((Scheme.Modules.tensorPullback i).mapHomologicalComplex (.up ℤ)).obj P
    Nonempty (((derivedInternalHom (Opens.grothendieckTopology Y) Y.sheaf).obj
      (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj (F.obj J))) ≅
        DerivedCategory.Q.obj (F.obj (homComplex (R := Z.sheaf) T J))) := by
  let AY := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let AZ := SheafOfModules.{u} (moduleRings Z.toRingedSpace)
  let QY := DerivedCategory.Q (C := AY)
  let QZ := DerivedCategory.Q (C := AZ)
  let E := Scheme.Modules.tensorPullback i
  let F := (Scheme.Modules.pushforward i).mapHomologicalComplex (.up ℤ)
  let T := (E.mapHomologicalComplex (.up ℤ)).obj P
  let C : CochainComplex AZ ℤ := homComplex (R := Z.sheaf) T J
  let HY := derivedInternalHom (Opens.grothendieckTopology Y) Y.sheaf
  let HZ := derivedInternalHom (Opens.grothendieckTopology Z) Z.sheaf
  let L := derivedPullback i
  let R := schemeDerivedDirectImage i
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
      E₀, hE₀, hEmap₀, hEadd₀, ε, hderived, htri, hε⟩ :=
    (derivedPullback_spec i)
  have hE : E₀ = E := CategoryTheory.Functor.ext hE₀ (fun _ _ f ↦ hEmap₀ f)
  subst E₀
  have he := hε P hP
  let eP : L.obj (QY.obj P) ≅ QZ.obj T :=
    L.mapIso ((DerivedCategory.quotientCompQhIso AY).app P).symm ≪≫
      asIso (ε.app ((HomotopyCategory.quotient AY (.up ℤ)).obj P)) ≪≫
      DerivedCategory.Qh.mapIso ((E.mapHomotopyCategoryFactors (.up ℤ)).app P) ≪≫
      (DerivedCategory.quotientCompQhIso AZ).app T
  have hT : CochainComplex.IsKFlatTensor (R := Z.sheaf) T := by
    convert CochainComplex.isKFlat_pullback i.base Z.sheaf Y.sheaf ⟨i.c⟩ P hP using 1
    rfl
  have : J.IsKInjective := hJ
  have : C.IsKInjective :=
    CochainComplex.isKInjective_homComplex_of_isKFlat (R := Z.sheaf) T J hT
  obtain ⟨eJ⟩ := RingedSpace.derivedModuleDirectImage_computed_by_resolution
    i.toLRSHom.toShHom (𝟙 J)
  obtain ⟨eC⟩ := RingedSpace.derivedModuleDirectImage_computed_by_resolution
    i.toLRSHom.toShHom (𝟙 C)
  obtain ⟨eH⟩ := derivedInternalHom_obj_iso (Opens.grothendieckTopology Z) Z.sheaf
    (L.obj (QY.obj P)) (QZ.obj J) T J eP.symm (Iso.refl _)
  obtain ⟨a, bY, bZ, t, γ, d, z, eY, eZ, rest⟩ :=
    derivedInternalHom_pullback_adjunction i
  exact ⟨HY.mapIso ((Iso.refl (QY.obj P)).op.prod eJ.symm) ≪≫
    d.app (op (QY.obj P), QZ.obj J) ≪≫ R.mapIso eH ≪≫ eC⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- For a K-flat source and K-injective complex on the source scheme, derived
internal Hom into its termwise direct image is represented by the direct image of
internal Hom from the termwise tensor pullback.

Source: Stacks Project, Cohomology, Remark 08I3, Section 08DH, Tags 06YS and 079P.
(blueprint: lem-pc-derived-hom-pushforward-kflat-model).

Proof: First work in standard derived localizations on both schemes. For a K-injective
complex J, Ri_*Q(J) is represented by Q(i_*J). For K-flat P, Li*Q(P) is represented by
Q(i*P). Apply the internal-Hom pullback/direct-image adjunction of Remark 08I3 to Q(P)
and Q(J). The K-injective representative theorem identifies the internal Hom on Z
with Q(Hom(i*P,J)). This Hom complex is K-injective: on each open subset, tensoring
an acyclic complex with the restriction of the K-flat i*P gives an acyclic complex,
and mapping it into the restriction of J gives an acyclic Hom complex. Thus its
derived direct image is computed by its termwise direct image. Compose these
comparisons. Finally use the equivalence between the standard localization on Y and
the supplied localization; its defining comparison with Q transports internal Hom
and the two actual complexes, giving the asserted isomorphism in the supplied
universe. No auxiliary derived category on Z is part of the statement. The identity
map reduces to the K-injective Hom computation; zero complexes and empty schemes
are respected by every comparison. No closed-immersion hypothesis is needed. -/
theorem nonempty_derivedHom_pushforward_kFlat_model
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [hY : HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [(Scheme.Modules.tensorPullback i).Additive]
    (P : CochainComplex Y.Modules ℤ) (J : CochainComplex Z.Modules ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := Y.sheaf) P) (hJ : J.IsKInjective) :
    let F := (Scheme.Modules.pushforward i).mapHomologicalComplex (.up ℤ)
    let T := ((Scheme.Modules.tensorPullback i).mapHomologicalComplex (.up ℤ)).obj P
    Nonempty (((derivedInternalHom (Opens.grothendieckTopology Y) Y.sheaf).obj
      (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj (F.obj J))) ≅
        DerivedCategory.Q.obj (F.obj (homComplex (R := Z.sheaf) T J))) := by
  let AY := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let AZ := SheafOfModules.{u} (moduleRings Z.toRingedSpace)
  let sY := HasDerivedCategory.standard AY
  let sZ := HasDerivedCategory.standard AZ
  let QY := @DerivedCategory.Q AY _ _ hY
  let QS := @DerivedCategory.Q AY _ _ sY
  let W := HomologicalComplex.quasiIso AY (.up ℤ)
  let e := Localization.uniq QS QY W
  let eQ := Localization.compUniqFunctor QS QY W
  let F := (Scheme.Modules.pushforward i).mapHomologicalComplex (.up ℤ)
  let FJ : CochainComplex AY ℤ := F.obj J
  let T := ((Scheme.Modules.tensorPullback i).mapHomologicalComplex (.up ℤ)).obj P
  let C : CochainComplex AY ℤ := F.obj (homComplex (R := Z.sheaf) T J)
  let : IsGrothendieckAbelian.{u} AY := SheafOfModules.isGrothendieckAbelian _
  let I := CochainComplex.kInjectiveResolutionFunctor.{u} AY
  let η := CochainComplex.toKInjectiveResolution.{u} AY
  have hI (M : CochainComplex AY ℤ) : QuasiIso (η.app M) ∧ (I.obj M).IsKInjective :=
    ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} AY M).2,
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} AY M⟩
  obtain ⟨eY⟩ := @derivedInternalHom_comparison _ _
    (Opens.grothendieckTopology Y) Y.sheaf hY I η hI
  obtain ⟨eS⟩ := @derivedInternalHom_comparison _ _
    (Opens.grothendieckTopology Y) Y.sheaf sY I η hI
  obtain ⟨eM⟩ := @model_same_localization Z Y i sY sZ inferInstance P J hP hJ
  let D : CochainComplex AY ℤ := homComplex (R := Y.sheaf) P (I.obj FJ)
  exact ⟨eY.app (op P, FJ) ≪≫ (eQ.app D).symm ≪≫
    e.functor.mapIso ((eS.app (op P, FJ)).symm ≪≫ eM) ≪≫ eQ.app C⟩

end AlgebraicGeometry
