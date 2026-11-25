/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffineOrdinaryTensorStalkCoordinates
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Algebra.Homology.AffineStalkScalarExtensionCoordinates
import WeilConjectures.Algebra.Homology.AffineScalarLocalizedTensorSquare

/-! # AffineLocalizedTensorStalkSquare

Source: Stacks Project, Tag 0DJ8.
(blueprint: lem-pc-affine-localized-tensor-stalk-square). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wM
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
noncomputable section
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

set_option linter.unusedVariables false in
/-- The algebraic localization square before ordinary pullback target coordinates.
Source: Stacks Project, Tag 0DJ8, displayed affine localization identity;
Tags 06Y6, 01HV and 01I9.
(blueprint: lem-pc-affine-localized-tensor-stalk-square).

Proof: exists_affineStalkScalarExtensionCoordinates supplies a chain isomorphism
chi from scalar extension of C to the stalk of tilde C, its germ formula, and
additive source coordinates e(U), natural for the map a0 into ordinary homology.
Compose chi with the supplied tau. Its nested pure-tensor formula follows from
the two germ formulas. Apply exists_affineScalarLocalizedTensorSquare to this
algebraic chain isomorphism, obtaining the source isomorphism eU and the
algebraic cohomology square. Define lU as e(U) followed by the additive equivalence
of eU. Substitute the exact stalk homology naturality formula, and use
homologyMap_comp to identify homology(chi followed by tau). Evaluation of the
algebraic square at e(U)(x) gives the required equation. The scalar-extension
coordinate argument is proved; the algebraic model-localization square is a
separate named statement. The argument works for zero complexes and identity
localizations; a zero fourth ring supplies no prime. -/
theorem exists_affineLocalizedTensorStalkSquare
    (R A R' A' : Type u) [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] [Algebra (A ⊗[R] R') A']
    [HasDerivedCategory.{wM} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wM} (ModuleCat.{u} R')]
    (φg' : A →+* A') (φf' : R' →+* A')
    (hφg' : (algebraMap (A ⊗[R] R') A').comp
      (algebraMap A (A ⊗[R] R')) = φg')
    (hφf' : (algebraMap (A ⊗[R] R') A').comp
      Algebra.TensorProduct.includeRight.toRingHom = φf')
    (sq : IsPullback (Spec.map (CommRingCat.ofHom φg')) (Spec.map (CommRingCat.ofHom φf'))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat M)
    (i : ℤ) (m : ModuleCat.BaseDerivedTensorCohomologyModel R A R' M A') :
    let P := ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
      (@id (ModuleCat.{u} A ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)
    let T := ((Scheme.Modules.tensorPullback
      (Spec.map (CommRingCat.ofHom φg'))).mapHomologicalComplex (.up ℤ)).obj P
    let C := ((ModuleCat.extendScalars φg').mapHomologicalComplex (.up ℤ)).obj M
    let U := affineBaseChangeTildeModule R A R' A' M m i
    let a₀ := affineBaseChangeTildeModuleMap R A R' A' M m φg' hφg' i
      (C.homology i) (Iso.refl _)
    (p : PrimeSpectrum A') →
      let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
      let f' := Spec.map (CommRingCat.ofHom φf')
      let g := Spec.map (CommRingCat.ofHom (algebraMap R R'))
      let g' := Spec.map (CommRingCat.ofHom φg')
      letI := SingleComplexBaseChange.leftAlgebra f g' p
      letI := SingleComplexBaseChange.rightAlgebra f f' g g' sq p
      letI := (SingleComplexBaseChange.tensorMap f f' g g' sq p).toAlgebra
      letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.R f g' p))
      letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.B f' p))
      let N := ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
        (@id (ModuleCat.{u} A' ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace))
            (tilde.functor (.of A'))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj C)
      let s := RingedSpace.moduleStalkFunctor (Spec (.of A')).toRingedSpace p
      let ρ := (SingleComplexBaseChange.tensorMap f f' g g' sq p).comp
        (algebraMap (SingleComplexBaseChange.A g' p)
          (SingleComplexBaseChange.A g' p ⊗[SingleComplexBaseChange.R f g' p]
            SingleComplexBaseChange.B f' p))
      let l :=
        (SingleComplexBaseChange.cohomologyModel f f' g g' sq p P).localizedComparison i
      ∀ τ : (s.mapHomologicalComplex (.up ℤ)).obj N ≅
          SingleComplexBaseChange.tensorComplex f f' g g' sq p P,
        (∀ (j : ℤ) (x : M.X j),
          τ.hom.f j (TopCat.Presheaf.germ (N.X j).val.presheaf ⊤ p trivial
            (tilde.toOpen (R := .of A') (C.X j) ⊤ ((1 : A') ⊗ₜ[A, φg'] x))) =
            (1 : (Spec (.of A')).presheaf.stalk p) ⊗ₜ[SingleComplexBaseChange.A g' p, ρ]
              (TopCat.Presheaf.germ (P.X j).val.presheaf ⊤ (g' p) trivial
                (tilde.toOpen (R := .of A) (M.X j) ⊤ x))) →
        ∃ lU : LocalizedModule p.asIdeal.primeCompl U ≃+
            (Arrow.mk l).left,
          ∀ x, HomologicalComplex.homologyMap τ.hom i
              (affineTildeHomologyLocalization A' C p i
                (LocalizedModule.map p.asIdeal.primeCompl a₀.hom x)) =
            l (lU x)  := by
  dsimp only
  intro p τ hτ
  let C := ((ModuleCat.extendScalars φg').mapHomologicalComplex (.up ℤ)).obj M
  let U := affineBaseChangeTildeModule R A R' A' M m i
  let a₀ := affineBaseChangeTildeModuleMap R A R' A' M m φg' hφg' i
    (C.homology i) (Iso.refl _)
  let κ := (StructureSheaf.toStalk A' p).hom
  let F := ModuleCat.extendScalars κ
  have : PreservesFiniteLimits F :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.mpr
        (IsLocalization.flat ((Spec.structureSheaf A').presheaf.stalk p)
          p.asIdeal.primeCompl))
  obtain ⟨χ, hχ, e, hcoord⟩ :=
    exists_affineStalkScalarExtensionCoordinates A' C p i
  obtain ⟨eU, hsquare⟩ := exists_affineScalarLocalizedTensorSquare
    R A R' A' φg' φf' hφg' hφf' sq M hM i m p
  let τD := χ ≪≫ τ
  have hs := hsquare τD (by
    intro j x
    change τ.hom.f j (χ.hom.f j _) = _
    rw [hχ]
    exact hτ j x)
  refine ⟨(e U).trans eU.toLinearEquiv.toAddEquiv, ?_⟩
  intro x
  rw [hcoord U a₀ x]
  have h := congrArg (fun a ↦ a (e U x)) hs
  simp only [τD, Iso.trans_hom, HomologicalComplex.homologyMap_comp,
    ModuleCat.comp_apply] at h
  exact h

end AlgebraicGeometry
