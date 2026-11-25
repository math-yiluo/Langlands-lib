/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffineTensorPullbackStalkCoordinates
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Algebra.Homology.AffineLocalizedTensorStalkSquare

/-! # AffineBaseChangeOrdinaryStalkComparison

Source: Stacks Project, Tag 0DJ8.
(blueprint: lem-pc-affine-base-change-ordinary-stalk-comparison). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wM
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- Localize the tensor comparison before passing through the derived pullback counit.
Source: Stacks Project, Tag 0DJ8, affine displayed localization identity;
Tags 06Y6, 01HV and 01I9.
(blueprint: lem-pc-affine-base-change-ordinary-stalk-comparison).

Proof: the cartesian spectrum square identifies A tensor_R R' with A'. Contract
p to the other three rings. Their structure-sheaf stalk maps are localizations at
the contracted primes. Localize a K-flat resolution of M over R; exactness of
localization and tensor associativity identify its tensor cohomology localized
at p with the cohomology model on the localized complex, extended to the fourth
stalk ring. The universal counit and coefficient-action equations transport this
identification to the supplied model m and the fixed stalk model. K-flatness of
M over A identifies ordinary A'-tensor cohomology with the A-derived target.
The localization theorem's comparison square and m.localized_eq identify the
localized comparison with the local model's localizedComparison. Termwise tilde
stalk localization, tensorStalkIso and exact stalk homology then identify its
ordinary target with the stalk of the ordinary tensor pullback complex. The
canonical target identification is affineTensorPullbackHomologyStalkIso, since
its tilde, tensor-pullback and homology factors send the same germs to the same
tensor generators. Thus the displayed square commutes. All steps are exact in
all degrees; identity localizations and zero complexes require no change. There
is no prime to consider when A' is the zero ring. -/
theorem exists_affineBaseChangeOrdinaryStalkComparison
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
    ∀ p : PrimeSpectrum A',
      let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
      let f' := Spec.map (CommRingCat.ofHom φf')
      let g := Spec.map (CommRingCat.ofHom (algebraMap R R'))
      let g' := Spec.map (CommRingCat.ofHom φg')
      letI := SingleComplexBaseChange.leftAlgebra f g' p
      letI := SingleComplexBaseChange.rightAlgebra f f' g g' sq p
      letI := (SingleComplexBaseChange.tensorMap f f' g g' sq p).toAlgebra
      letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.R f g' p))
      letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.B f' p))
      let q := (SingleComplexBaseChange.cohomologyModel
        f f' g g' sq p P).localizedComparison i ≫
          HomologicalComplex.homologyMap
            (SingleComplexBaseChange.tensorStalkIso f f' g g' sq p P).hom i ≫
          (affineRepresentativeStalkIso (Spec (.of A')) p T i).inv
      ∃ lU : LocalizedModule p.asIdeal.primeCompl U ≃+ (Arrow.mk q).left,
        ∀ x, affineTensorPullbackHomologyStalkIso A A' φg' M p i
          (LocalizedModule.map p.asIdeal.primeCompl a₀.hom x) = q (lU x) := by
  -- Keep the complexes and comparison maps shared when unpacking the coordinate squares.
  intro P T C U a₀ p f f' g g' q
  obtain ⟨τ, hτ, hcoord⟩ := exists_affineOrdinaryTensorStalkCoordinates
    R A R' A' φg' φf' hφg' hφf' sq M i p
  obtain ⟨lU, hsquare⟩ := exists_affineLocalizedTensorStalkSquare
    R A R' A' φg' φf' hφg' hφf' sq M hM i m p τ hτ
  refine ⟨lU, ?_⟩
  intro x
  exact (hcoord _).trans (congrArg _ (congrArg _ (hsquare x)))

end AlgebraicGeometry
