/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeCoordinates

import WeilConjectures.Algebra.Homology.AffineDirectLocalizedTensorSquareCore

/-! # AffineDirectLocalizedTensorSquare

Source: Stacks Project, Tag 0DJ8.
(blueprint: lem-pc-affine-direct-localized-tensor-square). -/

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

/-- Localize the input and the two base rings, with the final coefficient ring
already the fourth stalk. Source: Stacks Project, Tag 0DJ8, displayed affine
localization identity, and Tags 06Y6 and 01I9.
(blueprint: lem-pc-affine-direct-localized-tensor-square).

Proof: the cartesian spectrum square identifies A' with A tensor_R R'. The
canonical maps from A, R, R' to their stalks are localizations at the contracted
primes; their composites to D agree by naturality of scheme stalk maps. The
termwise tilde/stalk localization identifies localization of M with stalkComplex P,
sending 1 tensor x to its germ. First localize the A-factor by
derivedTensor_first_localization_models. Then localize the base and second factor
by derivedTensor_base_second_localization_models. Use the same intermediate model
and compose the resulting D-linear source isomorphisms. The fixed stalk model is
transported from the localized module complex by the termwise tilde/stalk iso.
The universal counit identifies its derived functor with the transported one;
this also accommodates the standard local derived-category universes, since both
localizations are computed from the same K-flat resolutions. The counit equations
and cohomologyIso_smul retain the tensor-algebra scalar action. The two comparison
squares compose, with tensor associativity identifying their ordinary targets.
Their coefficient chain map sends 1 tensor x to 1 tensor its germ. D-linearity
and ExtendScalars.hom_ext make any tau with the displayed formula equal to this
map. Apply homology and compose the comparison squares to get the equation.
There is no extension of ordinary cohomology from A' to D in this assertion:
all its cohomology targets are already computed over D. No K-flatness of M over
R is needed, and the construction works for zero complexes and identity
localizations. A zero A' has no prime p. -/
theorem exists_affineDirectLocalizedTensorSquare
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
    (i : ℤ) :
    let P := ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
      (@id (ModuleCat.{u} A ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)
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
      let D : Type u := (Spec.structureSheaf A').presheaf.stalk p
      let κ := (StructureSheaf.toStalk A' p).hom
      letI : Algebra (A ⊗[R] R') D :=
        (κ.comp (algebraMap (A ⊗[R] R') A')).toAlgebra
      (n : ModuleCat.BaseDerivedTensorCohomologyModel R A R' M D) →
      let C := ((ModuleCat.extendScalars (κ.comp φg')).mapHomologicalComplex (.up ℤ)).obj M
      let U := affineBaseChangeTildeModule R A R' D M n i
      let hφ : (algebraMap (A ⊗[R] R') D).comp
          (algebraMap A (A ⊗[R] R')) = κ.comp φg' :=
        by
          change (κ.comp (algebraMap (A ⊗[R] R') A')).comp _ = _
          rw [RingHom.comp_assoc, hφg']
      let a := affineBaseChangeTildeModuleMap R A R' D M n (κ.comp φg') hφ i
        (C.homology i) (Iso.refl _)
      let ρ := (SingleComplexBaseChange.tensorMap f f' g g' sq p).comp
        (algebraMap (SingleComplexBaseChange.A g' p)
          (SingleComplexBaseChange.A g' p ⊗[SingleComplexBaseChange.R f g' p]
            SingleComplexBaseChange.B f' p))
      let l :=
        (SingleComplexBaseChange.cohomologyModel f f' g g' sq p P).localizedComparison i
      ∃ e : U ≅ (Arrow.mk l).left,
        ∀ τ : C ≅
            SingleComplexBaseChange.tensorComplex f f' g g' sq p P,
          (∀ (j : ℤ) (x : M.X j),
            τ.hom.f j ((1 : D) ⊗ₜ[A, κ.comp φg'] x) =
              (1 : (Spec (.of A')).presheaf.stalk p) ⊗ₜ[SingleComplexBaseChange.A g' p, ρ]
                (TopCat.Presheaf.germ (P.X j).val.presheaf ⊤ (g' p) trivial
                  (tilde.toOpen (R := .of A) (M.X j) ⊤ x))) →
          a ≫ HomologicalComplex.homologyMap τ.hom i = e.hom ≫ l := by
  dsimp only
  intro p
  apply affineDirectLocalizedTensorSquare_core R A R' A' φg' φf' hφg' hφf' sq M i



end AlgebraicGeometry
