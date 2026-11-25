/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeCoordinates
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat

import WeilConjectures.Algebra.Homology.FlatFinalCoefficientModelComparison
import WeilConjectures.Algebra.Homology.AffineDirectLocalizedTensorSquare

/-! # AffineScalarLocalizedTensorSquare

Source: Stacks Project, Tag 0DJ8.
(blueprint: lem-pc-affine-scalar-localized-tensor-square). -/

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

/-- Algebraic comparison after extension to the fourth stalk ring, before exact
stalk homology coordinates. Source: Stacks Project, Tag 0DJ8, affine displayed
localization identity; Tags 06Y6, 01HV and 01I9.
(blueprint: lem-pc-affine-scalar-localized-tensor-square).

Proof: first change only the final coefficient ring from A' to its flat stalk D.
exists_flatFinalCoefficientModelComparison constructs the source isomorphism
from universal derived-model uniqueness, tensor associativity, and the flat
iterated scalar-extension homology square. Next apply
exists_affineDirectLocalizedTensorSquare to the resulting model over D, which
localizes the input, base and second factor. The inverse scalar-associativity
chain isomorphism flattens 1 tensor (1 tensor x) to 1 tensor x. Factor each
supplied tau through it, use the generator formula to apply the direct square,
and compose the two equations by functoriality of homology. All source
isomorphisms are composed explicitly. This reduction does not require hM;
the original hypothesis and statement are retained unchanged. Zero complexes
and identity localizations use the same maps; the zero fourth ring has no primes. -/
theorem exists_affineScalarLocalizedTensorSquare
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
      let D : Type u := (Spec.structureSheaf A').presheaf.stalk p
      let κ := (StructureSheaf.toStalk A' p).hom
      let F := ModuleCat.extendScalars κ
      letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
        (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat D p.asIdeal.primeCompl))
      let ρ := (SingleComplexBaseChange.tensorMap f f' g g' sq p).comp
        (algebraMap (SingleComplexBaseChange.A g' p)
          (SingleComplexBaseChange.A g' p ⊗[SingleComplexBaseChange.R f g' p]
            SingleComplexBaseChange.B f' p))
      let l :=
        (SingleComplexBaseChange.cohomologyModel f f' g g' sq p P).localizedComparison i
      ∃ e : F.obj U ≅ (Arrow.mk l).left,
        ∀ τ : (F.mapHomologicalComplex (.up ℤ)).obj C ≅
            SingleComplexBaseChange.tensorComplex f f' g g' sq p P,
          (∀ (j : ℤ) (x : M.X j),
            τ.hom.f j ((1 : D) ⊗ₜ[A', κ] ((1 : A') ⊗ₜ[A, φg'] x)) =
              (1 : (Spec (.of A')).presheaf.stalk p) ⊗ₜ[SingleComplexBaseChange.A g' p, ρ]
                (TopCat.Presheaf.germ (P.X j).val.presheaf ⊤ (g' p) trivial
                  (tilde.toOpen (R := .of A) (M.X j) ⊤ x))) →
          F.map a₀ ≫ ((C.sc i).mapHomologyIso F).inv ≫
              HomologicalComplex.homologyMap τ.hom i = e.hom ≫ l := by
  have _ := hM
  dsimp only
  intro p
  let D : Type u := (Spec.structureSheaf A').presheaf.stalk p
  let κ := (StructureSheaf.toStalk A' p).hom
  let : Module ((structurePresheafInCommRingCat A').stalk p) D :=
    inferInstanceAs (Module D D)
  let F := ModuleCat.extendScalars κ
  have hk : κ.Flat := RingHom.flat_algebraMap_iff.mpr
    (IsLocalization.flat D p.asIdeal.primeCompl)
  have : PreservesFiniteLimits F :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hk
  let : Algebra (A ⊗[R] R') D :=
    (κ.comp (algebraMap (A ⊗[R] R') A')).toAlgebra
  let n := ModuleCat.baseDerivedTensorCohomologyModel R A R' M D
  let C := ((ModuleCat.extendScalars φg').mapHomologicalComplex (.up ℤ)).obj M
  let CD := ((ModuleCat.extendScalars (κ.comp φg')).mapHomologicalComplex (.up ℤ)).obj M
  let α : (F.mapHomologicalComplex (.up ℤ)).obj C ≅ CD :=
    (Functor.mapHomologicalComplexCompIso
      (ModuleCat.extendScalarsComp φg' κ).symm (.up ℤ)).app M
  have hα (j : ℤ) (x : M.X j) :
      α.hom.f j ((1 : D) ⊗ₜ[A', κ] ((1 : A') ⊗ₜ[A, φg'] x)) =
        (1 : D) ⊗ₜ[A, κ.comp φg'] x := by
    let e := (ModuleCat.extendScalarsComp φg' κ).app (M.X j)
    have hx := ModuleCat.extendScalarsComp_hom_app_one_tmul φg' κ (M.X j) x
    have hi := ConcreteCategory.congr_hom e.hom_inv_id
      ((1 : D) ⊗ₜ[A, κ.comp φg'] x)
    exact (congrArg (fun z ↦ e.inv z) hx).symm.trans hi
  obtain ⟨e₁, hc⟩ := ModuleCat.exists_flatFinalCoefficientModelComparison
    R A R' A' D κ hk rfl φg' hφg' M m n i
  have hcα := hc α hα
  obtain ⟨e₂, hl⟩ := exists_affineDirectLocalizedTensorSquare
    R A R' A' φg' φf' hφg' hφf' sq M i p n
  refine ⟨e₁ ≪≫ e₂, ?_⟩
  intro τ hτ
  let β := α.symm ≪≫ τ
  have hβ (j : ℤ) (x : M.X j) :
      β.hom.f j ((1 : D) ⊗ₜ[A, κ.comp φg'] x) =
        τ.hom.f j ((1 : D) ⊗ₜ[A', κ] ((1 : A') ⊗ₜ[A, φg'] x)) := by
    change τ.hom.f j (α.inv.f j _) = _
    rw [← hα j x]
    congr 1
    let e := (HomologicalComplex.eval (ModuleCat.{u} D) (.up ℤ) j).mapIso α
    exact e.toLinearEquiv.symm_apply_apply _
  have hlβ := hl β (fun j x ↦ (hβ j x).trans (hτ j x))
  have ht : α.hom ≫ β.hom = τ.hom := by simp [β]
  rw [← ht, HomologicalComplex.homologyMap_comp]
  simpa only [Category.assoc, Iso.trans_hom] using
    (congrArg (fun k ↦ k ≫ HomologicalComplex.homologyMap β.hom i) hcα).trans
      (by simpa only [Category.assoc] using congrArg (fun k ↦ e₁.hom ≫ k) hlβ)

end AlgebraicGeometry
