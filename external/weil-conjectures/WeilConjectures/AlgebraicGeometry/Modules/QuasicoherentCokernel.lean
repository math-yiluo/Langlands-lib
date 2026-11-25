/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-!
# Cokernels of quasi-coherent modules

Let `X` be a scheme. The cokernel of a morphism of quasi-coherent `𝒪_X`-modules is
quasi-coherent, and on a locally Noetherian scheme the cokernel of a morphism from a
quasi-coherent module to a module of finite presentation is of finite presentation.

The proofs reduce to affine opens, through the open immersions `Spec Γ(X, U) ⟶ X`: restriction
along an open immersion is a left adjoint, so it commutes with cokernels, and on `Spec R` a
quasi-coherent module is `M^~` for an `R`-module `M`, while `M ↦ M^~` is a left adjoint, so it
commutes with cokernels too.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_cokernel`: the cokernel of a morphism of
  quasi-coherent modules is quasi-coherent.
- `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_cokernel`: on a locally Noetherian
  scheme, the cokernel of a morphism from a quasi-coherent module to a module of finite
  presentation is of finite presentation.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- On `Spec R`, the cokernel of a morphism `φ : M ⟶ N` with `M ≅ Γ(M)^~` and `N ≅ Γ(N)^~` is
`Q^~` for the cokernel `Q` of `Γ(φ)`, since `M ↦ M^~` commutes with cokernels. -/
noncomputable def tildeCokernelIso {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [IsIso M.fromTildeΓ] [IsIso N.fromTildeΓ] (φ : M ⟶ N) :
    (tilde.functor R).obj (cokernel (moduleSpecΓFunctor.map φ)) ≅ cokernel φ :=
  PreservesCokernel.iso (tilde.functor R) _ ≪≫
    cokernel.mapIso _ _ (asIso M.fromTildeΓ) (asIso N.fromTildeΓ)
      (fromTildeΓNatTrans.naturality φ)

/-- On `Spec R`, the cokernel of a morphism of modules of the form `M^~` is of this form. -/
theorem isIso_fromTildeΓ_cokernel {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [IsIso M.fromTildeΓ] [IsIso N.fromTildeΓ] (φ : M ⟶ N) : IsIso (cokernel φ).fromTildeΓ :=
  isIso_fromTildeΓ_iff.mpr ⟨_, ⟨tildeCokernelIso φ⟩⟩

variable {X : Scheme.{u}}

/-- **The cokernel of a morphism of quasi-coherent modules is quasi-coherent.** On an affine
open `U`, restriction along `Spec Γ(X, U) ⟶ X` commutes with cokernels, and on `Spec Γ(X, U)`
the cokernel of a morphism between modules of the form `M^~` is of this form. -/
theorem isQuasicoherent_cokernel {M N : X.Modules}
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) N] (φ : M ⟶ N) :
    SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) (cokernel φ) := by
  refine isQuasicoherent_of_iSup_opensRange_eq_top (cokernel φ)
    (fun U : {U : X.Opens // IsAffineOpen U} ↦ U.2.fromSpec) iSup_opensRange_fromSpec_eq_top
    fun U ↦ ?_
  have : IsIso (M.restrict U.2.fromSpec).fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent _
  have : IsIso (N.restrict U.2.fromSpec).fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent _
  have : IsIso (cokernel ((restrictFunctor U.2.fromSpec).map φ)).fromTildeΓ :=
    isIso_fromTildeΓ_cokernel _
  let e := PreservesCokernel.iso (restrictFunctor U.2.fromSpec) φ
  haveI : IsIso (C := SheafOfModules.{u} (Spec Γ(X, U.1)).ringCatSheaf) e.inv :=
    (inferInstance : IsIso e.inv)
  exact (presentationOfIsIsoFromTildeΓ _).ofIsIso e.inv

/-- **Cokernels into modules of finite presentation on a locally Noetherian scheme.** Let `X` be
locally Noetherian and `φ : M ⟶ N` a morphism from a quasi-coherent module to a module of
finite presentation. Then `cokernel φ` is of finite presentation: it is quasi-coherent, and over
an affine open `U` its sections are a quotient of the finite module `Γ(N, U)` over the
Noetherian ring `Γ(X, U)`. -/
theorem isFinitePresentation_cokernel [IsLocallyNoetherian X] {M N : X.Modules}
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) N]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) N] (φ : M ⟶ N) :
    SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) (cokernel φ) := by
  have := isQuasicoherent_cokernel φ
  have hfin (U : {U : X.Opens // IsAffineOpen U}) :
      Module.Finite Γ(X, U.1) Γ((cokernel φ).restrict U.2.fromSpec, ⊤) := by
    have : IsIso (M.restrict U.2.fromSpec).fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent _
    have : IsIso (N.restrict U.2.fromSpec).fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent _
    have := finite_sections_of_isFinitePresentation (N.restrict U.2.fromSpec)
      (isAffineOpen_top (Spec Γ(X, U.1)))
    have hN := finite_sections_top_of_finite (N.restrict U.2.fromSpec)
    let φ' := (restrictFunctor U.2.fromSpec).map φ
    let Q := cokernel (moduleSpecΓFunctor.map φ')
    have : Module.Finite Γ(X, U.1) Q := by
      have : Module.Finite Γ(X, U.1) (moduleSpecΓFunctor.obj (N.restrict U.2.fromSpec)) := hN
      exact Module.Finite.of_surjective (cokernel.π (moduleSpecΓFunctor.map φ')).hom
        ((ModuleCat.epi_iff_surjective _).mp inferInstance)
    let e : Q ≅ moduleSpecΓFunctor.obj ((cokernel φ).restrict U.2.fromSpec) :=
      tilde.isoTop Q ≪≫ moduleSpecΓFunctor.mapIso
        (tildeCokernelIso φ' ≪≫ (PreservesCokernel.iso (restrictFunctor U.2.fromSpec) φ).symm)
    exact Module.Finite.equiv e.toLinearEquiv
  choose P hP using fun U : {U : X.Opens // IsAffineOpen U} ↦
    have := IsLocallyNoetherian.component_noetherian ⟨U.1, U.2⟩
    exists_presentation_isFinite (R := Γ(X, U.1)) ((cokernel φ).restrict U.2.fromSpec)
  exact isFinitePresentation_of_iSup_opensRange_eq_top (cokernel φ) _
    iSup_opensRange_fromSpec_eq_top P

end AlgebraicGeometry.Scheme.Modules
