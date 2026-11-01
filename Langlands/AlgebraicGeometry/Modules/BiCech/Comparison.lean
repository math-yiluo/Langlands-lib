import Langlands.AlgebraicGeometry.Modules.BiCech.Complex
import Langlands.AlgebraicGeometry.Modules.CechResolution.CechCohomologyIso

/-!
# The bi-Čech complex computes relative cohomology

Let `π : P ⟶ Spec R` be separated, `𝒲` a `BiCover P` all of whose opens
`biOpen s t = f⁻¹(𝒰.inter s) ∩ g⁻¹(𝒱.inter t)` are affine, and `F` a quasi-coherent
`𝒪_P`-module. Every term of the bi-Čech complex is a finite biproduct of modules
`sheafOn F W` with `W` affine, hence has vanishing higher `R`-module cohomology
(`CechResolution.isZero_relativeCohomology_sheafOn`). Since the augmentation
`F[0] ⟶ bicechComplex 𝒲 F` is a quasi-isomorphism, the derived comparison of
`CechResolution.isIso_derivedResolutionComparison` is an isomorphism, and therefore
`Hⁿ(P, F)` is the `n`-th cohomology of the complex of `R`-module global sections of the
bi-Čech complex.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Modules.BiCech

open CechResolution Langlands.Cohomology Langlands.Cohomology.AcyclicResolution

variable {R : CommRingCat.{u}} {P : Scheme.{u}} (π : P ⟶ Spec R) [IsSeparated π]
  (𝒲 : BiCover P) (F : P.Modules) [F.IsQuasicoherent]

/-- The terms of the bi-Čech complex have vanishing higher `R`-module cohomology when all
the opens `biOpen s t` are affine. -/
theorem isZero_relativeCohomology_term
    (hW : ∀ {p q : ℕ} (s : 𝒲.𝒰.Idx p) (t : 𝒲.𝒱.Idx q), IsAffineOpen (biOpen 𝒲 s t))
    (i n : ℕ) : IsZero ((DerivedSections.relativeCohomology π (n + 1)).obj (term 𝒲 F i)) :=
  haveI : (DerivedSections.relativeCohomology π (n + 1)).Additive :=
    rightDerived_additive (DerivedSections.relativeGlobalSections π) (n + 1)
  isZero_obj_biproduct _ _ fun x => isZero_relativeCohomology_sheafOn π F (hW x.2.1 x.2.2) n

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- `Hⁿ(P, F)` is the `n`-th cohomology of the `R`-module global sections of the bi-Čech
complex. -/
theorem nonempty_relativeCohomology_iso_bicech_homology
    (hW : ∀ {p q : ℕ} (s : 𝒲.𝒰.Idx p) (t : 𝒲.𝒱.Idx q), IsAffineOpen (biOpen 𝒲 s t))
    (n : ℕ) :
    Nonempty ((DerivedSections.relativeCohomology π n).obj F ≅
      (((DerivedSections.relativeGlobalSections π).mapHomologicalComplex _).obj
        (bicechComplex 𝒲 F)).homology n) := by
  let G := DerivedSections.relativeGlobalSections π
  have hK : ∀ i n : ℕ, IsZero ((G.rightDerived (n + 1)).obj ((bicechComplex 𝒲 F).X i)) :=
    fun i n => isZero_relativeCohomology_term π 𝒲 F hW i n
  have := quasiIso_bicechAug 𝒲 F
  have hiso := isIso_derivedResolutionComparison G (bicechAug 𝒲 F) hK
  exact ⟨rightDerivedObjIsoHomologyOfDerivedIso G _
    (DerivedCategory.Q.mapIso (extendMapIso _ G _).symm ≪≫ @asIso _ _ _ _ _ hiso) n⟩

end Derived

end Langlands.AlgebraicGeometry.Modules.BiCech
