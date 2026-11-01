import Langlands.AlgebraicGeometry.Modules.CechResolution.Comparison

/-!
# Čech cohomology computes relative cohomology in every degree

A natural-indexed complex `K` whose integer extension is isomorphic, in the derived
category, to the right derived complex of `F` at `A` computes the right derived functors:
`(F.rightDerived n).obj A ≅ K.homology n` for every `n : ℕ`. Applied to the derived Čech
comparison, this identifies relative cohomology of a quasi-coherent module on a scheme
separated over `Spec R` with the cohomology of its alternating Čech cochain complex for any
finite ordered affine cover.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.CechResolution

open Langlands.Cohomology

section Abstract

universe w w' v v' u₁ u₂

variable {C : Type u₁} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [EnoughInjectives C]
  {D : Type u₂} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive]

/-- A natural-indexed complex representing the right derived complex of `F` at `A`
computes every right derived functor of `F` at `A`. -/
def rightDerivedObjIsoHomologyOfDerivedIso {A : C} (K : CochainComplex D ℕ)
    (e : DerivedCategory.Q.obj (K.extend ComplexShape.embeddingUpNat) ≅
      DerivedCategory.Plus.ι.obj ((DerivedPlus.derivedComplex F).obj A)) (n : ℕ) :
    (F.rightDerived n).obj A ≅ K.homology n :=
  (DerivedPlus.homologyIso F (injectiveResolution A) n).symm ≪≫
    (DerivedCategory.homologyFunctor D (n : ℤ)).mapIso e.symm ≪≫
    (DerivedCategory.homologyFunctorFactors D (n : ℤ)).app
      (K.extend ComplexShape.embeddingUpNat) ≪≫
    K.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl

end Abstract

section Relative

attribute [local instance] HasDerivedCategory.standard

universe u

/-- For a quasi-coherent module on a scheme separated over `Spec R` and any finite ordered
affine cover, relative cohomology in degree `n` is the `n`-th cohomology of the alternating
Čech cochain complex. -/
theorem nonempty_relativeCohomology_iso_cechCochainComplex_homology {R : CommRingCat.{u}}
    {X : Scheme.{u}} (π : X ⟶ Spec R) [IsSeparated π] (𝒰 : X.OrderedAffineCover)
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    Nonempty ((DerivedSections.relativeCohomology π n).obj M ≅
      (cechCochainComplex π 𝒰 M).homology n) :=
  (nonempty_cechCochainComplex_iso R X π 𝒰 M).map fun e =>
    rightDerivedObjIsoHomologyOfDerivedIso _ _ e n

end Relative

end Langlands.AlgebraicGeometry.Modules.CechResolution
