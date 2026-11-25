/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.CechAcyclic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Scalar sections on an affine open

Source: Stacks Project, Tag 0BED, the short exact coefficient diagram.
(blueprint: lem-sc-picard-scalar-affine-sections-exact).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable {k : Type w} [Field k] {X : Scheme.{w}}

/-- Sections with scalars restricted along the structure map.
Source: Stacks, Tag 0BED (blueprint: lem-sc-picard-scalar-affine-sections-exact). -/
def picardScalarSectionsFunctor (f : X ⟶ Spec (CommRingCat.of k)) (W : X.Opens) :
    X.Modules ⥤ ModuleCat.{w} k :=
  scalarFunctor f ⋙ sheafToPresheaf _ _ ⋙
    (CategoryTheory.evaluation X.Opensᵒᵖ (ModuleCat.{w} k)).obj (op W)

/-- Restriction of scalars and evaluation send zero maps to zero.
Source: sectionwise module maps (blueprint: lem-sc-picard-scalar-affine-sections-exact). -/
instance picardScalarSectionsFunctor_zero (f : X ⟶ Spec (CommRingCat.of k)) (W : X.Opens) :
    (picardScalarSectionsFunctor f W).PreservesZeroMorphisms where
  map_zero := by
    intro M N
    ext x
    rfl

/-- A quasi-coherent short exact sequence gives a short exact scalar section sequence
on an affine open.
Source: Stacks, Tags 01IC, 01IB and 0BED
(blueprint: lem-sc-picard-scalar-affine-sections-exact).

Proof: Evaluation preserves kernels and monomorphisms of module sheaves. Affine
Cech acyclicity of the quasi-coherent kernel makes the map on sections surjective.
Thus evaluation gives a short exact sequence over the ring of sections. Restriction
of scalars is exact and gives the asserted sequence over k. The empty affine open
has zero section modules and satisfies the same argument. -/
theorem picardScalar_affine_sections_exact
    (f : X ⟶ Spec (CommRingCat.of k)) (W : X.Opens) (hW : IsAffineOpen W)
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    (S.map (picardScalarSectionsFunctor f W)).ShortExact := by
  let S' : ShortComplex (SheafOfModules.{w} X.ringCatSheaf) := S
  have hS' : S'.ShortExact := hS
  have := hS'.mono_f
  have := hS'.epi_g
  let E := SheafOfModules.evaluation X.ringCatSheaf (op W)
  have he : (S'.map E).Exact :=
    hS'.exact.map_of_mono_of_preservesKernel E inferInstance inferInstance
  have hg : Function.Surjective (S'.g.val.app (op W)) :=
    surjective_app_of_cechAcyclicOnAffines
      (hS'.map_of_exact (SheafOfModules.toSheaf X.ringCatSheaf))
      (cechAcyclicOnAffines_of_isQuasicoherent S.X₁) hW
  have : Epi ((S'.map E).g) := (ModuleCat.epi_iff_surjective _).mpr hg
  have : Mono ((S'.map E).f) := Functor.map_mono E S'.f
  have hs : (S'.map E).ShortExact := .mk' he inferInstance inferInstance
  exact hs.map_of_exact (ModuleCat.restrictScalars (scalarMap f W))

end
end AlgebraicGeometry.Scheme.Modules
