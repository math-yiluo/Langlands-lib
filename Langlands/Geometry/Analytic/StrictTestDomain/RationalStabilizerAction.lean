import Langlands.Geometry.Analytic.StrictTestDomain.RationalAutomorphism
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import Mathlib.GroupTheory.GroupAction.Defs

/-! # Rational-locus stabilizers acting on a fixed section algebra -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism

open CategoryTheory
open scoped Pointwise

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {P : PresentedStrictAffinoidAlgebra K}

/-- The subgroup preserving the actual rational locus, without requiring its
chosen presentation or its individual points to be fixed. -/
def locusStabilizer (d : RationalData K P) : Subgroup (Aut P) :=
  MulAction.stabilizer (Aut P) d.locus

@[simp] theorem mem_locusStabilizer (d : RationalData K P) (g : Aut P) :
    g ∈ locusStabilizer d ↔
      (fun x : BanachSpectrum P => g • x) '' d.locus = d.locus := Iff.rfl

/-- Stabilizer membership identifies the moved locus with the original one. -/
theorem locus_smul_eq (d : RationalData K P) (g : locusStabilizer d) :
    ((g : Aut P) • d).locus = d.locus :=
  (locus_smul (g : Aut P) d).trans g.property

variable [CompleteSpace K]

/-- An actual inclusion returns a moved presentation to the fixed locus. -/
def stabilizerInclusion (d : RationalData K P) (g : locusStabilizer d) :
    d ⟶ (g : Aut P) • d :=
  ⟨fun _ hx => (locus_smul_eq d g).symm ▸ hx⟩

/-- Transport to the moved quotient and restrict back to the original quotient. -/
def stabilizerSectionMap (d : RationalData K P) (g : locusStabilizer d) :
    BoundedAlgHom K d.algebra d.algebra :=
  (stabilizerInclusion d g).restriction.comp (d.comparison (g : Aut P).hom)

@[simp] theorem stabilizerSectionMap_comp_baseMap
    (d : RationalData K P) (g : locusStabilizer d) :
    (stabilizerSectionMap d g).comp d.baseMap = d.baseMap.comp (g : Aut P).hom := by
  rw [stabilizerSectionMap, BoundedAlgHom.comp_assoc, d.comparison_comp_baseMap,
    ← BoundedAlgHom.comp_assoc]
  change ((stabilizerInclusion d g).restriction.comp
    ((g : Aut P) • d).baseMap).comp (g : Aut P).hom = _
  rw [RationalData.Inclusion.restriction_comp_baseMap]

@[simp] theorem stabilizerSectionMap_one (d : RationalData K P) :
    stabilizerSectionMap d 1 = BoundedAlgHom.id K d.algebra := by
  apply d.hom_ext
  rw [stabilizerSectionMap_comp_baseMap]
  rfl

/-- Multiplication acts by composition, with the right factor applied first. -/
theorem stabilizerSectionMap_mul (d : RationalData K P) (g h : locusStabilizer d) :
    stabilizerSectionMap d (g * h) =
      (stabilizerSectionMap d g).comp (stabilizerSectionMap d h) := by
  apply d.hom_ext
  rw [stabilizerSectionMap_comp_baseMap, BoundedAlgHom.comp_assoc,
    stabilizerSectionMap_comp_baseMap, ← BoundedAlgHom.comp_assoc,
    stabilizerSectionMap_comp_baseMap]
  rfl

/-- The actual bounded automorphism of the fixed rational section algebra. -/
def stabilizerSectionAut (d : RationalData K P) (g : locusStabilizer d) :
    Aut d.algebra where
  hom := stabilizerSectionMap d g
  inv := stabilizerSectionMap d g⁻¹
  hom_inv_id := by
    change (stabilizerSectionMap d g⁻¹).comp (stabilizerSectionMap d g) = _
    rw [← stabilizerSectionMap_mul, inv_mul_cancel, stabilizerSectionMap_one]
    rfl
  inv_hom_id := by
    change (stabilizerSectionMap d g).comp (stabilizerSectionMap d g⁻¹) = _
    rw [← stabilizerSectionMap_mul, mul_inv_cancel, stabilizerSectionMap_one]
    rfl

/-- The locus stabilizer acts by bounded automorphisms on a single quotient. -/
def stabilizerSectionAction (d : RationalData K P) :
    locusStabilizer d →* Aut d.algebra where
  toFun := stabilizerSectionAut d
  map_one' := by
    apply CategoryTheory.Iso.ext
    exact stabilizerSectionMap_one d
  map_mul' g h := by
    apply CategoryTheory.Iso.ext
    exact stabilizerSectionMap_mul d g h

/-- Each section operator extends the forward base-algebra operator. -/
@[simp] theorem stabilizerSectionAction_baseMap
    (d : RationalData K P) (g : locusStabilizer d) (a : P) :
    (stabilizerSectionAction d g).hom.toAlgHom (d.baseMap a) =
      d.baseMap ((g : Aut P).hom.toAlgHom a) :=
  congrArg (fun f : BoundedAlgHom K P d.algebra => f a)
    (stabilizerSectionMap_comp_baseMap d g)

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism
