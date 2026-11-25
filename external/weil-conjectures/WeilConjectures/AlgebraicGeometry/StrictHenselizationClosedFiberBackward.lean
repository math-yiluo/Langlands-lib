/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme
set_option autoImplicit false
/-- The closed point of an affine presentation of a strict henselization maps to the
selected geometric point. This is the backward half of the singleton-fibre theorem.
Source: Stacks Project, Tags 04GW and 04GP.
(blueprint: lem-weil-pbc-strict-henselization-closed-fiber-backward)
Proof: give Ω the algebra structure induced by the geometric-point residue map.
The existing strictHenselizationResidue theorem supplies a local-ring structure on the
coordinate-ring colimit C and says that its closed point maps to s(closedPoint Ω).
Every point of a local spectrum specializes to its closed point. Apply this in C to
e(closedPoint A), and in A to e.inv(closedPoint C), then map the latter specialization
by e.hom. The inverse identity gives specializations in both directions. Since Spec C
is T0, e(closedPoint A) = closedPoint C. Substitute in the structural-image equation. -/
theorem strictHenselizationStructuralMap_closedPoint_eq
    {S : Scheme.{u}} {Ω A : Type u} [Field Ω] [IsAlgClosed Ω]
    [CommRing A] [IsLocalRing A]
    (s : Spec (.of Ω) ⟶ S) (e : Spec (.of A) ≅ strictLocalization s) :
    (e.hom ≫ strictLocalizationToBase s) (IsLocalRing.closedPoint A) =
      s (IsLocalRing.closedPoint Ω) := by
  let : Algebra (S.residueField (s (IsLocalRing.closedPoint Ω))) Ω :=
    (descResidueField (stalkClosedPointTo s)).hom.toAlgebra
  obtain ⟨hlocal, _, hbase, _⟩ := AlgebraicGeometry.strictHenselizationResidue s rfl
  let := hlocal
  have hforward := IsLocalRing.specializes_closedPoint
    (e.hom (IsLocalRing.closedPoint A))
  have hbackward := (IsLocalRing.specializes_closedPoint
    (e.inv (IsLocalRing.closedPoint (strictHenselization s)))).map e.hom.continuous
  have hpoint : e.hom (IsLocalRing.closedPoint A) =
      IsLocalRing.closedPoint (strictHenselization s) := by
    apply (hforward.antisymm ?_).eq
    rw [← Scheme.Hom.comp_apply, e.inv_hom_id] at hbackward
    exact hbackward
  simpa only [Scheme.Hom.comp_apply, hpoint] using hbase
end AlgebraicGeometry.Scheme
