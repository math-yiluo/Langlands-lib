import Langlands.GroupScheme.IntegralModel.Iso

/-! # The generic comparison induced by an abstract integral isomorphism -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G H J : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G) (N : IntegralModel R K H)

/-- The actual generic isomorphism obtained from an abstract integral
isomorphism and both original generic identifications. -/
def inducedGenericIso (e : M.group ≅ N.group) : G ≅ H :=
  M.genericIso.symm ≪≫
    (GroupScheme.baseChange (Spec.algebraMap R K)).mapIso e ≪≫ N.genericIso

/-- Every abstract integral isomorphism is compatible with its induced generic
isomorphism, with no hypothesis on its relation to another generic map. -/
def Iso.ofGroupIso (e : M.group ≅ N.group) :
    M.Iso N (M.inducedGenericIso N e) where
  iso := e
  generic_comm := by
    simp [inducedGenericIso]

/-- The original generic compatibility determines the induced generic map. -/
theorem Iso.inducedGenericIso_eq {f : G ≅ H} (e : M.Iso N f) :
    M.inducedGenericIso N e.iso = f := by
  apply CategoryTheory.Iso.ext
  change M.genericIso.inv ≫
    ((GroupScheme.baseChange (Spec.algebraMap R K)).map e.iso.hom ≫
      N.genericIso.hom) = f.hom
  rw [e.generic_comm, ← Category.assoc, M.genericIso.inv_hom_id, Category.id_comp]

/-- The adapter retains the complete supplied integral isomorphism. -/
@[simp] theorem Iso.ofGroupIso_iso (e : M.group ≅ N.group) :
    (Iso.ofGroupIso M N e).iso = e := rfl

/-- The actual image of the first model is carried onto the actual image of
the second by the induced generic map. -/
theorem map_integralPoints_inducedGenericIso (e : M.group ≅ N.group) :
    M.integralPoints.map (rationalPoints.map (M.inducedGenericIso N e).hom) =
      N.integralPoints :=
  (Iso.ofGroupIso M N e).map_integralPoints

/-- Identity integral comparisons induce the original generic identity. -/
@[simp] theorem inducedGenericIso_refl :
    M.inducedGenericIso M (CategoryTheory.Iso.refl M.group) =
      CategoryTheory.Iso.refl G := by
  apply CategoryTheory.Iso.ext
  simp [inducedGenericIso]

/-- Induced generic comparisons compose in the same order as the integral
isomorphisms; the intermediate supplied generic identifications cancel. -/
theorem inducedGenericIso_trans (P : IntegralModel R K J)
    (e : M.group ≅ N.group) (d : N.group ≅ P.group) :
    M.inducedGenericIso P (e ≪≫ d) =
      M.inducedGenericIso N e ≪≫ N.inducedGenericIso P d := by
  apply CategoryTheory.Iso.ext
  simp [inducedGenericIso]

/-- Reversing the integral isomorphism reverses its induced generic map. -/
@[simp] theorem inducedGenericIso_symm (e : M.group ≅ N.group) :
    N.inducedGenericIso M e.symm = (M.inducedGenericIso N e).symm := by
  apply CategoryTheory.Iso.ext
  simp [inducedGenericIso]

end Langlands.GroupScheme.IntegralModel
