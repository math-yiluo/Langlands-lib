import Langlands.AlgebraicGeometry.AffineCechDeRham

/-! # Forgetting the form component in degree one -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AffineCechDeRham

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) (U : Scheme.AffineOpenCover.{u} X)

/-- Degree-one cocycles of the function part of the affine Čech complex. -/
abbrev structureCocycles : Submodule R (Cochains U (functions f) 1) :=
  (cechD U (functions f) 1).ker

/-- The function Čech differential into the cocycle submodule. -/
def structureBoundaryMap : C0 f U →ₗ[R] structureCocycles f U :=
  LinearMap.codRestrict _ (cechD U (functions f) 0) (cechD_cechD U (functions f) 0)

/-- The function Čech boundaries, as a submodule of its degree-one cocycles. -/
def structureBoundaries : Submodule R (structureCocycles f U) :=
  (structureBoundaryMap f U).range

/-- The degree-one Čech cohomology of functions on the supplied affine cover. -/
abbrev structureH1 := structureCocycles f U ⧸ structureBoundaries f U

/-- Send a de Rham cocycle to its function cochain, which is a Čech cocycle. -/
def forgetFormsCocycle : cocycles f U →ₗ[R] structureCocycles f U :=
  LinearMap.codRestrict _ ((LinearMap.fst _ _ _).comp (cocycles f U).subtype) (fun a => by
    have ha := a.property
    change D1 f U a.val = 0 at ha
    rw [D1_apply] at ha
    exact congrArg Prod.fst ha)

variable [Smooth f] [IsSeparated f] [Finite U.I₀]

/-- The projection in the first Hodge exact sequence, induced by forgetting the one-forms. -/
def toStructureH1 : H1 f U →ₗ[R] structureH1 f U :=
  (boundaries f U).liftQ ((structureBoundaries f U).mkQ.comp (forgetFormsCocycle f U)) (by
    rintro a ⟨h, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨h, rfl⟩)

@[simp]
lemma toStructureH1_class (a : cocycles f U) :
    toStructureH1 f U ((boundaries f U).mkQ a) =
      (structureBoundaries f U).mkQ (forgetFormsCocycle f U a) := rfl

/-- The kernel of the projection to function Čech classes is the first Hodge step. -/
theorem ker_toStructureH1 : (toStructureH1 f U).ker = hodgeF1 f U := by
  ext z
  obtain ⟨a, rfl⟩ := (boundaries f U).mkQ_surjective z
  constructor
  · intro ha
    change toStructureH1 f U ((boundaries f U).mkQ a) = 0 at ha
    rw [toStructureH1_class] at ha
    obtain ⟨h, hh⟩ := (Submodule.Quotient.mk_eq_zero _).mp ha
    have hh₀ : cechD U (functions f) 0 h = a.val.1 := congrArg Subtype.val hh
    let c := a - boundaryMap f U h
    have hc₀ : c.val.1 = 0 := by
      change a.val.1 - cechD U (functions f) 0 h = 0
      rw [hh₀, sub_self]
    have hc := c.property
    change D1 f U (c.val.1, c.val.2) = 0 at hc
    rw [hc₀, D1_apply, map_zero, map_zero, sub_zero] at hc
    have hclosed : cechD U (oneForms f) 0 c.val.2 = 0 ∧
        cochainMap U (exteriorD1 f) 0 c.val.2 = 0 :=
      ⟨congrArg (fun x => x.2.1) hc, congrArg (fun x => x.2.2) hc⟩
    let b : closedForms f U := ⟨c.val.2, hclosed⟩
    have hcb : closedFormClass f U b = (boundaries f U).mkQ c := by
      apply congrArg ((boundaries f U).mkQ)
      exact Subtype.ext (Prod.ext hc₀.symm rfl)
    refine ⟨b, hcb.trans ?_⟩
    have hz : (boundaries f U).mkQ (boundaryMap f U h) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨h, rfl⟩
    change (boundaries f U).mkQ (a - boundaryMap f U h) = _
    rw [map_sub, hz, sub_zero]
  · rintro ⟨b, hb⟩
    change toStructureH1 f U ((boundaries f U).mkQ a) = 0
    rw [← hb]
    change (structureBoundaries f U).mkQ (0 : structureCocycles f U) = 0
    exact map_zero _

end Langlands.AlgebraicGeometry.AffineCechDeRham
