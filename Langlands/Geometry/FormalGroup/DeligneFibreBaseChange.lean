import Langlands.Geometry.FormalGroup.DeligneStructuralBaseChange
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Actual residue-field fibres under structural base change -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable {S S' : Scheme.{u}} (f : S' ⟶ S)

/-- The actual fibre of a structural pullback is the scalar pullback of the fibre. -/
def structuralFibreBaseChangeIso (x : S') :
    Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback (S'.fromSpecResidueField x) ≅
      Scheme.Modules.pullback (S.fromSpecResidueField (f x)) ⋙
        Scheme.Modules.pullback (Spec.map (f.residueFieldMap x)) :=
  Scheme.Modules.pullbackComp (S'.fromSpecResidueField x) f ≪≫
    Scheme.Modules.pullbackCongr
      (f.SpecMap_residueFieldMap_fromSpecResidueField x).symm ≪≫
    (Scheme.Modules.pullbackComp (Spec.map (f.residueFieldMap x))
      (S.fromSpecResidueField (f x))).symm

namespace GradedPiSheaf

variable {d : ℕ} [NeZero d] {a : Γ(S, ⊤)}
  (M : GradedPiSheaf d S.sheaf (schemeScalar S a))

@[reassoc]
theorem pullbackComponentIso_hom_pi (i : ZMod d) :
    (Scheme.Modules.pullback f).map (M.componentPi i) ≫
        (M.pullbackComponentIso f (i + 1)).hom =
      (M.pullbackComponentIso f i).hom ≫ (M.pullback f).componentPi i := by
  let : Mono ((M.pullback f).componentInclusion (i + 1)) :=
    inferInstanceAs (Mono ((M.pullback f).component (i + 1)).ι)
  have hi (j : ZMod d) :
      (M.pullbackComponentIso f j).hom ≫ (M.pullback f).componentInclusion j =
        (Scheme.Modules.pullback f).map (M.componentInclusion j) :=
    splitRangeIso_hom_inclusion _ _ _
  apply (cancel_mono ((M.pullback f).componentInclusion (i + 1))).mp
  rw [Category.assoc, hi,
    Category.assoc, (M.pullback f).componentPi_inclusion,
    ← Category.assoc, hi]
  change (Scheme.Modules.pullback f).map (M.componentPi i) ≫
      (Scheme.Modules.pullback f).map (M.componentInclusion (i + 1)) =
    (Scheme.Modules.pullback f).map (M.componentInclusion i) ≫
      (Scheme.Modules.pullback f).map M.pi
  rw [← Functor.map_comp, ← Functor.map_comp, M.componentPi_inclusion]

@[reassoc]
theorem pullbackComponentIso_inv_pi (i : ZMod d) :
    (M.pullback f).componentPi i ≫ (M.pullbackComponentIso f (i + 1)).inv =
      (M.pullbackComponentIso f i).inv ≫
        (Scheme.Modules.pullback f).map (M.componentPi i) := by
  apply (cancel_epi (M.pullbackComponentIso f i).hom).mp
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← M.pullbackComponentIso_hom_pi,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Compare actual homogeneous fibres using the residual triangle and split ranges. -/
def fibrePullbackIso (i : ZMod d) (x : S') :
    (M.pullback f).fibreComponent i x ≅
      (Scheme.Modules.pullback (Spec.map (f.residueFieldMap x))).obj
        (M.fibreComponent i (f x)) :=
  (Scheme.Modules.pullback (S'.fromSpecResidueField x)).mapIso
    (M.pullbackComponentIso f i).symm ≪≫
      (structuralFibreBaseChangeIso f x).app (M.componentSheaf i)

@[reassoc]
theorem fibrePullbackIso_pi (i : ZMod d) (x : S') :
    (M.pullback f).fibrePi i x ≫ (M.fibrePullbackIso f (i + 1) x).hom =
      (M.fibrePullbackIso f i x).hom ≫
        (Scheme.Modules.pullback (Spec.map (f.residueFieldMap x))).map
          (M.fibrePi i (f x)) := by
  let Q := Scheme.Modules.pullback (S'.fromSpecResidueField x)
  let e := structuralFibreBaseChangeIso f x
  change Q.map ((M.pullback f).componentPi i) ≫
      (Q.map (M.pullbackComponentIso f (i + 1)).inv ≫
        e.hom.app (M.componentSheaf (i + 1))) =
    (Q.map (M.pullbackComponentIso f i).inv ≫
      e.hom.app (M.componentSheaf i)) ≫ _
  rw [← Category.assoc, ← Q.map_comp, M.pullbackComponentIso_inv_pi,
    Q.map_comp, Category.assoc]
  exact congrArg (fun k => Q.map (M.pullbackComponentIso f i).inv ≫ k)
    (e.hom.naturality (M.componentPi i))

/-- The comparison detects vanishing precisely after the actual field scalar pullback. -/
theorem fibrePi_pullback_eq_zero_iff (i : ZMod d) (x : S') :
    (M.pullback f).fibrePi i x = 0 ↔
      (Scheme.Modules.pullback (Spec.map (f.residueFieldMap x))).map
        (M.fibrePi i (f x)) = 0 := by
  constructor
  · intro h
    apply (cancel_epi (M.fibrePullbackIso f i x).hom).mp
    rw [comp_zero, ← M.fibrePullbackIso_pi, h, zero_comp]
  · intro h
    apply (cancel_mono (M.fibrePullbackIso f (i + 1) x).hom).mp
    rw [zero_comp, M.fibrePullbackIso_pi, h, comp_zero]

/-- Vanishing on the original fibre implies vanishing on every pulled fibre. -/
theorem mem_piZeroLocus_pullback (i : ZMod d) (x : S')
    (hx : f x ∈ M.piZeroLocus i) :
    x ∈ (M.pullback f).piZeroLocus i := by
  have hz : M.fibrePi i (f x) = 0 := hx
  change (M.pullback f).fibrePi i x = 0
  apply (M.fibrePi_pullback_eq_zero_iff f i x).mpr
  rw [hz, Functor.map_zero]

/-- The inverse image of the original zero locus lies in the pulled zero locus. -/
theorem preimage_piZeroLocus_subset (i : ZMod d) :
    f ⁻¹' M.piZeroLocus i ⊆ (M.pullback f).piZeroLocus i :=
  fun x hx => M.mem_piZeroLocus_pullback f i x hx

end GradedPiSheaf

end Langlands.DeligneFormalSpace
