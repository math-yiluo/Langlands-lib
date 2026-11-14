import Langlands.Geometry.FormalGroup.DeligneFibreBaseChange
import Langlands.Geometry.StructuralLineZeroReflection

/-! # Actual Pi-zero loci under structural base change -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

variable {S S' : Scheme.{u}} (f : S' ⟶ S)
  {d : ℕ} [NeZero d] {a : Γ(S, ⊤)}

namespace LinePiSheaf

variable (M : LinePiSheaf d S a)

/-- Vanishing on actual line fibres is preserved and reflected by base change. -/
theorem fibrePi_pullback_eq_zero_iff (i : ZMod d) (x : S') :
    (M.pullback f).graded.fibrePi i x = 0 ↔ M.graded.fibrePi i (f x) = 0 :=
  (M.graded.fibrePi_pullback_eq_zero_iff f i x).trans
    (specField_pullback_line_map_eq_zero_iff (f.residueFieldMap x)
      (IsLineSheaf.pullback (S.fromSpecResidueField (f x)) (M.line i))
      (IsLineSheaf.pullback (S.fromSpecResidueField (f x)) (M.line (i + 1)))
      (M.graded.fibrePi i (f x)))

/-- The actual Pi-zero locus is precisely the inverse image of the original one. -/
theorem piZeroLocus_pullback (i : ZMod d) :
    (M.pullback f).graded.piZeroLocus i = f ⁻¹' M.graded.piZeroLocus i := by
  ext x
  exact M.fibrePi_pullback_eq_zero_iff f i x

/-- The actual continuous map between Pi-zero-locus subspaces. -/
def piZeroPullbackMap (i : ZMod d) :
    TopCat.of ((M.pullback f).graded.piZeroLocus i) ⟶
      TopCat.of (M.graded.piZeroLocus i) :=
  TopCat.ofHom ⟨fun x => ⟨f x.val,
    (M.fibrePi_pullback_eq_zero_iff f i x.val).mp x.property⟩,
      (f.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- The map on zero loci is the restriction of the original base morphism. -/
@[simp]
theorem piZeroPullbackMap_apply (i : ZMod d)
    (x : (M.pullback f).graded.piZeroLocus i) :
    (M.piZeroPullbackMap f i x).val = f x.val := rfl

end LinePiSheaf

end Langlands.DeligneFormalSpace
