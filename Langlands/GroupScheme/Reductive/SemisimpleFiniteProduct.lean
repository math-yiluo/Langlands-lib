import Langlands.GroupScheme.Reductive.DirectProductProof
import Langlands.GroupScheme.SimplyConnected.CommutativeDerivedCoverConstruction
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-! # Semisimplicity of finite products of field groups -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

private instance semisimpleClosedUnderIso :
    ObjectProperty.IsClosedUnderIsomorphisms (@IsSemisimple k _) where
  of_iso e h := h.of_iso e.symm

private instance semisimpleContainsZero :
    ObjectProperty.ContainsZero (@IsSemisimple k _) where
  exists_zero := ⟨Grp.trivial _, Grp.isZero_trivial _, isSemisimple_trivial⟩

private instance semisimpleClosedUnderBinary :
    ObjectProperty.IsClosedUnderBinaryProducts (@IsSemisimple k _) where
  limitsOfShape_le X h := by
    obtain ⟨p⟩ := h
    let Y := p.diag.obj ⟨WalkingPair.left⟩
    let Z := p.diag.obj ⟨WalkingPair.right⟩
    let c : BinaryFan Y Z := BinaryFan.mk (p.π.app ⟨WalkingPair.left⟩)
      (p.π.app ⟨WalkingPair.right⟩)
    have hc : IsLimit c :=
      (IsLimit.equivOfNatIsoOfIso (diagramIsoPair p.diag) _ _
        (by exact Cone.ext (Iso.refl _) (by rintro ⟨_ | _⟩ <;> simp [c]))).1 p.isLimit
    exact IsSemisimple.of_iso
      (hc.conePointUniqueUpToIso (tensorProductIsBinaryProduct Y Z))
      (DirectProduct.isSemisimple_tensor (p.prop_diag_obj ⟨WalkingPair.left⟩)
        (p.prop_diag_obj ⟨WalkingPair.right⟩))

/-- Finite categorical products of semisimple field groups are semisimple,
including the empty product. -/
theorem IsSemisimple.pi {I : Type u} [Finite I]
    (H : I → GroupScheme (Spec (CommRingCat.of k)))
    (hH : ∀ i, IsSemisimple (H i)) : IsSemisimple (pi H) := by
  let : ObjectProperty.IsClosedUnderFiniteProducts (@IsSemisimple k _) := ObjectProperty.IsClosedUnderFiniteProducts.mk'
  exact ObjectProperty.prop_product (@IsSemisimple k _) hH

/-- The actual finite categorical product, bundled with its semisimplicity witness. -/
def semisimplePi {I : Type u} [Finite I]
    (H : I → GroupScheme (Spec (CommRingCat.of k)))
    (hH : ∀ i, IsSemisimple (H i)) :
    {P : GroupScheme (Spec (CommRingCat.of k)) // IsSemisimple P} :=
  ⟨pi H, IsSemisimple.pi H hH⟩

@[simp] theorem semisimplePi_val {I : Type u} [Finite I]
    (H : I → GroupScheme (Spec (CommRingCat.of k))) (hH : ∀ i, IsSemisimple (H i)) :
    (semisimplePi H hH).val = pi H := rfl

end Langlands.GroupScheme
