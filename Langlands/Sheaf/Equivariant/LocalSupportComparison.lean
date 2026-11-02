import Langlands.Sheaf.Equivariant.LocalSupport
import Langlands.Sheaf.Equivariant.CompactSupport

/-! # Comparing local-vanishing and stalk compact-section representations -/

noncomputable section

universe u v

namespace Langlands.Sheaf.Equivariant.LocalCompactSections

open CategoryTheory Opposite

variable {R : Type u} [CommRing R] {G : Type v} [Group G]
  {X : Type u} [TopologicalSpace X] [MulAction G X]

/-- The proved equality of compact-support conditions gives the identity on sections. -/
def stalkLinearEquiv (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R) :
    Langlands.Sheaf.LocalSupport.submodule (ordinary F) ≃ₗ[R]
      Langlands.Sheaf.CompactSupport.submodule (ordinary F) where
  toFun s := ⟨s.val, by
    change IsCompact (Langlands.Sheaf.CompactSupport.support (ordinary F) s.val)
    rw [← Langlands.Sheaf.LocalSupport.support_eq_stalkSupport]
    exact s.property⟩
  invFun s := ⟨s.val, by
    change IsCompact (Langlands.Sheaf.LocalSupport.support (ordinary F) s.val)
    rw [Langlands.Sheaf.LocalSupport.support_eq_stalkSupport]
    exact s.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem stalkLinearEquiv_apply (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R)
    (s : Langlands.Sheaf.LocalSupport.submodule (ordinary F)) :
    (stalkLinearEquiv F s).val = s.val := rfl

@[simp]
theorem stalkLinearEquiv_symm_apply (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R)
    (s : Langlands.Sheaf.CompactSupport.submodule (ordinary F)) :
    ((stalkLinearEquiv F).symm s).val = s.val := rfl

variable [ContinuousConstSMul G X]

/-- Both constructions restrict the same original group operators. -/
def stalkEquiv (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R) :
    (representation F).Equiv (CompactSections.representation F) :=
  Representation.Equiv.mk (stalkLinearEquiv F) (fun _ =>
    LinearMap.ext (fun _ => Subtype.ext rfl))

/-- The whole compact-section representations are isomorphic by identity on sections. -/
def stalkRepIso (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R) :
    Rep.of (representation F) ≅ Rep.of (CompactSections.representation F) :=
  Rep.mkIso (stalkEquiv F)

variable (R G X)

/-- The support comparison is natural for every equivariant sheaf morphism. -/
def stalkComparison :
    functor R G X ≅ CompactSections.functor R G X :=
  NatIso.ofComponents (fun F => stalkRepIso F.obj) (by
    intro F F' f
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    rfl)

/-- The comparison commutes with the actual inclusion into global sections. -/
theorem stalkComparison_inclusion :
    (stalkComparison R G X).hom ≫ CompactSections.inclusion R G X =
      inclusion R G X := by
  apply NatTrans.ext
  funext F
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro s
  rfl

end Langlands.Sheaf.Equivariant.LocalCompactSections
