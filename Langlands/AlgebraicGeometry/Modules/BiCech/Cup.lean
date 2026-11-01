import Langlands.AlgebraicGeometry.Modules.BiCech.TensorFrame
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection

/-!
# The cup map into an external tensor product

For morphisms `f : P ⟶ X`, `g : P ⟶ Y` and module sheaves `L` on `X`, `M` on `Y`, write
`extTensor f g L M = tensorObj (f^* L) (g^* M)`. For opens `U ⊆ X`, `V ⊆ Y` and
`W ⊆ f⁻¹ U ∩ g⁻¹ V`, the cup map sends `l ∈ L(U)` and `m ∈ M(V)` to the image of
`f^* l|_W ⊗ g^* m|_W` under the sheafification unit, where `f^* l` is the pulled-back local
section `Scheme.Modules.pullbackLocalSection f l` (the adjunction unit applied to `l`).

The cup map is additive in each variable, semilinear over `f^♯` and `g^♯`, compatible with
restriction in `W`, `U` and `V`, and sends a pair of frames to a frame
(`IsFrameOn.pullbackLocalSection` and `isFrameOn_tsec`).
-/

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct

noncomputable section

namespace Langlands.AlgebraicGeometry.Modules.BiCech

open Langlands.Scheme.Modules Scheme.Modules

variable {P X Y : Scheme.{u}} (f : P ⟶ X) (g : P ⟶ Y) (L : X.Modules) (M : Y.Modules)

/-- The external tensor product `f^* L ⊗ g^* M` on `P`. -/
abbrev extTensor : P.Modules :=
  tensorObj ((Scheme.Modules.pullback f).obj L) ((Scheme.Modules.pullback g).obj M)

variable {f g L M}

section Tsec

variable {Z : Scheme.{u}} {A B : Z.Modules} {W : Z.Opens}

lemma tsec_add_left (a a' : Γ(A, W)) (b : Γ(B, W)) : tsec (a + a') b = tsec a b + tsec a' b := by
  unfold tsec
  erw [TensorProduct.add_tmul, map_add]
  rfl

lemma tsec_add_right (a : Γ(A, W)) (b b' : Γ(B, W)) : tsec a (b + b') = tsec a b + tsec a b' := by
  unfold tsec
  erw [TensorProduct.tmul_add, map_add]
  rfl

lemma tsec_smul_right (r : Γ(Z, W)) (a : Γ(A, W)) (b : Γ(B, W)) :
    tsec a (r • b) = r • tsec a b := by
  unfold tsec
  have h : ((a : A.val.obj (op W)) ⊗ₜ[Z.presheaf.obj (op W)] ((r • b : Γ(B, W)) : B.val.obj (op W))) =
      (show Z.presheaf.obj (op W) from r) •
        ((a : A.val.obj (op W)) ⊗ₜ[Z.presheaf.obj (op W)] (b : B.val.obj (op W))) :=
    TensorProduct.tmul_smul _ _ _
  erw [h, LinearMap.map_smul]
  rfl

end Tsec

/-- The cup map `L(U) × M(V) → (f^* L ⊗ g^* M)(W)` for `W ⊆ f⁻¹ U ∩ g⁻¹ V`. -/
def cup {U : X.Opens} {V : Y.Opens} {W : P.Opens} (hW : W ≤ f ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V)
    (l : Γ(L, U)) (m : Γ(M, V)) : Γ(extTensor f g L M, W) :=
  tsec (((Scheme.Modules.pullback f).obj L).presheaf.map (homOfLE (hW.trans inf_le_left)).op
      (pullbackLocalSection f l))
    (((Scheme.Modules.pullback g).obj M).presheaf.map (homOfLE (hW.trans inf_le_right)).op
      (pullbackLocalSection g m))

variable {U : X.Opens} {V : Y.Opens} {W : P.Opens} (hW : W ≤ f ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V)

lemma cup_add_left (l l' : Γ(L, U)) (m : Γ(M, V)) :
    cup hW (l + l') m = cup hW l m + cup hW l' m := by
  rw [cup, pullbackLocalSection_add, map_add, tsec_add_left]
  rfl

lemma cup_add_right (l : Γ(L, U)) (m m' : Γ(M, V)) :
    cup hW l (m + m') = cup hW l m + cup hW l m' := by
  rw [cup, pullbackLocalSection_add, map_add, tsec_add_right]
  rfl

lemma cup_smul_left (a : Γ(X, U)) (l : Γ(L, U)) (m : Γ(M, V)) :
    cup hW (a • l) m = f.appLE U W (hW.trans inf_le_left) a • cup hW l m := by
  rw [cup, pullbackLocalSection_smul, Scheme.Modules.map_smul, tsec_smul]
  rfl

lemma cup_smul_right (b : Γ(Y, V)) (l : Γ(L, U)) (m : Γ(M, V)) :
    cup hW l (b • m) = g.appLE V W (hW.trans inf_le_right) b • cup hW l m := by
  rw [cup, pullbackLocalSection_smul, Scheme.Modules.map_smul, tsec_smul_right]
  rfl

lemma map_cup {W' : P.Opens} (h : W' ≤ W) (l : Γ(L, U)) (m : Γ(M, V)) :
    (extTensor f g L M).presheaf.map (homOfLE h).op (cup hW l m) = cup (h.trans hW) l m := by
  rw [cup, tsec_map, cup, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

lemma cup_map_left {U' : X.Opens} (hU : U' ≤ U) (hW' : W ≤ f ⁻¹ᵁ U' ⊓ g ⁻¹ᵁ V)
    (l : Γ(L, U)) (m : Γ(M, V)) :
    cup hW' (L.presheaf.map (homOfLE hU).op l) m = cup hW l m := by
  rw [cup, ← map_homOfLE_pullbackLocalSection, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

lemma cup_map_right {V' : Y.Opens} (hV : V' ≤ V) (hW' : W ≤ f ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V')
    (l : Γ(L, U)) (m : Γ(M, V)) :
    cup hW' l (M.presheaf.map (homOfLE hV).op m) = cup hW l m := by
  rw [cup, ← map_homOfLE_pullbackLocalSection, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The cup of two frames is a frame. -/
theorem isFrameOn_cup {e : Γ(L, U)} {e' : Γ(M, V)} (he : IsFrameOn e U) (he' : IsFrameOn e' V) :
    IsFrameOn (cup hW e e') W :=
  isFrameOn_tsec (((he.pullbackLocalSection f).map _).mono (hW.trans inf_le_left))
    (((he'.pullbackLocalSection g).map _).mono (hW.trans inf_le_right))

end Langlands.AlgebraicGeometry.Modules.BiCech
