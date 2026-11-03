import Langlands.GroupScheme.Dynamic.LieProof
import Langlands.GroupScheme.Dynamic.OppositeIntersection

/-! # Positive Lie weights distinguish opposite dynamic parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

section Opposite

variable {B : Scheme.{u}} {G : GroupScheme B}

/-- Reversing the parameter of a cocharacter twice returns the cocharacter. -/
@[simp] theorem oppositeCocharacter_oppositeCocharacter
    (χ : (Gm B).toGrp ⟶ G) :
    oppositeCocharacter (oppositeCocharacter χ) = χ := by
  have h : Gm.powerHom B (-1) ≫ Gm.powerHom B (-1) = 𝟙 (Gm B) := by
    simp only [Gm.powerHom_apply, neg_one_zsmul, Preadditive.neg_comp,
      Preadditive.comp_neg, Category.id_comp, neg_neg]
  rw [oppositeCocharacter, oppositeCocharacter, ← Category.assoc]
  change CommGroupScheme.groupHom
    (Gm.powerHom B (-1) ≫ Gm.powerHom B (-1)) ≫ χ = χ
  rw [h]
  exact Category.id_comp χ

end Opposite

section AffineBase

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} [IsAffine G.X.left]

/-- A nonidentity point in the dynamic unipotent distinguishes the dynamic
parabolic from its opposite. The test scheme is arbitrary. -/
theorem parabolic_ne_opposite_of_mem_unipotent
    (χ : (Gm (Spec R)).toGrp ⟶ G) {U : Over (Spec R)} {g : U ⟶ G.X}
    (hg : g ∈ (unipotent χ).carrier U) (hg1 : g ≠ 1) :
    parabolic χ ≠ parabolic (oppositeCocharacter χ) := by
  intro h
  have hp : g ∈ (parabolic (oppositeCocharacter χ)).carrier U := by
    rw [← h]
    exact unipotent_le_parabolic χ U hg
  have hm : g ∈ (unipotent (oppositeCocharacter (oppositeCocharacter χ))).carrier U := by
    simpa only [oppositeCocharacter_oppositeCocharacter] using hg
  exact hg1 (eq_one_of_mem_opposite_unipotent_of_mem_parabolic
    (oppositeCocharacter χ) hm hp)

end AffineBase

section Field

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- The actual Lie algebra has a nonzero vector of strictly positive integer
weight for the specified cocharacter. -/
def HasPositiveLieWeight (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) : Prop :=
  ∃ (n : ℕ) (X : lieKernel G k), X ≠ 1 ∧
    Additive.ofMul X ∈ weightSpace χ (Gm.powerHom _ (n + 1))

variable [LocallyOfFiniteType G.X.hom]

/-- A nonzero positive Lie-weight vector distinguishes a dynamic parabolic from
its opposite over an arbitrary field. -/
theorem parabolic_ne_opposite_of_positive_weight
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (n : ℕ) (X : lieKernel G k) (hX : X ≠ 1)
    (hw : Additive.ofMul X ∈ weightSpace χ (Gm.powerHom _ (n + 1))) :
    parabolic χ ≠ parabolic (oppositeCocharacter χ) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  apply parabolic_ne_opposite_of_mem_unipotent χ (g := X.val)
  · exact (dynamicLie k G χ X).2.2.mpr (Submodule.mem_iSup_of_mem n hw)
  · exact fun h => hX (Subtype.ext h)

/-- The positive Lie-weight condition implies that the two dynamic parabolics
are distinct. -/
theorem HasPositiveLieWeight.parabolic_ne_opposite
    {χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G} (h : HasPositiveLieWeight χ) :
    parabolic χ ≠ parabolic (oppositeCocharacter χ) := by
  obtain ⟨n, X, hX, hw⟩ := h
  exact parabolic_ne_opposite_of_positive_weight χ n X hX hw

end Field

end Langlands.GroupScheme.Dynamic
