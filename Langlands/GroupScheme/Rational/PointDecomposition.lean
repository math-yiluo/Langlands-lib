import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Dynamic.LimitMap

/-! # Rational points of dynamic parabolics and their Levi decompositions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A connected reductive group over a field has separated structure morphism,
because its structure morphism is affine. -/
theorem IsConnectedReductive.isSeparated {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G) :
    IsSeparated G.X.hom := by
  have := hG.isAffineHom
  infer_instance

namespace RationalPoint

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)

/-- Rational points of the dynamic parabolic of a field-defined cocharacter. -/
abbrev parabolic : Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :=
  (Dynamic.parabolic χ).carrier (Over.mk (𝟙 _))

/-- Rational points of the dynamic Levi of a field-defined cocharacter. -/
abbrev levi : Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :=
  (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _))

/-- Rational points of the dynamic unipotent subgroup of a field-defined cocharacter. -/
abbrev unipotent : Subgroup (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :=
  (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _))

theorem levi_le_parabolic : levi χ ≤ parabolic χ :=
  Dynamic.centralizer_le_parabolic χ _

theorem unipotent_le_parabolic : unipotent χ ≤ parabolic χ :=
  Dynamic.unipotent_le_parabolic χ _

/-- The unipotent points form a normal subgroup of the parabolic points. -/
theorem unipotent_normal :
    ((unipotent χ).subgroupOf (parabolic χ)).Normal :=
  Dynamic.unipotent_subgroupOf_parabolic_normal χ _

/-- The Levi points normalize the unipotent points in the ambient group of rational points. -/
theorem levi_le_normalizer_unipotent :
    levi χ ≤ Subgroup.normalizer (unipotent χ : Set (Over.mk (𝟙 _) ⟶ G.X)) :=
  Dynamic.centralizer_le_normalizer_unipotent χ _

/-- The inclusion of the Levi points in the parabolic points. -/
abbrev leviInclusion : levi χ →* parabolic χ :=
  Subgroup.inclusion (levi_le_parabolic χ)

/-- The action of the Levi points on the unipotent points by conjugation. -/
abbrev leviConj : levi χ →* MulAut (unipotent χ) :=
  Dynamic.centralizerConj χ _

@[simp] theorem leviConj_apply_coe (l : levi χ) (x : unipotent χ) :
    (leviConj χ l x : Over.mk (𝟙 _) ⟶ G.X) = l * x * l⁻¹ :=
  rfl

variable [IsAffineHom G.X.hom]

/-- The Levi and unipotent points have trivial intersection. -/
theorem levi_inf_unipotent : levi χ ⊓ unipotent χ = ⊥ := by
  apply bot_unique
  intro g hg
  exact Subgroup.mem_bot.mpr
    (Dynamic.eq_one_of_mem_centralizer_of_mem_unipotent χ
      (fun _ _ _ _ hl hl' => hl.unique χ hl') hg.1 hg.2)

/-- Every parabolic point has a unique expression as a unipotent point times a Levi point. -/
theorem existsUnique_unipotent_mul_levi
    {g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X} (hg : g ∈ parabolic χ) :
    ∃! p : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) ×
        (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X),
      p.1 ∈ unipotent χ ∧ p.2 ∈ levi χ ∧ g = p.1 * p.2 := by
  obtain ⟨l, hl⟩ := Dynamic.exists_hasLimit χ hg
  have hz := hl.mem_centralizer χ
  have hu : g * l⁻¹ ∈ unipotent χ := by
    change Dynamic.HasLimit χ (g * l⁻¹) 1
    simpa only [mul_inv_cancel] using
      hl.mul χ (Dynamic.hasLimit_of_mem_centralizer χ hz).inv
  refine ⟨(g * l⁻¹, l), ⟨hu, hz, (inv_mul_cancel_right g l).symm⟩, ?_⟩
  rintro ⟨x, z⟩ ⟨hx, hz', hgz⟩
  have hl' : Dynamic.HasLimit χ g z := by
    rw [hgz]
    simpa only [one_mul] using
      (hx : Dynamic.HasLimit χ x 1).mul χ (Dynamic.hasLimit_of_mem_centralizer χ hz')
  have hzl : z = l := hl'.unique χ hl
  apply Prod.ext _ hzl
  change x = g * l⁻¹
  rw [hgz, ← hzl, mul_inv_cancel_right]

/-- Every parabolic point has a unique expression as a Levi point times a unipotent point. -/
theorem existsUnique_levi_mul_unipotent
    {g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X} (hg : g ∈ parabolic χ) :
    ∃! p : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) ×
        (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X),
      p.1 ∈ levi χ ∧ p.2 ∈ unipotent χ ∧ g = p.1 * p.2 := by
  obtain ⟨l, hl⟩ := Dynamic.exists_hasLimit χ hg
  have hz := hl.mem_centralizer χ
  have hu : l⁻¹ * g ∈ unipotent χ := by
    change Dynamic.HasLimit χ (l⁻¹ * g) 1
    simpa only [inv_mul_cancel] using
      ((Dynamic.hasLimit_of_mem_centralizer χ hz).inv χ).mul χ hl
  refine ⟨(l, l⁻¹ * g), ⟨hz, hu, (mul_inv_cancel_left l g).symm⟩, ?_⟩
  rintro ⟨z, x⟩ ⟨hz', hx, hgz⟩
  have hl' : Dynamic.HasLimit χ g z := by
    rw [hgz]
    simpa only [mul_one] using
      (Dynamic.hasLimit_of_mem_centralizer χ hz').mul χ hx
  have hzl : z = l := hl'.unique χ hl
  apply Prod.ext hzl
  change x = l⁻¹ * g
  rw [hgz, ← hzl, inv_mul_cancel_left]

/-- The rational-point limit homomorphism, with values in the Levi points. -/
abbrev limitHom : parabolic χ →* levi χ :=
  Dynamic.limitHom χ _

/-- The kernel is the unipotent subgroup, viewed inside the parabolic. -/
theorem ker_limitHom :
    (limitHom χ).ker = (unipotent χ).subgroupOf (parabolic χ) :=
  Dynamic.ker_limitHom χ _

/-- The Levi inclusion is a section of the limit homomorphism. -/
theorem limitHom_comp_leviInclusion :
    (limitHom χ).comp (leviInclusion χ) = MonoidHom.id (levi χ) :=
  Dynamic.limitHom_comp_inclusion χ _

@[simp] theorem limitHom_leviInclusion (l : levi χ) :
    limitHom χ (leviInclusion χ l) = l :=
  Dynamic.limitHom_inclusion χ _ l

theorem limitHom_surjective : Function.Surjective (limitHom χ) :=
  Dynamic.limitHom_surjective χ _

/-- Multiplication identifies the semidirect product of unipotent and Levi points
with the parabolic points. -/
abbrev semidirectEquiv :
    unipotent χ ⋊[leviConj χ] levi χ ≃* parabolic χ :=
  Dynamic.semidirectEquiv χ _

@[simp] theorem semidirectEquiv_apply_coe
    (x : unipotent χ ⋊[leviConj χ] levi χ) :
    (semidirectEquiv χ x : Over.mk (𝟙 _) ⟶ G.X) = x.left * x.right :=
  rfl

/-- The limit homomorphism is projection onto the Levi factor. -/
theorem limitHom_comp_semidirectEquiv :
    (limitHom χ).comp (semidirectEquiv χ).toMonoidHom = SemidirectProduct.rightHom :=
  Dynamic.limitHom_comp_semidirectEquiv χ _

end RationalPoint

end Langlands.GroupScheme
