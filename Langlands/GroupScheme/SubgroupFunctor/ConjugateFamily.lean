import Langlands.GroupScheme.SubgroupFunctor.ConjugatePullback
import Langlands.GroupScheme.HomScheme.AdmissibleRestrictionPoints
import Langlands.GroupScheme.CocharacterTransport

/-! # Conjugate subgroup families and evaluation -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.SubgroupFunctor

open TorusSubgroupModuli

variable {S : Scheme.{u}} {H G : GroupScheme S} {M T : Over S}

/-- The actual conjugate family attached to a group-valued parameter. -/
def conjugateFamily (i : H ⟶ G) (g : M ⟶ G.X) :
    (GroupScheme.baseChange M.hom).obj H ⟶ (GroupScheme.baseChange M.hom).obj G :=
  conjugatePullback M.hom i ((baseChangeBasePointsEquiv M.hom G).symm g)

/-- A relative test has its usual structure morphism to the parameter scheme. -/
abbrev familyTestMap (M : Over S) (V : Over M.left) :
    (Over.map M.hom).obj V ⟶ M :=
  Over.homMk V.hom rfl

/-- Projecting the conjugator of a family recovers its original group-valued
parameter on every test scheme. -/
theorem conjugateFamily_conjugator (g : M ⟶ G.X) (V : Over M.left) :
    MaximalTorusParameterExistence.baseMap M.hom V ≫
        baseChangePointsEquiv M.hom G _
          ((baseChangeBasePointsEquiv M.hom G).symm g) =
      familyTestMap M V ≫ g := by
  apply Over.OverMorphism.ext
  have h := congrArg (fun x : M ⟶ G.X => x.left)
    ((baseChangeBasePointsEquiv M.hom G).apply_symm_apply g)
  rw [baseChangeBasePointsEquiv_left] at h
  simpa only [Over.comp_left, baseChangePointsEquiv_left,
    MaximalTorusParameterExistence.baseMap, Over.map_map_left, Over.homMk_left,
    familyTestMap, Category.assoc] using congrArg (V.hom ≫ ·) h

/-- Membership in a conjugate family is inverse conjugation by the parameter,
on all actual relative test schemes. -/
theorem mem_range_conjugateFamily_iff (i : H ⟶ G) (g : M ⟶ G.X)
    {V : Over M.left} (y : V ⟶ ((GroupScheme.baseChange M.hom).obj G).X) :
    y ∈ (range (conjugateFamily i g)).carrier V ↔
      (familyTestMap M V ≫ g)⁻¹ * baseChangePointsEquiv M.hom G V y *
          (familyTestMap M V ≫ g) ∈ (range i).carrier ((Over.map M.hom).obj V) := by
  rw [conjugateFamily, mem_range_conjugatePullback_iff, conjugateFamily_conjugator]

/-- Actual family evaluation pulls back its all-test condition through the
canonical direct-to-iterated point comparison. -/
theorem mem_evaluate_iff {K : GroupScheme M.left}
    (j : K ⟶ (GroupScheme.baseChange M.hom).obj G) (a : T ⟶ M)
    {V : Over T.left} (y : V ⟶ ((GroupScheme.baseChange T.hom).obj G).X) :
    y ∈ (evaluate j a).carrier V ↔
      familyPointsEquiv (G := G) a V y ∈
        (range j).carrier ((Over.map a.left).obj V) := by
  rw [evaluate, familyHom, range_comp_iso, range_baseChangeHom]
  rfl

/-- Evaluating a conjugate family at a parameter morphism is the conjugate
family of the restricted group-valued parameter. -/
theorem evaluate_conjugateFamily (i : H ⟶ G) (g : M ⟶ G.X) (a : T ⟶ M) :
    evaluate (conjugateFamily i g) a = range (conjugateFamily i (a ≫ g)) := by
  ext V y
  rw [mem_evaluate_iff, mem_range_conjugateFamily_iff, mem_range_conjugateFamily_iff]
  let w : (Over.map T.hom).obj V ≅
      (Over.map M.hom).obj ((Over.map a.left).obj V) :=
    Over.isoMk (Iso.refl _) (by simp only [Over.map_obj_hom, Iso.refl_hom,
      Category.id_comp, Category.assoc, Over.w a])
  have transport : ∀ z :
      (Over.map M.hom).obj ((Over.map a.left).obj V) ⟶ G.X,
      z ∈ (range i).carrier _ ↔ w.hom ≫ z ∈ (range i).carrier _ := fun z =>
    ⟨fun h => (range i).comp_mem _ h, fun h => by
      simpa only [Iso.inv_hom_id_assoc] using (range i).comp_mem w.inv h⟩
  rw [transport, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv]
  have hparam :
      w.hom ≫ familyTestMap M ((Over.map a.left).obj V) ≫ g =
        familyTestMap T V ≫ (a ≫ g) := by
    apply Over.OverMorphism.ext
    simp only [w, Over.isoMk_hom_left, Iso.refl_hom, Over.comp_left,
      familyTestMap, Over.homMk_left, Over.map_obj_hom, Category.id_comp, Category.assoc]
  have hpoint :
      w.hom ≫ baseChangePointsEquiv M.hom G _
        (familyPointsEquiv (G := G) a V y) = baseChangePointsEquiv T.hom G V y := by
    apply Over.OverMorphism.ext
    simp only [w, Over.isoMk_hom_left, Iso.refl_hom, Over.comp_left,
      baseChangePointsEquiv_left, Category.id_comp, familyPointsEquiv_original]
  rw [hparam, hpoint]

/-- Parameters differing by the full normalizer give the same actual family. -/
theorem range_conjugateFamily_eq_of_normalizer (i : H ⟶ G)
    (g₁ g₂ : M ⟶ G.X)
    (hn : g₁⁻¹ * g₂ ∈ (range i).normalizer.carrier M) :
    range (conjugateFamily i g₁) = range (conjugateFamily i g₂) := by
  ext V y
  rw [mem_range_conjugateFamily_iff, mem_range_conjugateFamily_iff]
  apply MaximalTorusParameterExistence.conj_mem_iff_of_inv_mul_mem_normalizer
  have h := (range i).normalizer.comp_mem (familyTestMap M V) hn
  rwa [MonObj.comp_mul, GrpObj.comp_inv] at h

end Langlands.GroupScheme.SubgroupFunctor
