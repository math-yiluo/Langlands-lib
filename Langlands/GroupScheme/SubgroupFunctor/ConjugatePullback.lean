import Langlands.GroupScheme.Rational.MaximalTorusParameterExistenceProof
import Langlands.GroupScheme.InnerAutomorphismHom

/-! # Actual conjugate subgroup inclusions and their overlap invariance -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S S' : Scheme.{u}} {H G : GroupScheme S}

/-- Pull back an actual subgroup inclusion and conjugate it by the supplied
point of the actual pulled-back ambient group. -/
def conjugatePullback (b : S' ⟶ S) (i : H ⟶ G)
    (g : Over.mk (𝟙 S') ⟶ ((GroupScheme.baseChange b).obj G).X) :
    (GroupScheme.baseChange b).obj H ⟶ (GroupScheme.baseChange b).obj G :=
  (GroupScheme.baseChange b).map i ≫
    (((GroupScheme.baseChange b).obj G).innerIso g).hom

/-- Conjugating a pulled-back inclusion preserves closedness. -/
theorem isClosedSubgroup_conjugatePullback (b : S' ⟶ S) (i : H ⟶ G)
    (hi : IsClosedSubgroup i)
    (g : Over.mk (𝟙 S') ⟶ ((GroupScheme.baseChange b).obj G).X) :
    IsClosedSubgroup (conjugatePullback b i g) :=
  (hi.baseChange b).comp_iso _

/-- The source of the conjugated inclusion retains the pulled-back smoothness. -/
theorem smooth_conjugatePullback_source (b : S' ⟶ S)
    (hH : Smooth H.X.hom) :
    Smooth ((GroupScheme.baseChange b).obj H).X.hom := by
  let : Smooth H.X.hom := hH
  change Smooth (pullback.snd H.X.hom b)
  infer_instance

/-- Membership in the conjugate inclusion is an all-test condition on the
original group, with both the point and its conjugator projected back to it. -/
theorem mem_range_conjugatePullback_iff (b : S' ⟶ S) (i : H ⟶ G)
    (g : Over.mk (𝟙 S') ⟶ ((GroupScheme.baseChange b).obj G).X)
    {V : Over S'} (y : V ⟶ ((GroupScheme.baseChange b).obj G).X) :
    y ∈ (range (conjugatePullback b i g)).carrier V ↔
      (MaximalTorusParameterExistence.baseMap b V ≫ baseChangePointsEquiv b G _ g)⁻¹ *
          baseChangePointsEquiv b G V y *
          (MaximalTorusParameterExistence.baseMap b V ≫ baseChangePointsEquiv b G _ g) ∈
        (range i).carrier ((Over.map b).obj V) :=
  MaximalTorusParameterExistence.mem_range_baseChange_comp_innerIso_iff b i g y

/-- Conjugators whose quotient lies in the full normalizer give identical
subgroup functors after pullback. No torus or field hypothesis is needed. -/
theorem range_conjugatePullback_eq_of_normalizer (b : S' ⟶ S) (i : H ⟶ G)
    (g₁ g₂ : Over.mk (𝟙 S') ⟶ ((GroupScheme.baseChange b).obj G).X)
    (hn : (baseChangePointsEquiv b G _ g₁)⁻¹ * baseChangePointsEquiv b G _ g₂ ∈
      (range i).normalizer.carrier ((Over.map b).obj (Over.mk (𝟙 S')))) :
    range (conjugatePullback b i g₁) = range (conjugatePullback b i g₂) := by
  ext V y
  rw [mem_range_conjugatePullback_iff, mem_range_conjugatePullback_iff]
  apply MaximalTorusParameterExistence.conj_mem_iff_of_inv_mul_mem_normalizer
  have h := (range i).normalizer.comp_mem
    (MaximalTorusParameterExistence.baseMap b V) hn
  rwa [MonObj.comp_mul, GrpObj.comp_inv] at h

open Descent in
/-- A conjugate inclusion lying over one parameter has equal all-test ranges
on the two actual Čech pullbacks whenever parameter fibres are normalizer cosets.
This supplies the invariant inclusion needed for effective subgroup descent. -/
theorem conjugatePullback_overlap_range_eq (b : S' ⟶ S) (i : H ⟶ G)
    {Q : Over S} (q : G.X ⟶ Q)
    (hfib : ∀ (U : Over S) (a₁ a₂ : U ⟶ G.X), a₁ ≫ q = a₂ ≫ q →
      a₁⁻¹ * a₂ ∈ (range i).normalizer.carrier U)
    (g : Over.mk (𝟙 S') ⟶ ((GroupScheme.baseChange b).obj G).X) (x : S ⟶ Q.left)
    (hg : g.left ≫ pullback.fst G.X.hom b ≫ q.left = b ≫ x) :
    range ((GroupScheme.baseChange (fst b)).map (conjugatePullback b i g) ≫
        (canonicalOverlap b G).hom) =
      range ((GroupScheme.baseChange (snd b)).map (conjugatePullback b i g)) := by
  ext V y
  rw [MaximalTorusParameterExistence.mem_range_comp_iso_iff,
    range_baseChangeHom, mem_baseChange, range_baseChangeHom, mem_baseChange,
    mem_range_conjugatePullback_iff, mem_range_conjugatePullback_iff]
  let w : (Over.map b).obj ((Over.map (snd b)).obj V) ≅
      (Over.map b).obj ((Over.map (fst b)).obj V) :=
    Over.isoMk (Iso.refl _) (by
      simp only [Over.map_obj_hom, Iso.refl_hom, Category.id_comp, Category.assoc]
      rw [pullback.condition])
  have transport : ∀ z : (Over.map b).obj ((Over.map (fst b)).obj V) ⟶ G.X,
      z ∈ (range i).carrier _ ↔ w.hom ≫ z ∈ (range i).carrier _ := fun z =>
    ⟨fun h => (range i).comp_mem _ h, fun h => by
      simpa only [Iso.inv_hom_id_assoc] using (range i).comp_mem w.inv h⟩
  rw [transport, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv]
  have hinv : (canonicalOverlap b G).inv.hom.hom.left ≫
      (canonicalOverlap b G).hom.hom.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom]
    rfl
  have hZ : w.hom ≫ baseChangePointsEquiv b G _
      (baseChangePointsEquiv (fst b) ((GroupScheme.baseChange b).obj G) V
        (y ≫ (canonicalOverlap b G).inv.hom.hom)) =
      baseChangePointsEquiv b G _
        (baseChangePointsEquiv (snd b) ((GroupScheme.baseChange b).obj G) V y) := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, baseChangePointsEquiv_left, w, Over.isoMk_hom_left,
      Iso.refl_hom, Category.id_comp, Category.assoc]
    rw [← canonicalOverlap_fst, reassoc_of% hinv]
  rw [hZ]
  apply MaximalTorusParameterExistence.conj_mem_iff_of_inv_mul_mem_normalizer
  apply hfib
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, baseChangePointsEquiv_left, w, Over.isoMk_hom_left,
    Iso.refl_hom, Category.id_comp, Category.assoc, Over.map_map_left, Over.homMk_left,
    Over.map_obj_hom]
  rw [hg, pullback.condition_assoc]

end Langlands.GroupScheme.SubgroupFunctor
