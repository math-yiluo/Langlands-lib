import Langlands.GroupScheme.Lie.ElementCentralizer
import Langlands.GroupScheme.Lie.TorusCentralizer
import Langlands.GroupScheme.RepresentedSubgroup
import Langlands.GroupScheme.Rational.Characters

/-! # Tangents of the full scheme center -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

set_option backward.isDefEq.respectTransparency false

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}
  {A : Type u} [CommRing A] [Algebra R A]

/-- A point fixing a tangent vector commutes with every square-zero evaluation
of that vector over the same coefficient algebra. -/
theorem commute_of_mem_elementCentralizer
    (X : lieKernel G R) (f : DualNumber R →ₐ[R] A)
    (g : AffinePoints G A)
    (hg : g ∈ (elementCentralizer G X).carrier
      ((algSpec R).obj (op (CommAlgCat.of R A)))) :
    Commute (affineMap G f X.val) g := by
  have hc := ((commute_constant_iff G g _).2
    ((mem_elementCentralizer_affine_iff G X g).1 hg)).symm
  have he := hc.map (affineMap G (dualNumberEvaluation (f DualNumber.eps) (by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero])))
  simpa only [lieKernelMap_val, ← affineMap_comp, dualNumberEvaluation_factor,
    affineMap_dualNumberEvaluation_constant] using he

variable [IsAffineHom G.X.hom]

/-- A tangent vector fixed by every group point is a tangent of the full
scheme center, including its infinitesimal structure. -/
theorem mem_center_lie_of_elementCentralizer_eq_top (X : lieKernel G R)
    (hX : elementCentralizer G X = ⊤) :
    Additive.ofMul X ∈ (center G).lie R := by
  change X.val ∈ (center G).carrier _
  intro V a g
  let B : CommAlgCat R := unop ((algΓ R).obj V)
  let f : DualNumber R →ₐ[R] B :=
    (((algΓAlgSpecAdjunction R).homEquiv V
      (op (CommAlgCat.of R (DualNumber R)))).symm a).unop.hom
  have ha : (algΓAlgSpecAdjunction R).unit.app V ≫
      (algSpec R).map (CommAlgCat.ofHom f).op = a :=
    ((algΓAlgSpecAdjunction R).homEquiv V
      (op (CommAlgCat.of R (DualNumber R)))).apply_symm_apply a
  have hg : affinizationFactor G g ∈ (elementCentralizer G X).carrier
      ((algSpec R).obj (op B)) := by
    rw [hX]
    exact Subgroup.mem_top _
  have hc := commute_of_mem_elementCentralizer X f (affinizationFactor G g) hg
  have hp := congrArg (fun q => (algΓAlgSpecAdjunction R).unit.app V ≫ q) hc.eq
  change (a ≫ X.val) * g = g * (a ≫ X.val)
  simpa only [MonObj.comp_mul, affineMap_apply, ← Category.assoc, ha,
    unit_affinizationFactor] using hp

/-- A tangent of the full scheme center is fixed by every group point. -/
theorem elementCentralizer_eq_top_of_mem_center_lie (X : lieKernel G R)
    (hX : Additive.ofMul X ∈ (center G).lie R) :
    elementCentralizer G X = ⊤ := by
  apply SubgroupFunctor.ext
  intro U
  apply top_unique
  intro g _ A _ _ a
  change X.val ∈ (center G).carrier _ at hX
  have hc := hX _ ((algSpec R).map
    (CommAlgCat.ofHom (GeneralLinear.DualNumber.coefficientAlgMap
      (Algebra.ofId R A))).op) (constant G (a ≫ g))
  exact hc.symm

/-- Full scheme centralizers of tangent vectors characterize tangents of the
full scheme center. No smoothness of the group or its center is needed. -/
theorem elementCentralizer_eq_top_iff_mem_center_lie (X : lieKernel G R) :
    elementCentralizer G X = ⊤ ↔ Additive.ofMul X ∈ (center G).lie R :=
  ⟨mem_center_lie_of_elementCentralizer_eq_top X,
    elementCentralizer_eq_top_of_mem_center_lie X⟩

/-- The actual tangent lift to any representative of the full scheme center
of a vector fixed by every group point. -/
def centerTangentFactor {Z : GroupScheme (Spec R)} (z : Z ⟶ G)
    (hz : (center G).IsRepresentedBy z)
    (X : lieKernel G R) (hX : elementCentralizer G X = ⊤) : lieKernel Z R := by
  have hm := mem_center_lie_of_elementCentralizer_eq_top X hX
  let y := (hz.pointsEquiv _).symm ⟨X.val, hm⟩
  have hy : y ≫ z.hom.hom = X.val := hz.pointsEquiv_symm_comp _
  have : Mono z.hom.hom := hz.1
  refine ⟨y, mem_lieKernel_of_comp z y ?_⟩
  rw [hy]
  exact X.property

@[simp]
theorem targetMap_centerTangentFactor {Z : GroupScheme (Spec R)} (z : Z ⟶ G)
    (hz : (center G).IsRepresentedBy z)
    (X : lieKernel G R) (hX : elementCentralizer G X = ⊤) :
    targetMap z R (centerTangentFactor z hz X hX) = X := by
  apply Subtype.ext
  exact hz.pointsEquiv_symm_comp _

/-- Factoring through the full scheme center is equivalent to full actual
centralizer, without any smoothness or reducedness premise on the center. -/
theorem elementCentralizer_eq_top_iff_exists_center_tangent
    {Z : GroupScheme (Spec R)} (z : Z ⟶ G)
    (hz : (center G).IsRepresentedBy z) (X : lieKernel G R) :
    elementCentralizer G X = ⊤ ↔
      ∃ Y : lieKernel Z R, targetMap z R Y = X := by
  constructor
  · intro hX
    exact ⟨centerTangentFactor z hz X hX, targetMap_centerTangentFactor z hz X hX⟩
  · rintro ⟨Y, rfl⟩
    apply elementCentralizer_eq_top_of_mem_center_lie
    change (Y.val ≫ z.hom.hom) ∈ (center G).carrier _
    rw [← hz.2]
    exact SubgroupFunctor.mem_range.2 ⟨Y.val, rfl⟩

end Langlands.GroupScheme.Lie
