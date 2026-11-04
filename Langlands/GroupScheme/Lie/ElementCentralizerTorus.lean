import Langlands.GroupScheme.Lie.ElementCentralizer
import Langlands.GroupScheme.Torus.MaximalTransport
import Langlands.GroupScheme.Torus.Geometry
import Langlands.GroupScheme.IdentityComponent

/-! # Tori in actual Lie-element centralizers -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Lie

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}
  {T : CommGroupScheme (Spec R)}

/-- A commutative subgroup centralizes every tangent vector in its image. -/
theorem range_le_elementCentralizer_target (i : T.toGrp ⟶ G) (X : lieKernel T.toGrp R) :
    SubgroupFunctor.range i ≤ elementCentralizer G (targetMap i R X) := by
  intro U g hg
  obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.1 hg
  intro A _ _ a
  rw [lieKernelMap_target]
  have hc : Commute (constant T.toGrp (a ≫ t))
      (lieKernelMap T.toGrp (Algebra.ofId R A) X).val := Commute.all _ _
  apply (commute_iff_eq _ _).2
  have he := congrArg (fun z => z ≫ i.hom.hom) hc.eq
  simpa only [MonObj.mul_comp, constant, affineMap_apply, lieKernelTarget_val,
    Category.assoc] using he

/-- Membership in a commutative subgroup's tangent image gives all-test
containment in the corresponding Lie-element centralizer. -/
theorem range_le_elementCentralizer_of_tangent (i : T.toGrp ⟶ G)
    {X : lieKernel G R} (hX : ∃ Y : lieKernel T.toGrp R, targetMap i R Y = X) :
    SubgroupFunctor.range i ≤ elementCentralizer G X := by
  obtain ⟨Y, rfl⟩ := hX
  exact range_le_elementCentralizer_target i Y

/-- The canonical factor of a commutative subgroup containing the tangent
vector through a representative of its Lie-element centralizer. -/
def elementCentralizerTorusFactor {C : GroupScheme (Spec R)} (j : C ⟶ G)
    {X : lieKernel G R} (hrep : (elementCentralizer G X).IsRepresentedBy j)
    (i : T.toGrp ⟶ G)
    (hX : ∃ Y : lieKernel T.toGrp R, targetMap i R Y = X) : T.toGrp ⟶ C :=
  hrep.factorHom i (range_le_elementCentralizer_of_tangent i hX)

@[simp]
theorem elementCentralizerTorusFactor_comp {C : GroupScheme (Spec R)} (j : C ⟶ G)
    {X : lieKernel G R} (hrep : (elementCentralizer G X).IsRepresentedBy j)
    (i : T.toGrp ⟶ G)
    (hX : ∃ Y : lieKernel T.toGrp R, targetMap i R Y = X) :
    elementCentralizerTorusFactor j hrep i hX ≫ j = i :=
  hrep.factorHom_comp i (range_le_elementCentralizer_of_tangent i hX)

end Lie

variable {k : Type u} [Field k]
  {G C : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth C.X.hom] [IsAffineHom C.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- If a tangent vector lies in a maximal torus of its smooth centralizer's
identity component, that torus is maximal in the ambient group. -/
theorem IsMaximalTorus.comp_identityComponent_elementCentralizer
    {i : T.toGrp ⟶ identityComponent C} (hi : IsMaximalTorus i)
    (j : C ⟶ G) (hj : IsClosedSubgroup j) {X : lieKernel G k}
    (hrep : (Lie.elementCentralizer G X).IsRepresentedBy j)
    (hX : ∃ Y : lieKernel T.toGrp k,
      Lie.targetMap (i ≫ identityComponentι C ≫ j) k Y = X) :
    IsMaximalTorus (i ≫ identityComponentι C ≫ j) := by
  let j₀ : identityComponent C ⟶ G := identityComponentι C ≫ j
  have hj₀ : IsClosedSubgroup j₀ :=
    (IdentityComponent.isClosedSubgroup_identityComponentι C).comp hj
  refine ⟨hi.1, hi.2.1.comp hj₀, ?_⟩
  intro T' i' f hT' hi' hf
  obtain ⟨Y, hY⟩ := hX
  have hY' : Lie.targetMap i' k (Lie.targetMap f k Y) = X := by
    rw [← hY]
    apply Subtype.ext
    change (Y.val ≫ f.hom.hom) ≫ i'.hom.hom =
      Y.val ≫ (i ≫ identityComponentι C ≫ j).hom.hom
    rw [Category.assoc, ← Grp.comp_hom_hom, hf]
  let c' : T'.toGrp ⟶ C := Lie.elementCentralizerTorusFactor j hrep i' ⟨_, hY'⟩
  have hc' : c' ≫ j = i' := Lie.elementCentralizerTorusFactor_comp j hrep i' ⟨_, hY'⟩
  have : ConnectedSpace T'.X.left := hT'.connectedSpace
  let q : T'.toGrp ⟶ identityComponent C := IdentityComponent.factor C c'
  have hq : q ≫ j₀ = i' := by
    dsimp only [j₀, q]
    rw [← Category.assoc, IdentityComponent.factor_identityComponentι, hc']
  have hqclosed : IsClosedSubgroup q := IsClosedSubgroup.of_comp hj₀ (by rwa [hq])
  apply hi.2.2 T' q f hT' hqclosed
  apply IdentityComponent.hom_ext_of_isOpenImmersion (identityComponentι C)
  apply hrep.hom_ext
  simpa only [j₀, Category.assoc] using
    (congrArg (fun a => f ≫ a) hq).trans hf

end Langlands.GroupScheme
