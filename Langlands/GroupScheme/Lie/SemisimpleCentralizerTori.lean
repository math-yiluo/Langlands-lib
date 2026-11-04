import Langlands.GroupScheme.Lie.CartanTangentContainment

/-! # Maximal tori in identity components of Lie-element centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G C : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth C.X.hom] [IsAffineHom C.X.hom]

local instance : CommGroup (lieKernel (identityComponent C) k) :=
  lieKernelCommGroup (identityComponent C)

local instance : Module k (Additive (lieKernel (identityComponent C) k)) :=
  lieKernelModule (identityComponent C)

namespace Lie

section Lift

variable (hstructure : NilpotentCentralTorusStatement.{u})
    (hvan : UnipotentSemisimpleStatement.{u})
    (X : lieKernel G k) (j : C ⟶ G)
    (hrep : (elementCentralizer G X).IsRepresentedBy j)
    (hj : IsClosedSubgroup j)
    (hX : Additive.ofMul X ∈ elementCentralizerLie G X)
    (hcartan : ∀ (D : GroupScheme (Spec (CommRingCat.of k)))
      (d : D ⟶ identityComponent C), IsCartanSubgroup d →
        ConnectedSpace D.X.left ∧ IsNilpotentGroupScheme D)
    (hreflect : ∀ (D : GroupScheme (Spec (CommRingCat.of k)))
      (d : D ⟶ G), IsClosedSubgroup d →
        ∀ Y : lieKernel D k, targetMap d k Y = X → IsSemisimpleElement D Y)
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ identityComponent C) (hi : IsMaximalTorus i)

include hstructure hvan hrep hj hX hcartan hreflect hi

/-- Conditional on Cartan structure and semisimplicity of closed-subgroup
lifts, every prescribed maximal torus in the centralizer's identity component
contains an actual tangent preimage of the original vector. -/
theorem exists_tangent_lift_identityComponent_elementCentralizer :
    ∃ Y : lieKernel T.toGrp k,
      targetMap (i ≫ identityComponentι C ≫ j) k Y = X := by
  let j₀ : identityComponent C ⟶ G := identityComponentι C ≫ j
  have hj₀ : IsClosedSubgroup j₀ :=
    (IdentityComponent.isClosedSubgroup_identityComponentι C).comp hj
  have : IsClosedImmersion j₀.hom.hom.left := hj₀
  have hj₀mono : Mono j₀.hom.hom := Over.mono_of_mono_left _
  have hXrange : Additive.ofMul X ∈ LinearMap.range (targetMapLinear j₀ k) := by
    rw [← hrep.lie_eq_range_identityComponent k]
    exact hX
  obtain ⟨Y₀, hY₀⟩ := hXrange
  have hY : targetMap j₀ k Y₀.toMul = X := congrArg Additive.toMul hY₀
  have hfixG : SubgroupFunctor.range (i ≫ j₀) ≤ elementCentralizer G X := by
    rw [← hrep.2]
    intro U x hx
    obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    refine SubgroupFunctor.mem_range.mpr
      ⟨(t ≫ i.hom.hom) ≫ (identityComponentι C).hom.hom, ?_⟩
    simp only [j₀, Grp.comp_hom_hom, Category.assoc]
  have hfix : SubgroupFunctor.range i ≤
      elementCentralizer (identityComponent C) Y₀.toMul :=
    range_le_elementCentralizer_of_mono j₀ hj₀mono i Y₀.toMul
      (by rwa [hY])
  have : IsAffine (identityComponent C).X.left :=
    isAffine_of_isAffineHom (identityComponent C).X.hom
  obtain ⟨D, d, hd, hdrep⟩ := exists_isCartanSubgroup_of_isMaximalTorus hi
  obtain ⟨hconn, hnil⟩ := hcartan D d hd
  have hsem : ∀ Z : lieKernel D k,
      targetMap d k Z = Y₀.toMul → IsSemisimpleElement D Z := by
    intro Z hZ
    apply hreflect D (d ≫ j₀) (hd.isClosedSubgroup.comp hj₀) Z
    rw [← hY, ← hZ]
    apply Subtype.ext
    change Z.val ≫ (d ≫ j₀).hom.hom =
      (Z.val ≫ d.hom.hom) ≫ j₀.hom.hom
    rw [Grp.comp_hom_hom, Category.assoc]
  let Y := cartanTangentFactor hstructure hvan i hi d hdrep
    hd.isClosedSubgroup hconn hnil Y₀.toMul hfix hsem
  have htorus : targetMap i k Y = Y₀.toMul :=
    targetMap_cartanTangentFactor hstructure hvan i hi d hdrep
      hd.isClosedSubgroup hconn hnil Y₀.toMul hfix hsem
  refine ⟨Y, ?_⟩
  change targetMap (i ≫ j₀) k Y = X
  rw [← hY, ← htorus]
  apply Subtype.ext
  change Y.val ≫ (i ≫ j₀).hom.hom =
    (Y.val ≫ i.hom.hom) ≫ j₀.hom.hom
  rw [Grp.comp_hom_hom, Category.assoc]

/-- The actual tangent preimage in a prescribed maximal torus of the
centralizer's identity component, under the displayed structural premises. -/
def elementCentralizerIdentityTorusFactor : lieKernel T.toGrp k :=
  Classical.choose
    (exists_tangent_lift_identityComponent_elementCentralizer
      hstructure hvan X j hrep hj hX hcartan hreflect i hi)

@[simp]
theorem targetMap_elementCentralizerIdentityTorusFactor :
    targetMap (i ≫ identityComponentι C ≫ j) k
      (elementCentralizerIdentityTorusFactor
        hstructure hvan X j hrep hj hX hcartan hreflect i hi) = X :=
  Classical.choose_spec
    (exists_tangent_lift_identityComponent_elementCentralizer
      hstructure hvan X j hrep hj hX hcartan hreflect i hi)

end Lift

end Lie

/-- The conditional Cartan tangent construction supplies the maximal-torus
preservation input used in the semisimple-centralizer induction. -/
theorem preservesMaximalTori_identityComponent_elementCentralizer_of_cartanLifts
    (hstructure : NilpotentCentralTorusStatement.{u})
    (hvan : UnipotentSemisimpleStatement.{u})
    (X : lieKernel G k) (j : C ⟶ G)
    (hrep : (Lie.elementCentralizer G X).IsRepresentedBy j)
    (hj : IsClosedSubgroup j)
    (hX : Additive.ofMul X ∈ Lie.elementCentralizerLie G X)
    (hcartan : ∀ (D : GroupScheme (Spec (CommRingCat.of k)))
      (d : D ⟶ identityComponent C), IsCartanSubgroup d →
        ConnectedSpace D.X.left ∧ IsNilpotentGroupScheme D)
    (hreflect : ∀ (D : GroupScheme (Spec (CommRingCat.of k)))
      (d : D ⟶ G), IsClosedSubgroup d →
        ∀ Y : lieKernel D k, Lie.targetMap d k Y = X →
          Lie.IsSemisimpleElement D Y) :
    PreservesMaximalTori (identityComponentι C ≫ j) := by
  intro T i hi
  exact hi.comp_identityComponent_elementCentralizer j hj hrep
    (Lie.exists_tangent_lift_identityComponent_elementCentralizer
      hstructure hvan X j hrep hj hX hcartan hreflect i hi)

end Langlands.GroupScheme
