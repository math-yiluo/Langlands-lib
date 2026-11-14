import Langlands.GroupScheme.Torus.Relative
import Langlands.GroupScheme.Torus.MaximalAmbient
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Commutativity of relative tori -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeTorus

private theorem hom_ext_etaleCover {X Y : Scheme.{u}}
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) X) (f g : X ⟶ Y)
    (h : ∀ j, 𝒰.f j ≫ f = 𝒰.f j ≫ g) : f = g := by
  let 𝒱 := 𝒰.changeProp (Q := @Flat ⊓ @LocallyOfFinitePresentation)
    (fun j => ⟨inferInstance, inferInstance⟩)
  have hs : Presieve.IsSheafFor (yoneda.obj Y) (Presieve.ofArrows 𝒰.X 𝒰.f) :=
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      (J := Scheme.fppfTopology) (yoneda.obj Y)).isSheafFor _
        (Precoverage.generate_mem_toGrothendieck 𝒱.mem₀)
  apply hs.isSeparatedFor.ext
  rintro _ _ ⟨j⟩
  exact h j

/-- Every relative torus is commutative, by descent from its actual étale
split-torus cover. -/
theorem IsTorus.isCommMonObj {S : Scheme.{u}} {G : GroupScheme S}
    (hG : IsTorus G) : IsCommMonObj G.X := by
  obtain ⟨𝒰, h𝒰⟩ := hG
  apply (isCommMonObj_iff_isMulCommutative _).2
  intro U
  refine ⟨⟨fun x y => ?_⟩⟩
  apply Over.OverMorphism.ext
  apply hom_ext_etaleCover (𝒰.pullback₁ U.hom)
  intro j
  let V : Over (𝒰.X j) := Over.mk (pullback.snd U.hom (𝒰.f j))
  let a : (Over.map (𝒰.f j)).obj V ⟶ U :=
    Over.homMk (pullback.fst U.hom (𝒰.f j)) pullback.condition
  let : IsCommMonObj ((GroupScheme.baseChange (𝒰.f j)).obj G).X := (h𝒰 j).isCommMonObj
  let E := baseChangePointsEquiv (𝒰.f j) G V
  have hc := congrArg E (mul_comm (E.symm (a ≫ x)) (E.symm (a ≫ y)))
  simp only [map_mul, MulEquiv.apply_symm_apply] at hc
  rw [← MonObj.comp_mul, ← MonObj.comp_mul] at hc
  exact congrArg CommaMorphism.left hc

/-- The same actual relative torus, with its descended commutative group law
made explicit. -/
def IsTorus.commGroupScheme {S : Scheme.{u}} {G : GroupScheme S}
    (hG : IsTorus G) : CommGroupScheme S :=
  { G with comm := hG.isCommMonObj }

@[simp]
theorem IsTorus.commGroupScheme_toGrp {S : Scheme.{u}} {G : GroupScheme S}
    (hG : IsTorus G) : hG.commGroupScheme.toGrp = G := rfl

end Langlands.GroupScheme.RelativeTorus
