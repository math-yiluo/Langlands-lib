import Langlands.GroupScheme.Torus.RelativeCommutativity
import Langlands.GroupScheme.Torus.Relative
import Langlands.GroupScheme.Torus.MaximalAmbient
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Hypercover.Subcanonical

/-! # Commutativity of tori over an arbitrary base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- Commutativity of a group scheme descends from an étale covering family of its base. -/
theorem isCommMonObj_of_etaleCover
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (hG : ∀ i, IsCommMonObj ((baseChange (𝒰.f i)).obj G).X) :
    IsCommMonObj G.X := by
  have hle : Scheme.precoverage @Etale ≤ Scheme.fppfPrecoverage := by
    change Scheme.precoverage @Etale ≤
      Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)
    exact Scheme.precoverage_mono fun _ _ _ _ => ⟨inferInstance, inferInstance⟩
  let : (Scheme.precoverage @Etale).toGrothendieck.Subcanonical :=
    .of_le (Precoverage.toGrothendieck_mono hle)
  apply (isCommMonObj_iff_isMulCommutative _).2
  intro T
  refine ⟨⟨fun x y => ?_⟩⟩
  apply Over.OverMorphism.ext
  apply (𝒰.pullback₁ T.hom).hom_ext
  intro i
  let V : Over (𝒰.X i) := Over.mk (pullback.snd T.hom (𝒰.f i))
  let a : (Over.map (𝒰.f i)).obj V ⟶ T :=
    Over.homMk (pullback.fst T.hom (𝒰.f i)) pullback.condition
  let e := baseChangePointsEquiv (𝒰.f i) G V
  let : IsCommMonObj ((baseChange (𝒰.f i)).obj G).X := hG i
  have h : (e.symm (a ≫ x)) * (e.symm (a ≫ y)) =
      (e.symm (a ≫ y)) * (e.symm (a ≫ x)) := mul_comm _ _
  have he := congrArg e h
  simp only [map_mul, MulEquiv.apply_symm_apply] at he
  exact congrArg (fun z => z.left)
    ((MonObj.comp_mul a x y).trans (he.trans (MonObj.comp_mul a y x).symm))

namespace RelativeTorus

end RelativeTorus
end Langlands.GroupScheme
