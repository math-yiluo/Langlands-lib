import Langlands.GroupScheme.RelativeLevi.TorusDynamicLevi
import Langlands.GroupScheme.RelativeLevi.TorusDynamicPresentationStatement
import Langlands.GroupScheme.Reductive.BaseChange

/-! # Étale local Levi witnesses along a prescribed torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.RelativeLevi

/-- A cocharacter of the prescribed commutative group dynamically presenting
the given parabolic inclusion. -/
structure TorusDynamicPresentation {S : Scheme.{u}} {G P : GroupScheme S}
    {T : CommGroupScheme S} (i : P ⟶ G) (t : T.toGrp ⟶ P) where
  cocharacter : (Gm S).toGrp ⟶ T.toGrp
  represents : (Dynamic.parabolic (cocharacter ≫ t ≫ i)).IsRepresentedBy i

namespace TorusDynamicPresentation

variable {S S' : Scheme.{u}} {G P : GroupScheme S} {T : CommGroupScheme S}
    {i : P ⟶ G} {t : T.toGrp ⟶ P}

/-- The presentation persists after an arbitrary change of base. -/
def baseChange (d : TorusDynamicPresentation i t) (b : S' ⟶ S) :
    TorusDynamicPresentation ((GroupScheme.baseChange b).map i)
      (T := (CommGroupScheme.baseChange b).obj T) ((GroupScheme.baseChange b).map t) where
  cocharacter := Dynamic.baseChangeCocharacter b d.cocharacter
  represents := by
    have h := d.represents.baseChange b
    rw [← Dynamic.parabolic_baseChange] at h
    have heq : Dynamic.baseChangeCocharacter b (d.cocharacter ≫ t ≫ i) =
        Dynamic.baseChangeCocharacter b d.cocharacter ≫
          (GroupScheme.baseChange b).map t ≫ (GroupScheme.baseChange b).map i := by
      simp only [Dynamic.baseChangeCocharacter, Functor.map_comp, Category.assoc]
    rw [heq] at h
    exact h

/-- Apply the dynamic construction to this presentation. -/
def witness (d : TorusDynamicPresentation i t)
    (hDynamic : DynamicRelativeLeviStatement.{u})
    (hRadical : RelativeUnipotentRadicalStatement.{u}) (hG : IsReductive G) :
    TorusLeviWitness t :=
  torusDynamicLeviWitness hDynamic hRadical i t d.cocharacter hG d.represents

end TorusDynamicPresentation

/-- An étale cover with prescribed-torus dynamic presentations and actual
unique Levi witnesses on its members. -/
structure EtaleTorusLeviData {S : Scheme.{u}} {G P : GroupScheme S}
    {T : CommGroupScheme S} (i : P ⟶ G) (t : T.toGrp ⟶ P) where
  cover : Scheme.Cover.{u} (Scheme.precoverage @Etale) S
  presentation : ∀ a : cover.I₀,
    TorusDynamicPresentation ((GroupScheme.baseChange (cover.f a)).map i)
      (T := (CommGroupScheme.baseChange (cover.f a)).obj T)
      ((GroupScheme.baseChange (cover.f a)).map t)
  witness : ∀ a : cover.I₀,
    TorusLeviWitness (T := (CommGroupScheme.baseChange (cover.f a)).obj T)
      ((GroupScheme.baseChange (cover.f a)).map t)

/-- Reduce the local existence and uniqueness step to the three explicit
relative structure statements. -/
def torusLeviEtaleData
    (hPresentation : RelativeTorusDynamicPresentationStatement.{u})
    (hDynamic : DynamicRelativeLeviStatement.{u})
    (hRadical : RelativeUnipotentRadicalStatement.{u})
    {S : Scheme.{u}} {G P : GroupScheme S} {T : CommGroupScheme S}
    (i : P ⟶ G) (t : T.toGrp ⟶ P) (hG : IsReductive G)
    (hP : IsRelativeParabolicSubgroup i) (hT : RelativeTorus.IsTorus T.toGrp)
    (ht : IsClosedSubgroup t) (hmax : IsFibrewiseMaximalTorus t) :
    EtaleTorusLeviData i t := by
  apply Classical.choice
  obtain ⟨𝒰, h𝒰⟩ := hPresentation S G P i T t hG hP hT ht hmax
  let d : ∀ a : 𝒰.I₀,
      TorusDynamicPresentation ((GroupScheme.baseChange (𝒰.f a)).map i)
        (T := (CommGroupScheme.baseChange (𝒰.f a)).obj T)
        ((GroupScheme.baseChange (𝒰.f a)).map t) :=
    fun a => ⟨(h𝒰 a).choose, (h𝒰 a).choose_spec⟩
  exact ⟨⟨𝒰, d, fun a => (d a).witness hDynamic hRadical (hG.baseChange (𝒰.f a))⟩⟩

end Langlands.GroupScheme.RelativeLevi
