import Langlands.AlgebraicGeometry.Picard.PresheafLineBundle
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

/-! # The overlap scheme of a local presheaf representer -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard.LocalRepresenter

variable {S U : Scheme.{u}} (p : U ⟶ S)
    {F : (Over S)ᵒᵖ ⥤ Type v} {M : Over U}
    (e : ((Over.map p).op ⋙ F).RepresentableBy M)

/-- The local representing chart viewed over the original base. -/
abbrev chart : Over S := (Over.map p).obj M

/-- The universal family of the local chart, over the original base. -/
def family : F.obj (op (chart p (M := M))) := e.homEquiv (𝟙 M)

/-- A local chart together with a second lift to the covering base. -/
abbrev overlap : Scheme.{u} := pullback (M.hom ≫ p) p

/-- The overlap viewed over the second covering-base coordinate. -/
abbrev overlapOver : Over U := Over.mk (pullback.snd (M.hom ≫ p) p)

/-- The first chart projection over the original base. -/
def firstOver : (Over.map p).obj (overlapOver p (M := M)) ⟶ chart p (M := M) :=
  Over.homMk (pullback.fst (M.hom ≫ p) p) pullback.condition

/-- The second projection classifies the restricted first universal family. -/
def secondOver : overlapOver p (M := M) ⟶ M :=
  e.homEquiv.symm (F.map (firstOver p).op (family p e))

/-- The first scheme projection. -/
abbrev first : overlap p (M := M) ⟶ M.left := pullback.fst (M.hom ≫ p) p

/-- The second scheme projection. -/
def second : overlap p (M := M) ⟶ M.left := (secondOver p e).left

/-- The two chart projections classify the same family. -/
theorem family_eq :
    F.map (firstOver p).op (family p e) =
      F.map ((Over.map p).map (secondOver p e)).op (family p e) := by
  exact (e.homEquiv.apply_symm_apply _).symm.trans (e.homEquiv_eq _)

/-- Lift a map to the first chart with a chosen covering-base coordinate. -/
def lift {T : Over U} (a : (Over.map p).obj T ⟶ chart p (M := M)) :
    T ⟶ overlapOver p (M := M) :=
  Over.homMk (pullback.lift a.left T.hom a.w) (pullback.lift_snd _ _ _)

@[simp]
theorem lift_first {T : Over U} (a : (Over.map p).obj T ⟶ chart p (M := M)) :
    (Over.map p).map (lift p a) ≫ firstOver p = a := by
  apply Over.OverMorphism.ext
  exact pullback.lift_fst _ _ _

/-- The second projection of a lift is the unique local classifier. -/
theorem lift_second {T : Over U} (a : (Over.map p).obj T ⟶ chart p (M := M)) :
    lift p a ≫ secondOver p e = e.homEquiv.symm (F.map a.op (family p e)) := by
  apply e.homEquiv.injective
  rw [e.homEquiv_comp, e.homEquiv.apply_symm_apply, e.homEquiv_eq (secondOver p e)]
  change F.map ((Over.map p).map (lift p a)).op
    (F.map ((Over.map p).map (secondOver p e)).op (family p e)) = _
  rw [← family_eq p e, ← Functor.map_comp_apply]
  change F.map ((Over.map p).map (lift p a) ≫ firstOver p).op (family p e) = _
  rw [lift_first]

/-- A matching second chart map is recovered by the overlap lift. -/
theorem lift_second_of {T : Over U} (a : (Over.map p).obj T ⟶ chart p (M := M))
    (b : T ⟶ M) (h : F.map a.op (family p e) = e.homEquiv b) :
    lift p a ≫ secondOver p e = b := by
  rw [lift_second, h, e.homEquiv.symm_apply_apply]

end Langlands.AlgebraicGeometry.Picard.LocalRepresenter
