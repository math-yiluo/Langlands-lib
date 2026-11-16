import Langlands.GroupScheme.Dynamic.FiberwiseContainment
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # Recovering a cocharacter centralizer from its residue fibres -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.Dynamic

variable {S : Scheme.{u}} {G C : GroupScheme S} {T : CommGroupScheme S}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [Smooth T.X.hom]
    (i : T.toGrp ⟶ G) [Mono i.hom.hom]
    (χT : (Gm S).toGrp ⟶ T.toGrp)
    {j : C ⟶ G} (hj : (centralizer (χT ≫ i)).IsRepresentedBy j)
    (hf : ∀ s : S,
      centralizer (baseChangeCocharacter (S.fromSpecResidueField s) (χT ≫ i)) =
        SubgroupFunctor.range ((GroupScheme.baseChange (S.fromSpecResidueField s)).map i))

/-- The canonical map from a smooth commutative subgroup to a represented
cocharacter centralizer is an isomorphism if it is so on all residue fibres. -/
def torusFactorIsoOfResidueFibres : T.toGrp ≅ C := by
  let f := torusFactor i χT hj
  have hcomp : f ≫ j = i := torusFactor_comp i χT hj
  have : Smooth C.X.hom :=
    ((dynamicBaseSmoothConnected S G (χT ≫ i) C j).2.2 hj).1
  have hfib : ∀ s : S,
      IsIso ((Over.pullback (S.fromSpecResidueField s)).map f.hom.hom).left := by
    intro s
    let b := S.fromSpecResidueField s
    let B := GroupScheme.baseChange b
    have hjB : (centralizer (baseChangeCocharacter b (χT ≫ i))).IsRepresentedBy
        (B.map j) :=
      isRepresentedBy_centralizer_baseChange b _ hj
    have hiB : (SubgroupFunctor.range (B.map i)).IsRepresentedBy (B.map i) := by
      have hi : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨inferInstance, rfl⟩
      exact ⟨(hi.baseChange b).1, rfl⟩
    have hiC : (centralizer (baseChangeCocharacter b (χT ≫ i))).IsRepresentedBy
        (B.map i) := by
      rw [hf s]
      exact hiB
    let e := hiC.isoOfIsRepresentedBy hjB
    have he : B.map f = e.hom := by
      apply hjB.hom_ext
      rw [SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp,
        ← Functor.map_comp, hcomp]
    have : IsIso (B.map f) := by rw [he]; infer_instance
    exact Functor.map_isIso (Grp.forget₂Mon _ ⋙ Mon.forget _ ⋙ Over.forget _) (B.map f)
  have : IsIso f.hom.hom.left :=
    DynamicContainment.isIso_of_residueFibres f.hom.hom hfib
  have : IsIso ((Over.forget S).map f.hom.hom) := ‹IsIso f.hom.hom.left›
  have : IsIso f.hom.hom := isIso_of_reflects_iso _ (Over.forget S)
  have : IsIso ((Mon.forget _).map f.hom) := ‹IsIso f.hom.hom›
  have : IsIso f.hom := isIso_of_reflects_iso _ (Mon.forget _)
  have : IsIso ((Grp.forget₂Mon _).map f) := ‹IsIso f.hom›
  have : IsIso f := isIso_of_reflects_iso _ (Grp.forget₂Mon _)
  exact asIso f

@[reassoc (attr := simp)]
theorem torusFactorIsoOfResidueFibres_hom_comp :
    (torusFactorIsoOfResidueFibres i χT hj hf).hom ≫ j = i :=
  torusFactor_comp i χT hj

include hf in
/-- Equality with a smooth commutative subgroup can be checked on the residue
fibres of a cocharacter centralizer in a smooth affine group. -/
theorem centralizer_eq_range_of_residueFibres :
    centralizer (χT ≫ i) = SubgroupFunctor.range i := by
  obtain ⟨C, j, -, -, hj⟩ := (dynamicBaseRepresentability S G (χT ≫ i)).2.2
  let e := torusFactorIsoOfResidueFibres i χT hj hf
  have he : e.hom ≫ j = i := torusFactorIsoOfResidueFibres_hom_comp i χT hj hf
  rw [← hj.2, ← he, SubgroupFunctor.range_iso_comp]

end Langlands.GroupScheme.Dynamic
