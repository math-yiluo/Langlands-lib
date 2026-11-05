import Langlands.GroupScheme.Dynamic.RelativeProperAffineExtension
import Langlands.GroupScheme.CentralIsogeny.CommutatorDescent
import Langlands.GroupScheme.Dynamic.Functoriality

/-! # Rational contracting points lift through a central isogeny -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme


namespace Dynamic

variable {k : Type u} [Field k]
    {C G : GroupScheme (Spec (CommRingCat.of k))}
    [C.X.left.IsSeparated] [G.X.left.IsSeparated]
    (q : C ⟶ G) (hq : IsCentralIsogeny q)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)

include hq

/-- Every contracting field point lifts through a central isogeny. -/
theorem exists_lift_of_mem_unipotent
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (hg : g ∈ (unipotent χ).carrier (Over.mk (𝟙 _))) :
    ∃ g' : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ C.X, g' ≫ q.hom.hom = g := by
  have : IsFinite q.hom.hom.left := hq.isFinite
  have : Flat q.hom.hom.left := hq.flat
  have : Surjective q.hom.hom.left := hq.surjective
  rcases hg with ⟨e, he, he0⟩
  let T := Over.mk (𝟙 (Spec (CommRingCat.of k)))
  let a : T ⊗ (Gm (Spec (CommRingCat.of k))).X ⟶ G.X :=
    snd T _ ≫ χ.hom.hom
  let b : T ⊗ (Gm (Spec (CommRingCat.of k))).X ⟶ G.X := fst T _ ≫ g
  let c := lift a b ≫ CommutatorDescent.hom q hq.isCentral_kernelι
  let r : T ⊗ AffineLine.scheme (Spec (CommRingCat.of k)) ⟶ G.X :=
    e * (fst T _ ≫ g)⁻¹
  have hc : c ≫ q.hom.hom = T ◁ AffineLine.unitInclusion _ ≫ r := by
    dsimp only [c, r]
    rw [Category.assoc, CommutatorDescent.hom_comp, commutatorMap_lift]
    simp only [Grp.id_hom_hom, Category.comp_id]
    rw [MonObj.comp_mul, GrpObj.comp_inv, he, whiskerLeft_fst_assoc]
    rfl
  obtain ⟨r', _, hr'⟩ := AffineLine.exists_base_lift_of_isProper q.hom.hom r c hc
  refine ⟨(evalZero r')⁻¹, ?_⟩
  rw [GrpObj.inv_comp, ← evalZero_comp, hr']
  dsimp only [r]
  rw [evalZero_mul, evalZero_inv, evalZero_fst, he0, one_mul, inv_inv]

/-- A chosen actual lift of a contracting rational point through the central cover. -/
def centralIsogenyLift
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (hg : g ∈ (unipotent χ).carrier (Over.mk (𝟙 _))) :
    Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ C.X :=
  (exists_lift_of_mem_unipotent q hq χ g hg).choose

/-- The chosen lift has the original rational point as its exact composite. -/
theorem centralIsogenyLift_comp
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (hg : g ∈ (unipotent χ).carrier (Over.mk (𝟙 _))) :
    centralIsogenyLift q hq χ g hg ≫ q.hom.hom = g :=
  (exists_lift_of_mem_unipotent q hq χ g hg).choose_spec

end Dynamic

end Langlands.GroupScheme
