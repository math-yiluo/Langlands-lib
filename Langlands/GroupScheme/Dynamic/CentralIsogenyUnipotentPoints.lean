import Langlands.GroupScheme.Dynamic.CentralIsogenyRationalLift
import Langlands.GroupScheme.Dynamic.LimitMap
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # Rational contracting subgroups under a central isogeny -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

section ArbitraryBase

variable {S : Scheme.{u}} {C G : GroupScheme S}
    (q : C ⟶ G) (χ : (Gm S).toGrp ⟶ C)

/-- Restriction of the actual point map to the contracting subgroups. -/
def unipotentPointsMap (T : Over S) :
    (unipotent χ).carrier T →* (unipotent (χ ≫ q)).carrier T where
  toFun g := ⟨(g : T ⟶ C.X) ≫ q.hom.hom, unipotent_le_comap χ q T g.2⟩
  map_one' := Subtype.ext (MonObj.one_comp _)
  map_mul' _g _h := Subtype.ext (MonObj.mul_comp _ _ _)

@[simp] theorem unipotentPointsMap_coe (T : Over S) (g : (unipotent χ).carrier T) :
    (unipotentPointsMap q χ T g : T ⟶ G.X) = (g : T ⟶ C.X) ≫ q.hom.hom := rfl

/-- The full central kernel meets the contracting subgroup trivially. -/
theorem eq_one_of_mem_unipotent_of_comp_eq_one [IsSeparated C.X.hom]
    (hq : IsCentral (kernelι q)) {T : Over S} {g : T ⟶ C.X}
    (hg : g ∈ (unipotent χ).carrier T) (hgq : g ≫ q.hom.hom = 1) : g = 1 := by
  have hz := center_le_dynamicCentralizer χ T ((isCentral_kernelι_iff q).mp hq T g hgq)
  exact (hasLimit_of_mem_centralizer χ hz).unique χ hg

/-- A homomorphism with central full kernel is injective on every contracting subgroup. -/
theorem unipotentPointsMap_injective [IsSeparated C.X.hom]
    (hq : IsCentral (kernelι q)) (T : Over S) :
    Function.Injective (unipotentPointsMap q χ T) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply Subtype.ext
  exact eq_one_of_mem_unipotent_of_comp_eq_one q χ hq g.2 (congrArg Subtype.val hg)

end ArbitraryBase

section Field

variable {k : Type u} [Field k] {C G : GroupScheme (Spec (CommRingCat.of k))}
    [C.X.left.IsSeparated] [G.X.left.IsSeparated]
    (q : C ⟶ G) (hq : IsCentralIsogeny q)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ C)

include hq

/-- Every rational contracting point has a lift contracting for the supplied cocharacter. -/
theorem exists_unipotent_lift
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (hg : g ∈ (unipotent (χ ≫ q)).carrier (Over.mk (𝟙 _))) :
    ∃ g' : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ C.X,
      g' ∈ (unipotent χ).carrier (Over.mk (𝟙 _)) ∧ g' ≫ q.hom.hom = g := by
  have : IsFinite q.hom.hom.left := hq.isFinite
  obtain ⟨g', hg'⟩ := exists_lift_of_mem_unipotent q hq (χ ≫ q) g hg
  obtain ⟨e, he, he0⟩ := hg
  obtain ⟨e', he', he'q⟩ := AffineLine.exists_base_lift_of_isProper q.hom.hom e
    (orbit χ g') (by rw [← orbit_comp_hom, hg']; exact he.symm)
  have hlim : HasLimit χ g' (evalZero e') := ⟨e', he', rfl⟩
  have hlq : evalZero e' ≫ q.hom.hom = 1 := by
    rw [← evalZero_comp, he'q, he0]
  have hlz : evalZero e' ∈ (centralizer χ).carrier (Over.mk (𝟙 _)) :=
    center_le_dynamicCentralizer χ _ (hq.mem_center_of_comp_eq_one hlq)
  refine ⟨g' * (evalZero e')⁻¹, ?_, ?_⟩
  · have h := hlim.mul χ (hasLimit_of_mem_centralizer χ hlz).inv
    change HasLimit χ (g' * (evalZero e')⁻¹) 1
    simpa only [mul_inv_cancel] using h
  · rw [MonObj.mul_comp, GrpObj.inv_comp, hg', hlq, inv_one, mul_one]

/-- The actual rational point map is surjective on the contracting subgroup. -/
theorem unipotentPointsMap_surjective :
    Function.Surjective (unipotentPointsMap q χ (Over.mk (𝟙 _))) := by
  intro g
  obtain ⟨g', hg', hg'q⟩ := exists_unipotent_lift q hq χ g g.2
  exact ⟨⟨g', hg'⟩, Subtype.ext hg'q⟩

/-- A central isogeny identifies rational contracting subgroups, for an actual source
cocharacter and its composite with the isogeny. -/
def centralIsogenyUnipotentPointsEquiv :
    (unipotent χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ≃*
      (unipotent (χ ≫ q)).carrier (Over.mk (𝟙 _)) :=
  MulEquiv.ofBijective (unipotentPointsMap q χ (Over.mk (𝟙 _)))
    ⟨unipotentPointsMap_injective q χ hq.isCentral_kernelι _,
      unipotentPointsMap_surjective q hq χ⟩

/-- The equivalence is the restriction of the original isogeny on rational points. -/
@[simp] theorem centralIsogenyUnipotentPointsEquiv_coe
    (g : (unipotent χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    (centralIsogenyUnipotentPointsEquiv q hq χ g :
      Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) =
      (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ C.X) ≫ q.hom.hom := rfl

end Field

end Langlands.GroupScheme.Dynamic
