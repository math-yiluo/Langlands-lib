import Langlands.GroupScheme.SimplyConnected.FactorMaximalTorus
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleConjugateProductGalois
import Langlands.GroupScheme.Derived.AlmostSimplePerfect
import Langlands.GroupScheme.Derived.KernelAnnihilation

/-! # Intrinsic uniqueness of retractions onto actual normal product factors -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- A perfect group scheme has no nontrivial morphism with commutative
all-test image, even when the target itself is not commutative. -/
theorem hom_eq_one_of_commute_image {S : Scheme.{u}} {A B : GroupScheme S}
    [IsSeparated B.X.hom] (hA : derivedSubgroup A = ⊤) (f : A ⟶ B)
    (hc : ∀ (U : Over S) (x y : U ⟶ A.X), Commute (x ≫ f.hom.hom) (y ≫ f.hom.hom)) :
    f.hom.hom = 1 := by
  have hk : derivedSubgroup A ≤ SubgroupFunctor.range (kernelι f) := by
    apply derivedSubgroup_le_range (kernelι f)
      (inferInstanceAs (IsClosedImmersion (kernelι f).hom.hom.left))
    intro U x y
    apply (mem_range_kernelι_iff f _).mpr
    rw [MonObj.mul_comp, MonObj.mul_comp, MonObj.mul_comp,
      GrpObj.inv_comp, GrpObj.inv_comp, (hc U x y).eq]
    group
  have hx := (mem_range_kernelι_iff f _).mp
    (hk A.X (by rw [hA]; exact Subgroup.mem_top (𝟙 A.X)))
  simpa only [Category.id_comp] using hx

namespace SimplyConnectedAlmostSimpleProduct

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (D : SimplyConnectedAlmostSimpleProduct G)

/-- Actual distinct product-factor inclusions commute on every test scheme. -/
theorem commute_distinct_inclusions (i j : D.Index) (hij : i ≠ j)
    {U : Over (Spec (CommRingCat.of k))} (x : U ⟶ (D.factor i).X) (y : U ⟶ (D.factor j).X) :
    Commute (x ≫ (D.inclusion i).hom.hom) (y ≫ (D.inclusion j).hom.hom) := by
  apply (D.commute_inclusion_iff i x _).mpr
  rw [D.inclusion_projection_points_ne j i (Ne.symm hij)]
  exact Commute.one_right x

/-- Any retraction onto the specified actual normal factor equals the
intrinsic product projection. Perfectness kills all other factor images. -/
theorem retraction_eq_projection (i : D.Index) (q : G ⟶ D.factor i)
    (hq : D.inclusion i ≫ q = 𝟙 (D.factor i)) : q = D.projection i := by
  let : IsAffineHom (D.factor i).X.hom :=
    (D.isSimplyConnected i).isSemisimple.isConnectedReductive.isAffineHom
  have hzero (j : D.Index) (hji : j ≠ i) : (D.inclusion j ≫ q).hom.hom = 1 := by
    apply hom_eq_one_of_commute_image (D.isAlmostSimple j).derivedSubgroup_eq_top
    intro U x y
    have hc := (D.commute_distinct_inclusions j i hji x
      (y ≫ (D.inclusion j ≫ q).hom.hom)).map
        ((yonedaGrp.map q).app (Opposite.op U)).hom
    change Commute ((x ≫ (D.inclusion j).hom.hom) ≫ q.hom.hom)
      (((y ≫ (D.inclusion j ≫ q).hom.hom) ≫ (D.inclusion i).hom.hom) ≫ q.hom.hom) at hc
    simpa only [Category.assoc, ← Grp.comp_hom_hom, hq,
      Grp.id_hom_hom, Category.comp_id] using hc
  apply (cancel_epi D.iso.inv).mp
  apply pi_hom_ext_of_factorInclusion D.factor
  intro j
  change D.inclusion j ≫ q = D.inclusion j ≫ D.projection i
  by_cases hji : j = i
  · subst j
    rw [hq, D.inclusion_projection]
  · apply Grp.hom_ext
    rw [hzero j hji]
    simpa only [Grp.comp_hom_hom, Category.id_comp] using
      (D.inclusion_projection_points_ne j i hji (𝟙 _)).symm

/-- A retraction transported through actual subgroup and ambient comparison
isomorphisms is exactly the selected geometric product projection. -/
theorem transported_retraction_eq_projection
    {H C : GroupScheme (Spec (CommRingCat.of k))} (i : D.Index)
    (r : H ≅ D.factor i) (e : C ≅ G) (j : H ⟶ C) (q : C ⟶ H)
    (hj : j = r.hom ≫ D.inclusion i ≫ e.inv) (hq : j ≫ q = 𝟙 H) :
    e.inv ≫ q ≫ r.hom = D.projection i := by
  apply D.retraction_eq_projection i
  have hi : r.inv ≫ j = D.inclusion i ≫ e.inv := by
    rw [hj, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (D.inclusion i), ← hi, Category.assoc,
    ← Category.assoc j, hq, Category.id_comp, Iso.inv_hom_id]

/-- Universal intrinsic uniqueness of actual normal product-factor retractions. -/
def FactorRetractionUniqueStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (D : SimplyConnectedAlmostSimpleProduct G) (i : D.Index) (q : G ⟶ D.factor i),
    D.inclusion i ≫ q = 𝟙 (D.factor i) → q = D.projection i

/-- The full scheme-theoretic argument proves the universal assertion. -/
theorem factorRetractionUnique : FactorRetractionUniqueStatement.{u} := by
  intro k _ G D i q hq
  exact D.retraction_eq_projection i q hq

end SimplyConnectedAlmostSimpleProduct
end Langlands.GroupScheme
