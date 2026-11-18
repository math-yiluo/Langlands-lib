import Langlands.GroupScheme.PointCentralizer
import Langlands.GroupScheme.Descent.GaloisClosedSubgroups
import Langlands.GroupScheme.Descent.GaloisSubgroupTransport
import Langlands.GroupScheme.Torus.MaximalDescent
import Langlands.GroupScheme.IntegralModel

/-! # Descent of a maximal torus that centralizes a Galois point -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false in
/-- A coefficient map that fixes or inverts the point preserves its all-test centralizer. -/
theorem descentTransport_pointCentralizer_of_eq_or_inv {B S : Scheme.{u}}
    (b : S ⟶ B) (a : S ⟶ S) (ha : a ≫ b = b) (G : GroupScheme B)
    (y : Over.mk b ⟶ G.X)
    (h : (Over.homMk a ha : Over.mk b ⟶ Over.mk b) ≫ y = y ∨
      (Over.homMk a ha : Over.mk b ⟶ Over.mk b) ≫ y = y⁻¹) :
    SubgroupFunctor.descentTransport b a ha G
        (((baseChange b).obj G).pointCentralizer ((baseChangeBasePointsEquiv b G).symm y)) =
      ((baseChange b).obj G).pointCentralizer ((baseChangeBasePointsEquiv b G).symm y) := by
  ext T x
  rw [SubgroupFunctor.mem_descentTransport_iff_descentPoint]
  simp only [mem_pointCentralizer_baseChange_iff, baseChangePointsEquiv_descentPoint]
  let e := (descentTestIso b a ha T).inv
  let r : (Over.map b).obj T ⟶ Over.mk b := Over.homMk T.hom (by simp)
  let q : Over.mk b ⟶ Over.mk b := Over.homMk a ha
  let c := baseChangePointsEquiv b G T x
  have hr : (Over.homMk (U := (Over.map b).obj ((Over.map a).obj T))
      (V := Over.mk b) ((Over.map a).obj T).hom (by simp)) = e ≫ r ≫ q := by
    apply Over.OverMorphism.ext
    change T.hom ≫ a = 𝟙 _ ≫ T.hom ≫ a
    rw [Category.id_comp]
  rw [hr]
  change Commute (e ≫ c) ((e ≫ r ≫ q) ≫ y) ↔ Commute c (r ≫ y)
  have hcomm : Commute (e ≫ c) (e ≫ r ≫ y) ↔ Commute c (r ≫ y) := by
    change (e ≫ c) * (e ≫ (r ≫ y)) = (e ≫ (r ≫ y)) * (e ≫ c) ↔ _
    rw [← MonObj.comp_mul, ← MonObj.comp_mul, cancel_epi]
    rfl
  simp only [Category.assoc]
  rcases h with h | h
  · rw [show q ≫ y = y from h]
    exact hcomm
  · rw [show q ≫ y = y⁻¹ from h, GrpObj.comp_inv, GrpObj.comp_inv, Commute.inv_right_iff]
    exact hcomm

section Field

variable {K M : Type u} [Field K] [Field M] [Algebra K M]
  [FiniteDimensional K M] [IsGalois K M]
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of M))}

set_option backward.isDefEq.respectTransparency false in
/-- If the centralizer of a point is a geometric maximal torus and every
coefficient automorphism fixes or inverts the point, it factors through
a maximal torus over the original field. -/
theorem exists_maximalTorus_factor_of_galois_centralizer
    (y : ringTest K M ⟶ G.X)
    (j : T.toGrp ⟶ (baseChange (algebraBaseMap K M)).obj G)
    (hj : IsMaximalTorus j)
    (hc : SubgroupFunctor.range j = ((baseChange (algebraBaseMap K M)).obj G).pointCentralizer
      ((baseChangeBasePointsEquiv (algebraBaseMap K M) G).symm y))
    (h : ∀ σ : M ≃ₐ[K] M, ringTestMap K σ.toAlgHom ≫ y = y ∨
      ringTestMap K σ.toAlgHom ≫ y = y⁻¹) :
    ∃ (T₀ : CommGroupScheme (Spec (CommRingCat.of K))) (i : T₀.toGrp ⟶ G),
      IsMaximalTorus i ∧ ∃ t : ringTest K M ⟶ T₀.X, t ≫ i.hom.hom = y := by
  let b := algebraBaseMap K M
  have hd := hj.2.1.overlap_range_eq_of_galois_range_eq (fun σ => by
    rw [← SubgroupFunctor.descentTransport_range, hc]
    exact descentTransport_pointCentralizer_of_eq_or_inv b (galoisBaseMap K M σ)
      (galoisBaseMap_over K M σ) G y (h σ))
  obtain ⟨T₀, i, e, hi, -, he⟩ := hj.exists_descent_of_overlap_range_eq hd
  let z := (baseChangeBasePointsEquiv b G).symm y
  have hz : z ∈ (SubgroupFunctor.range j).carrier (Over.mk (𝟙 _)) := by
    rw [hc, mem_pointCentralizer]
    change z * (toUnit (Over.mk (𝟙 _)) ≫ z) = (toUnit (Over.mk (𝟙 _)) ≫ z) * z
    rw [toUnit_unique (toUnit (Over.mk (𝟙 (Spec (CommRingCat.of M))))) (𝟙 _),
      Category.id_comp]
  obtain ⟨t, ht⟩ := SubgroupFunctor.mem_range.mp hz
  refine ⟨T₀, i, hi, baseChangeBasePointsEquiv b T₀.toGrp (t ≫ e.inv.hom.hom), ?_⟩
  rw [← baseChangeBasePointsEquiv_comp, he, Grp.comp_hom_hom, Category.assoc,
    ← Category.assoc e.inv.hom.hom e.hom.hom.hom, ← Grp.comp_hom_hom, Iso.inv_hom_id,
    Grp.id_hom_hom, Category.id_comp, ht, MulEquiv.apply_symm_apply]

end Field

/-- A Galois point with maximal torus centralizer and fixed up to inversion
factors through a maximal torus over the base field. -/
def GaloisToralPointDescentStatement : Prop :=
  ∀ (K M : Type u) [Field K] [Field M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    (y : ringTest K M ⟶ G.X) (T : CommGroupScheme (Spec (CommRingCat.of M)))
    (j : T.toGrp ⟶ (baseChange (algebraBaseMap K M)).obj G),
    IsMaximalTorus j →
    SubgroupFunctor.range j = ((baseChange (algebraBaseMap K M)).obj G).pointCentralizer
        ((baseChangeBasePointsEquiv (algebraBaseMap K M) G).symm y) →
    (∀ σ : M ≃ₐ[K] M, ringTestMap K σ.toAlgHom ≫ y = y ∨
      ringTestMap K σ.toAlgHom ≫ y = y⁻¹) →
    ∃ (T₀ : CommGroupScheme (Spec (CommRingCat.of K))) (i : T₀.toGrp ⟶ G),
      IsMaximalTorus i ∧ ∃ t : ringTest K M ⟶ T₀.X, t ≫ i.hom.hom = y

theorem galoisToralPointDescent : GaloisToralPointDescentStatement.{u} := by
  intro K M _ _ _ _ _ G _ y T j hj hc h
  exact exists_maximalTorus_factor_of_galois_centralizer y j hj hc h

end Langlands.GroupScheme
