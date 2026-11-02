import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Rational.StandardParabolic
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.HomConjugacy
import Langlands.GroupScheme.InnerAutomorphismHom
import Langlands.AlgebraicGeometry.PointTopology.RationalPointGroups

/-! # Rational-point adapters for conjugate algebraic parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [CommRing k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- At the identity test scheme, a constant base point is that point itself. -/
theorem constantPoint_rationalPoint (g : rationalPoints G) :
    G.constantPoint g (Over.mk (𝟙 (Spec (CommRingCat.of k)))) = g := by
  exact G.constantPoint_self g

/-- The rational-point map of an inner automorphism is literal conjugation. -/
theorem rationalPoints_map_innerIso (g : rationalPoints G) :
    rationalPoints.map (G.innerIso g).hom = (MulAut.conj g).toMonoidHom := by
  ext x
  rw [rationalPoints.map_apply, comp_innerIso_hom, constantPoint_rationalPoint]
  rfl

/-- The inverse scheme inner automorphism gives inverse conjugation on points. -/
theorem rationalPoints_map_innerIso_inv (g : rationalPoints G) :
    rationalPoints.map (G.innerIso g).inv = (MulAut.conj g⁻¹).toMonoidHom := by
  rw [← G.innerIso_inv_hom, rationalPoints_map_innerIso]

namespace SubgroupFunctor

/-- The actual base-valued points of a subgroup functor, inside `G(k)`. -/
abbrev rationalPoints (P : SubgroupFunctor G) : Subgroup (GroupScheme.rationalPoints G) :=
  P.carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))

/-- The points of a represented subgroup are the range of its actual point map. -/
theorem rationalPoints_range (j : H ⟶ G) :
    (range j).rationalPoints = (GroupScheme.rationalPoints.map j).range := rfl

/-- A represented subgroup functor has the image of its representing point map. -/
theorem rationalPoints_eq_range {P : SubgroupFunctor G} {j : H ⟶ G}
    (hP : P.IsRepresentedBy j) :
    P.rationalPoints = (GroupScheme.rationalPoints.map j).range := by
  rw [← hP.2, rationalPoints_range]

/-- Taking actual base-valued points commutes with preimage. -/
theorem rationalPoints_comap (P : SubgroupFunctor G) (j : H ⟶ G) :
    (P.comap j).rationalPoints =
      P.rationalPoints.comap (GroupScheme.rationalPoints.map j) := rfl

/-- Preimage under `Int(g)` has the `g⁻¹ P(k) g` orientation. -/
theorem rationalPoints_comap_innerIso_hom (P : SubgroupFunctor G)
    (g : GroupScheme.rationalPoints G) :
    (P.comap (G.innerIso g).hom).rationalPoints =
      P.rationalPoints.comap (MulAut.conj g).toMonoidHom := by
  rw [rationalPoints_comap, rationalPoints_map_innerIso]

/-- In image form, preimage under `Int(g)` is `g⁻¹ P(k) g`. -/
theorem rationalPoints_comap_innerIso_hom_eq_map (P : SubgroupFunctor G)
    (g : GroupScheme.rationalPoints G) :
    (P.comap (G.innerIso g).hom).rationalPoints =
      P.rationalPoints.map (MulAut.conj g⁻¹).toMonoidHom := by
  rw [rationalPoints_comap_innerIso_hom]
  ext x
  simp only [Subgroup.mem_comap, Subgroup.mem_map_equiv,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.conj_symm_apply, inv_inv]

/-- Preimage under `Int(g)⁻¹` is the image `g P(k) g⁻¹`. -/
theorem rationalPoints_comap_innerIso_inv (P : SubgroupFunctor G)
    (g : GroupScheme.rationalPoints G) :
    (P.comap (G.innerIso g).inv).rationalPoints =
      P.rationalPoints.map (MulAut.conj g).toMonoidHom := by
  rw [← G.innerIso_inv_hom, rationalPoints_comap_innerIso_hom]
  ext x
  simp only [Subgroup.mem_comap, Subgroup.mem_map_equiv,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.conj_symm_apply, inv_inv]

/-- Membership in the classification convention tests `g x g⁻¹` in `P(k)`. -/
theorem mem_rationalPoints_comap_innerIso_hom (P : SubgroupFunctor G)
    (g x : GroupScheme.rationalPoints G) :
    x ∈ (P.comap (G.innerIso g).hom).rationalPoints ↔
      g * x * g⁻¹ ∈ P.rationalPoints := by
  rw [rationalPoints_comap_innerIso_hom, Subgroup.mem_comap]
  rfl

end SubgroupFunctor

/-- Conjugating an actual algebraic subgroup inclusion conjugates its rational-point range. -/
theorem rationalPoints_range_comp_innerIso (j : H ⟶ G) (g : rationalPoints G) :
    (rationalPoints.map (j ≫ (G.innerIso g).hom)).range =
      (rationalPoints.map j).range.map (MulAut.conj g).toMonoidHom := by
  ext x
  change (∃ y, (y ≫ j.hom.hom) ≫ (G.innerIso g).hom.hom.hom = x) ↔ _
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y ≫ j.hom.hom, ⟨y, rfl⟩, ?_⟩
    simpa only [comp_innerIso_hom, constantPoint_rationalPoint,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, rationalPoints.map_apply] using hy
  · rintro ⟨z, ⟨y, rfl⟩, hz⟩
    refine ⟨y, ?_⟩
    simpa only [comp_innerIso_hom, constantPoint_rationalPoint,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, rationalPoints.map_apply] using hz

namespace Dynamic

/-- On actual rational points, the dynamic parabolic of a conjugate cocharacter
is the image under conjugation by the same rational point. -/
theorem rationalPoints_parabolic_conjugate
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (g : rationalPoints G) :
    (parabolic (χ ≫ (G.innerIso g).hom)).rationalPoints =
      (parabolic χ).rationalPoints.map (MulAut.conj g).toMonoidHom := by
  have h := parabolic_eq_comap_of_iso χ (G.innerIso g)
  have hc := congrArg
    (fun P : SubgroupFunctor G => P.comap (G.innerIso g).inv) h
  rw [← SubgroupFunctor.comap_comp, Iso.inv_hom_id, SubgroupFunctor.comap_id] at hc
  rw [← hc, SubgroupFunctor.rationalPoints_comap_innerIso_inv]

end Dynamic

section Standard

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) (J : Set (characterLattice T))

/-- The standard-parabolic classification convention gives `g⁻¹ P_J(k) g`. -/
theorem standardParabolicPoints_comap_innerIso_hom (g : rationalPoints G) :
    ((standardParabolic i ν J).comap (G.innerIso g).hom).rationalPoints =
      (standardParabolicPoints i ν J).map (MulAut.conj g⁻¹).toMonoidHom :=
  SubgroupFunctor.rationalPoints_comap_innerIso_hom_eq_map _ g

/-- The forward conjugate of a standard parabolic has points `g P_J(k) g⁻¹`. -/
theorem standardParabolicPoints_comap_innerIso_inv (g : rationalPoints G) :
    ((standardParabolic i ν J).comap (G.innerIso g).inv).rationalPoints =
      (standardParabolicPoints i ν J).map (MulAut.conj g).toMonoidHom :=
  SubgroupFunctor.rationalPoints_comap_innerIso_inv _ g

end Standard

section Topology

open Langlands.AlgebraicGeometry.PointTopology

variable (G : GroupScheme (Spec (CommRingCat.of k)))
  [TopologicalSpace k] [IsTopologicalRing k]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- Conjugation on actual rational points is a group homeomorphism for the
canonical evaluation topology. -/
def rationalPointsConjHomeomorph (g : rationalPoints G) :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology k G.X
    rationalPoints G ≃ₜ* rationalPoints G := by
  letI : TopologicalSpace (rationalPoints G) := rationalPointTopology k G.X
  letI : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup k G
  exact
    { MulAut.conj g with
      continuous_toFun := IsTopologicalGroup.continuous_conj g
      continuous_invFun := by
        change Continuous (fun h : rationalPoints G => g⁻¹ * h * g)
        exact (continuous_const.mul continuous_id).mul continuous_const }

@[simp] theorem rationalPointsConjHomeomorph_apply (g x : rationalPoints G) :
    rationalPointsConjHomeomorph G g x = g * x * g⁻¹ :=
  rfl

end Topology

end Langlands.GroupScheme
