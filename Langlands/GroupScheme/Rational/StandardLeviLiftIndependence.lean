import Langlands.GroupScheme.Rational.StandardParabolic
import Langlands.GroupScheme.Dynamic.Functoriality

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- A base point belonging to a subgroup functor preserves it by inner conjugation. -/
theorem comap_innerIso_hom_eq_of_mem (F : SubgroupFunctor G)
    {g : Over.mk (𝟙 S) ⟶ G.X} (hg : g ∈ F.carrier (Over.mk (𝟙 S))) :
    F.comap (G.innerIso g).hom = F := by
  apply ext
  intro U
  apply Subgroup.ext
  intro x
  rw [mem_comap, comp_innerIso_hom]
  have hgU : G.constantPoint g U ∈ F.carrier U :=
    F.comp_mem (Over.homMk U.hom (by simp)) hg
  rw [(F.carrier U).mul_mem_cancel_right ((F.carrier U).inv_mem hgU),
    (F.carrier U).mul_mem_cancel_left hgU]

/-- Inner conjugate images coincide when the lifts differ on the right by a point
of the subgroup functor. -/
theorem comap_innerIso_inv_eq_of_inv_mul_mem (F : SubgroupFunctor G)
    (n m : Over.mk (𝟙 S) ⟶ G.X)
    (h : n⁻¹ * m ∈ F.carrier (Over.mk (𝟙 S))) :
    F.comap (G.innerIso n).inv = F.comap (G.innerIso m).inv := by
  have hm : m = n * (n⁻¹ * m) := by simp
  conv_rhs => rw [hm, ← innerIso_inv_hom, mul_inv_rev, innerIso_mul_hom,
    comap_comp, comap_innerIso_hom_eq_of_mem F ((F.carrier _).inv_mem h)]
  rw [innerIso_inv_hom]

end SubgroupFunctor

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- On every test scheme, conjugate images of any overgroup of the whole-torus
centralizer depend only on the actual relative Weyl class of a lift. -/
theorem comap_innerIso_inv_eq_of_relativeWeyl_eq (i : T.toGrp ⟶ G)
    (F : SubgroupFunctor G) (hF : torusCentralizer i ≤ F)
    (n m : normalizerPoints i)
    (h : (QuotientGroup.mk n : relativeWeylGroup i) = QuotientGroup.mk m) :
    F.comap (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X)).inv =
      F.comap (G.innerIso (m : Over.mk (𝟙 _) ⟶ G.X)).inv := by
  apply F.comap_innerIso_inv_eq_of_inv_mul_mem
  apply hF (Over.mk (𝟙 _))
  change (n : Over.mk (𝟙 _) ⟶ G.X)⁻¹ * (m : Over.mk (𝟙 _) ⟶ G.X) ∈
    (torusCentralizer i).carrier (Over.mk (𝟙 _))
  rw [torusCentralizer_carrier_base]
  exact (QuotientGroup.eq.mp h : n⁻¹ * m ∈
    (centralizerPoints i).subgroupOf (normalizerPoints i))

/-- Conjugation of an overgroup of the whole-torus centralizer by an actual
relative Weyl element, defined independently of a normalizer lift. -/
def relativeWeylConjugateSubgroupFunctor (i : T.toGrp ⟶ G)
    (F : SubgroupFunctor G) (hF : torusCentralizer i ≤ F)
    (w : relativeWeylGroup i) : SubgroupFunctor G :=
  Quotient.liftOn' w
    (fun n : normalizerPoints i =>
      F.comap (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X)).inv)
    (fun n m h => comap_innerIso_inv_eq_of_relativeWeyl_eq i F hF n m
      (Quotient.sound' h))

@[simp] theorem relativeWeylConjugateSubgroupFunctor_mk (i : T.toGrp ⟶ G)
    (F : SubgroupFunctor G) (hF : torusCentralizer i ≤ F)
    (n : normalizerPoints i) :
    relativeWeylConjugateSubgroupFunctor i F hF (QuotientGroup.mk n) =
      F.comap (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X)).inv :=
  rfl

/-- The lift-independence clause for standard Levis, with no reductivity,
maximal-splitness, genericity or subset hypothesis. -/
theorem standardLevi_comap_innerIso_inv_eq_of_relativeWeyl_eq
    [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    (J : Set (characterLattice T)) (n m : normalizerPoints i)
    (h : (QuotientGroup.mk n : relativeWeylGroup i) = QuotientGroup.mk m) :
    (standardLevi i ν J).comap (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X)).inv =
      (standardLevi i ν J).comap (G.innerIso (m : Over.mk (𝟙 _) ⟶ G.X)).inv :=
  comap_innerIso_inv_eq_of_relativeWeyl_eq i (standardLevi i ν J)
    (torusCentralizer_le_standardLevi i ν J) n m h

end Langlands.GroupScheme
