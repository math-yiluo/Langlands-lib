import Langlands.GroupScheme.Rational.SteinbergCanonicalRepresentatives
import Langlands.GroupScheme.Rational.RootFactorPairGaloisTransport

/-! # Coefficient transport of canonical simple-reflection points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option autoImplicit false

namespace RelativeRoot

section ChangeTorus

variable {k : Type u} [Field k]
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {i : T.toGrp ⟶ G} {j : T'.toGrp ⟶ G}
    {a : characterLattice T} {x : rationalPoints G}
    {q : rationalPoints G × rationalPoints G}

/-- Changing the acting torus by its actual isomorphism preserves both
ordered factors and the middle point. -/
theorem IsOppositeFactorPair.changeTorus (e : T ≅ T')
    (h : i = CommGroupScheme.groupHom e.hom ≫ j)
    (hq : IsOppositeFactorPair i a x q) :
    IsOppositeFactorPair j (characterLattice.congr e a) x q := by
  have hs : i ≫ (𝟙 G) = CommGroupScheme.groupHom e.hom ≫ j := by
    simpa only [Category.comp_id] using h
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Grp.id_hom_hom, Category.comp_id, map_neg] using
      comp_mem_subgroup_of_transport e (𝟙 G) hs (-a) hq.1
  · simpa only [Grp.id_hom_hom, Category.comp_id, map_neg] using
      comp_mem_subgroup_of_transport e (𝟙 G) hs (-a) hq.2.1
  · simpa only [Iso.refl_hom, Grp.id_hom_hom, Category.comp_id] using
      (mem_normalizerPoints_transport_iff e (Iso.refl G) hs
        (q.1 * x * q.2)).mpr hq.2.2

/-- The complete opposite-pair predicate is unchanged by the same actual
torus identification. -/
theorem isOppositeFactorPair_changeTorus_iff (e : T ≅ T')
    (h : i = CommGroupScheme.groupHom e.hom ≫ j) :
    IsOppositeFactorPair j (characterLattice.congr e a) x q ↔
      IsOppositeFactorPair i a x q := by
  constructor
  · intro hq
    have hs : i ≫ (Iso.refl G).hom = CommGroupScheme.groupHom e.hom ≫ j := by
      simpa only [Iso.refl_hom, Category.comp_id] using h
    have hi : j = CommGroupScheme.groupHom e.inv ≫ i := by
      simpa only [Iso.refl_inv, Category.comp_id] using
        torusTransport_inverse_square e (Iso.refl G) hs
    simpa [characterLattice.congr_apply] using hq.changeTorus e.symm hi
  · exact IsOppositeFactorPair.changeTorus e h

end ChangeTorus

end RelativeRoot

namespace SplitPinning

section Galois

open GaloisPointComparison

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G)

local instance steinbergCanonicalGaloisTransportIsAffineHom :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

variable (p : Langlands.GroupScheme.SplitPinning
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))

variable (eT : p.torus ≅ ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))

variable (hT : p.inclusion = CommGroupScheme.groupHom eT.hom ≫
    (GroupScheme.baseChange (algebraBaseMap k K)).map i)

namespace NormalizedRootParametrization

variable {a c : p.base.support}
    (x : p.NormalizedRootParametrization a) (y : p.NormalizedRootParametrization c)
    (σ : K ≃ₐ[k] K)
    (hroot : characterLattice.congr eT (p.rootDatum.root c) =
      characterLattice.galoisRepresentation k K T σ
        (characterLattice.congr eT (p.rootDatum.root a)))
    (hunit : rationalConjugate k K G σ x.unitPoint = y.unitPoint)

include hT hroot hunit

/-- Compatibility of the actual normalized unit points forces transport of
the canonical ordered opposite pairs. -/
theorem oppositeFactorPair_rationalConjugate :
    (rationalConjugate k K G σ x.oppositeFactorPair.1,
      rationalConjugate k K G σ x.oppositeFactorPair.2) = y.oppositeFactorPair := by
  have hx := x.oppositeFactorPair_spec.changeTorus eT hT
  have hq := hx.rationalConjugate k K i σ
  rw [← hroot, hunit] at hq
  exact y.eq_oppositeFactorPair
    ((RelativeRoot.isOppositeFactorPair_changeTorus_iff eT hT).mp hq)

/-- The canonical simple-reflection point is the transported ordered triple. -/
theorem reflectionRepresentative_rationalConjugate :
    rationalConjugate k K G σ x.reflectionRepresentative.point =
      y.reflectionRepresentative.point := by
  have hq := oppositeFactorPair_rationalConjugate k K i p eT hT x y σ hroot hunit
  have hq1 : rationalConjugate k K G σ x.oppositeFactorPair.1 =
      y.oppositeFactorPair.1 := congrArg Prod.fst hq
  have hq2 : rationalConjugate k K G σ x.oppositeFactorPair.2 =
      y.oppositeFactorPair.2 := congrArg Prod.snd hq
  rw [x.reflectionRepresentative_point, y.reflectionRepresentative_point,
    map_mul, map_mul, hunit, hq1, hq2]

end NormalizedRootParametrization

/-- The supplied normalized unit points intertwine a supplied simple-root
permutation with the actual coefficient action. -/
def UnitPointsGaloisCompatible
    (x : p.NormalizedSimpleRootParametrizations)
    (ρ : (K ≃ₐ[k] K) →* Equiv.Perm p.base.support) : Prop :=
  ∀ (σ : K ≃ₐ[k] K) (a : p.base.support),
    rationalConjugate k K G σ (x a).unitPoint = (x (ρ σ a)).unitPoint

include hT in
/-- Once actual root and unit-point compatibility are supplied, the entire
canonical family of simple-reflection points is coefficient compatible. -/
theorem canonicalSimpleReflectionRepresentatives_rationalConjugate
    (x : p.NormalizedSimpleRootParametrizations)
    (ρ : (K ≃ₐ[k] K) →* Equiv.Perm p.base.support)
    (hroot : ∀ (σ : K ≃ₐ[k] K) (a : p.base.support),
      characterLattice.congr eT (p.rootDatum.root (ρ σ a)) =
        characterLattice.galoisRepresentation k K T σ
          (characterLattice.congr eT (p.rootDatum.root a)))
    (hunit : UnitPointsGaloisCompatible k K p x ρ)
    (σ : K ≃ₐ[k] K) (a : p.base.support) :
    rationalConjugate k K G σ (canonicalSimpleReflectionRepresentatives x a).point =
      (canonicalSimpleReflectionRepresentatives x (ρ σ a)).point :=
  NormalizedRootParametrization.reflectionRepresentative_rationalConjugate
    k K i p eT hT (x a) (x (ρ σ a)) σ (hroot σ a) (hunit σ a)

end Galois

end SplitPinning

end Langlands.GroupScheme
