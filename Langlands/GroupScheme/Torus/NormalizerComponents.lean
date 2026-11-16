import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof
import Langlands.GroupScheme.Absolute.RationalSubgroupContainment
import Langlands.GroupScheme.IdentityComponent.Transport
import Langlands.GroupScheme.Rational.TorusNormalizer
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Maximal-torus normalizers detect connectedness -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth G.X.hom] [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (t : T.toGrp ⟶ identityComponent G) (ht : IsMaximalTorus t)

include ht

/-- Multiplication by a point of the identity component moves any rational
point into the normalizer of a maximal torus of that component. -/
theorem exists_identityPoint_mul_mem_normalizer
    (g : rationalPoints G) :
    ∃ p : rationalPoints (identityComponent G),
      (p ≫ (identityComponentι G).hom.hom) * g ∈
        normalizerPoints (t ≫ identityComponentι G) := by
  let e := IdentityComponent.mapIso (G.innerIso g)
  have he : identityComponentι G ≫ (G.innerIso g).hom =
      e.hom ≫ identityComponentι G :=
    (IdentityComponent.mapIso_hom_identityComponentι (G.innerIso g)).symm
  obtain ⟨p, a, ha⟩ := maximalTorusConjugacy k (identityComponent G)
    T T (t ≫ e.hom) t (ht.comp_iso e) ht
  refine ⟨p, a, ?_⟩
  change (t ≫ identityComponentι G) ≫
      (G.innerIso ((p ≫ (identityComponentι G).hom.hom) * g)).hom =
    CommGroupScheme.groupHom a.hom ≫ (t ≫ identityComponentι G)
  calc
    _ = ((t ≫ e.hom) ≫ ((identityComponent G).innerIso p).hom) ≫
        identityComponentι G := by
      rw [innerIso_mul_hom]
      simp only [Category.assoc]
      rw [reassoc_of% he, innerIso_hom_comp (identityComponentι G) p]
    _ = _ := by rw [ha, Category.assoc]

/-- An actual normalizer point in the component of a prescribed rational point. -/
def normalizerComponentRepresentative (g : rationalPoints G) :
    normalizerPoints (t ≫ identityComponentι G) :=
  ⟨((exists_identityPoint_mul_mem_normalizer t ht g).choose ≫
      (identityComponentι G).hom.hom) * g,
    (exists_identityPoint_mul_mem_normalizer t ht g).choose_spec⟩

/-- The representative differs on the left from the original point by an
actual identity-component point. -/
theorem normalizerComponentRepresentative_mul_inv
    (g : rationalPoints G) :
    (normalizerComponentRepresentative t ht g).val * g⁻¹ ∈
      (SubgroupFunctor.range (identityComponentι G)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
  change ((_ ≫ (identityComponentι G).hom.hom) * g) * g⁻¹ ∈ _
  rw [mul_inv_cancel_right]
  exact SubgroupFunctor.mem_range.mpr ⟨_, rfl⟩

/-- If the full normalizer of such a torus lies in the identity component on
rational points, every rational point of the ambient group lies there. -/
theorem mem_identityComponent_of_normalizerPoints_le
    (hN : normalizerPoints (t ≫ identityComponentι G) ≤
      (SubgroupFunctor.range (identityComponentι G)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
    (g : rationalPoints G) :
    g ∈ (SubgroupFunctor.range (identityComponentι G)).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
  obtain ⟨p, hp⟩ := exists_identityPoint_mul_mem_normalizer t ht g
  have hp0 : p ≫ (identityComponentι G).hom.hom ∈
      (SubgroupFunctor.range (identityComponentι G)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :=
    SubgroupFunctor.mem_range.mpr ⟨p, rfl⟩
  have hh := ((SubgroupFunctor.range (identityComponentι G)).carrier _).mul_mem
    (((SubgroupFunctor.range (identityComponentι G)).carrier _).inv_mem hp0) (hN hp)
  simpa only [inv_mul_cancel_left] using hh

/-- The identity-component inclusion is an actual isomorphism if it contains
the full maximal-torus normalizer on rational points. -/
def identityComponentIsoOfNormalizerPoints
    (hN : normalizerPoints (t ≫ identityComponentι G) ≤
      (SubgroupFunctor.range (identityComponentι G)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    identityComponent G ≅ G := by
  have : IsReduced G.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k _ G.X.hom
  have hle : SubgroupFunctor.range (𝟙 G) ≤
      SubgroupFunctor.range (identityComponentι G) :=
    SubgroupFunctor.range_le_of_algClosed_points
      (IdentityComponent.isClosedSubgroup_identityComponentι G)
      (fun g _ => mem_identityComponent_of_normalizerPoints_le t ht hN g)
  have hrep : (SubgroupFunctor.range (identityComponentι G)).IsRepresentedBy
      (identityComponentι G) := ⟨Over.mono_of_mono_left _, rfl⟩
  let f := hrep.factorHom (𝟙 G) hle
  have hf : f ≫ identityComponentι G = 𝟙 G := hrep.factorHom_comp _ _
  refine ⟨identityComponentι G, f, ?_, hf⟩
  apply hrep.hom_ext
  rw [Category.assoc, hf, Category.comp_id, Category.id_comp]

@[simp]
theorem identityComponentIsoOfNormalizerPoints_hom
    (hN : normalizerPoints (t ≫ identityComponentι G) ≤
      (SubgroupFunctor.range (identityComponentι G)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    (identityComponentIsoOfNormalizerPoints t ht hN).hom = identityComponentι G :=
  rfl

/-- A smooth affine group over an algebraically closed field is connected if
the normalizer of a maximal torus in its identity component lies there. -/
theorem connectedSpace_of_normalizerPoints_le_identityComponent
    (hN : normalizerPoints (t ≫ identityComponentι G) ≤
      (SubgroupFunctor.range (identityComponentι G)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    ConnectedSpace G.X.left := by
  let e := identityComponentIsoOfNormalizerPoints t ht hN
  have : IsIso e.hom.hom.hom.left :=
    Functor.map_isIso (Grp.forget₂Mon _ ⋙ Mon.forget _ ⋙ Over.forget _) e.hom
  exact e.hom.hom.hom.left.surjective.connectedSpace
    e.hom.hom.hom.left.continuous

end Langlands.GroupScheme
