import Langlands.BruhatTits.IntegralModels.FacetLieWeights
import Langlands.GroupScheme.IntegralModel.ClosedSubgroupIntegralPoints
import Langlands.GroupScheme.Rational.CrossTorusLieTransport
import Langlands.GroupScheme.Rational.SteinbergCanonicalGaloisTransport

/-! # Generic roots and opposite pairs through the specified integral torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels.IntegralTorusData

open GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {D : RelativeComponentModelData R K G}
    {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
    (T : IntegralTorusData D S i)

/-- The specified generic torus isomorphism preserves maximal splitness
of the ambient torus inclusion. -/
theorem genericHom_isMaximalSplitTorus (hi : IsMaximalSplitTorus i) :
    IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T.torus)
      (D.neutral.genericHom T.inclusion) := by
  change IsMaximalSplitTorus
    (T := (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T.torus)
    ((baseChange (Spec.algebraMap R K)).map T.inclusion ≫ D.neutral.genericIso.hom)
  rw [T.generic_comm]
  refine ⟨⟨IsSplitTorus.of_iso T.genericIso hi.1.1,
    hi.1.2.iso_comp T.genericIso⟩, ?_⟩
  intro S' i' hi' f hf
  have heq : (T.genericIso.inv ≫ f) ≫ i' = i := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
      congrArg (fun a => T.genericIso.inv ≫ a) hf
  have : IsIso (T.genericIso.inv ≫ f) := hi.2 S' i' hi' _ heq
  have : IsIso (T.genericIso.hom ≫ (T.genericIso.inv ≫ f)) := inferInstance
  simpa only [Iso.hom_inv_id_assoc] using this

/-- The same generic point belongs to the same actual root functor after
using the specified integral torus's generic identification. -/
theorem generic_subgroup_eq (χ : characterLattice T.torus) :
    RelativeRoot.subgroup (D.neutral.genericHom T.inclusion)
        (characterLattice.baseChange (Spec.algebraMap R K) T.torus χ) =
      RelativeRoot.subgroup i (T.genericCharacter χ) := by
  let e : (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T.torus ≅ S :=
    CommGroupScheme.isoOfGroupIso T.genericIso
  have hc : D.neutral.genericHom T.inclusion =
      CommGroupScheme.groupHom e.hom ≫ i := T.generic_comm
  have hs : D.neutral.genericHom T.inclusion ≫ (Iso.refl G).hom =
      CommGroupScheme.groupHom e.hom ≫ i := by
    simpa only [Iso.refl_hom, Category.comp_id] using hc
  have hchar : characterLattice.congr e
      (characterLattice.baseChange (Spec.algebraMap R K) T.torus χ) =
        T.genericCharacter χ := rfl
  simpa only [hchar, Iso.refl_hom, SubgroupFunctor.comap_id] using
    (RelativeRoot.subgroup_comap_of_transport e (Iso.refl G) hs
      (characterLattice.baseChange (Spec.algebraMap R K) T.torus χ)).symm

/-- The actual relative-root predicate uses the same canonical generic
character identification as the root functor. -/
theorem generic_mem_relativeRoots_iff [IsAffineHom G.X.hom]
    (χ : characterLattice T.torus) :
    characterLattice.baseChange (Spec.algebraMap R K) T.torus χ ∈
        relativeRoots (D.neutral.genericHom T.inclusion) ↔
      T.genericCharacter χ ∈ relativeRoots i := by
  let e : (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T.torus ≅ S :=
    CommGroupScheme.isoOfGroupIso T.genericIso
  have hc : D.neutral.genericHom T.inclusion =
      CommGroupScheme.groupHom e.hom ≫ i := T.generic_comm
  have hs : D.neutral.genericHom T.inclusion ≫ (Iso.refl G).hom =
      CommGroupScheme.groupHom e.hom ≫ i := by
    simpa only [Iso.refl_hom, Category.comp_id] using hc
  exact (roots_mem_of_transport_iff e (Iso.refl G) hs
    (characterLattice.baseChange (Spec.algebraMap R K) T.torus χ)).symm

/-- Both ordered opposite factors and the middle point are unchanged
under the specified generic torus identification. -/
theorem generic_isOppositeFactorPair_iff (χ : characterLattice T.torus)
    (x : rationalPoints G) (p : rationalPoints G × rationalPoints G) :
    RelativeRoot.IsOppositeFactorPair i (T.genericCharacter χ) x p ↔
      RelativeRoot.IsOppositeFactorPair (D.neutral.genericHom T.inclusion)
        (characterLattice.baseChange (Spec.algebraMap R K) T.torus χ) x p := by
  let e : (CommGroupScheme.baseChange (Spec.algebraMap R K)).obj T.torus ≅ S :=
    CommGroupScheme.isoOfGroupIso T.genericIso
  exact RelativeRoot.isOppositeFactorPair_changeTorus_iff e T.generic_comm

/-- An equivalence of the actual ordered opposite-pair types, whose value
is the original pair of ambient generic points. -/
def genericOppositeFactorPairsEquiv (χ : characterLattice T.torus)
    (x : rationalPoints G) :
    {p // RelativeRoot.IsOppositeFactorPair (D.neutral.genericHom T.inclusion)
      (characterLattice.baseChange (Spec.algebraMap R K) T.torus χ) x p} ≃
    {p // RelativeRoot.IsOppositeFactorPair i (T.genericCharacter χ) x p} where
  toFun p := ⟨p.val, (T.generic_isOppositeFactorPair_iff χ x p.val).mpr p.property⟩
  invFun p := ⟨p.val, (T.generic_isOppositeFactorPair_iff χ x p.val).mp p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Langlands.BruhatTits.IntegralModels.IntegralTorusData
