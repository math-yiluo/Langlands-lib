import Langlands.Geometry.Analytic.StrictTestDomain.RationalContinuity
import Langlands.Geometry.Analytic.StrictTestDomain.RationalPresheaf

/-! # Rational sites and presheaves under bounded algebra equivalences -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain.RationalData

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P Q : PresentedStrictAffinoidAlgebra K}

omit [CompleteSpace K] in
private theorem inverse_comp (e : BoundedAlgEquiv K P Q) :
    e.symm.toBoundedAlgHom.comp e.toBoundedAlgHom = BoundedAlgHom.id K P := by
  ext a
  exact e.symm_apply_apply a

omit [CompleteSpace K] in
private theorem comp_inverse (e : BoundedAlgEquiv K P Q) :
    e.toBoundedAlgHom.comp e.symm.toBoundedAlgHom = BoundedAlgHom.id K Q := by
  ext a
  exact e.apply_symm_apply a

/-- Transport rational input data and their locus inclusions along an actual
bounded algebra equivalence. The inverse uses the bounded inverse algebra map. -/
def rationalCategoryEquivalence (e : BoundedAlgEquiv K P Q) :
    RationalData K P ≌ RationalData K Q where
  functor := pullbackFunctor e.toBoundedAlgHom
  inverse := pullbackFunctor e.symm.toBoundedAlgHom
  unitIso := eqToIso (by
    rw [← pullbackFunctor_comp, inverse_comp, pullbackFunctor_id])
  counitIso := eqToIso (by
    rw [← pullbackFunctor_comp, comp_inverse, pullbackFunctor_id])
  functor_unitIso_comp _ := (inferInstance : Subsingleton (Inclusion _ _)).elim _ _

omit [CompleteSpace K] in
/-- Transport preserves and reflects point-covering families, with no nonempty
or finiteness assumption on the index type. -/
theorem familyCovers_pullback_equiv_iff (e : BoundedAlgEquiv K P Q)
    {I : Type u} (d : RationalData K P) (D : I → RationalData K P) :
    FamilyCovers (d.pullback e.toBoundedAlgHom)
      (fun i => (D i).pullback e.toBoundedAlgHom) ↔ FamilyCovers d D := by
  constructor
  · intro h x hx
    obtain ⟨y, rfl⟩ := e.spectrumHomeomorph.surjective x
    exact h y hx
  · intro h
    exact h.pullback e.toBoundedAlgHom

/-- The category equivalence's forward functor is continuous for the finite
rational topologies, by the existing base-change construction. -/
instance rationalCategoryEquivalence_functor_isContinuous (e : BoundedAlgEquiv K P Q) :
    (rationalCategoryEquivalence e).functor.IsContinuous
      (finiteRationalTopology K P) (finiteRationalTopology K Q) :=
  pullbackFunctor_isContinuous e.toBoundedAlgHom

/-- The inverse functor is also continuous for the finite rational topologies. -/
instance rationalCategoryEquivalence_inverse_isContinuous (e : BoundedAlgEquiv K P Q) :
    (rationalCategoryEquivalence e).inverse.IsContinuous
      (finiteRationalTopology K Q) (finiteRationalTopology K P) :=
  pullbackFunctor_isContinuous e.symm.toBoundedAlgHom

private theorem inverse_compatibility (d : RationalData K P) (e : BoundedAlgEquiv K P Q) :
    (BoundedAlgHom.id K d.algebra).comp d.baseMap =
      (d.baseMap.comp e.symm.toBoundedAlgHom).comp e.toBoundedAlgHom := by
  rw [BoundedAlgHom.comp_assoc, inverse_comp]
  rfl

/-- The inverse of the actual quotient comparison is constructed by the
published bounded extension, using the inverse base map. -/
def comparisonInverse (d : RationalData K P) (e : BoundedAlgEquiv K P Q) :
    BoundedAlgHom K (d.pullback e.toBoundedAlgHom).algebra d.algebra :=
  d.extension e.toBoundedAlgHom (BoundedAlgHom.id K d.algebra)
    (d.baseMap.comp e.symm.toBoundedAlgHom) (inverse_compatibility d e)

@[simp]
theorem comparisonInverse_comp_baseMap (d : RationalData K P) (e : BoundedAlgEquiv K P Q) :
    (d.comparisonInverse e).comp (d.pullback e.toBoundedAlgHom).baseMap =
      d.baseMap.comp e.symm.toBoundedAlgHom :=
  d.extension_comp_baseMap e.toBoundedAlgHom (BoundedAlgHom.id K d.algebra)
    (d.baseMap.comp e.symm.toBoundedAlgHom) (inverse_compatibility d e)

@[simp]
theorem comparisonInverse_comp_comparison (d : RationalData K P)
    (e : BoundedAlgEquiv K P Q) :
    (d.comparisonInverse e).comp (d.comparison e.toBoundedAlgHom) =
      BoundedAlgHom.id K d.algebra :=
  d.extension_comp_comparison e.toBoundedAlgHom (BoundedAlgHom.id K d.algebra)
    (d.baseMap.comp e.symm.toBoundedAlgHom) (inverse_compatibility d e)

@[simp]
theorem comparison_comp_comparisonInverse (d : RationalData K P)
    (e : BoundedAlgEquiv K P Q) :
    (d.comparison e.toBoundedAlgHom).comp (d.comparisonInverse e) =
      BoundedAlgHom.id K (d.pullback e.toBoundedAlgHom).algebra := by
  apply (d.pullback e.toBoundedAlgHom).hom_ext
  rw [BoundedAlgHom.comp_assoc, comparisonInverse_comp_baseMap,
    ← BoundedAlgHom.comp_assoc, comparison_comp_baseMap, BoundedAlgHom.comp_assoc,
    comp_inverse]
  rfl

/-- The existing bounded comparison is an actual isomorphism of the constructed
quotient algebras when its base map is a bounded algebra equivalence. -/
def comparisonIso (d : RationalData K P) (e : BoundedAlgEquiv K P Q) :
    d.algebra ≅ (d.pullback e.toBoundedAlgHom).algebra where
  hom := d.comparison e.toBoundedAlgHom
  inv := d.comparisonInverse e
  hom_inv_id := d.comparisonInverse_comp_comparison e
  inv_hom_id := d.comparison_comp_comparisonInverse e

/-- The bounded quotient isomorphisms form an isomorphism of the actual bounded
presheaves; its forward map is the previously constructed comparison. -/
def rationalBoundedPresheafIso (e : BoundedAlgEquiv K P Q) :
    rationalBoundedPresheaf K P ≅
      (pullbackFunctor e.toBoundedAlgHom).op ⋙ rationalBoundedPresheaf K Q :=
  NatIso.ofComponents (fun d => d.unop.comparisonIso e)
    (fun {_ _} h => (h.unop.restriction_pullback_comp_comparison e.toBoundedAlgHom).symm)

/-- Forgetting norms gives an isomorphism of the commutative K-algebra
presheaves, without any assumption or assertion of sheafness. -/
def rationalPresheafIso (e : BoundedAlgEquiv K P Q) :
    rationalPresheaf K P ≅
      (pullbackFunctor e.toBoundedAlgHom).op ⋙ rationalPresheaf K Q :=
  NatIso.ofComponents
    (fun d => (PresentedStrictAffinoidAlgebra.toCommAlgCat K).mapIso (d.unop.comparisonIso e))
    (fun {_ _} h => by
      apply CommAlgCat.hom_ext
      exact congrArg BoundedAlgHom.toAlgHom
        (h.unop.restriction_pullback_comp_comparison e.toBoundedAlgHom).symm)

@[simp]
theorem rationalPresheafIso_hom (e : BoundedAlgEquiv K P Q) :
    (rationalPresheafIso e).hom = rationalPresheafComparison e.toBoundedAlgHom := by
  ext d a
  rfl

end Langlands.Analytic.StrictTestDomain.RationalData
