import Langlands.GroupScheme.Torus.WeightRestriction
import Langlands.GroupScheme.Lie.SplitTorusCoordinates
import Langlands.GroupScheme.Rational.SplitTorusSurjection

/-! # Weight and root comparison under injective character pullback -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
  {G' : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G'.X.hom] [LocallyOfFiniteType G'.X.hom]

/-- Injectivity of character pullback makes each pulled-back weight space equal to
its original weight space for split tori. -/
theorem weightSpace_comp_eq_of_character_injective
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (t : T ⟶ T') (i' : T'.toGrp ⟶ G')
    (hinj : Function.Injective (fun χ : characterLattice T' => t ≫ χ))
    (χ : characterLattice T') :
    weightSpace (CommGroupScheme.groupHom t ≫ i') (t ≫ χ) = weightSpace i' χ := by
  rw [weightSpace_comp_eq_iSup hT' hT t i' (t ≫ χ)]
  apply le_antisymm
  · refine iSup_le fun ψ => ?_
    exact le_of_eq (congrArg (weightSpace i') (hinj ψ.property))
  · exact le_iSup_of_le ⟨χ, rfl⟩ le_rfl

/-- The weight-space identification under injective character pullback leaves each
actual Lie vector unchanged. -/
def Lie.weightSpaceCompEquiv
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (t : T ⟶ T') (i' : T'.toGrp ⟶ G')
    (hinj : Function.Injective (fun χ : characterLattice T' => t ≫ χ))
    (χ : characterLattice T') :
    weightSpace (CommGroupScheme.groupHom t ≫ i') (t ≫ χ) ≃ₗ[k] weightSpace i' χ :=
  LinearEquiv.ofEq _ _ (weightSpace_comp_eq_of_character_injective hT hT' t i' hinj χ)

@[simp] theorem Lie.weightSpaceCompEquiv_coe
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (t : T ⟶ T') (i' : T'.toGrp ⟶ G')
    (hinj : Function.Injective (fun χ : characterLattice T' => t ≫ χ))
    (χ : characterLattice T')
    (X : weightSpace (CommGroupScheme.groupHom t ≫ i') (t ≫ χ)) :
    (Lie.weightSpaceCompEquiv hT hT' t i' hinj χ X : Additive (lieKernel G' k)) = X :=
  rfl

/-- Equality of root supports for the same source-torus action gives the actual
root pullback bijection once character pullback is injective. -/
theorem roots_bijOn_of_comp_eq
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (t : T ⟶ T') (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ G') (q : G ⟶ G')
    (ht : i ≫ q = CommGroupScheme.groupHom t ≫ i')
    (hinj : Function.Injective (fun χ : characterLattice T' => t ≫ χ))
    (hroots : roots (i ≫ q) = roots i) :
    Set.BijOn (fun χ : characterLattice T' => t ≫ χ) (roots i') (roots i) := by
  have heq : roots (CommGroupScheme.groupHom t ≫ i') = roots i := by
    rw [← ht, hroots]
  refine ⟨?_, hinj.injOn, ?_⟩
  · intro χ hχ
    rw [← heq, mem_roots_comp_iff hT' hT t i']
    refine ⟨?_, χ, hχ, rfl⟩
    intro hz
    apply hχ.1
    apply hinj
    simpa using hz
  · intro ψ hψ
    rw [← heq, mem_roots_comp_iff hT' hT t i'] at hψ
    obtain ⟨χ, hχ, hχψ⟩ := hψ.2
    exact ⟨χ, hχ, hχψ⟩

/-- A torus isogeny and explicit self-centralizer equalities give the zero-weight
dimension comparison for the same torus acting on source and target. -/
theorem Lie.finrank_zeroWeight_eq_comp_of_torus_isogeny
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    [IsAffineHom T.toGrp.X.hom] [IsAffineHom T'.toGrp.X.hom]
    (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ G') [Mono i.hom.hom] [Mono i'.hom.hom]
    (hself : torusCentralizer i = SubgroupFunctor.range i)
    (hself' : torusCentralizer i' = SubgroupFunctor.range i')
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (q : G ⟶ G') (t : T ⟶ T') (ht : i ≫ q = CommGroupScheme.groupHom t ≫ i')
    (htiso : IsIsogeny (CommGroupScheme.groupHom t)) :
    Module.finrank k (weightSpace i 0) = Module.finrank k (weightSpace (i ≫ q) 0) := by
  have : Flat (CommGroupScheme.groupHom t).hom.hom.left := htiso.2.1
  have : Surjective (CommGroupScheme.groupHom t).hom.hom.left := htiso.2.2
  have : Epi (CommGroupScheme.groupHom t).hom.hom.left :=
    Flat.epi_of_flat_of_surjective _
  have hinj := RealTorusSpace.characterRestrict_injective_of_epi t
  have heq := weightSpace_comp_eq_of_character_injective hT hT' t i' hinj 0
  simp only [Limits.comp_zero] at heq
  rw [ht, heq]
  exact Lie.finrank_zeroWeight_eq_of_torus_isogeny i i' hself hself' hT hT' t htiso

end Langlands.GroupScheme
