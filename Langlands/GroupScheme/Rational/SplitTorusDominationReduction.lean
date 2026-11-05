import Langlands.GroupScheme.Rational.SplitTorusDominationOperations
import Langlands.GroupScheme.Rational.UnipotentSplitTorusDominationStatement
import Langlands.GroupScheme.Rational.SplitSeriesExtension
import Langlands.GroupScheme.Unipotent.AdditiveCharacter
import Langlands.GroupScheme.UnipotentClosedSubgroupProof
import Langlands.GroupScheme.Derived.KernelAnnihilation
import Langlands.GroupScheme.Derived.ConnectedSmoothness
import Langlands.GroupScheme.NormalSubgroupQuotientProof
import Langlands.GroupScheme.Reductive.UnipotentQuotient
import Langlands.GroupScheme.CentralIsogeny.CommutatorDescent
import Langlands.GroupScheme.Lie.DimensionInduction

/-! # Reduction of split-torus domination to commutative unipotent groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- A nontrivial affine unipotent group cannot equal its actual derived subgroup:
a nonzero additive character vanishes on that subgroup. -/
theorem IsDerivedSubgroup.not_isIso_of_isUnipotent
    {D G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffine G.X.left] {d : D ⟶ G} (hd : IsDerivedSubgroup d)
    (hU : IsUnipotent G) (hnt : SubgroupFunctor.range (𝟙 G) ≠ ⊥) :
    ¬ IsIso d := by
  obtain ⟨q, hq⟩ := Unipotent.exists_additive_character hU hnt
  intro hiso
  let : IsIso d := hiso
  let : IsCommMonObj (VectorGroup.groupScheme (CommRingCat.of k) 1).X := by
    apply (isCommMonObj_iff_isMulCommutative _).2
    intro T
    refine ⟨⟨fun x y => ?_⟩⟩
    apply (VectorGroup.coordinates (CommRingCat.of k) 1 T).injective
    simp only [map_mul, mul_comm]
  let : IsSeparated (VectorGroup.groupScheme (CommRingCat.of k) 1).X.hom := by
    change IsSeparated (Spec.map _)
    infer_instance
  apply hq
  have h := hd.comp_eq_one q
  change d ≫ q = 0 at h
  have h' : d ≫ q = d ≫ (0 : G ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1) := by
    simpa only [CategoryTheory.Limits.comp_zero] using h
  exact (cancel_epi d).1 h'

namespace RelativeRoot

/-- An fpqc quotient whose full kernel contains the commutators is commutative.
The epimorphism on the product of two source schemes tests the universal
commutator equation, so no lifting of all rational points is asserted. -/
theorem IsFppfQuotient.isCommMonObj_of_containsCommutators
    {S : Scheme.{u}} {G Q : GroupScheme S} {F : SubgroupFunctor G}
    {q : G ⟶ Q} (hq : IsFppfQuotient F q)
    [QuasiCompact q.hom.hom.left] (hF : F.ContainsCommutators) :
    IsCommMonObj Q.X := by
  let : Flat q.hom.hom.left := hq.1
  let : Surjective q.hom.hom.left := hq.2.1
  let : Epi (q.hom.hom ⊗ₘ q.hom.hom) := CommutatorDescent.epi_tensorHom q
  have hc : commutatorMap (𝟙 G) (𝟙 G) ≫ q.hom.hom = 1 := by
    have h := hF (G.X ⊗ G.X) (fst G.X G.X) (snd G.X G.X)
    rw [← hq.2.2.2, mem_range_kernelι_iff] at h
    have hf := commutatorMap_points (𝟙 G) (𝟙 G) (𝟙 (G.X ⊗ G.X))
    simp only [Category.id_comp, Grp.id_hom_hom, Category.comp_id] at hf
    rw [hf]
    exact h
  have hcQ : commutatorMap (𝟙 Q) (𝟙 Q) = 1 := by
    apply (cancel_epi (q.hom.hom ⊗ₘ q.hom.hom)).1
    rw [CommutatorDescent.tensorHom_commutatorMap, hc, MonObj.comp_one]
  apply (isCommMonObj_iff_isMulCommutative _).2
  intro T
  refine ⟨⟨fun x y => ?_⟩⟩
  have h : x * y * x⁻¹ * y⁻¹ = 1 := by
    simpa only [commutatorMap_lift, Grp.id_hom_hom, Category.comp_id,
      MonObj.comp_one] using congrArg (fun f => lift x y ≫ f) hcQ
  calc x * y = (x * y * x⁻¹) * x := by group
       _ = y * x := by rw [mul_inv_eq_one.mp h]

end RelativeRoot

/-- It suffices to prove splitness for commutative smooth connected affine
unipotent groups with pointed split-torus domination over the same field.
The actual derived subgroup is dominated and has smaller Lie dimension;
the quotient is commutative, unipotent and dominated. -/
theorem splitUnipotent_of_splitTorusDomination_of_commutative
    (hcomm : ∀ (H : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
      [IsCommMonObj H.X], IsUnipotent H → HasPointedSplitTorusDomination H →
        RelativeRoot.IsSplitUnipotent H)
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hU : IsUnipotent G) (hG : HasPointedSplitTorusDomination G) :
    RelativeRoot.IsSplitUnipotent G := by
  classical
  refine smoothConnectedAffineGroup_lieDimension_induction
    (fun H => IsUnipotent H → HasPointedSplitTorusDomination H →
      RelativeRoot.IsSplitUnipotent H) ?_ G hU hG
  intro H _ _ _ ih hHu hHd
  by_cases ht : SubgroupFunctor.range (𝟙 H) = ⊥
  · exact ⟨0, ht⟩
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let E := smoothConnectedCommutatorImage k H inferInstance inferInstance inferInstance
  let D := E.val.group
  let d : D ⟶ H := E.val.inclusion
  have hd : IsDerivedSubgroup d := E.val.isDerivedSubgroup
  let : Smooth D.X.hom := E.property.1
  let : IsAffineHom D.X.hom := E.property.2.1
  let : Subsingleton (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  let : GeometricallyConnected D.X.hom := E.property.2.2.1
  let : ConnectedSpace D.X.left := GeometricallyConnected.connectedSpace_of_subsingleton D.X.hom
  obtain ⟨m, hm⟩ := ih D (Lie.dimension_lt_of_proper_closedSubgroup d hd.1
    (hd.not_isIso_of_isUnipotent hHu ht))
    (unipotentClosedSubgroup k H D d hd.1 hHu) (hHd.derivedSubgroup d hd)
  obtain ⟨Q, q, hQs, hQa, hq⟩ := normalSubgroupQuotient k H D d hd.1 hd.isNormal
  let : Smooth Q.X.hom := hQs
  let : IsAffineHom Q.X.hom := hQa
  let : Flat q.hom.hom.left := hq.1
  let : Surjective q.hom.hom.left := hq.2.1
  let : ConnectedSpace Q.X.left := q.hom.hom.left.surjective.connectedSpace
    q.hom.hom.left.continuous
  let : IsAffineHom q.hom.hom.left := IsAffineHom.of_comp q.hom.hom.left Q.X.hom
  let : QuasiCompact q.hom.hom.left := inferInstance
  let : IsCommMonObj Q.X := hq.isCommMonObj_of_containsCommutators hd.containsCommutators
  obtain ⟨n, hn⟩ := hcomm Q (hHu.of_flat_surjective q) (hHd.postcomp q)
  exact ⟨m + n, hm.of_fppfQuotient_of_field d q hd.1 inferInstance hq hn⟩

/-- Choose the finite represented additive series supplied by the derived
reduction, retaining the commutative case as an explicit premise. -/
def splitSeriesOfSplitTorusDominationOfCommutative
    (hcomm : ∀ (H : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
      [IsCommMonObj H.X], IsUnipotent H → HasPointedSplitTorusDomination H →
        RelativeRoot.IsSplitUnipotent H)
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hU : IsUnipotent G) (hG : HasPointedSplitTorusDomination G) :
    {n : ℕ // RelativeRoot.HasSplitSeries n G} :=
  let h := splitUnipotent_of_splitTorusDomination_of_commutative hcomm G hU hG
  ⟨h.choose, h.choose_spec⟩

end Langlands.GroupScheme
