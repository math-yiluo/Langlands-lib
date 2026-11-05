import Langlands.GroupScheme.Derived.SplitTorusCommutators
import Langlands.GroupScheme.Reductive.SplitSemisimpleRootSpanNecessity

/-! # Split tori with actual semisimple root data lie in the derived subgroup -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

section Field

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
  {J : Type*} {P : RootDatum J (characterLattice T) (cocharacterLattice T)}

/-- A split torus whose actual root datum has finite coroot index is contained
in the full scheme-theoretic derived subgroup. -/
theorem IsRootDatumOf.range_le_derivedSubgroup_of_finite_corootIndex
    (hP : IsRootDatumOf i P) (hT : IsSplitTorus T.toGrp)
    [Finite (cocharacterLattice T ⧸ P.corootSpan ℤ)] :
    SubgroupFunctor.range i ≤ derivedSubgroup G := by
  rintro U x hx H j hj hcomm
  have hspan : P.corootSpan ℤ ≤ cocharactersLandingIn i (SubgroupFunctor.range j) := by
    apply Submodule.span_le.mpr
    rintro ν ⟨a, rfl⟩
    exact hP.coroot_mem_cocharactersLandingIn i hj hcomm a
  have htotal : cocharactersLandingIn i (SubgroupFunctor.range j) = ⊤ := by
    apply top_unique
    intro ν _
    obtain ⟨m, hm, hmν⟩ :=
      (isOfFinAddOrder_of_finite ((P.corootSpan ℤ).mkQ ν)).exists_nsmul_eq_zero
    have hmν' : (m : ℤ) • ν ∈ P.corootSpan ℤ := by
      apply (Submodule.Quotient.mk_eq_zero (P.corootSpan ℤ)).mp
      change (P.corootSpan ℤ).mkQ ((m : ℤ) • ν) = 0
      rw [map_zsmul, natCast_zsmul]
      exact hmν
    exact mem_cocharactersLandingIn_of_zsmul_mem i hj
      (Int.natCast_ne_zero.mpr hm.ne') (hspan hmν')
  exact hT.range_le_of_cocharacters i (SubgroupFunctor.range j) htotal U hx

/-- For a semisimple group, any supplied actual root datum of a closed split
torus gives containment of that torus in the derived subgroup. Reducedness and
maximality of the torus are not extra premises. -/
theorem IsSemisimple.range_torus_le_derivedSubgroup_of_rootDatum
    (hG : IsSemisimple G) (hT : IsSplitTorus T.toGrp)
    (hi : IsClosedSubgroup i) (hP : IsRootDatumOf i P) :
    SubgroupFunctor.range i ≤ derivedSubgroup G := by
  have := hG.isConnectedReductive.smooth
  have : Finite J := hP.finite_index hT
  have : Module.Finite ℤ (characterLattice T) := hT.finite_characterLattice
  have : Finite (cocharacterLattice T ⧸ P.corootSpan ℤ) :=
    P.finite_quotient_rootSpan_iff_corootSpan.mp (hG.finite_quotient_rootSpan hT hi hP)
  exact hP.range_le_derivedSubgroup_of_finite_corootIndex i hT

end Field

/-- The internal all-test torus-containment assertion for supplied actual root
data in semisimple field groups. -/
def SemisimpleRootDatumTorusDerivedStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsSemisimple G) (T : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T.toGrp → ∀ i : T.toGrp ⟶ G, IsClosedSubgroup i →
      haveI := hG.isConnectedReductive.isAffineHom
      ∀ (J : Type u) (P : RootDatum J (characterLattice T) (cocharacterLattice T)),
        IsRootDatumOf i P → SubgroupFunctor.range i ≤ derivedSubgroup G

/-- Proof of the internal semisimple torus-containment assertion. -/
theorem semisimpleRootDatumTorusDerived : SemisimpleRootDatumTorusDerivedStatement.{u} := by
  intro k _ G hG T hT i hi J P hP
  have := hG.isConnectedReductive.isAffineHom
  have : IsClosedImmersion i.hom.hom.left := hi
  exact hG.range_torus_le_derivedSubgroup_of_rootDatum i hT hi hP

end Langlands.GroupScheme
