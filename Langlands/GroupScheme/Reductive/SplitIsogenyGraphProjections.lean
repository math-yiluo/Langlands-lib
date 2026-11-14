import Langlands.GroupScheme.Reductive.SplitIsogenyGraph

/-! # Faithfully flat projections of the local-isogeny graph -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.RootDatumIsogenyRealization

variable {k : Type u} [Field k]

/-- Surjective precomposition detects a closed condition on a reduced group. -/
theorem factorsThrough_of_surjective_precomp
    {H K Q R : GroupScheme (Spec (CommRingCat.of k))} [IsReduced K.X.left]
    (p : H ⟶ K) (hp : Surjective p.hom.hom.left) (a : K ⟶ R)
    (j : Q ⟶ R) (hj : IsClosedSubgroup j)
    (hpa : FactorsThrough (p ≫ a).hom.hom j) : FactorsThrough a.hom.hom j := by
  obtain ⟨b, hb⟩ := hpa
  apply LeviGluing.factorsThrough_of_range_subset hj
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hp.surj x
  refine ⟨b.left y, ?_⟩
  have h := congrArg (fun f => f.left y) hb
  simpa only [Over.comp_left, Grp.comp_hom_hom, Scheme.Hom.comp_apply, hy] using h

variable {G G' : GroupScheme (Spec (CommRingCat.of k))}
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    {I : Type v} {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G'} {t : T ⟶ T'}
    {ν : I → cocharacterLattice T} {ν' : I → cocharacterLattice T'}
    {C : ∀ j, LocalIsogeny i i' t (ν j) (ν' j)}

namespace LocalIsogenyGraphEnvelope

variable (D : LocalIsogenyGraphEnvelope C)

/-- A closed subgroup containing the second projection contains every target
centralizer, even when the local isogeny has a nonsmooth kernel. -/
theorem localRight_le_of_second_factorsThrough
    [Smooth G'.X.hom] [IsAffineHom G'.X.hom]
    {K : GroupScheme (Spec (CommRingCat.of k))} (q : K ⟶ G')
    (hq : IsClosedSubgroup q) (hD : FactorsThrough D.second.hom.hom q) (j : I) :
    SubgroupFunctor.range (C j).rightInclusion ≤ SubgroupFunctor.range q := by
  let : IsReduced (C j).right.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k _ (C j).right.X.hom
  apply (factorsThrough_hom_iff_range_le (C j).rightInclusion q).mp
  apply factorsThrough_of_surjective_precomp (C j).hom (C j).isogeny.2.2 _ q hq
  obtain ⟨b, hb⟩ := hD
  refine ⟨(D.localLift j).hom.hom ≫ b, ?_⟩
  rw [Category.assoc, hb, ← Grp.comp_hom_hom, D.localLift_second]

/-- The prescribed torus isogeny makes the whole target torus lie in every
closed subgroup through which the second projection factors. -/
theorem torus_le_of_second_factorsThrough
    (hT' : IsSplitTorus T'.toGrp) (ht : IsIsogeny (CommGroupScheme.groupHom t))
    {K : GroupScheme (Spec (CommRingCat.of k))} (q : K ⟶ G')
    (hq : IsClosedSubgroup q) (hD : FactorsThrough D.second.hom.hom q) :
    SubgroupFunctor.range i' ≤ SubgroupFunctor.range q := by
  let : Smooth T'.toGrp.X.hom := hT'.smooth
  let : IsReduced T'.toGrp.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k _ T'.toGrp.X.hom
  apply (factorsThrough_hom_iff_range_le i' q).mp
  apply factorsThrough_of_surjective_precomp (CommGroupScheme.groupHom t) ht.2.2 _ q hq
  obtain ⟨b, hb⟩ := hD
  refine ⟨D.torusLift.hom.hom ≫ b, ?_⟩
  rw [Category.assoc, hb, ← Grp.comp_hom_hom, D.torusLift_second]

/-- The second projection is faithfully flat if its target local directions
cover a generic simple system and its torus map is an isogeny. -/
theorem second_geometry
    [Smooth G'.X.hom] [IsAffineHom G'.X.hom] [ConnectedSpace G'.X.left]
    (hT' : IsSplitTorus T'.toGrp) (hi' : IsClosedSubgroup i')
    (ht : IsIsogeny (CommGroupScheme.groupHom t))
    {J : Type u} (P' : RootDatum J (characterLattice T') (cocharacterLattice T'))
    (hP' : IsRootDatumOf i' P') (ζ' : cocharacterLattice T')
    (hζ' : IsGenericCocharacter i' ζ')
    (hcover : ∀ α ∈ simpleRelativeRoots i' ζ', ∃ j, latticePairing T' α (ν' j) = 0)
    (hZ : Dynamic.centralizer (CommGroupScheme.groupHom ζ' ≫ i') = SubgroupFunctor.range i') :
    Flat D.second.hom.hom.left ∧ Surjective D.second.hom.hom.left ∧
      LocallyOfFinitePresentation D.second.hom.hom.left ∧ QuasiCompact D.second.hom.hom.left := by
  obtain ⟨E, q, p, hq, hpq, hflat, hsurj, hqc, hlfp, _, _, _⟩ :=
    HomImage.exists_image D.second
  have hD : FactorsThrough D.second.hom.hom q :=
    ⟨p.hom.hom, congrArg (fun f => f.hom.hom) hpq⟩
  have hroot : ∀ j α, latticePairing T' α (ν' j) = 0 →
      RelativeRoot.subgroup i' α ≤ SubgroupFunctor.range q := by
    intro j α hα
    apply (RelativeRoot.subgroup_le_dynamicCentralizer_of_pairing_eq_zero i' α (ν' j) hα).trans
    rw [← (C j).rightRep.2]
    exact D.localRight_le_of_second_factorsThrough q hq hD j
  let : IsIso q := LeviGluing.isIso_of_simpleRootLevis hT' hi' hP' hζ' q hq
    (fun α hα => by obtain ⟨j, hj⟩ := hcover α hα; exact hroot j α hj)
    (fun α hα => by
      obtain ⟨j, hj⟩ := hcover α hα
      apply hroot j (-α)
      simp only [map_neg, LinearMap.neg_apply, hj, neg_zero])
    (by rw [hZ]; exact D.torus_le_of_second_factorsThrough hT' ht q hq hD)
  let : IsIso q.hom := inferInstanceAs (IsIso ((Grp.forget₂Mon _).map q))
  let : IsIso q.hom.hom := inferInstanceAs (IsIso ((Mon.forget _).map q.hom))
  let : IsIso q.hom.hom.left := inferInstanceAs (IsIso ((Over.forget _).map q.hom.hom))
  let : Flat p.hom.hom.left := hflat
  let : Surjective p.hom.hom.left := hsurj
  let : QuasiCompact p.hom.hom.left := hqc
  let : LocallyOfFinitePresentation p.hom.hom.left := hlfp
  have heq : p.hom.hom.left ≫ q.hom.hom.left = D.second.hom.hom.left :=
    congrArg (fun f => f.hom.hom.left) hpq
  rw [← heq]
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

end LocalIsogenyGraphEnvelope


/-- The actual local-isogeny graph with faithfully flat geometry recorded for
both projections. -/
structure FaithfullyFlatLocalIsogenyGraphEnvelope
    {G G' : GroupScheme (Spec (CommRingCat.of k))}
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    {I : Type v} {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G'} {t : T ⟶ T'}
    {ν : I → cocharacterLattice T} {ν' : I → cocharacterLattice T'}
    (C : ∀ j, LocalIsogeny i i' t (ν j) (ν' j)) where
  graph : LocalIsogenyGraphEnvelope C
  firstGeometry : Flat graph.first.hom.hom.left ∧ Surjective graph.first.hom.hom.left ∧
    LocallyOfFinitePresentation graph.first.hom.hom.left ∧ QuasiCompact graph.first.hom.hom.left
  secondGeometry : Flat graph.second.hom.hom.left ∧ Surjective graph.second.hom.hom.left ∧
    LocallyOfFinitePresentation graph.second.hom.hom.left ∧ QuasiCompact graph.second.hom.hom.left

/-- Certify the two projections from simple-direction coverage for the two
possibly different tori and chambers. -/
def faithfullyFlatLocalIsogenyGraphEnvelope
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth G'.X.hom] [IsAffineHom G'.X.hom] [ConnectedSpace G'.X.left]
    (D : LocalIsogenyGraphEnvelope C)
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (hi : IsClosedSubgroup i) (hi' : IsClosedSubgroup i')
    (ht : IsIsogeny (CommGroupScheme.groupHom t))
    {J J' : Type u}
    (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (P' : RootDatum J' (characterLattice T') (cocharacterLattice T'))
    (hP : IsRootDatumOf i P) (hP' : IsRootDatumOf i' P')
    (ζ : cocharacterLattice T) (ζ' : cocharacterLattice T')
    (hζ : IsGenericCocharacter i ζ) (hζ' : IsGenericCocharacter i' ζ')
    (hcover : ∀ α ∈ simpleRelativeRoots i ζ, ∃ j, latticePairing T α (ν j) = 0)
    (hcover' : ∀ α ∈ simpleRelativeRoots i' ζ', ∃ j, latticePairing T' α (ν' j) = 0)
    (hZ : Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i) = SubgroupFunctor.range i)
    (hZ' : Dynamic.centralizer (CommGroupScheme.groupHom ζ' ≫ i') = SubgroupFunctor.range i') :
    FaithfullyFlatLocalIsogenyGraphEnvelope C :=
  ⟨D, D.first_geometry hT hi P hP ζ hζ hcover hZ,
    D.second_geometry hT' hi' ht P' hP' ζ' hζ' hcover' hZ'⟩

end Langlands.GroupScheme.RootDatumIsogenyRealization
