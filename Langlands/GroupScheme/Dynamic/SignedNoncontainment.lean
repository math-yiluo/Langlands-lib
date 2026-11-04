import Langlands.GroupScheme.Lie.SignedDynamicDimension

/-! # A dynamic direction outside a proper smooth closed subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace RelativeRoot

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The actual positive, central and negative dynamic tangent submodules span
the whole Lie algebra. -/
theorem sup_signed_dynamic_tangentSubmodules
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) :
    tangentSubmodule (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)) ⊔
      tangentSubmodule (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)) ⊔
      tangentSubmodule (Dynamic.unipotent (CommGroupScheme.groupHom (-ν) ≫ i)) = ⊤ := by
  rw [tangentSubmodule_unipotent_eq_semigroupWeightSpan hT i ν,
    tangentSubmodule_centralizer_eq_semigroupWeightSpan hT i ν,
    tangentSubmodule_unipotent_eq_semigroupWeightSpan hT i (-ν)]
  apply top_unique
  rw [← iSup_actionWeightSpace_eq_top (AutomorphicAction.conjugation i) hT]
  refine iSup_le fun α => ?_
  rcases lt_trichotomy 0 (latticePairing T α ν) with hα | hα | hα
  · have hp : actionWeightSpace (AutomorphicAction.conjugation i) α ≤
        semigroupWeightSpan (AutomorphicAction.conjugation i) (positiveSemigroup ν) :=
      le_iSup (fun χ : positiveSemigroup ν =>
        actionWeightSpace (AutomorphicAction.conjugation i) χ.val) ⟨α, hα⟩
    exact (hp.trans le_sup_left).trans le_sup_left
  · have hz : actionWeightSpace (AutomorphicAction.conjugation i) α ≤
        semigroupWeightSpan (AutomorphicAction.conjugation i) (zeroSemigroup ν) :=
      le_iSup (fun χ : zeroSemigroup ν =>
        actionWeightSpace (AutomorphicAction.conjugation i) χ.val) ⟨α, hα.symm⟩
    exact (hz.trans le_sup_right).trans le_sup_left
  · have hn : 0 < latticePairing T α (-ν) := by
      rw [map_neg]
      omega
    have hm : actionWeightSpace (AutomorphicAction.conjugation i) α ≤
        semigroupWeightSpan (AutomorphicAction.conjugation i) (positiveSemigroup (-ν)) :=
      le_iSup (fun χ : positiveSemigroup (-ν) =>
        actionWeightSpace (AutomorphicAction.conjugation i) χ.val) ⟨α, hn⟩
    exact hm.trans le_sup_right

end RelativeRoot

namespace Dynamic

variable {k : Type u} [Field k]
    {G B : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    [IsAffineHom B.X.hom] [Smooth B.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A smooth closed subgroup containing all three actual signed dynamic
subgroups is the entire connected smooth affine group. -/
theorem isIso_of_signed_dynamic_le_range
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    (b : B ⟶ G) (hb : IsClosedSubgroup b)
    (hp : unipotent (CommGroupScheme.groupHom ν ≫ i) ≤ SubgroupFunctor.range b)
    (hz : centralizer (CommGroupScheme.groupHom ν ≫ i) ≤ SubgroupFunctor.range b)
    (hn : unipotent (CommGroupScheme.groupHom (-ν) ≫ i) ≤ SubgroupFunctor.range b) :
    IsIso b := by
  let : IsClosedImmersion b.hom.hom.left := hb
  let : Mono b.hom.hom := Over.mono_of_mono_left _
  have htop : RelativeRoot.tangentSubmodule (SubgroupFunctor.range b) = ⊤ := by
    apply top_unique
    rw [← RelativeRoot.sup_signed_dynamic_tangentSubmodules hT i ν]
    exact sup_le (sup_le (RelativeRoot.tangentSubmodule_mono hp)
      (RelativeRoot.tangentSubmodule_mono hz)) (RelativeRoot.tangentSubmodule_mono hn)
  apply Lie.isIso_of_surjective_targetMapLinear b hb
  apply LinearMap.range_eq_top.mp
  rwa [← RelativeRoot.tangentSubmodule_range b]

/-- If a proper smooth closed subgroup contains the actual dynamic centralizer,
at least one signed identity-limit subgroup is not contained in it. -/
theorem not_le_range_unipotent_or_neg
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    (b : B ⟶ G) (hb : IsClosedSubgroup b) (hproper : ¬ IsIso b)
    (hz : centralizer (CommGroupScheme.groupHom ν ≫ i) ≤ SubgroupFunctor.range b) :
    (¬ unipotent (CommGroupScheme.groupHom ν ≫ i) ≤ SubgroupFunctor.range b) ∨
      ¬ unipotent (CommGroupScheme.groupHom (-ν) ≫ i) ≤ SubgroupFunctor.range b := by
  by_cases hp : unipotent (CommGroupScheme.groupHom ν ≫ i) ≤ SubgroupFunctor.range b
  · right
    intro hn
    exact hproper (isIso_of_signed_dynamic_le_range hT i ν b hb hp hz hn)
  · exact Or.inl hp

/-- A choice of an actual signed cocharacter whose dynamic identity-limit
subgroup is not contained in the prescribed subgroup. -/
structure NoncontainedSignedDirection (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    (b : B ⟶ G) where
  cocharacter : cocharacterLattice T
  signed : cocharacter = ν ∨ cocharacter = -ν
  noncontained : ¬ unipotent (CommGroupScheme.groupHom cocharacter ≫ i) ≤
    SubgroupFunctor.range b

/-- Choose the noncontained sign, using the actual centralizer containment
and properness of the smooth closed subgroup. -/
def noncontainedSignedDirection
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    (b : B ⟶ G) (hb : IsClosedSubgroup b) (hproper : ¬ IsIso b)
    (hz : centralizer (CommGroupScheme.groupHom ν ≫ i) ≤ SubgroupFunctor.range b) :
    NoncontainedSignedDirection i ν b := by
  classical
  by_cases hp : unipotent (CommGroupScheme.groupHom ν ≫ i) ≤ SubgroupFunctor.range b
  · exact ⟨-ν, Or.inr rfl,
      (not_le_range_unipotent_or_neg hT i ν b hb hproper hz).resolve_left (not_not.mpr hp)⟩
  · exact ⟨ν, Or.inl rfl, hp⟩

end Dynamic

end Langlands.GroupScheme
