import Langlands.GroupScheme.Rational.StandardAssociatedOppositeTransportStatement
import Langlands.GroupScheme.Rational.StandardAssociatedConjugation
import Langlands.GroupScheme.Rational.CocharacterStandardFace
import Langlands.GroupScheme.Rational.RootSignUnipotentLie
import Langlands.GroupScheme.Rational.RelativeTitsNondegeneracy
import Langlands.GroupScheme.Dynamic.ConnectedProof

/-! # Associated opposite transport from negation stability of relative roots

For a longest lift `n` of `longestRep cs J` and a standard cocharacter `zeta`
for `J`, conjugation by `n` pulls the dynamic groups of the opposite of `zeta`
back to the dynamic groups of one cocharacter of the torus. That cocharacter is
standard for the associated subset once the actual relative roots are stable
under negation. The root-sign comparisons for dynamic parabolics and radicals
then identify those groups with the associated standard parabolic and radical.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.Aubert.General.RationalPointFamily Langlands.Group.RelativeWeylIndexing

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [IsAffineHom G.X.hom]

section Conjugation

/-- The cocharacter whose dynamic groups are the pullbacks, under conjugation by
`n`, of the dynamic groups of the opposite of `zeta`. -/
def associatedOppositeCocharacter (n : normalizerPoints i) (zeta : cocharacterLattice T) :
    cocharacterLattice T :=
  (cocharacterAut (normalizingAut i n)).symm (-zeta)

omit [IsAffineHom G.X.hom] in
theorem groupHom_cocharacterAut_associatedOppositeCocharacter
    (n : normalizerPoints i) (zeta : cocharacterLattice T) :
    CommGroupScheme.groupHom
        (cocharacterAut (normalizingAut i n) (associatedOppositeCocharacter i n zeta)) ≫ i =
      Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i) := by
  rw [associatedOppositeCocharacter, LinearEquiv.apply_symm_apply,
    groupHom_neg_comp_eq_oppositeCocharacter i zeta]

omit [IsAffineHom G.X.hom] in
/-- Conjugation by `n` pulls the opposite dynamic parabolic of `zeta` back to the
dynamic parabolic of the associated opposite cocharacter, on every test scheme. -/
theorem parabolic_oppositeCocharacter_comap_innerIso
    (n : normalizerPoints i) (zeta : cocharacterLattice T) :
    (Dynamic.parabolic
        (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i))).comap
        (G.innerIso (n : GroupScheme.rationalPoints G)).hom =
      Dynamic.parabolic
        (CommGroupScheme.groupHom (associatedOppositeCocharacter i n zeta) ≫ i) := by
  rw [← groupHom_cocharacterAut_associatedOppositeCocharacter i n zeta,
    groupHom_cocharacterAut_comp]
  exact (Dynamic.parabolic_eq_comap_of_iso _ _).symm

omit [IsAffineHom G.X.hom] in
/-- Conjugation by `n` pulls the opposite dynamic radical of `zeta` back to the
dynamic radical of the associated opposite cocharacter, on every test scheme. -/
theorem unipotent_oppositeCocharacter_comap_innerIso
    (n : normalizerPoints i) (zeta : cocharacterLattice T) :
    (Dynamic.unipotent
        (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom zeta ≫ i))).comap
        (G.innerIso (n : GroupScheme.rationalPoints G)).hom =
      Dynamic.unipotent
        (CommGroupScheme.groupHom (associatedOppositeCocharacter i n zeta) ≫ i) := by
  rw [← groupHom_cocharacterAut_associatedOppositeCocharacter i n zeta,
    groupHom_cocharacterAut_comp]
  exact (Dynamic.unipotent_eq_comap_of_iso _ _).symm

variable [Mono i.hom.hom.left]

omit [IsAffineHom G.X.hom] in
/-- Pairing with the associated opposite cocharacter is minus pairing the Weyl
image with `zeta`. -/
theorem latticePairing_associatedOppositeCocharacter
    (n : normalizerPoints i) (zeta : cocharacterLattice T) (α : characterLattice T) :
    latticePairing T α (associatedOppositeCocharacter i n zeta) =
      -latticePairing T (weylAction i n α) zeta := by
  have h := latticePairing_characterAut_cocharacterAut (normalizingAut i n) α
    (associatedOppositeCocharacter i n zeta)
  rw [associatedOppositeCocharacter, LinearEquiv.apply_symm_apply] at h
  rw [associatedOppositeCocharacter, ← h, map_neg]
  rfl

end Conjugation

section Realization

variable [Mono i.hom.hom.left] (ν : cocharacterLattice T)
  [Fintype (SimpleRoot i ν)] [Fintype (relativeWeylGroup i)]
  {CM : CoxeterMatrix (SimpleRoot i ν)}
  (cs : CoxeterSystem CM (relativeWeylGroup i))

/-- Under negation stability, the associated opposite cocharacter of a longest
lift and a standard cocharacter for `J` is standard for the associated subset. -/
theorem isStandardCocharacter_associatedOppositeCocharacter
    (hν : IsGenericCocharacter i ν)
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i)
    (h : IsRelativeWeylCoxeterRealization i ν cs)
    (J : Finset (SimpleRoot i ν)) (n : normalizerPoints i)
    (hn : QuotientGroup.mk n = longestRep cs J)
    {zeta : cocharacterLattice T} (hzeta : IsStandardCocharacter i ν (rootSet i ν J) zeta) :
    IsStandardCocharacter i ν (rootSet i ν (associatedSubset cs J))
      (associatedOppositeCocharacter i n zeta) := by
  have hK := (weylAction_image_associatedStandardFamily i ν cs h J n hn ∅).2
  refine ⟨rootSet_subset i ν _, fun α hα => ?_, fun α hα hαK => ?_⟩
  · rw [latticePairing_associatedOppositeCocharacter,
      hzeta.2.1 _ (hK ▸ Set.mem_image_of_mem _ hα), neg_zero]
  · rw [latticePairing_associatedOppositeCocharacter, Left.neg_pos_iff]
    let a : SimpleRoot i ν := ⟨α, hα⟩
    have ha : a ∉ associatedSubset cs J := fun ha => hαK ((val_mem_rootSet i ν _ a).2 ha)
    have hroot : weylAction i n α ∈ relativeRoots i :=
      weylAction_mapsTo_relativeRoots i n hα.1.1
    have hnotpos : weylAction i n α ∉ positiveRelativeRoots i ν := by
      intro hpos
      apply ha
      rw [← positiveSimpleSet_longestRep cs J, mem_positiveSimpleSet]
      apply (h.2.2.1 _ a).mpr
      rw [← hn, schemeWeylCharacterAction_mk]
      exact hpos
    have hν' : latticePairing T (weylAction i n α) ν < 0 :=
      lt_of_le_of_ne (not_lt.mp fun hlt => hnotpos ⟨hroot, hlt⟩) (hν _ hroot)
    have hpos : -weylAction i n α ∈ positiveRelativeRoots i ν :=
      ⟨hneg _ hroot, by simpa using neg_pos.mpr hν'⟩
    have hnot : -weylAction i n α ∉ AddSubmonoid.closure (rootSet i ν J) := by
      intro hmem
      have key : ∀ x ∈ AddSubmonoid.closure (rootSet i ν J),
          0 ≤ latticePairing T ((weylAction i n).symm x) ν := by
        intro x hx
        induction hx using AddSubmonoid.closure_induction with
        | mem x hx =>
          rw [← hK] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          rw [LinearEquiv.symm_apply_apply]
          exact (rootSet_subset i ν _ hy).1.2.le
        | zero => simp
        | add x y _ _ hx hy =>
          rw [map_add, map_add]
          exact add_nonneg hx hy
      have hle := key _ hmem
      rw [map_neg, LinearEquiv.symm_apply_apply, map_neg] at hle
      have hαν := hα.1.2
      simp only [LinearMap.neg_apply] at hle
      omega
    have hlt := (hzeta.pairing_pos_iff_not_mem_closure i ν hpos).mpr hnot
    simpa using hlt

/-- Associated opposite transport for one Coxeter realization, from negation
stability of the relative roots and the two root-sign comparisons. -/
theorem isStandardAssociatedOppositeTransport_of_rootSigns
    (hν : IsGenericCocharacter i ν)
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i)
    (hparabolic : ∀ zeta eta : cocharacterLattice T,
      (∀ α ∈ relativeRoots i,
        0 ≤ latticePairing T α zeta → 0 ≤ latticePairing T α eta) →
      Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i) ≤
        Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i))
    (hunipotent : ∀ zeta eta : cocharacterLattice T,
      (∀ α ∈ relativeRoots i,
        0 < latticePairing T α zeta → 0 < latticePairing T α eta) →
      Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i) ≤
        Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i))
    (h : IsRelativeWeylCoxeterRealization i ν cs) :
    IsStandardAssociatedOppositeTransport i ν cs := by
  intro J n hn zeta hzeta
  have hxi := isStandardCocharacter_associatedOppositeCocharacter i ν cs hν hneg h J n hn hzeta
  rw [parabolic_oppositeCocharacter_comap_innerIso, unipotent_oppositeCocharacter_comap_innerIso]
  refine ⟨(dynamicParabolic_eq_standardParabolic_of_isStandardCocharacter i ν hν hneg
    hparabolic hxi).symm, le_antisymm (standardUnipotent_le_dynamicUnipotent i ν hxi) ?_⟩
  intro U g hg
  rw [mem_standardUnipotent]
  intro eta heta
  exact hunipotent _ eta (fun α hα hpos =>
    (heta.root_pairing_implications_of_subset i ν hν hneg hxi (Set.Subset.refl _) hα).2.2
      hpos) U hg

end Realization

/-- Negation stability of the actual relative roots implies the associated
opposite transport target at its full field and universe scope. -/
theorem standardAssociatedOppositeTransport_of_relativeRootNegation
    (hnegation : RelativeRootNegationStatement.{u}) :
    StandardAssociatedOppositeTransportStatement.{u} := by
  intro k _ G hG T i hi ν
  let _ := hG.isAffineHom
  let _ := hi.isSplitSubtorus.mono
  intro hν _ _ CM cs h
  have hsigns := relativeRootSignInclusions_of_connectedness dynamicConnected k G hG T i hi
  exact isStandardAssociatedOppositeTransport_of_rootSigns i ν cs hν
    (hnegation k G hG T i hi) (fun zeta eta => (hsigns zeta eta).1.2)
    (fun zeta eta => (hsigns zeta eta).2) h

end Langlands.GroupScheme
