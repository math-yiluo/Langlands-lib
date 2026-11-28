import Langlands.GroupScheme.Rational.TypeE6BranchLineMatching
import Langlands.GroupScheme.Rational.TypeE6BranchLeviCocenter
import Langlands.GroupScheme.Rational.NumberFieldTypeE6LeviReduction
import Langlands.GroupScheme.SimplyConnected.FactorCartanComponent
import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerDerivedProof
import Langlands.GroupScheme.Reductive.SeparablyClosedAlmostSimpleAbsoluteProof
import Langlands.GroupScheme.Derived.RepresentabilityProof
import Langlands.GroupScheme.Rational.SplitTorusCharacterRestriction
import Langlands.GroupScheme.SimplyConnected.TrivialStarInnerTwist
import Langlands.GroupScheme.Torus.WeilRestrictionNormOneCharacters

/-! # The E6 branch Levi factorization from the distinguished vertex -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false in
private theorem isAbsolutelyAlmostSimple_of_simplyConnected_typeA5
    {k : Type u} [Field k] {D : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom]
    (hsc : IsSimplyConnected D) (d : TitsIndexData D) (e : d.Vertex ≃ Fin 5)
    (hCartan : ∀ a c, d.cartan a c = CartanMatrix.A 5 (e a) (e c)) :
    IsAbsolutelyAlmostSimple D := by
  let E := SeparableClosure k
  let D_E := (GroupScheme.baseChange (algebraBaseMap k E)).obj D
  have hscE : IsSimplyConnected D_E := isSimplyConnectedFieldExtension k E D hsc
  let hsem := hscE.isSemisimple
  let : IsAffineHom D_E.X.hom := hsem.isConnectedReductive.isAffineHom
  let : Smooth D_E.X.hom := hsem.isConnectedReductive.smooth
  let P := hscE.almostSimpleProduct
  let p := d.pinning.toSplitPinning
  let f (a : Fin 5) : P.Index := d.geometricFactorIndex P hsem (e.symm a)
  have hstep (a c : Fin 5) (hac : CartanMatrix.A 5 a c ≠ 0) : f a = f c := by
    apply d.geometricFactorIndex_eq_of_cartanConnected
    apply d.cartanConnected_of_cartan_ne_zero
    simpa only [hCartan, e.apply_symm_apply] using hac
  have h01 := hstep 0 1 (by decide)
  have h12 := hstep 1 2 (by decide)
  have h23 := hstep 2 3 (by decide)
  have h34 := hstep 3 4 (by decide)
  have hall (a : Fin 5) : f 0 = f a := by
    fin_cases a
    · rfl
    · exact h01
    · exact h01.trans h12
    · exact h01.trans (h12.trans h23)
    · exact h01.trans (h12.trans (h23.trans h34))
  have hsurj : Function.Surjective f := by
    intro i
    let t := P.factorMaximalTorus hsem.isConnectedReductive p.inclusion
      p.isSplitTorus p.isMaximalTorus i
    let hpart := (P.isAlmostSimple i).isSemisimple.isConnectedReductive
    let : IsAffineHom (P.factor i).X.hom := hpart.isAffineHom
    obtain ⟨J, hJ, R, hR, hRred⟩ :=
      rootDatumExistence E (P.factor i) hpart t.torus t.split t.subgroupHom t.isMaximalTorus
    let : Finite J := hJ
    let : R.IsReduced := hRred
    obtain ⟨α, hα⟩ :=
      (P.isAlmostSimple i).relativeRoots_nonempty_of_split_maximalTorus t.subgroupHom
        t.split t.isMaximalTorus
    let : Nonempty J := ⟨hR.relativeRootIndex ⟨α, hα⟩⟩
    let B := t.inducedBase P hsem p hR
    obtain ⟨x⟩ : Nonempty B.support := B.support_nonempty.to_subtype
    let y := t.simpleRootIndexEquiv P hsem p hR x
    refine ⟨e y.val, ?_⟩
    simpa only [f, e.symm_apply_apply, TitsIndexData.geometricFactorIndex, p,
      GaloisPinningData.toSplitPinning] using y.property
  let : Subsingleton P.Index := ⟨by
    intro i j
    obtain ⟨a, rfl⟩ := hsurj i
    obtain ⟨c, rfl⟩ := hsurj j
    exact (hall a).symm.trans (hall c)⟩
  let : Unique P.Index := uniqueOfSubsingleton (f 0)
  have hE : IsAlmostSimple D_E :=
    (P.isAlmostSimple (default : P.Index)).of_iso (P.iso ≪≫ productUniqueIso P.factor)
  exact IsAbsolutelyAlmostSimple.of_fieldExtension (K := E)
    (separablyClosedAlmostSimpleAbsolute E D_E hE)

set_option backward.isDefEq.respectTransparency false in
private theorem TypeE6BranchDerivedPinning.trivial_star_of_split_ambient
    {F : Type u} [Field F] [NumberField F]
    {G M D : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom]
    {d : TitsIndexData G} {e : d.Vertex ≃ Fin 6} {i : D ⟶ M}
    (p : TypeE6BranchDerivedPinning d e i) (hi : IsDerivedSubgroup i)
    (dD : TitsIndexData D) (hT : IsSplitTorus d.pinning.torus.toGrp)
    (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (a : dD.Vertex) : dD.star σ a = a := by
  let E := SeparableClosure F
  let b := algebraBaseMap F E
  let B := GroupScheme.baseChange b
  let C := CommGroupScheme.baseChange b
  let t := CommGroupScheme.groupHom (C.map p.torusMap)
  have ht : IsClosedSubgroup t := by
    refine IsClosedSubgroup.of_comp (p.centralizerTorus_maximal.2.1.baseChange b) ?_
    change IsClosedSubgroup (B.map (CommGroupScheme.groupHom p.torusMap) ≫ B.map p.centralizerTorus)
    rw [← Functor.map_comp, p.square, Functor.map_comp]
    exact p.pinning.isMaximalTorus.2.1.comp (hi.1.baseChange b)
  let : Mono t.hom.hom.left := ht.mono
  have hg : p.pinning.galoisAction σ = 1 := by
    apply StarActionIndependence.equiv_ext_of_weightMap
    intro β
    rw [StarActionIndependence.galoisAction_weightMap_apply]
    obtain ⟨α, hα⟩ := p.pinning.isSplitTorus.characterRestrict_surjective_of_mono (hT.baseChange b) t β
    change C.map p.torusMap ≫ α = β at hα
    rw [← hα, characterLattice.galoisRepresentation_precompose,
      TrivialStarInnerTwist.galoisRepresentation_of_isSplitTorus d.pinning.torus hT]
    rfl
  have hp : p.pinning.starAction σ = 1 := (p.pinning.starAction_eq_one_iff σ).mpr (by
    rw [hg]
    exact Subgroup.one_mem _)
  obtain ⟨_, _, A, _, _, _, hA⟩ :=
    StarActionIndependence.starActionIndependence F E D p.pinning dD.pinning
  have hd : dD.pinning.starAction σ = 1 := by
    apply Subtype.ext
    apply StarActionIndependence.equiv_ext_of_weightMap
    intro α
    obtain ⟨β, rfl⟩ := A.weightEquiv.surjective α
    have h := hA σ
    rw [hp] at h
    exact (congrArg (fun w => w.weightMap β) h).symm
  apply Subtype.ext
  change (dD.pinning.starAction σ).val.indexEquiv a.val = a.val
  rw [hd]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The branch factorization has inner derived type whenever the ambient
torus of the supplied index is already split over the number field. -/
theorem TypeE6BranchCentralizerCocycle.exists_leviFactorization
    {F : Type u} [Field F] [NumberField F]
    {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {d : TitsIndexData G} {e : d.Vertex ≃ Fin 6}
    {U : Over (Spec (CommRingCat.of F))} {ξ : Cocycle G U}
    (p : TypeE6BranchCentralizerCocycle d e ξ)
    (hsc : IsSimplyConnected G)
    (hCartan : ∀ a c, d.cartan a c = CartanMatrix.E 6 (e a) (e c)) :
    ∃ q : TypeE6SplitLeviCocycleFactorization ξ,
      IsSplitTorus d.pinning.torus.toGrp →
        ∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (a : q.index.Vertex),
          q.index.star σ a = a := by
  let χ := CommGroupScheme.groupHom p.cocharacter ≫ d.splitInclusion
  have hM := splitTorusCentralizerReductive F G hsc.isSemisimple.isConnectedReductive
    (Gm _) χ isSplitTorus_gm p.centralizer p.inclusion p.represents
  let : IsAffineHom p.centralizer.X.hom := hM.isAffineHom
  let : Smooth p.centralizer.X.hom := hM.smooth
  obtain ⟨D, i, hDa, hDf, hi⟩ := derivedSubgroupRepresentability F p.centralizer
  let : IsAffineHom D.X.hom := hDa
  let : LocallyOfFiniteType D.X.hom := hDf
  have hD := splitTorusCentralizerDerivedSimplyConnected F G hsc (Gm _) χ
    ⟨isSplitTorus_gm, p.line_closed⟩ p.centralizer p.inclusion p.represents D i hi
  obtain ⟨dD⟩ := titsIndexExistence F D hD.isSemisimple
  obtain ⟨t⟩ := nonempty_typeE6BranchDerivedPinning d e hCartan p.cocharacter p.coweight_eq
    p.inclusion p.represents hM i hi
  obtain ⟨eD, heD⟩ := t.exists_typeA5_numbering hCartan dD
  obtain ⟨Q, q, hQ, hq⟩ := t.exists_splitCocenter hsc hM hi p.cocharacter p.coweight_eq
  refine ⟨{
    line := χ
    line_closed := p.line_closed
    centralizer := p.centralizer
    inclusion := p.inclusion
    centralizer_closed := p.centralizer_closed
    represents := p.represents
    derivedGroup := D
    derivedInclusion := i
    isDerived := hi
    simplyConnected := hD
    absolutelyAlmostSimple := isAbsolutelyAlmostSimple_of_simplyConnected_typeA5 hD dD eD heD
    index := dD
    numbering := eD
    cartan_eq := heD
    quotient := Q.toGrp
    quotientMap := q
    quotient_split := hQ
    isQuotient := hq
    cochain := p.cochain
    cocycle := p.cocycle
    factorization := p.factorization }, ?_⟩
  exact t.trivial_star_of_split_ambient hi dD

/-- The arithmetic marking of the short-arm vertex implies the A5 Levi
factorization for totally complex E6 groups. -/
def NumberFieldTotallyComplexTypeE6BranchLeviReductionStatement : Prop :=
  NumberFieldTotallyComplexTypeE6BranchDistinguishedStatement.{u} →
    NumberFieldTotallyComplexTypeE6LeviFactorizationStatement.{u}

theorem numberFieldTotallyComplexTypeE6BranchLeviReduction :
    NumberFieldTotallyComplexTypeE6BranchLeviReductionStatement.{u} := by
  intro hmark F _ _ hF G _ _ d e hsc habs hCartan L _ _ _ _ ξ
  obtain ⟨M, _, _, _, _, _, _, ⟨p⟩⟩ :=
    exists_typeE6BranchCentralizerCocycle hmark hF d e hCartan hsc habs L ξ
  obtain ⟨q, _⟩ := p.exists_leviFactorization hsc hCartan
  exact ⟨M, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ⟨q⟩⟩

/-- The marked-vertex arithmetic and the outer type A Hasse kernel suffice
for totally complex vanishing in both forms of E6. -/
theorem numberFieldTotallyComplexTypeE6Vanishing_of_branchDistinguished
    (hmark : NumberFieldTotallyComplexTypeE6BranchDistinguishedStatement.{u})
    (houter : NumberFieldOuterTypeAHasseStatement.{u}) :
    NumberFieldTotallyComplexTypeE6VanishingStatement.{u} :=
  numberFieldTotallyComplexTypeE6Vanishing_of_leviFactorization
    (numberFieldTotallyComplexTypeE6BranchLeviReduction hmark) houter

end Langlands.GroupScheme
