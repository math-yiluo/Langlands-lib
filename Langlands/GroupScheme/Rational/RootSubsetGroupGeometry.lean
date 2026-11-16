import Langlands.GroupScheme.Rational.ClosedRootSubsetStatements
import Langlands.GroupScheme.GeneratedFamilyBaseChange
import Langlands.GroupScheme.Rational.RootSubgroupRealizationProof
import Langlands.GroupScheme.Rational.RootSubgroupBaseChange
import Langlands.GroupScheme.Torus.CentralizerConnected
import Langlands.GroupScheme.Torus.CentralizerSmooth

/-! # Geometry and field extension of generated root-subset groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (X : Set (characterLattice T))

/-- Representatives of the centralizer and the selected root functors turn
the root-subset minimality condition into ordinary family generation. -/
theorem isRootSubsetGroup_iff_isGeneratedByFamily
    (A : Option X → GroupScheme (Spec (CommRingCat.of k)))
    (a : ∀ j, A j ⟶ G)
    (hz : (torusCentralizer i).IsRepresentedBy (a none))
    (hr : ∀ γ : X, (RelativeRoot.subgroup i γ.val).IsRepresentedBy (a (some γ)))
    {H : GroupScheme (Spec (CommRingCat.of k))} (h : H ⟶ G) :
    IsRootSubsetGroup i X h ↔ IsGeneratedByFamily A a h := by
  have hfamily {Q : GroupScheme (Spec (CommRingCat.of k))} (q : Q ⟶ G) :
      (∀ j, FactorsThrough (a j).hom.hom q) ↔
        torusCentralizer i ≤ SubgroupFunctor.range q ∧
          ∀ γ ∈ X, RelativeRoot.subgroup i γ ≤ SubgroupFunctor.range q := by
    constructor
    · intro ha
      refine ⟨?_, ?_⟩
      · rw [← hz.2]
        exact (factorsThrough_hom_iff_range_le _ _).mp (ha none)
      · intro γ hγ
        rw [← (hr ⟨γ, hγ⟩).2]
        exact (factorsThrough_hom_iff_range_le _ _).mp (ha (some ⟨γ, hγ⟩))
    · rintro ⟨hc, hr'⟩ j
      apply (factorsThrough_hom_iff_range_le _ _).mpr
      cases j with
      | none => exact hz.2.le.trans hc
      | some γ => exact (hr γ).2.le.trans (hr' γ.val γ.property)
  constructor
  · intro hh
    refine ⟨hh.1, (hfamily h).mpr ⟨hh.2.1, hh.2.2.1⟩, ?_⟩
    intro Q q hq ha
    exact hh.2.2.2 Q q hq ((hfamily q).mp ha).1 ((hfamily q).mp ha).2
  · intro hh
    refine ⟨hh.1, ((hfamily h).mp hh.2.1).1, ((hfamily h).mp hh.2.1).2, ?_⟩
    intro Q q hq hc hr'
    exact hh.2.2 Q q hq ((hfamily q).mpr ⟨hc, hr'⟩)

variable [IsAffineHom G.X.hom]

/-- There is a smooth affine connected family representing the whole-torus
centralizer and every selected actual relative-root functor. -/
theorem exists_rootSubsetGeneratingFamily (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hX : X ⊆ relativeRoots i) :
    ∃ (A : Option X → GroupScheme (Spec (CommRingCat.of k))) (a : ∀ j, A j ⟶ G),
      (∀ j, Smooth (A j).X.hom ∧ IsAffineHom (A j).X.hom ∧
        ConnectedSpace (A j).X.left) ∧
      (torusCentralizer i).IsRepresentedBy (a none) ∧
      ∀ γ : X, (RelativeRoot.subgroup i γ.val).IsRepresentedBy (a (some γ)) := by
  classical
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  obtain ⟨Z, z, hzc, hzs, hz⟩ :=
    torusCentralizer_hasSmoothClosedRepresentative i hi.1 hG.smooth
  have hconn : ConnectedSpace Z.X.left := hi.1.1.connectedSpace_centralizer i hz
  have hroot (γ : X) :
      ∃ (U : GroupScheme (Spec (CommRingCat.of k))) (j : U ⟶ G),
        (RelativeRoot.subgroup i γ.val).IsRepresentedBy j ∧ IsClosedSubgroup j ∧
          Smooth U.X.hom ∧ ConnectedSpace U.X.left := by
    obtain ⟨U, j, hj, hjc, hjs, hjconn, _⟩ :=
      RelativeRoot.rootSubgroupRealization k G hG T i hi γ.val (hX γ.property)
    exact ⟨U, j, hj, hjc, hjs, hjconn⟩
  choose U j hj hjc hjs hjconn using hroot
  let A : Option X → GroupScheme (Spec (CommRingCat.of k)) := fun q =>
    match q with
    | none => Z
    | some γ => U γ
  let a : ∀ q, A q ⟶ G := fun q =>
    match q with
    | none => z
    | some γ => j γ
  refine ⟨A, a, ?_, hz, hj⟩
  intro q
  cases q with
  | none => exact ⟨hzs, hzc.isAffineHom, hconn⟩
  | some γ => exact ⟨hjs γ, (hjc γ).isAffineHom, hjconn γ⟩

/-- Any subset of actual relative roots has a smooth affine connected closed
generated subgroup, without a closure or convexity assumption on the subset. -/
theorem exists_smooth_rootSubsetGroup (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hX : X ⊆ relativeRoots i) :
    ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ G),
      IsRootSubsetGroup i X h ∧ Smooth H.X.hom ∧ IsAffineHom H.X.hom ∧
        ConnectedSpace H.X.left := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  obtain ⟨A, a, hA, hz, hr⟩ := exists_rootSubsetGeneratingFamily i X hG hi hX
  obtain ⟨H, h, hs, ha, hc, hh⟩ :=
    FiniteGeneration.exists_smooth_generated_family (A := A) (a := a) hA
  exact ⟨H, h, (isRootSubsetGroup_iff_isGeneratedByFamily i X A a hz hr h).mpr hh,
    hs, ha, hc⟩

/-- The minimality predicate forces the same smooth affine connected geometry
on every supplied representative of the generated group. -/
theorem IsRootSubsetGroup.smooth_affine_connected (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hX : X ⊆ relativeRoots i)
    {H : GroupScheme (Spec (CommRingCat.of k))} {h : H ⟶ G}
    (hh : IsRootSubsetGroup i X h) :
    Smooth H.X.hom ∧ IsAffineHom H.X.hom ∧ ConnectedSpace H.X.left := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨L, l, hl, hs, ha, hc⟩ := exists_smooth_rootSubsetGroup i X hG hi hX
  have hr : (SubgroupFunctor.range h).IsRepresentedBy h := by
    let : IsClosedImmersion h.hom.hom.left := hh.1
    exact ⟨Over.mono_of_mono_left _, rfl⟩
  have hr' : (SubgroupFunctor.range h).IsRepresentedBy l := by
    let : IsClosedImmersion l.hom.hom.left := hl.1
    exact ⟨Over.mono_of_mono_left _, (hh.range_eq hl).symm⟩
  let e := (Grp.forget _).mapIso (hr.isoOfIsRepresentedBy hr')
  exact ⟨smooth_of_over_iso e hs, hh.1.isAffineHom, connectedSpace_of_over_iso e hc⟩

/-- Generation by the whole-torus centralizer and selected root functors
commutes with every field extension. The root subset is its actual character
image, and no maximality of the extended split torus is asserted. -/
theorem IsRootSubsetGroup.baseChange (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hX : X ⊆ relativeRoots i)
    {H : GroupScheme (Spec (CommRingCat.of k))} {h : H ⟶ G}
    (hh : IsRootSubsetGroup i X h)
    (K : Type u) [Field K] [Algebra k K] :
    let b := FamilyBaseChange.extension (k := k) K
    IsRootSubsetGroup ((GroupScheme.baseChange b).map i)
      (characterLattice.baseChange b T '' X) ((GroupScheme.baseChange b).map h) := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let b := FamilyBaseChange.extension (k := k) K
  let B := GroupScheme.baseChange b
  obtain ⟨A, a, hA, hz, hr⟩ := exists_rootSubsetGeneratingFamily i X hG hi hX
  have hg := (isRootSubsetGroup_iff_isGeneratedByFamily i X A a hz hr h).mp hh
  have hb := hg.baseChange K A a hA
  have hzK : (torusCentralizer (T := (CommGroupScheme.baseChange b).obj T)
      (B.map i)).IsRepresentedBy (B.map (a none)) := by
    rw [torusCentralizer_baseChange]
    exact hz.baseChange b
  have hrK (γ : X) :
      (RelativeRoot.subgroup (B.map i) (characterLattice.baseChange b T γ.val)).IsRepresentedBy
        (B.map (a (some γ))) := by
    rw [RelativeRoot.subgroup_baseChange]
    exact (hr γ).baseChange b
  refine ⟨hb.1, ?_, ?_, ?_⟩
  · rw [← hzK.2]
    exact (factorsThrough_hom_iff_range_le _ _).mp (hb.2.1 none)
  · rintro γ ⟨δ, hδ, rfl⟩
    rw [← (hrK ⟨δ, hδ⟩).2]
    exact (factorsThrough_hom_iff_range_le _ _).mp (hb.2.1 (some ⟨δ, hδ⟩))
  · intro Q q hq hc hroot
    apply hb.2.2 Q q hq
    intro j
    apply (factorsThrough_hom_iff_range_le _ _).mpr
    cases j with
    | none => exact hzK.2.le.trans hc
    | some γ => exact (hrK γ).2.le.trans (hroot _ ⟨γ.val, γ.property, rfl⟩)

/-- Uniform existence, geometry of supplied representatives, and field-extension
compatibility for the closed groups generated by a root subset and the torus
centralizer. -/
def RootSubsetGroupGeometryStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (_hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    ∀ X : Set (characterLattice T), X ⊆ relativeRoots i →
      (∃ (H : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ G),
        IsRootSubsetGroup i X h ∧ Smooth H.X.hom ∧ IsAffineHom H.X.hom ∧
          ConnectedSpace H.X.left) ∧
      ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ G),
        IsRootSubsetGroup i X h →
          (Smooth H.X.hom ∧ IsAffineHom H.X.hom ∧ ConnectedSpace H.X.left) ∧
          ∀ (K : Type u) [Field K] [Algebra k K],
            let b := FamilyBaseChange.extension (k := k) K
            IsRootSubsetGroup ((GroupScheme.baseChange b).map i)
              (characterLattice.baseChange b T '' X) ((GroupScheme.baseChange b).map h)

theorem rootSubsetGroupGeometry : RootSubsetGroupGeometryStatement.{u} := by
  intro k _ G hG T i hi
  let : IsAffineHom G.X.hom := hG.isAffineHom
  intro X hX
  refine ⟨exists_smooth_rootSubsetGroup i X hG hi hX, ?_⟩
  intro H h hh
  refine ⟨IsRootSubsetGroup.smooth_affine_connected i X hG hi hX hh, ?_⟩
  intro K _ _
  exact IsRootSubsetGroup.baseChange i X hG hi hX hh K

end Langlands.GroupScheme
