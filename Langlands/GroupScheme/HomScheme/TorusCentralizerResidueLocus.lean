import Langlands.AlgebraicGeometry.Morphisms.FppfLocalAtTarget
import Langlands.GroupScheme.FppfExtensionClosedImmersionProof
import Langlands.GroupScheme.HomScheme.AffineFiberArtinian
import Langlands.GroupScheme.HomScheme.AffineFiberTorusAdicLimitsProof
import Langlands.GroupScheme.HomScheme.AffineFiberTorusCentralizer
import Langlands.GroupScheme.HomScheme.CentralTorusSubgroupRepresentability
import Langlands.GroupScheme.HomScheme.TorusCentralizerFieldReflection
import Langlands.GroupScheme.RelativeLevi.ParabolicFieldPointEquality
import Langlands.GroupScheme.Rational.SplitSeriesExtension
import Langlands.GroupScheme.Torus.ClosedImmersionLocus

/-! # The open locus of torus-centralizer residue fibres -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.TorusSubgroupModuli

open SubgroupFunctor

/-- The given subgroup is a torus centralizer on the actual residue fibre. -/
abbrev IsTorusCentralizerAt {S : Scheme.{u}} {G H : GroupScheme S}
    (i : H ⟶ G) (s : S) : Prop :=
  IsTorusCentralizer (range ((baseChange (S.fromSpecResidueField s)).map i))

/-- The residue-fibre homomorphisms of the given inclusion are closed. -/
def HasClosedResidueFibres {S : Scheme.{u}} {G H : GroupScheme S} (i : H ⟶ G) : Prop :=
  ∀ s : S, IsClosedSubgroup ((baseChange (S.fromSpecResidueField s)).map i)

/-- Closedness of the residue fibres is preserved by arbitrary base change. -/
theorem HasClosedResidueFibres.baseChange {S S' : Scheme.{u}} {G H : GroupScheme S}
    {i : H ⟶ G} (hi : HasClosedResidueFibres i) (b : S' ⟶ S) :
    HasClosedResidueFibres ((GroupScheme.baseChange b).map i) := by
  intro s
  let a := S'.fromSpecResidueField s
  let c := S.fromSpecResidueField (b s)
  let r := Spec.map (b.residueFieldMap s)
  have h : r ≫ c = a ≫ b := b.SpecMap_residueFieldMap_fromSpecResidueField s
  apply (TorusClosedImmersionLocus.closed_comp_baseChange_iff b a i).mp
  rw [← h]
  exact (TorusClosedImmersionLocus.closed_comp_baseChange_iff c r i).mpr ((hi (b s)).baseChange r)

private theorem isTorusCentralizer_iterated_iff {S U V : Scheme.{u}} {G H : GroupScheme S}
    (i : H ⟶ G) (b : U ⟶ S) (a : V ⟶ U) (c : V ⟶ S) (he : a ≫ b = c) :
    IsTorusCentralizer (range ((baseChange a).map ((baseChange b).map i))) ↔
      IsTorusCentralizer (range ((baseChange c).map i)) := by
  let e := Descent.pullbackComparison b a c he G
  have h := (isTorusCentralizer_comp_iso_iff ((baseChange a).map ((baseChange b).map i)) e).symm
  change IsTorusCentralizer (range ((baseChange a).map ((baseChange b).map i))) ↔
    IsTorusCentralizer (range (((baseChange a).map ((baseChange b).map i)) ≫
      (Descent.pullbackComparison b a c he G).hom)) at h
  rwa [Descent.pullbackComparison_naturality, range_iso_comp] at h

/-- The residue-fibre condition is invariant under arbitrary change of base. -/
theorem isTorusCentralizerAt_baseChange_iff_of_closedFibres {S S' : Scheme.{u}} {G H : GroupScheme S}
    [Smooth H.X.hom] (hG : HasAffineResidueFibers G) (i : H ⟶ G)
    (hi : HasClosedResidueFibres i) (b : S' ⟶ S) (s : S') :
    IsTorusCentralizerAt ((baseChange b).map i) s ↔ IsTorusCentralizerAt i (b s) := by
  let a := S'.fromSpecResidueField s
  let c := S.fromSpecResidueField (b s)
  let r := Spec.map (b.residueFieldMap s)
  have h : r ≫ c = a ≫ b := b.SpecMap_residueFieldMap_fromSpecResidueField s
  have : IsAffineHom ((baseChange c).obj G).X.hom := hG (b s)
  have : Smooth ((baseChange c).obj H).X.hom :=
    MorphismProperty.pullback_snd (P := @Smooth) _ _ inferInstance
  exact (isTorusCentralizer_iterated_iff i b a (a ≫ b) rfl).trans
    ((isTorusCentralizer_iterated_iff i c r (a ≫ b) h).symm.trans
      (isTorusCentralizer_of_fieldMap_iff ((baseChange c).map i) (hi (b s)) r))

/-- The same residue-fibre comparison for a globally closed inclusion. -/
theorem isTorusCentralizerAt_baseChange_iff {S S' : Scheme.{u}} {G H : GroupScheme S}
    [Smooth H.X.hom] (hG : HasAffineResidueFibers G) (i : H ⟶ G)
    (hi : IsClosedSubgroup i) (b : S' ⟶ S) (s : S') :
    IsTorusCentralizerAt ((baseChange b).map i) s ↔ IsTorusCentralizerAt i (b s) :=
  isTorusCentralizerAt_baseChange_iff_of_closedFibres hG i
    (fun x => hi.baseChange (S.fromSpecResidueField x)) b s

private theorem evaluate_eq_centralizer_of_range {S : Scheme.{u}} {G : GroupScheme S}
    {M U : Over S} {H T : GroupScheme M.left}
    (i : H ⟶ (baseChange M.hom).obj G) (t : T ⟶ (baseChange M.hom).obj G)
    (hi : range i = (range t).centralizer) (a : U ⟶ M) :
    evaluate i a = (evaluate t a).centralizer := by
  let e := Descent.pullbackComparison M.hom a.left U.hom a.w G
  change range ((baseChange a.left).map i ≫ e.hom) =
    (range ((baseChange a.left).map t ≫ e.hom)).centralizer
  rw [range_comp_iso, range_baseChangeHom, hi, SubgroupFunctor.centralizer_baseChange,
    ← range_baseChangeHom]
  simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
    (centralizer_range_eq_comap_of_iso ((baseChange a.left).map t ≫ e.hom) e.symm).symm

private theorem range_le_centralizer_of_central {S : Scheme.{u}} {G H T : GroupScheme S}
    {t : T ⟶ H} (ht : IsCentral t) (i : H ⟶ G) : range i ≤ (range (t ≫ i)).centralizer := by
  have htop : (⊤ : SubgroupFunctor H) ≤ (range t).centralizer := by
    rw [le_centralizer_iff, centralizer_top]
    exact (isCentral_iff_range_le_center t).mp ht
  intro U x hx
  obtain ⟨y, rfl⟩ := hx
  have hy : y ∈ (⊤ : SubgroupFunctor H).carrier U := trivial
  exact centralizer_range_le_comap t i U (htop U hy)

private theorem baseChanged_ranges_eq_of_centralizer_evaluation {S : Scheme.{u}}
    {G H : GroupScheme S} (i : H ⟶ G) {M U : Over S}
    {T C : GroupScheme M.left} (t : T ⟶ (baseChange M.hom).obj H)
    (c : C ⟶ (baseChange M.hom).obj G)
    (hc : range c = (range (t ≫ (baseChange M.hom).map i)).centralizer)
    (a : U ⟶ M) {T₀ : GroupScheme U.left} (t₀ : T₀ ⟶ (baseChange U.hom).obj G)
    (s : T₀ ⟶ (baseChange U.hom).obj H) (hs : s ≫ (baseChange U.hom).map i = t₀)
    (he : evaluate t a = range s) (hi : range ((baseChange U.hom).map i) = (range t₀).centralizer) :
    range ((baseChange a.left).map ((baseChange M.hom).map i)) =
      range ((baseChange a.left).map c) := by
  let iM := (baseChange M.hom).map i
  let iU := (baseChange U.hom).map i
  let e := Descent.pullbackComparison M.hom a.left U.hom a.w G
  apply (range_comp_iso_eq_iff _ _ e).mp
  change evaluate iM a = evaluate c a
  have hl : evaluate (t ≫ iM) a = range t₀ := by
    change range (familyHom (t ≫ (baseChange M.hom).map i) a) = _
    rw [familyHom_postcomp, range_postcomp_congr (familyHom t a) s iU he, hs]
  rw [evaluate_eq_centralizer_of_range c (t ≫ iM) hc a, hl, ← hi]
  rw [evaluate, familyHom, Descent.pullbackComparison_naturality, range_iso_comp]

section Openness

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {G H : GroupScheme S}
  [Smooth G.X.hom] [IsSeparated G.X.hom] [GeometricallyConnected G.X.hom]
  [Smooth H.X.hom]

set_option maxHeartbeats 1200000 in
private theorem exists_etale_neighbourhood_of_centralizer_fibre (hG : HasAffineResidueFibers G)
    (i : H ⟶ G) [Mono i.hom.hom.left] (hi : HasClosedResidueFibres i)
    {M : Over S} [Etale M.hom]
    {T : GroupScheme M.left} (t : T ⟶ (baseChange M.hom).obj H)
    (ht : IsClosedSubgroup t) (hT : RelativeTorus.IsTorus T) (htc : IsCentral t)
    (hu : IsCentralUniversal t) (s : S) (hs : IsTorusCentralizerAt i s) :
    ∃ (V : M.left.Opens), s ∈ Set.range (V.ι ≫ M.hom) ∧
      Set.range (V.ι ≫ M.hom) ⊆ {x | IsTorusCentralizerAt i x} ∧
      IsClosedSubgroup ((baseChange (V.ι ≫ M.hom)).map i) := by
  let f := S.fromSpecResidueField s
  let U := Over.mk f
  let i₀ := (baseChange f).map i
  obtain ⟨T₀, t₀, ht₀, hT₀, he₀⟩ := hs
  let B := hT₀.commGroupScheme
  let b : B.toGrp ⟶ (baseChange f).obj G := t₀
  have hi₀ : IsClosedImmersion i₀.hom.hom.left := hi s
  let hrep : (torusCentralizer b).IsRepresentedBy i₀ :=
    ⟨Over.mono_of_mono_left _, he₀.trans (torusCentralizer_eq_centralizer_range b).symm⟩
  let r := torusCentralizerFactor b hrep
  have hr := isClosedSubgroup_torusCentralizerFactor b hrep hi₀ ht₀
  obtain ⟨a, ha, -⟩ := hu U (range r) (isAdmissible_range r hr hT₀)
    ((isCentral_iff_range_le_center _).mp (isCentral_torusCentralizerFactor b hrep))
  let q := M.hom
  let G' := (baseChange q).obj G
  let H' := (baseChange q).obj H
  let i' : H' ⟶ G' := (baseChange q).map i
  let l := t ≫ i'
  let L := hT.commGroupScheme
  let l' : L.toGrp ⟶ G' := l
  have hq : IsLocallyNoetherian M.left := LocallyOfFiniteType.isLocallyNoetherian q
  have : Smooth G'.X.hom := MorphismProperty.pullback_snd (P := @Smooth) _ _ inferInstance
  have : IsSeparated G'.X.hom := MorphismProperty.pullback_snd (P := @IsSeparated) _ _ inferInstance
  have : GeometricallyConnected G'.X.hom :=
    MorphismProperty.pullback_snd (P := @GeometricallyConnected) _ _ inferInstance
  have : Smooth H'.X.hom := MorphismProperty.pullback_snd (P := @Smooth) _ _ inferInstance
  have hG' : HasAffineResidueFibers G' := hG.baseChange q
  obtain ⟨C, c, hrepC, hc⟩ := relativeTorusCentralizer_isClosedRepresentable_of_separated l' hT
  have hEq : range c = (range l).centralizer :=
    hrepC.2.trans (torusCentralizer_eq_centralizer_range l')
  have : Smooth C.X.hom := smooth_of_artinianAffineCentralizer
    (isAffineHom_artinianPullback_of_residueFibers M.left G' hG') l' hT hc hrepC
  have : GeometricallyConnected C.X.hom := geometricallyConnected_of_affineFiberCentralizer
    hG' l' hT hrepC
  have hi' : HasClosedResidueFibres i' := hi.baseChange q
  have : Mono i'.hom.hom.left := (baseChange_map_isPullback q i).flip.mono_snd_of_mono
  have : IsClosedImmersion c.hom.hom.left := hc
  have : Mono i'.hom.hom := Over.mono_of_mono_left _
  have : Mono c.hom.hom := Over.mono_of_mono_left _
  have hle : range i' ≤ range c := hEq.symm ▸ range_le_centralizer_of_central htc i'
  have he := baseChanged_ranges_eq_of_centralizer_evaluation i t c hEq a t₀ r
    (torusCentralizerFactor_comp b hrep) ha he₀
  let y := a.left (IsLocalRing.closedPoint (S.residueField s))
  have he' := residueFiber_range_eq_of_fieldPoint_range_eq i' c a.left he
  obtain ⟨V, hy, hV⟩ := exists_open_range_eq_of_residue_range_eq i' c hle y he'
  have hqy : q y = s := by
    change (a.left ≫ q) (IsLocalRing.closedPoint (S.residueField s)) = s
    rw [a.w]
    exact S.fromSpecResidueField_apply s _
  have : Mono ((baseChange V.ι).map i').hom.hom.left :=
    (baseChange_map_isPullback V.ι i').flip.mono_snd_of_mono
  have : Mono ((baseChange V.ι).map i').hom.hom := Over.mono_of_mono_left _
  have hiV : IsClosedSubgroup ((baseChange (V.ι ≫ q)).map i) :=
    (TorusClosedImmersionLocus.closed_comp_baseChange_iff q V.ι i).mpr
      (RelativeRoot.IsClosedSubgroup.of_range_eq (hc.baseChange V.ι) hV)
  refine ⟨V, ⟨⟨y, hy⟩, hqy⟩, ?_, hiV⟩
  rintro _ ⟨v, rfl⟩
  apply (isTorusCentralizerAt_baseChange_iff_of_closedFibres hG i hi q (V.ι v)).mp
  apply (isTorusCentralizerAt_baseChange_iff_of_closedFibres hG' i' hi' V.ι v).mp
  have hl : HasClosedResidueFibres l := by
    intro z
    change IsClosedSubgroup ((baseChange (M.left.fromSpecResidueField z)).map (t ≫ i'))
    rw [Functor.map_comp]
    exact (ht.baseChange _).comp (hi' z)
  let aV := V.toScheme.fromSpecResidueField v
  let lV := (baseChange V.ι).map l
  have hEl : range ((baseChange V.ι).map i') = (range lV).centralizer := by
    rw [hV, range_baseChangeHom, hEq, SubgroupFunctor.centralizer_baseChange,
      ← range_baseChangeHom]
  refine ⟨_, (baseChange aV).map lV, (hl.baseChange V.ι) v,
    (hT.baseChange V.ι).baseChange aV, ?_⟩
  change range ((baseChange aV).map ((baseChange V.ι).map i')) = _
  rw [range_baseChangeHom aV ((baseChange V.ι).map i'), hEl,
    SubgroupFunctor.centralizer_baseChange, ← range_baseChangeHom]

private theorem isClosedSubgroup_of_fppfCover {X : Scheme.{u}} {G H : GroupScheme X}
    (i : H ⟶ G) (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage X)
    (h : ∀ j, IsClosedSubgroup ((baseChange (𝒰.f j)).map i)) : IsClosedSubgroup i := by
  have := Langlands.AlgebraicGeometry.FppfLocal.isLocalAtTarget_fppfPrecoverage @IsClosedImmersion
  have : Precoverage.HasPullbacks Scheme.fppfPrecoverage.{u} :=
    inferInstanceAs (Precoverage.HasPullbacks
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)))
  let 𝒱 : Scheme.Cover.{u} Scheme.fppfPrecoverage G.X.left := 𝒰.pullback₁ G.X.hom
  change IsClosedImmersion i.hom.hom.left
  refine MorphismProperty.IsLocalAtTarget.of_zeroHypercover 𝒱 fun j => ?_
  let b := 𝒰.f j
  change IsClosedImmersion (pullback.snd i.hom.hom.left (pullback.fst G.X.hom b))
  have hp := TorusIsomorphismLocus.underlying_isPullback b i
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
    hp.isoPullback.hom, hp.isoPullback_hom_snd]
  exact h j

set_option maxHeartbeats 1600000 in
private theorem exists_torusCentralizerResidueOpen_of_centralUniversal (hG : HasAffineResidueFibers G)
    (i : H ⟶ G) [Mono i.hom.hom.left] (hi : HasClosedResidueFibres i)
    (M : Over S) [Etale M.hom] {T : GroupScheme M.left} (t : T ⟶ (baseChange M.hom).obj H)
    (ht : IsClosedSubgroup t) (hT : RelativeTorus.IsTorus T) (htc : IsCentral t)
    (hu : IsCentralUniversal t) :
    ∃ (W : S.Opens), (W : Set S) = {s | IsTorusCentralizerAt i s} ∧
      IsClosedSubgroup ((baseChange W.ι).map i) := by
  let E : Set S := {s | IsTorusCentralizerAt i s}
  have hn (s : S) (hs : s ∈ E) :=
    exists_etale_neighbourhood_of_centralizer_fibre hG i hi t ht hT htc hu s hs
  have hOpen : IsOpen E := by
    refine isOpen_iff_mem_nhds.mpr fun s hs => ?_
    obtain ⟨V, hsV, hV, _⟩ := hn s hs
    have ho : IsOpen (Set.range (V.ι ≫ M.hom)) := (V.ι ≫ M.hom).isOpenMap.isOpen_range
    exact Filter.mem_of_superset (ho.mem_nhds hsV) hV
  let W : S.Opens := ⟨E, hOpen⟩
  choose V hm hV hclosed using fun w : W => hn w.val w.property
  let q (w : W) : (V w).toScheme ⟶ W.toScheme :=
    IsOpenImmersion.lift W.ι ((V w).ι ≫ M.hom) (by
      rw [Scheme.Opens.range_ι]
      change Set.range ((V w).ι ≫ M.hom) ⊆ E
      exact hV w)
  have hq (w : W) : q w ≫ W.ι = (V w).ι ≫ M.hom := IsOpenImmersion.lift_fac _ _ _
  have het (w : W) : Etale (q w) := by
    have : Etale (q w ≫ W.ι) := by rw [hq]; infer_instance
    exact Etale.of_comp (q w) W.ι
  let 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) W.toScheme :=
    Scheme.Cover.mkOfCovers (P := @Etale) W (fun w => (V w).toScheme) q (fun w => by
      obtain ⟨v, hv⟩ := hm w
      refine ⟨w, v, W.ι.injective ?_⟩
      change (q w ≫ W.ι) v = w.val
      rw [hq, hv]) het
  let 𝒰' : Scheme.Cover.{u} Scheme.fppfPrecoverage W.toScheme :=
    𝒰.changeProp (fun w => by
      have : Etale (𝒰.f w) := 𝒰.map_prop w
      exact ⟨inferInstance, inferInstance⟩)
  refine ⟨W, rfl, isClosedSubgroup_of_fppfCover ((baseChange W.ι).map i) 𝒰' ?_⟩
  intro w
  change IsClosedSubgroup ((baseChange (q w)).map ((baseChange W.ι).map i))
  apply (TorusClosedImmersionLocus.closed_comp_baseChange_iff W.ι (q w) i).mp
  rw [hq]
  exact hclosed w

end Openness

/-- A monic smooth geometrically connected subgroup with closed residue fibres
becomes closed over its open torus-centralizer locus. -/
def TorusCentralizerResidueOpenMonicStatement : Prop :=
  ∀ (S : Scheme.{u}) [IsLocallyNoetherian S] (G H : GroupScheme S)
    [Smooth G.X.hom] [IsSeparated G.X.hom] [GeometricallyConnected G.X.hom]
    [Smooth H.X.hom] [IsSeparated H.X.hom] [QuasiCompact H.X.hom]
    [GeometricallyConnected H.X.hom],
    HasAffineResidueFibers G → ∀ (i : H ⟶ G) [Mono i.hom.hom.left], HasClosedResidueFibres i →
    ∃ (W : S.Opens), (W : Set S) = {s | IsTorusCentralizerAt i s} ∧
      IsClosedSubgroup ((baseChange W.ι).map i)

set_option maxHeartbeats 1200000 in
theorem exists_torusCentralizerResidueOpen_of_mono : TorusCentralizerResidueOpenMonicStatement.{u} := by
  intro S _ G H _ _ _ _ _ _ _ hG i _ hi
  have hH : HasAffineResidueFibers H := by
    intro s
    let b := S.fromSpecResidueField s
    let i' := (baseChange b).map i
    have : IsClosedImmersion i'.hom.hom.left := hi s
    have : IsAffineHom ((baseChange b).obj G).X.hom := hG s
    change IsAffineHom ((baseChange b).obj H).X.hom
    rw [← Over.w i'.hom.hom]
    infer_instance
  have hA := isAffineHom_artinianPullback_of_residueFibers S H hH
  have hArt : Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianNilpotentBijective
      (smallCentralAdmissiblePresheaf H) :=
    smallCentralAdmissiblePresheaf_artinianNilpotentBijective S H hA
  obtain ⟨Y, q, T, t, _, hq, ht, hT, htc, hu⟩ :=
    etaleCentralTorusSubgroupRepresentability S H (affineFiberTorusAdicLimits H hH) hArt
  let M := Over.mk q
  have hM : Etale M.hom := hq
  exact exists_torusCentralizerResidueOpen_of_centralUniversal hG i hi M t ht hT htc hu

/-- The residue-fibre torus-centralizer condition is open for smooth closed
geometrically connected subgroups in the affine-residue-fibre setting. -/
def TorusCentralizerResidueLocusStatement : Prop :=
  ∀ (S : Scheme.{u}) [IsLocallyNoetherian S] (G H : GroupScheme S)
    [Smooth G.X.hom] [IsSeparated G.X.hom] [QuasiCompact G.X.hom]
    [GeometricallyConnected G.X.hom] [Smooth H.X.hom] [GeometricallyConnected H.X.hom],
    HasAffineResidueFibers G → ∀ (i : H ⟶ G), IsClosedSubgroup i →
      IsOpen {s : S | IsTorusCentralizerAt i s}

theorem isOpen_torusCentralizerResidueLocus : TorusCentralizerResidueLocusStatement.{u} := by
  intro S _ G H _ _ _ _ _ _ hG i hi
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsSeparated H.X.hom := by rw [← Over.w i.hom.hom]; infer_instance
  have : QuasiCompact H.X.hom := by rw [← Over.w i.hom.hom]; infer_instance
  obtain ⟨W, hW, _⟩ := exists_torusCentralizerResidueOpen_of_mono S G H hG i
    (fun s => hi.baseChange (S.fromSpecResidueField s))
  rw [← hW]
  exact W.2

/-- The residue-fibre condition on a test is equivalent to its image lying
in the torus-centralizer locus. -/
theorem range_subset_torusCentralizerResidueLocus_iff_of_closedFibres {S S' : Scheme.{u}}
    {G H : GroupScheme S} [Smooth H.X.hom] (hG : HasAffineResidueFibers G)
    (i : H ⟶ G) (hi : HasClosedResidueFibres i) (b : S' ⟶ S) :
    Set.range b ⊆ {s : S | IsTorusCentralizerAt i s} ↔
      HasTorusCentralizerResidueFibres ((baseChange b).map i) := by
  constructor
  · intro h x
    exact (isTorusCentralizerAt_baseChange_iff_of_closedFibres hG i hi b x).mpr (h ⟨x, rfl⟩)
  · rintro h _ ⟨x, rfl⟩
    exact (isTorusCentralizerAt_baseChange_iff_of_closedFibres hG i hi b x).mp (h x)

/-- The image criterion for a globally closed inclusion. -/
theorem range_subset_torusCentralizerResidueLocus_iff {S S' : Scheme.{u}}
    {G H : GroupScheme S} [Smooth H.X.hom] (hG : HasAffineResidueFibers G)
    (i : H ⟶ G) (hi : IsClosedSubgroup i) (b : S' ⟶ S) :
    Set.range b ⊆ {s : S | IsTorusCentralizerAt i s} ↔
      HasTorusCentralizerResidueFibres ((baseChange b).map i) :=
  range_subset_torusCentralizerResidueLocus_iff_of_closedFibres hG i
    (fun s => hi.baseChange (S.fromSpecResidueField s)) b

end Langlands.GroupScheme.TorusSubgroupModuli
