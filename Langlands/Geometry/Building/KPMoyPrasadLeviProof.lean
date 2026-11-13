import Langlands.Geometry.Building.KPMoyPrasadLeviStatement
import Langlands.Geometry.Building.MoyPrasadProductCoordinates
import Langlands.BruhatTits.SpecialCompact.MoyPrasadParabolicProduct
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OpenCellPoints
import Langlands.BruhatTits.SpecialCompact.LeviValuationRestriction
import Langlands.BruhatTits.SpecialCompact.LeviApartmentComparison
import Langlands.GroupScheme.Rational.StandardParabolicEndpointsNegation
import Langlands.BruhatTits.Unipotent.RationalPointCompactOpen

/-!
# KP Proposition 13.2.5(5),(6) at positive depth

Proof of `MoyPrasadLeviStatement`: for `r > 0`, `P_{x,r}` has a topological Iwahori
decomposition with respect to every standard parabolic subgroup, conjugation by the
nonnegative part of a split component preserves its radical intersections, and its
intersection with a standard Levi subgroup is the image of the Levi's Moy–Prasad subgroup.
The covering comes from the published `range_orderedMoyPrasadProduct_eq`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.Geometry.Building.MoyPrasadLeviProof

section Covering

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G) (Zf : P.CentralizerFiltration)

/-- The published exact range of the ordered Moy–Prasad product covers `P_{x,r}` by the
opposite radical depth group, the literal Levi intersection and the radical depth group. -/
theorem moyPrasadRadicalDepthProduct_surjective
    (hP : P.SatisfiesApartmentAxioms) (hZ : Zf.IsCommutatorFriendly)
    (x : P.Apartment) (r : NNReal) (hr : 0 < r)
    (nu : cocharacterLattice P.S) (hnu : IsGenericCocharacter P.i nu)
    (J : Set (characterLattice P.S)) {zeta : cocharacterLattice P.S}
    (hzeta : IsStandardCocharacter P.i nu J zeta) :
    Function.Surjective (moyPrasadRadicalDepthProduct P Zf x nu J r) :=
  moyPrasadRadicalDepthProduct_surjective_of_ordered_cover P Zf x nu J r hzeta
    (fun _ _ aneg apos _ hrneg _ hrpos =>
      Zf.range_orderedMoyPrasadProduct_eq hP hZ x r hr nu hnu aneg apos hrneg hrpos)

end Covering

section Chamber

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {S A : CommGroupScheme (Spec (CommRingCat.of F))}

/-- A restricted character of normalized norm at most one has nonnegative order on the
image point. -/
theorem localFieldOrder_nonneg_of_characterNorm_le_one
    (q : A.toGrp ⟶ S.toGrp) (α : characterLattice S) (a : rationalPoints A.toGrp)
    (h : CocharacterUniformizer.characterNorm F A (componentCharacterRestriction q α) a ≤ 1) :
    0 ≤ localFieldOrder F
      (rationalCharacterEval ((rationalCharacters.equivCharacterLattice S).symm α)
        (rationalPoints.map q a)) := by
  have heq : CocharacterUniformizer.characterNorm F A (componentCharacterRestriction q α) a =
      ((Plancherel.fieldNormUnits F
        (rationalCharacterEval ((rationalCharacters.equivCharacterLattice S).symm α)
          (rationalPoints.map q a)) : NNReal) : ℝ) := by
    simp [CocharacterUniformizer.characterNorm, componentCharacterRestriction,
      Plancherel.rationalNormCharacters_apply, rationalCharacterEval_characterRestrict]
  rw [heq, Plancherel.fieldNormUnits_zpow] at h
  have hq : (1 : ℝ) < (LocalField.residueCardinality F : ℝ) := by
    exact_mod_cast LocalField.residueCardinality_gt_one F
  have h' := (zpow_le_one_iff_right₀ hq).mp h
  unfold localFieldOrder
  exact_mod_cast (by omega)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Negation of a closure of a set lands in the closure of the negated set. -/
theorem neg_mem_closure_neg_image {J : Set (characterLattice S)} {y : characterLattice S}
    (hy : y ∈ AddSubmonoid.closure J) : -y ∈ AddSubmonoid.closure (Neg.neg '' J) := by
  induction hy using AddSubmonoid.closure_induction with
  | mem y hy => exact AddSubmonoid.subset_closure ⟨y, hy, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => simpa using add_mem hz hy

variable {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G)

/-- Literal intersections equal to the generated radical depth groups are preserved by
conjugation by the nonnegative part of every split component (KP Definition 13.2.4(2)). -/
theorem weakChamberContraction_nonnegativePart
    (x : B.Apartment) (nu : cocharacterLattice B.S) (J : Set (characterLattice B.S))
    {A : CommGroupScheme (Spec (CommRingCat.of F))} (q : A.toGrp ⟶ B.S.toGrp)
    (K : Subgroup (rationalPoints G)) (r : ℝ)
    (hpos : K ⊓ standardUnipotentPoints B.i nu J = standardRadicalDepth B x nu J r)
    (hneg : K ⊓ standardOppositeUnipotentPoints B.i nu J =
      standardRadicalDepth B x (-nu) (Neg.neg '' J) r) :
    WeakChamberContraction K (standardUnipotentPoints B.i nu J)
      (standardOppositeUnipotentPoints B.i nu J)
      (standardComponentNonnegativePart B.i nu J q) := by
  rintro _ ⟨a, ha, rfl⟩
  have hroots := relativeRootNegation F G B.isConnectedReductive B.S B.i
    B.isMaximalSplitTorus
  constructor
  · rintro _ ⟨g, hg, rfl⟩
    rw [hpos] at hg ⊢
    apply map_rootDepthGeneratedSubgroup_conj_le B.apartment x _ _ (fun _ hb => hb.1.1)
      (rationalPoints.map q a) _ (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩)
    intro α hα
    exact localFieldOrder_nonneg_of_characterNorm_le_one q α a (ha α hα)
  · rintro _ ⟨g, hg, rfl⟩
    rw [hneg] at hg ⊢
    have hinv : (rationalPoints.map (q ≫ B.i) a)⁻¹ =
        rationalPoints.map B.i (rationalPoints.map q a⁻¹) := by
      rw [map_inv, map_inv]
      rfl
    rw [hinv]
    apply map_rootDepthGeneratedSubgroup_conj_le B.apartment x _ _ (fun _ hb => hb.1.1)
      (rationalPoints.map q a⁻¹) _ (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩)
    intro β hβ
    apply localFieldOrder_nonneg_of_characterNorm_le_one q β a⁻¹
    have hmem : -β ∈ positiveRelativeRoots B.i nu \
        (AddSubmonoid.closure J : Set (characterLattice B.S)) := by
      refine ⟨⟨hroots β hβ.1.1, ?_⟩, ?_⟩
      · have := hβ.1.2
        simpa using this
      · intro hc
        apply hβ.2
        simpa using neg_mem_closure_neg_image hc
    have h1 := ha (-β) hmem
    rw [← componentCharacterNorm_neg_inv] at h1
    simpa [map_neg] using h1

end Chamber

section Topology

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- An open-cell embedding `Q × Nbar → H`, `(p, v) ↦ p v⁻¹`, and a Levi decomposition
homeomorphism `M × N → Q` make the ordered multiplication `Nbar × M × N → H` an embedding;
a bijective ordered intersection product into `K` is then a homeomorphism. -/
theorem isHomeomorph_orderedIntersectionProduct_of_openCell
    (K M N Nbar Q : Subgroup H) (hMN : ∀ x : M × N, (x.1 : H) * x.2 ∈ Q)
    (hcell : IsEmbedding (HarishChandraSchwartz.openCellMap (P := Q) (V := Nbar)))
    (hlevi : IsHomeomorph (fun x : M × N => (⟨(x.1 : H) * x.2, hMN x⟩ : Q)))
    (hbij : HasIwahoriIntersectionDecomposition K M N Nbar) :
    IsHomeomorph (orderedIntersectionProduct K M N Nbar) := by
  let ψ := hlevi.homeomorph _
  have hΦ : IsEmbedding (fun t : Nbar × M × N => (t.1 : H) * t.2.1 * t.2.2) := by
    let e : Nbar × M × N ≃ₜ Q × Nbar :=
      (Homeomorph.prodComm Nbar (M × N)).trans
        ((ψ.trans (Homeomorph.inv Q)).prodCongr (Homeomorph.refl Nbar))
    have key : (fun t : Nbar × M × N => (t.1 : H) * t.2.1 * t.2.2) =
        (Homeomorph.inv H) ∘ HarishChandraSchwartz.openCellMap ∘ e := by
      funext t
      change (t.1 : H) * t.2.1 * t.2.2 =
        (((ψ t.2)⁻¹ : Q) * (t.1 : H)⁻¹)⁻¹
      change (t.1 : H) * t.2.1 * t.2.2 =
        ((((t.2.1 : H) * t.2.2)⁻¹) * (t.1 : H)⁻¹)⁻¹
      simp [mul_assoc]
    rw [key]
    exact (Homeomorph.inv H).isEmbedding.comp (hcell.comp e.isEmbedding)
  have hsub : ∀ {A B : Subgroup H} (h : A ≤ B), IsEmbedding (fun a : A => (⟨a, h a.2⟩ : B)) :=
    fun _ => (IsEmbedding.subtypeVal.of_comp_iff).mp IsEmbedding.subtypeVal
  have hincl := (hsub (inf_le_right : K ⊓ Nbar ≤ Nbar)).prodMap
    ((hsub (inf_le_right : K ⊓ M ≤ M)).prodMap (hsub (inf_le_right : K ⊓ N ≤ N)))
  have hcomp : IsEmbedding (Subtype.val ∘ orderedIntersectionProduct K M N Nbar) :=
    hΦ.comp hincl
  exact isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨(IsEmbedding.subtypeVal.of_comp_iff).mp hcomp, hbij.2⟩

end Topology

section TopologicalIwahori

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

/-- For a connected reductive `G`, the ordered intersection bijection of any subgroup `K`
with respect to a standard parabolic is a homeomorphism: the open cell and the Levi
decomposition of the dynamic parabolic of a standard cocharacter. -/
theorem isTopologicalIwahoriDecomposition_of_bijective
    (hG : IsConnectedReductive G) (i : S.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (nu : cocharacterLattice S) (hnu : IsGenericCocharacter i nu)
    (J : Set (characterLattice S)) (hJ : J ⊆ simpleRelativeRoots i nu)
    (K : Subgroup (rationalPoints G))
    (hbij : HasIwahoriIntersectionDecomposition K (standardLeviPoints i nu J)
      (standardUnipotentPoints i nu J) (standardOppositeUnipotentPoints i nu J)) :
    IsTopologicalIwahoriDecomposition K (standardLeviPoints i nu J)
      (standardUnipotentPoints i nu J) (standardOppositeUnipotentPoints i nu J) := by
  obtain ⟨⟨zeta, hzeta⟩, hcompare⟩ := standardCocharacter F G hG S i hi nu hnu J hJ
  obtain ⟨-, hLevi, hUni⟩ := hcompare zeta hzeta
  have hneg := relativeRootNegation F G hG S i hi
  obtain ⟨-, -, hUniNeg⟩ := standard_eq_dynamic_of_relativeRootNegation relativeRootNegation
    F G hG S i hi (-nu) (hnu.neg i nu) (Neg.neg '' J) (-zeta) (hzeta.neg i nu hneg)
  rw [groupHom_neg_comp_eq_oppositeCocharacter] at hUniNeg
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  have : Smooth G.X.hom := hG.smooth
  have : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  have : T2Space F := Langlands.BruhatTits.localField_t2Space F
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  have : IsOpenUnits F := inferInstance
  have eM : standardLeviPoints i nu J =
      (Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)).carrier (Over.mk (𝟙 _)) :=
    congrArg (fun H => SubgroupFunctor.carrier H (Over.mk (𝟙 _))) hLevi
  have eN : standardUnipotentPoints i nu J =
      (Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i)).carrier (Over.mk (𝟙 _)) :=
    congrArg (fun H => SubgroupFunctor.carrier H (Over.mk (𝟙 _))) hUni
  have eNbar : standardOppositeUnipotentPoints i nu J =
      (Dynamic.unipotent (Dynamic.oppositeCocharacter
        (CommGroupScheme.groupHom zeta ≫ i))).carrier (Over.mk (𝟙 _)) :=
    congrArg (fun H => SubgroupFunctor.carrier H (Over.mk (𝟙 _))) hUniNeg
  show IsHomeomorph (orderedIntersectionProduct K (standardLeviPoints i nu J)
      (standardUnipotentPoints i nu J) (standardOppositeUnipotentPoints i nu J))
  rw [eM, eN, eNbar] at hbij ⊢
  exact isHomeomorph_orderedIntersectionProduct_of_openCell K _ _ _ _ _
    (HarishChandraSchwartz.isOpenEmbedding_openCellMap_rationalPoint F G
      (CommGroupScheme.groupHom zeta ≫ i)).isEmbedding
    (HarishChandraSchwartz.isHomeomorph_leviUnipotentMul_rationalPoint F G
      (CommGroupScheme.groupHom zeta ≫ i)) hbij

end TopologicalIwahori

section LeviFiltration

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G M : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    [IsAffineHom M.X.hom] [LocallyOfFiniteType M.X.hom]
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G) [Mono i.hom.hom.left]
    (iM : S.toGrp ⟶ M) [Mono iM.hom.hom.left] (j : M ⟶ G) (hcomp : iM ≫ j = i)
    (ζ : cocharacterLattice S)
    (hj : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy j)
    (hjc : IsClosedSubgroup j)
    {D : KPApartmentData i (localFieldOrder F)} {DM : KPApartmentData iM (localFieldOrder F)}
    {x : D.Apartment} {xM : DM.Apartment}

include hS hcomp hj hjc in
/-- For a root `a` of the Levi `M` and a point `xM` restricting `x`, the inclusion `j` maps
the Levi filtration group `U^M_{a,xM,s}` onto the ambient `U_{a,x,s}`. -/
theorem map_leviFiltration_eq (hx : IsLeviRestriction j x xM)
    {a : characterLattice S} (ha : a ∈ relativeRoots iM) (s : ℝ) :
    (DM.filtration xM a s).map (rationalPoints.map j) = D.filtration x a s := by
  have hU := map_leviRootGroupPoints hS i iM j hcomp ζ hj hjc a ha
  ext g
  constructor
  · rintro ⟨m, ⟨hm, hval⟩, rfl⟩
    refine ⟨hU ▸ ⟨m, hm, rfl⟩, ?_⟩
    change (s : WithTop ℝ) ≤ x.val a (rationalPoints.map j m)
    rw [← hx a ha m]
    exact hval
  · rintro ⟨hg, hval⟩
    rw [← hU] at hg
    obtain ⟨m, hm, rfl⟩ := hg
    refine ⟨m, ⟨hm, ?_⟩, rfl⟩
    rw [hx a ha m]
    exact hval

end LeviFiltration

end Langlands.Geometry.Building.MoyPrasadLeviProof

namespace Langlands.Geometry.Building

open MoyPrasadLeviProof

section Assembly

/-- **KP Proposition 13.2.5(5)** at positive depth. -/
theorem moyPrasadIwahoriDecomposition : MoyPrasadIwahoriDecompositionStatement.{u} := by
  intro F _ _ _ _ G _ P Zf hP hZf x r hr nu hnu J hJ
  obtain ⟨zeta, hzeta⟩ := (standardCocharacter F G P.isConnectedReductive P.S P.i
    P.isMaximalSplitTorus nu hnu J hJ).1
  have hsurj := moyPrasadRadicalDepthProduct_surjective P Zf hP hZf.1 x r hr nu hnu J hzeta
  obtain ⟨hpos, hneg, hbij⟩ :=
    moyPrasad_intersections_and_iwahori_of_surjective P Zf x nu J r hzeta hsurj
  refine ⟨isTopologicalIwahoriDecomposition_of_bijective P.isConnectedReductive P.i
    P.isMaximalSplitTorus nu hnu J hJ _ hbij, ?_⟩
  intro A q _
  exact weakChamberContraction_nonnegativePart P.toValuationBuildingData x nu J q _ r
    hpos hneg

/-- **KP Proposition 13.2.5(6)** at positive depth. -/
theorem moyPrasadLeviIntersection : MoyPrasadLeviIntersectionStatement.{u} := by
  intro F _ _ _ _ G _ P Zf hP hZf x r hr nu hnu J hJ
  let : IsAffineHom (Standard.leviScheme P.i nu J).X.hom :=
    (Standard.isClosedSubgroup_leviHom P.i nu J).isAffineHom
  let : Mono (Standard.leviTorusHom P.i nu J).hom.hom.left :=
    (Standard.isMaximalSplitTorus_leviTorusHom P.i nu J
      P.isMaximalSplitTorus).isSplitSubtorus.mono
  intro DM xM hx
  classical
  have hG := P.isConnectedReductive
  have hi := P.isMaximalSplitTorus
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  have hM := standardLevi_isConnectedReductive hG P.i hi nu hnu J hJ
  let : Smooth (Standard.leviScheme P.i nu J).X.hom := hM.smooth
  obtain ⟨⟨ζ, hζ⟩, hcompare⟩ := standardCocharacter F G hG P.S P.i hi nu hnu J hJ
  have hj := Standard.isRepresentedBy_leviHom P.i nu J
  rw [(hcompare ζ hζ).2.1] at hj
  have hcomp := Standard.leviTorusHom_comp P.i nu J
  have hjc := Standard.isClosedSubgroup_leviHom P.i nu J
  have hS : IsSplitTorus P.S.toGrp := hi.isSplitSubtorus.1
  have hneg := relativeRootNegation F G hG P.S P.i hi
  have hroots := relativeRoots_centralizer_factor dynamicLie P.i
    (Standard.leviTorusHom P.i nu J) (Standard.leviHom P.i nu J) hcomp ζ hj
  have hfilt : ∀ a ∈ relativeRoots (Standard.leviTorusHom P.i nu J), ∀ s : ℝ,
      (DM.filtration xM a s).map (rationalPoints.map (Standard.leviHom P.i nu J)) =
        P.apartment.filtration x a s := fun a ha s =>
    map_leviFiltration_eq hS P.i _ _ hcomp ζ hj hjc hx ha s
  set j := Standard.leviHom P.i nu J with hjdef
  set L := (Zf.leviMoyPrasad j xM r).map (rationalPoints.map j) with hL
  have hmemL : ∀ m, m ∈ Zf.leviMoyPrasad j xM r → rationalPoints.map j m ∈ L :=
    fun m hm => ⟨m, hm, rfl⟩
  -- Ambient root filtration groups of the Levi roots lie in `L`.
  have hfiltL : ∀ a ∈ relativeRoots P.i, latticePairing P.S a ζ = 0 →
      P.apartment.filtration x a r ≤ L := by
    intro a ha haz
    have haM : a ∈ relativeRoots (Standard.leviTorusHom P.i nu J) := by
      rw [hroots]
      exact ⟨ha, haz⟩
    rw [← hfilt a haM]
    apply Subgroup.map_mono
    intro m hm
    show m ∈ (Zf.image r).comap (rationalPoints.map j) ⊔
      DM.sharpFiltration xM (fun _ => (r : ℝ))
    apply Subgroup.mem_sup_right
    rw [DM.sharpFiltration_eq_iSup]
    exact le_iSup (fun b : relativeRoots (Standard.leviTorusHom P.i nu J) =>
      DM.filtration xM b r) ⟨a, haM⟩ hm
  have hblockL : ∀ a ∈ relativeRoots P.i, latticePairing P.S a ζ = 0 →
      P.apartment.filtrationBlock x (fun _ => (r : ℝ)) a ⊆ L := by
    intro a ha haz g hg
    obtain ⟨v, hv, w, hw, rfl⟩ := P.apartment.mem_filtrationBlock.mp hg
    apply L.mul_mem (hfiltL a ha haz hv)
    by_cases h2a : 2 • a ∈ relativeRoots P.i
    · rw [P.apartment.doubleFiltration_of_mem x a r h2a] at hw
      apply hfiltL (2 • a) h2a _ hw
      simp [haz]
    · rw [P.apartment.doubleFiltration_of_not_mem x a r h2a] at hw
      rw [Subgroup.mem_bot.mp hw]
      exact L.one_mem
  have hZL : ∀ z : Zf.filtration r,
      rationalPoints.map P.centralizer.j (z : rationalPoints P.centralizer.Z) ∈ L := by
    intro z
    have hlev := (centralizerFiltration_map_mem_moyPrasad_inf_standardLevi P Zf x nu J r z).2
    obtain ⟨m, hm⟩ := (Standard.leviPointsEquiv P.i nu J).surjective ⟨_, hlev⟩
    have hm' : rationalPoints.map j m =
        rationalPoints.map P.centralizer.j (z : rationalPoints P.centralizer.Z) :=
      congrArg Subtype.val hm
    rw [← hm']
    apply hmemL
    show m ∈ (Zf.image r).comap (rationalPoints.map j) ⊔
      DM.sharpFiltration xM (fun _ => (r : ℝ))
    apply Subgroup.mem_sup_left
    change rationalPoints.map j m ∈ Zf.image r
    rw [hm']
    exact ⟨z, z.property, rfl⟩
  apply le_antisymm
  · rw [hL, Subgroup.map_le_iff_le_comap]
    show (Zf.image r).comap (rationalPoints.map j) ⊔
      DM.sharpFiltration xM (fun _ => (r : ℝ)) ≤ _
    refine sup_le ?_ ?_
    · intro m hm
      exact ⟨(le_sup_left : Zf.image r ≤ Zf.moyPrasad x r) hm,
        (Standard.leviPointsEquiv P.i nu J m).property⟩
    · rw [DM.sharpFiltration_eq_iSup]
      refine iSup_le fun a => ?_
      intro m hm
      have hjm : rationalPoints.map j m ∈ P.apartment.filtration x a r := by
        rw [← hfilt a a.2 r]
        exact ⟨m, hm, rfl⟩
      refine ⟨?_, (Standard.leviPointsEquiv P.i nu J m).property⟩
      apply (le_sup_right : P.apartment.sharpFiltration x (fun _ => (r : ℝ)) ≤
        Zf.moyPrasad x r)
      rw [P.apartment.sharpFiltration_eq_iSup]
      have haG : (a : characterLattice P.S) ∈ relativeRoots P.i :=
        ((Set.ext_iff.mp hroots _).mp a.2).1
      exact le_iSup (fun b : relativeRoots P.i => P.apartment.filtration x b r) ⟨a, haG⟩ hjm
  · rintro g ⟨hgK, hgM⟩
    have hfin (v : cocharacterLattice P.S) :
        (RelativeRoot.indivisiblePositiveRoots P.i v).Finite :=
      (P.isMaximalSplitTorus.1.1.finite_relativeRoots P.i).subset (fun _ ha => ha.1.1)
    obtain ⟨nb, nmneg, abar, amneg, hbmi, hbmr, hb, hmn⟩ :=
      exists_fin_enumeration_partition (RelativeRoot.indivisiblePositiveRoots P.i (-nu))
        (AddSubmonoid.closure (Neg.neg '' J) : Set (characterLattice P.S))ᶜ (hfin (-nu))
    obtain ⟨nmpos, np, ampos, apos, hmpi, hmpr, hmp, hp⟩ :=
      exists_fin_enumeration_partition (RelativeRoot.indivisiblePositiveRoots P.i nu)
        (AddSubmonoid.closure J : Set (characterLattice P.S)) (hfin nu)
    have hbar k : abar k ∈ positiveRelativeRoots P.i (-nu) \
        AddSubmonoid.closure (Neg.neg '' J) :=
      ⟨⟨(hb k).1.1.1, (hb k).1.2⟩, (hb k).2⟩
    have hmneg k : amneg k ∈ positiveRelativeRoots P.i (-nu) ∩
        (AddSubmonoid.closure (Neg.neg '' J) : Set (characterLattice P.S)) := by
      refine ⟨⟨(hmn k).1.1.1, (hmn k).1.2⟩, ?_⟩
      simpa only [Set.mem_compl_iff, not_not] using (hmn k).2
    have hmpos k : ampos k ∈ positiveRelativeRoots P.i nu ∩
        (AddSubmonoid.closure J : Set (characterLattice P.S)) :=
      ⟨⟨(hmp k).1.1.1, (hmp k).1.2⟩, (hmp k).2⟩
    have hpos k : apos k ∈ positiveRelativeRoots P.i nu \ AddSubmonoid.closure J :=
      ⟨⟨(hp k).1.1.1, (hp k).1.2⟩, (hp k).2⟩
    have hprod := Zf.range_orderedMoyPrasadProduct_eq hP hZf.1 x r hr nu hnu
      (Fin.append abar amneg) (Fin.append ampos apos) hbmr hmpr
    have hg : g ∈ (Zf.moyPrasad x r : Set (rationalPoints G)) := hgK
    rw [← hprod] at hg
    obtain ⟨p, hpg⟩ := hg
    let c := parabolicMoyPrasadCoordinates P Zf x nu J r hζ
      abar amneg ampos apos hbar hmneg hmpos hpos p
    have hc : (moyPrasadRadicalDepthProduct P Zf x nu J r c : rationalPoints G) = g :=
      (parabolicMoyPrasadCoordinates_product P Zf x nu J r hζ
        abar amneg ampos apos hbar hmneg hmpos hpos p).trans hpg
    have hmid : ((c.2.1 : ↥(Zf.moyPrasad x r ⊓ standardLeviPoints P.i nu J)) :
        rationalPoints G) =
        (List.ofFn fun k => (p.1 (Fin.natAdd nb k) : rationalPoints G)).prod *
          rationalPoints.map P.centralizer.j (p.2.1 : rationalPoints P.centralizer.Z) *
          (List.ofFn fun k => (p.2.2 (Fin.castAdd np k) : rationalPoints G)).prod :=
      rfl
    have hmidL : ((c.2.1 : ↥(Zf.moyPrasad x r ⊓ standardLeviPoints P.i nu J)) :
        rationalPoints G) ∈ L := by
      rw [hmid]
      refine L.mul_mem (L.mul_mem ?_ (hZL p.2.1)) ?_
      · apply ofFn_prod_mem_subgroup
        intro k
        have hk : (p.1 (Fin.natAdd nb k) : rationalPoints G) ∈
            P.apartment.filtrationBlock x (fun _ => (r : ℝ)) (amneg k) := by
          simpa only [Fin.append_right] using (p.1 (Fin.natAdd nb k)).property
        apply hblockL _ (hmneg k).1.1 _ hk
        have h0 := (hζ.neg P.i nu hneg).pairing_eq_zero_of_mem_closure P.i (-nu)
          (hmneg k).2
        simpa using h0
      · apply ofFn_prod_mem_subgroup
        intro k
        have hk : (p.2.2 (Fin.castAdd np k) : rationalPoints G) ∈
            P.apartment.filtrationBlock x (fun _ => (r : ℝ)) (ampos k) := by
          simpa only [Fin.append_left] using (p.2.2 (Fin.castAdd np k)).property
        exact hblockL _ (hmpos k).1.1 (hζ.pairing_eq_zero_of_mem_closure P.i nu (hmpos k).2) hk
    have hVN := standardRadicalDepth_le_standardUnipotentPoints
      P.toValuationBuildingData x nu J r
    have hVbarNbar := standardRadicalDepth_le_standardUnipotentPoints
      P.toValuationBuildingData x (-nu) (Neg.neg '' J) r
    have heq := standardTripleProduct_injective P.i nu hneg hζ
      (a₁ := (⟨c.1, hVbarNbar c.1.2⟩, ⟨c.2.1, c.2.1.2.2⟩, ⟨c.2.2, hVN c.2.2.2⟩))
      (a₂ := (1, ⟨g, hgM⟩, 1)) (by
        show (c.1 : rationalPoints G) * (c.2.1 : rationalPoints G) * (c.2.2 : rationalPoints G) =
          1 * g * 1
        rw [one_mul, mul_one]
        exact hc)
    have hcg : ((c.2.1 : ↥(Zf.moyPrasad x r ⊓ standardLeviPoints P.i nu J)) :
        rationalPoints G) = g :=
      congrArg (fun t : standardOppositeUnipotentPoints P.i nu J ×
        standardLeviPoints P.i nu J × standardUnipotentPoints P.i nu J =>
          ((t.2.1 : standardLeviPoints P.i nu J) : rationalPoints G)) heq
    rw [← hcg]
    exact hmidL

/-- **KP Proposition 13.2.5(5),(6)** at positive depth. -/
theorem moyPrasadLevi : MoyPrasadLeviStatement.{u} :=
  ⟨moyPrasadIwahoriDecomposition, moyPrasadLeviIntersection⟩

end Assembly

end Langlands.Geometry.Building
