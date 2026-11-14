import Langlands.GroupScheme.Torus.FibrewiseMaximalTransport
import Langlands.GroupScheme.Torus.EtaleLocalMaximalConjugacyStatement
import Langlands.GroupScheme.Torus.ExponentHomomorphisms
import Langlands.GroupScheme.Torus.IdentityTransporterEtaleLift
import Langlands.GroupScheme.Absolute.KernelMaximalTorusIdentityComponent
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof
import Langlands.GroupScheme.Rational.SubgroupConjugacy
import Langlands.GroupScheme.Torus.Locality

/-! # Etale-local conjugacy of maximal tori in smooth affine group schemes -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme
namespace splitTorus
variable (k : Type u) [Field k] (I J : Type u)
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- Extend the integral coordinates of a field isomorphism over any base. -/
def fieldIsoExtension (S : Scheme.{u})
    (c : splitTorus (Spec (CommRingCat.of k)) I ≅
      splitTorus (Spec (CommRingCat.of k)) J) :
    splitTorus S I ≅ splitTorus S J where
  hom := CommGroupScheme.groupHom (exponentHom S I J (characterMap I J c.hom))
  inv := CommGroupScheme.groupHom (exponentHom S J I (characterMap J I c.inv))
  hom_inv_id := by
    change CommGroupScheme.groupHom (_ ≫ _) = _
    rw [exponentHom_comp, ← characterMap_comp, c.hom_inv_id, characterMap_id,
      exponentHom_id]
    rfl
  inv_hom_id := by
    change CommGroupScheme.groupHom (_ ≫ _) = _
    rw [exponentHom_comp, ← characterMap_comp, c.inv_hom_id, characterMap_id,
      exponentHom_id]
    rfl

theorem fieldIsoExtension_hom
    (c : splitTorus (Spec (CommRingCat.of k)) I ≅
      splitTorus (Spec (CommRingCat.of k)) J) :
    (fieldIsoExtension k I J (Spec (CommRingCat.of k)) c).hom = c.hom :=
  congrArg CommGroupScheme.groupHom (exponentHom_characterMap k I J c.hom)

theorem fieldIsoExtension_baseChange (S : Scheme.{u})
    (c : splitTorus (Spec (CommRingCat.of k)) I ≅
      splitTorus (Spec (CommRingCat.of k)) J)
    (b : Spec (CommRingCat.of k) ⟶ S) :
    (baseChangeIso b I).inv ≫ (GroupScheme.baseChange b).map (fieldIsoExtension k I J S c).hom ≫
      (baseChangeIso b J).hom = c.hom := by
  have h := congrArg CommGroupScheme.groupHom
    (exponentHom_baseChange S I J b (characterMap I J c.hom))
  change (baseChangeIso b I).hom ≫
    (fieldIsoExtension k I J (Spec (CommRingCat.of k)) c).hom =
    (GroupScheme.baseChange b).map (fieldIsoExtension k I J S c).hom ≫
      (baseChangeIso b J).hom at h
  rw [← h, Iso.inv_hom_id_assoc, fieldIsoExtension_hom]

end splitTorus

namespace PointwiseSchemeAction
variable {S : Scheme.{u}} {H G : GroupScheme S} (i₁ i₂ : H ⟶ G)
  (g : Over.mk (𝟙 S) ⟶ G.X)

/-- Relate the all-test transporter convention to inner conjugation. -/
theorem isTransporter_iff_innerIso :
    IsTransporter i₁ i₂ g ↔ i₂ ≫ (G.innerIso g).hom = i₁ := by
  constructor
  · intro hg
    apply hom_ext_points
    intro V x
    rw [Grp.comp_hom_hom, ← Category.assoc, G.comp_innerIso_hom]
    exact (mul_inv_eq_iff_eq_mul.mpr
      (hg V (Over.homMk V.hom (by simp)) x).symm)
  · intro hg V a x
    have he := congrArg (fun f : H ⟶ G => x ≫ f.hom.hom) hg
    rw [Grp.comp_hom_hom, ← Category.assoc, G.comp_innerIso_hom] at he
    have hc : G.constantPoint g V = a ≫ g := by
      unfold GroupScheme.constantPoint
      congr 1
      apply Over.OverMorphism.ext
      change V.hom = a.left
      have ha := Over.w a
      change a.left ≫ 𝟙 S = V.hom at ha
      exact ha.symm.trans (Category.comp_id a.left)
    rw [hc] at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm

end PointwiseSchemeAction

/-- Geometric conjugacy may be realized inside the actual identity component,
without connectedness of the ambient group. -/
theorem maximalTorusConjugacy_in_identity {k : Type u} [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i') :
    ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (e : T.toGrp ≅ T'.toGrp),
      i ≫ (G.innerIso g).hom = e.hom ≫ i' ∧
      Set.range g.left ⊆ IdentityComponent.identitySet G := by
  obtain ⟨i₀, h₀, hi₀⟩ := exists_isMaximalTorus_identityComponent hi
  obtain ⟨i₀', h₀', hi₀'⟩ := exists_isMaximalTorus_identityComponent hi'
  obtain ⟨g, e, he⟩ := maximalTorusConjugacy k (identityComponent G) T T' i₀ i₀' hi₀ hi₀'
  let E : T.toGrp ≅ T'.toGrp :=
    { hom := CommGroupScheme.groupHom e.hom
      inv := CommGroupScheme.groupHom e.inv
      hom_inv_id := congrArg CommGroupScheme.groupHom e.hom_inv_id
      inv_hom_id := congrArg CommGroupScheme.groupHom e.inv_hom_id }
  refine ⟨g ≫ (identityComponentι G).hom.hom, E, ?_, ?_⟩
  · rw [← h₀, Category.assoc, ← innerIso_hom_comp, ← Category.assoc, he,
      Category.assoc, h₀']
  · rintro _ ⟨x, rfl⟩
    change (identityComponentι G).hom.hom.left (g.left x) ∈
      connectedComponent (IdentityComponent.identityPoint G)
    rw [← IdentityComponent.range_identityComponentι]
    exact ⟨g.left x, rfl⟩

namespace SubgroupConjugate
variable {S S' : Scheme.{u}} {G H H' K K' : GroupScheme S}
  {i : H ⟶ G} {i' : H' ⟶ G}

/-- Arbitrary base change preserves conjugacy with source isomorphisms. -/
theorem baseChange (h : SubgroupConjugate i i') (b : S' ⟶ S) :
    SubgroupConjugate ((GroupScheme.baseChange b).map i)
      ((GroupScheme.baseChange b).map i') := by
  obtain ⟨e, he⟩ := (subgroupConjugate_iff_exists_iso i i').mp h
  apply (subgroupConjugate_iff_exists_iso _ _).mpr
  refine ⟨(GroupScheme.baseChange b).mapIso e, ?_⟩
  change HomConjugate ((GroupScheme.baseChange b).map i)
    ((GroupScheme.baseChange b).map e.hom ≫ (GroupScheme.baseChange b).map i')
  rw [← Functor.map_comp]
  exact he.baseChange b

/-- Independent source coordinates can be removed from a conjugacy. -/
theorem of_precomp_isos (e : K ≅ H) (e' : K' ≅ H')
    (h : SubgroupConjugate (e.hom ≫ i) (e'.hom ≫ i')) :
    SubgroupConjugate i i' :=
  (SubgroupConjugate.iso_source e i).symm.trans
    (h.trans (SubgroupConjugate.iso_source e' i'))

end SubgroupConjugate

namespace splitTorus

/-- Standard split maximal tori are conjugate on an affine etale
neighbourhood through any prescribed base point. -/
theorem exists_etale_subgroupConjugate {R : CommRingCat.{u}}
    (I J : Type u) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (G : GroupScheme (Spec R)) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : splitTorus (Spec R) I ⟶ G) (i' : splitTorus (Spec R) J ⟶ G)
    (hi : IsFibrewiseMaximalTorus (T := commGroupScheme _ I) i)
    (hi' : IsFibrewiseMaximalTorus (T := commGroupScheme _ J) i') (s : Spec R) :
    ∃ (R' : CommRingCat.{u}) (b : Spec R' ⟶ Spec R),
      Etale b ∧ s ∈ Set.range b ∧
      SubgroupConjugate ((GroupScheme.baseChange b).map i) ((GroupScheme.baseChange b).map i') := by
  let k : Type u := AlgebraicClosure ((Spec R).residueField s)
  let b : Spec (CommRingCat.of k) ⟶ Spec R := geometricPoint (Spec R) s
  let Gk : GroupScheme (Spec (CommRingCat.of k)) := (GroupScheme.baseChange b).obj G
  let : Smooth Gk.X.hom := inferInstanceAs (Smooth (pullback.snd G.X.hom b))
  let : IsAffineHom Gk.X.hom := inferInstanceAs (IsAffineHom (pullback.snd G.X.hom b))
  let j : splitTorus (Spec (CommRingCat.of k)) I ⟶ Gk :=
    (baseChangeIso b I).inv ≫ (GroupScheme.baseChange b).map i
  let j' : splitTorus (Spec (CommRingCat.of k)) J ⟶ Gk :=
    (baseChangeIso b J).inv ≫ (GroupScheme.baseChange b).map i'
  have hj : IsMaximalTorus (T := commGroupScheme _ I) j :=
    IsMaximalTorus.iso_comp
      (T := (CommGroupScheme.baseChange b).obj (commGroupScheme _ I))
      (T' := commGroupScheme _ I) (baseChangeIso b I).symm (hi.fieldPoint b)
  have hj' : IsMaximalTorus (T := commGroupScheme _ J) j' :=
    IsMaximalTorus.iso_comp
      (T := (CommGroupScheme.baseChange b).obj (commGroupScheme _ J))
      (T' := commGroupScheme _ J) (baseChangeIso b J).symm (hi'.fieldPoint b)
  obtain ⟨g, c, hc, hg⟩ := maximalTorusConjugacy_in_identity Gk
    (T := commGroupScheme _ I) (T' := commGroupScheme _ J) j j' hj hj'
  let e : splitTorus (Spec R) I ≅ splitTorus (Spec R) J :=
    fieldIsoExtension k I J (Spec R) c
  have he : (baseChangeIso b I).inv ≫ (GroupScheme.baseChange b).map e.hom ≫
      (baseChangeIso b J).hom = c.hom :=
    fieldIsoExtension_baseChange k I J (Spec R) c b
  have ht : PointwiseSchemeAction.IsTransporter
      ((GroupScheme.baseChange b).map (e.hom ≫ i')) ((GroupScheme.baseChange b).map i) g := by
    apply (PointwiseSchemeAction.isTransporter_iff_innerIso _ _ g).mpr
    rw [Functor.map_comp]
    apply (cancel_epi (baseChangeIso b I).inv).mp
    calc
      _ = c.hom ≫ ((baseChangeIso b J).inv ≫ (GroupScheme.baseChange b).map i') := by
        simpa only [j, j', Category.assoc] using hc
      _ = _ := by rw [← he]; simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have hb : b default = s := by
    simpa only [Subsingleton.elim (default : Spec (CommRingCat.of k))
      (IsLocalRing.closedPoint k)] using geometricPoint_closedPoint s
  let d := PointwiseSchemeAction.etaleIdentityTransporterOfSplitTorus
    (e.hom ≫ i') i inferInstance s b hb g ht hg
  refine ⟨d.neighbourhoodRing, d.projection, d.etale, d.mem_range,
    d.baseChangedSection, (GroupScheme.baseChange d.projection).mapIso e, ?_⟩
  have hd := (PointwiseSchemeAction.isTransporter_iff_innerIso _ _
    d.baseChangedSection).mp d.baseChangedSection_isTransporter
  change (GroupScheme.baseChange d.projection).map i ≫
    (((GroupScheme.baseChange d.projection).obj G).innerIso d.baseChangedSection).hom =
      (GroupScheme.baseChange d.projection).map e.hom ≫ (GroupScheme.baseChange d.projection).map i'
  rw [← Functor.map_comp]
  exact hd

end splitTorus

/-- Fibrewise maximality is preserved under arbitrary change of the base. -/
theorem IsFibrewiseMaximalTorus.baseChange_forConjugacy {S S' : Scheme.{u}}
    {T : CommGroupScheme S} {G : GroupScheme S}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] {i : T.toGrp ⟶ G}
    (hi : IsFibrewiseMaximalTorus i) (b : S' ⟶ S) :
    IsFibrewiseMaximalTorus (T := (CommGroupScheme.baseChange b).obj T)
      ((GroupScheme.baseChange b).map i) := by
  intro s
  exact isMaximalTorus_baseChange_comp b (S'.fromSpecResidueField s) T i
    (hi.fieldPoint (S'.fromSpecResidueField s ≫ b))

namespace SubgroupConjugate
variable {S S' S'' : Scheme.{u}} {H H' G : GroupScheme S}
  {i : H ⟶ G} {i' : H' ⟶ G}

/-- Conjugacy transported along both source isomorphisms. -/
theorem precomp_isos {K K' : GroupScheme S} (h : SubgroupConjugate i i')
    (e : K ≅ H) (e' : K' ≅ H') :
    SubgroupConjugate (e.hom ≫ i) (e'.hom ≫ i') :=
  (SubgroupConjugate.iso_source e i).trans
    (h.trans (SubgroupConjugate.iso_source e' i').symm)

/-- Successive base changes give conjugacy on the composite base change. -/
theorem of_baseChange_comp (a : S' ⟶ S) (b : S'' ⟶ S')
    (h : SubgroupConjugate ((GroupScheme.baseChange b).map ((GroupScheme.baseChange a).map i))
      ((GroupScheme.baseChange b).map ((GroupScheme.baseChange a).map i'))) :
    SubgroupConjugate ((GroupScheme.baseChange (b ≫ a)).map i) ((GroupScheme.baseChange (b ≫ a)).map i') := by
  have hn := ((Functor.mapGrpNatIso (Over.pullbackComp b a)) ≪≫
    Functor.mapGrpCompIso).hom.naturality i
  have hn' := ((Functor.mapGrpNatIso (Over.pullbackComp b a)) ≪≫
    Functor.mapGrpCompIso).hom.naturality i'
  change (GroupScheme.baseChange (b ≫ a)).map i ≫ (baseChangeCompIso a b G).hom =
    (baseChangeCompIso a b H).hom ≫ (GroupScheme.baseChange b).map ((GroupScheme.baseChange a).map i) at hn
  change (GroupScheme.baseChange (b ≫ a)).map i' ≫ (baseChangeCompIso a b G).hom =
    (baseChangeCompIso a b H').hom ≫ (GroupScheme.baseChange b).map ((GroupScheme.baseChange a).map i') at hn'
  apply (SubgroupConjugate.comp_iso_iff _ _ (baseChangeCompIso a b G)).mp
  rw [hn, hn']
  exact h.precomp_isos (baseChangeCompIso a b H) (baseChangeCompIso a b H')

end SubgroupConjugate

/-- Internal strengthened conclusion, retaining an isomorphism of torus sources. -/
def EtaleLocallySubgroupConjugate {S : Scheme.{u}} {H H' G : GroupScheme S}
    (i : H ⟶ G) (i' : H' ⟶ G) : Prop :=
  ∃ 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S,
    ∀ j, SubgroupConjugate ((GroupScheme.baseChange (𝒰.f j)).map i) ((GroupScheme.baseChange (𝒰.f j)).map i')

namespace EtaleLocallySubgroupConjugate
variable {S : Scheme.{u}} {H H' G : GroupScheme S} {i : H ⟶ G} {i' : H' ⟶ G}

local instance : MorphismProperty.IsStableUnderComposition
    (@Etale : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsMultiplicative.toIsStableUnderComposition

/-- Assemble conjugacy covers through the composite base-change comparison. -/
theorem of_etaleCover (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (h : ∀ j, EtaleLocallySubgroupConjugate
      ((GroupScheme.baseChange (𝒰.f j)).map i) ((GroupScheme.baseChange (𝒰.f j)).map i')) :
    EtaleLocallySubgroupConjugate i i' := by
  choose 𝒱 h𝒱 using h
  refine ⟨𝒰.bind 𝒱, fun ⟨j, k⟩ => ?_⟩
  exact (h𝒱 j k).of_baseChange_comp (𝒰.f j) ((𝒱 j).f k)

/-- Source coordinates do not affect the etale-local assertion. -/
theorem of_precomp_isos {K K' : GroupScheme S} (e : K ≅ H) (e' : K' ≅ H')
    (h : EtaleLocallySubgroupConjugate (e.hom ≫ i) (e'.hom ≫ i')) :
    EtaleLocallySubgroupConjugate i i' := by
  obtain ⟨𝒰, h𝒰⟩ := h
  refine ⟨𝒰, fun j => ?_⟩
  have hj := h𝒰 j
  simp only [Functor.map_comp] at hj
  exact SubgroupConjugate.of_precomp_isos ((GroupScheme.baseChange (𝒰.f j)).mapIso e)
    ((GroupScheme.baseChange (𝒰.f j)).mapIso e') hj

/-- The pointwise affine neighbourhoods form an etale conjugacy cover. -/
theorem of_standardSplit_affine {R : CommRingCat.{u}}
    (I J : Type u) [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (G : GroupScheme (Spec R)) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : splitTorus (Spec R) I ⟶ G) (i' : splitTorus (Spec R) J ⟶ G)
    (hi : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hi' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ J) i') :
    EtaleLocallySubgroupConjugate i i' := by
  classical
  choose A b hb hs hc using
    (fun s => splitTorus.exists_etale_subgroupConjugate I J G i i' hi hi' s)
  refine ⟨Scheme.Cover.mkOfCovers (P := @Etale) (Spec R) (fun s => Spec (A s)) b
    (fun s => ?_) hb, hc⟩
  exact ⟨s, (hs s).choose, (hs s).choose_spec⟩

/-- Remove the chosen coordinates from two split tori over an affine base. -/
theorem of_isSplitTorus_affine {R : CommRingCat.{u}}
    {T T' : CommGroupScheme (Spec R)} {G : GroupScheme (Spec R)}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G}
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (hi : IsFibrewiseMaximalTorus i) (hi' : IsFibrewiseMaximalTorus i') :
    EtaleLocallySubgroupConjugate i i' := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  obtain ⟨J, hJ, ⟨e'⟩⟩ := hT'
  let : Finite I := hI
  let : Finite J := hJ
  let : Fintype I := Fintype.ofFinite I
  let : Fintype J := Fintype.ofFinite J
  apply of_precomp_isos e.symm e'.symm
  exact of_standardSplit_affine I J G (e.inv ≫ i) (e'.inv ≫ i')
    (hi.iso_comp (T' := splitTorus.commGroupScheme _ I) e.symm)
    (hi'.iso_comp (T' := splitTorus.commGroupScheme _ J) e'.symm)

/-- Affine open refinement removes any affineness assumption on the base. -/
theorem of_isSplitTorus {T T' : CommGroupScheme S}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G}
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (hi : IsFibrewiseMaximalTorus i) (hi' : IsFibrewiseMaximalTorus i') :
    EtaleLocallySubgroupConjugate i i' := by
  let 𝒰 := S.affineOpenCover.openCover.changeProp (Q := @Etale) (fun _ => inferInstance)
  apply of_etaleCover 𝒰
  intro j
  let : Smooth ((GroupScheme.baseChange (𝒰.f j)).obj G).X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.X.hom (𝒰.f j)))
  let : IsAffineHom ((GroupScheme.baseChange (𝒰.f j)).obj G).X.hom :=
    MorphismProperty.pullback_snd G.X.hom (𝒰.f j) inferInstance
  exact of_isSplitTorus_affine (R := S.affineOpenCover.X j)
    (T := (CommGroupScheme.baseChange (𝒰.f j)).obj T)
    (T' := (CommGroupScheme.baseChange (𝒰.f j)).obj T')
    (G := (GroupScheme.baseChange (𝒰.f j)).obj G)
    (i := (GroupScheme.baseChange (𝒰.f j)).map i)
    (i' := (GroupScheme.baseChange (𝒰.f j)).map i')
    (hT.baseChange (𝒰.f j)) (hT'.baseChange (𝒰.f j))
    (hi.baseChange_forConjugacy (𝒰.f j)) (hi'.baseChange_forConjugacy (𝒰.f j))

/-- Split both relative tori successively, then compose the conjugacy covers. -/
theorem of_relativeTori {T T' : CommGroupScheme S}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G}
    (hT : RelativeTorus.IsTorus T.toGrp) (hT' : RelativeTorus.IsTorus T'.toGrp)
    (hi : IsFibrewiseMaximalTorus i) (hi' : IsFibrewiseMaximalTorus i') :
    EtaleLocallySubgroupConjugate i i' := by
  obtain ⟨𝒰, h𝒰⟩ := hT
  apply of_etaleCover 𝒰
  intro j
  let : Smooth ((GroupScheme.baseChange (𝒰.f j)).obj G).X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.X.hom (𝒰.f j)))
  let : IsAffineHom ((GroupScheme.baseChange (𝒰.f j)).obj G).X.hom :=
    MorphismProperty.pullback_snd G.X.hom (𝒰.f j) inferInstance
  obtain ⟨𝒱, h𝒱⟩ := hT'.baseChange (𝒰.f j)
  apply of_etaleCover 𝒱
  intro k
  let : Smooth ((GroupScheme.baseChange (𝒱.f k)).obj
      ((GroupScheme.baseChange (𝒰.f j)).obj G)).X.hom :=
    inferInstanceAs (Smooth (pullback.snd _ (𝒱.f k)))
  let : IsAffineHom ((GroupScheme.baseChange (𝒱.f k)).obj
      ((GroupScheme.baseChange (𝒰.f j)).obj G)).X.hom :=
    MorphismProperty.pullback_snd _ (𝒱.f k) inferInstance
  exact of_isSplitTorus
    (T := (CommGroupScheme.baseChange (𝒱.f k)).obj
      ((CommGroupScheme.baseChange (𝒰.f j)).obj T))
    (T' := (CommGroupScheme.baseChange (𝒱.f k)).obj
      ((CommGroupScheme.baseChange (𝒰.f j)).obj T'))
    (G := (GroupScheme.baseChange (𝒱.f k)).obj
      ((GroupScheme.baseChange (𝒰.f j)).obj G))
    (i := (GroupScheme.baseChange (𝒱.f k)).map ((GroupScheme.baseChange (𝒰.f j)).map i))
    (i' := (GroupScheme.baseChange (𝒱.f k)).map ((GroupScheme.baseChange (𝒰.f j)).map i'))
    ((h𝒰 j).baseChange (𝒱.f k)) (h𝒱 k)
    ((hi.baseChange_forConjugacy (𝒰.f j)).baseChange_forConjugacy (𝒱.f k))
    ((hi'.baseChange_forConjugacy (𝒰.f j)).baseChange_forConjugacy (𝒱.f k))

end EtaleLocallySubgroupConjugate

/-- Maximal tori of every smooth affine group scheme are conjugate etale
locally, over an arbitrary base and in every universe. -/
theorem etaleLocalMaximalTorusConjugacy : EtaleLocalMaximalTorusConjugacyStatement.{u} := by
  intro S G _ _ T T' i i' hT _ hi hT' _ hi'
  obtain ⟨𝒰, h𝒰⟩ := EtaleLocallySubgroupConjugate.of_relativeTori hT hT' hi hi'
  refine ⟨𝒰, fun j => ?_⟩
  obtain ⟨g, e, he⟩ := h𝒰 j
  exact ⟨g, he ▸ SubgroupFunctor.range_iso_comp e _⟩

end Langlands.GroupScheme
