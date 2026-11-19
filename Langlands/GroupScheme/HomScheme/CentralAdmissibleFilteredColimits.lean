import Langlands.GroupScheme.HomScheme.AdmissibleFilteredColimits
import Langlands.GroupScheme.HomScheme.CentralAdmissiblePresheaf

/-! # Filtered colimits of central closed torus subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.TorusSubgroupModuli

open Langlands.AlgebraicGeometry.UnramifiedFunctor
open Langlands.AlgebraicGeometry.SchemeLimitModel

private theorem central_baseChange_iff_eq_maps {S T : Scheme.{u}}
    {H G : GroupScheme S} (i : H ⟶ G) (b : T ⟶ S) :
    IsCentral ((baseChange b).map i) ↔
      (Over.pullback b).map ((fst H.X G.X ≫ i.hom.hom) * snd H.X G.X) =
        (Over.pullback b).map (snd H.X G.X * (fst H.X G.X ≫ i.hom.hom)) := by
  let P := Over.pullback b
  constructor
  · intro h
    have h' := commute_of_mem_center
      (h (P.obj (H.X ⊗ G.X)) (P.map (fst H.X G.X))) (P.map (snd H.X G.X))
    simp only [Functor.map_comp, Functor.map_mul]
    exact h'.eq
  · intro h
    apply ArtinianCentrality.isCentral_of_universal_commute
    let J := (baseChange b).obj H
    let K := (baseChange b).obj G
    let e := CartesianMonoidalCategory.prodComparison P H.X G.X
    change (fst J.X K.X ≫ ((baseChange b).map i).hom.hom) * snd J.X K.X =
      snd J.X K.X * (fst J.X K.X ≫ ((baseChange b).map i).hom.hom)
    apply (cancel_epi e).mp
    have he₁ : e ≫ (fst J.X K.X ≫ ((baseChange b).map i).hom.hom) =
        P.map (fst H.X G.X ≫ i.hom.hom) := by
      change e ≫ (fst (P.obj H.X) (P.obj G.X) ≫ P.map i.hom.hom) = _
      rw [← Category.assoc]
      exact (congrArg (fun a => a ≫ P.map i.hom.hom)
        (CartesianMonoidalCategory.prodComparison_fst P H.X G.X)).trans (P.map_comp _ _).symm
    have he₂ : e ≫ snd J.X K.X = P.map (snd H.X G.X) :=
      CartesianMonoidalCategory.prodComparison_snd _ _ _
    simp only [MonObj.comp_mul, he₁, he₂]
    simpa only [Functor.map_mul] using! h

set_option maxHeartbeats 900000 in
private theorem exists_stage_central {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c) (i : J)
    {H G : GroupScheme (Spec (F.obj i))} [QuasiCompact H.X.hom]
    [QuasiCompact G.X.hom] [LocallyOfFiniteType G.X.hom]
    (j : H ⟶ G) (h : IsCentral ((baseChange (Spec.map (c.ι.app i))).map j)) :
    ∃ (l : J) (r : i ⟶ l), IsCentral ((baseChange (Spec.map (F.map r))).map j) := by
  let K := initialRingAlgebraDiagram F i
  let c₀ := initialRingAlgebraCocone F i c
  let B := F.obj i
  let D := spectrumDiagram B K
  let t := spectrumStructure B K
  let C := spectrumCone B K c₀
  let p := spectrumBaseMap B K c₀
  have hC : IsLimit C :=
    spectrumConeIsLimit B K c₀ (initialRingAlgebraCoconeIsColimit F i c hc)
  have hp : ∀ l, C.π.app l ≫ t.app l = p := spectrumCone_compat B K c₀
  have : ∀ l, IsAffine (D.obj l) := spectrumDiagram_obj_isAffine B K
  have : QuasiCompact (H.X ⊗ G.X).hom := by
    rw [Over.tensorObj_hom]
    infer_instance
  let x := fst H.X G.X ≫ j.hom.hom
  let y := snd H.X G.X
  have hmap : (Over.pullback p).map (x * y) = (Over.pullback p).map (y * x) := by
    exact (central_baseChange_iff_eq_maps j p).mp h
  obtain ⟨l, hl⟩ := Descent.AffineLimit.exists_level_map_eq_of_quasiCompact D t C hC p hp (x * y) (y * x) hmap
  exact ⟨l.unop.right, l.unop.hom, (central_baseChange_iff_eq_maps j (t.app l)).mpr (hl l (𝟙 l))⟩

section Stages

variable {S : Scheme.{u}} (G : GroupScheme S) [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
  {R : Type u} [CommRing R] (f : Spec (CommRingCat.of R) ⟶ S)
  {J : Type u} [SmallCategory J] [IsFiltered J]
  (K : J ⥤ CommAlgCat.{u} R) {c : Cocone K} (hc : IsColimit c)

include hc in
set_option maxHeartbeats 1200000 in
private theorem exists_central_stage (i : J)
    (x : (smallAdmissiblePresheaf G).obj (op (algebraOver f (K.obj i))))
    (h : (smallAdmissiblePresheaf G).map (algHomOver f (c.ι.app i).hom).op x ∈
      (centralAdmissibleSubfunctor G).obj (op (algebraOver f c.pt))) :
    ∃ (j : J) (r : i ⟶ j),
      (smallAdmissiblePresheaf G).map (algHomOver f (K.map r).hom).op x ∈
        (centralAdmissibleSubfunctor G).obj (op (algebraOver f (K.obj j))) := by
  let : IsConnected J := IsFiltered.isConnected J
  let U := forget₂ (CommAlgCat.{u} R) CommRingCat.{u}
  let F := K ⋙ U
  let c₀ := U.mapCocone c
  have hc₀ : IsColimit c₀ := isColimitOfPreserves
    ((commAlgCatEquivUnder (CommRingCat.of R)).functor ⋙ Under.forget _) hc
  let T := algebraOver f (K.obj i)
  let r := admissibleRepresentative (smallAdmissibleEquiv G T x)
  let Gᵢ : GroupScheme (Spec (F.obj i)) := (baseChange T.hom).obj G
  let Hᵢ : GroupScheme (Spec (F.obj i)) := r.group
  let jᵢ : Hᵢ ⟶ Gᵢ := r.hom
  have : IsAffineHom Hᵢ.X.hom := r.torus.isAffineHom
  have : QuasiCompact Hᵢ.X.hom := inferInstance
  have : QuasiCompact Gᵢ.X.hom :=
    MorphismProperty.pullback_snd (P := @QuasiCompact) _ _ inferInstance
  have : LocallyOfFiniteType Gᵢ.X.hom :=
    MorphismProperty.pullback_snd (P := @LocallyOfFiniteType) _ _ inferInstance
  let b : algebraOver f c.pt ⟶ T := algHomOver f (c.ι.app i).hom
  have hlim' := (mem_centralAdmissible_map_iff (G := G) b x).mp h
  have hb : Spec.map (c₀.ι.app i) = b.left := rfl
  have hlim : IsCentral ((baseChange (Spec.map (c₀.ι.app i))).map jᵢ) := by
    rw [hb]
    exact hlim'
  obtain ⟨j, a, hj⟩ := exists_stage_central F c₀ hc₀ i (H := Hᵢ) (G := Gᵢ) jᵢ hlim
  let d : algebraOver f (K.obj j) ⟶ T := algHomOver f (K.map a).hom
  have hd : Spec.map (F.map a) = d.left := rfl
  have hj' : IsCentral ((baseChange d.left).map r.hom) := by
    rw [← hd]
    exact hj
  exact ⟨j, a, (mem_centralAdmissible_map_iff (G := G) d x).mpr hj'⟩

end Stages

/-- The central closed torus-subgroup presheaf satisfies Murre's
filtered-colimit condition under the same hypotheses as the full presheaf. -/
def CentralAdmissibleFilteredColimitsStatement : Prop :=
  ∀ (S : Scheme.{u}) [IsLocallyNoetherian S] (G : GroupScheme S)
    [LocallyOfFinitePresentation G.X.hom] [QuasiCompact G.X.hom] [IsSeparated G.X.hom],
    FilteredColimits (smallCentralAdmissiblePresheaf G)

set_option maxHeartbeats 1200000 in
/-- All-test centrality descends at an algebra stage, and eventual equality
is inherited from actual closed torus-subgroup equality. -/
theorem smallCentralAdmissiblePresheaf_filteredColimits :
    CentralAdmissibleFilteredColimitsStatement.{u} := by
  intro S _ G _ _ _ R _ f hf
  let P := algebraFunctor f ⋙ smallAdmissiblePresheaf G
  have : PreservesFilteredColimitsOfSize.{u,u} P :=
    smallAdmissiblePresheaf_filteredColimits S G R f hf
  refine ⟨fun J _ _ => ⟨fun {K} => ⟨fun {c} hc => ⟨?_⟩⟩⟩⟩
  let c₀ := P.mapCocone c
  have hc₀ : IsColimit c₀ := isColimitOfPreserves P hc
  refine Types.FilteredColimit.isColimitOf' _ _ (fun x => ?_) (fun i x y h => ?_)
  · obtain ⟨i, y, hy⟩ := Types.jointly_surjective_of_isColimit hc₀ x.val
    have hcentral : c₀.ι.app i y ∈ (centralAdmissibleSubfunctor G).obj (op (algebraOver f c.pt)) :=
      hy.symm ▸ x.property
    obtain ⟨j, a, ha⟩ := exists_central_stage G f K hc i y hcentral
    refine ⟨j, ⟨(K ⋙ P).map a y, ha⟩, Subtype.ext ?_⟩
    exact hy.symm.trans (congrArg (fun m : (K ⋙ P).obj i ⟶ c₀.pt => m y) (c₀.w a)).symm
  · have hxy : c₀.ι.app i x.val = c₀.ι.app i y.val := congrArg Subtype.val h
    obtain ⟨j, a, ha⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc₀ x.val y.val).mp hxy
    exact ⟨j, a, Subtype.ext ha⟩

end Langlands.GroupScheme.TorusSubgroupModuli
