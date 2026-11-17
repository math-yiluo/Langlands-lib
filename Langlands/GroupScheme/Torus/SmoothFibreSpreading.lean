import Langlands.GroupScheme.Torus.RelativeLiftingProof
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.RelativeDescent
import Langlands.GroupScheme.SmoothMonoLocalIso
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.Reductive.EtaleResidueFibre
import Langlands.GroupScheme.Reductive.SpecialFibreCommonTorus

/-! # Spreading a torus fibre in a smooth affine group -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

/-- Connected residue fibres of a locally finite-type affine group are geometrically connected. -/
theorem geometricallyConnected_of_connected_residueFibres
    {S : Scheme.{u}} (G : GroupScheme S)
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]
    (hconn : ∀ s : S, ConnectedSpace (RelativeIdentityComponent.residueFiber G s).X.left) :
    GeometricallyConnected G.X.hom := by
  apply (GeometricallyConnected.iff_geometricallyConnected_fiber G.X.hom).mpr
  intro s
  let Gs := RelativeIdentityComponent.residueFiber G s
  have : LocallyOfFiniteType Gs.X.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd G.X.hom (S.fromSpecResidueField s)))
  have : IsAffineHom Gs.X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (S.fromSpecResidueField s)))
  have : ConnectedSpace Gs.X.left := hconn s
  exact Gs.geometricallyConnected_of_connected

/-- A split residue fibre of a smooth affine group with geometrically connected fibres
extends to a split presentation over an etale neighbourhood. -/
theorem exists_etale_split_of_split_residueFibre
    {S : Scheme.{u}} (G : GroupScheme S) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [GeometricallyConnected G.X.hom] (s : S)
    (hs : IsSplitTorus (RelativeIdentityComponent.residueFiber G s)) :
    ∃ (V : Scheme.{u}) (q : V ⟶ S), Etale q ∧ s ∈ Set.range q ∧
      IsSplitTorus ((baseChange q).obj G) := by
  let Gs := RelativeIdentityComponent.residueFiber G s
  obtain ⟨U, p, hp, b, hb, T, hT, i, hi, e, he⟩ :=
    relativeSplitTorusLifting S G s Gs hs (𝟙 Gs) inferInstance
  let : Etale p := hp
  have : Smooth T.X.hom := hT.smooth
  have : Smooth ((baseChange p).obj G).X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.X.hom p))
  have : GeometricallyConnected ((baseChange p).obj G).X.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd G.X.hom p))
  have : IsClosedImmersion i.hom.hom.left := hi
  let ε : (baseChange b).obj ((baseChange p).obj G) ≅ Gs :=
    (baseChangeCompIso p b G).symm ≪≫
      eqToIso (congrArg (fun f => (baseChange f).obj G) hb)
  have he' : (baseChange b).map i ≫ ε.hom = e.hom := by
    simpa only [ε, Iso.trans_hom, Iso.symm_hom, Category.comp_id] using he
  have hib : IsIso ((baseChange b).map i) := by
    apply (isIso_comp_right_iff _ ε.hom).mp
    rw [he']
    infer_instance
  let t := b (IsLocalRing.closedPoint (S.residueField s))
  have his : IsIso ((baseChange (U.fromSpecResidueField t)).map i) :=
    isIso_residueFibre_of_fieldPoint i b hib
  have his' : IsIso (((baseChange (U.fromSpecResidueField t)).map i).hom.hom.left) := by
    let := his
    infer_instance
  obtain ⟨W, htW, hiW⟩ := SmoothMonoLocalIso.isIsoNear_of_residueFiber i t his'
  have : IsIso (((baseChange W.ι).map i).hom.hom.left) := hiW
  have : IsIso ((baseChange W.ι).map i) :=
    TorusIsomorphismLocus.isIso_of_underlying _
  have hsplit : IsSplitTorus ((baseChange W.ι).obj ((baseChange p).obj G)) :=
    IsSplitTorus.of_iso (asIso ((baseChange W.ι).map i)).symm (hT.baseChange W.ι)
  refine ⟨W, W.ι ≫ p, inferInstance, ?_, ?_⟩
  · refine ⟨⟨t, htW⟩, ?_⟩
    change p (b (IsLocalRing.closedPoint (S.residueField s))) = s
    rw [← Scheme.Hom.comp_apply, hb, Scheme.fromSpecResidueField_apply]
  · exact IsSplitTorus.of_iso (baseChangeCompIso p W.ι G) hsplit

/-- A torus residue fibre of a smooth affine group with geometrically connected fibres
extends to a split presentation on some etale neighbourhood. -/
theorem exists_etale_split_of_torus_residueFibre
    {S : Scheme.{u}} (G : GroupScheme S) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [GeometricallyConnected G.X.hom] (s : S)
    (hs : IsTorus (RelativeIdentityComponent.residueFiber G s)) :
    ∃ (V : Scheme.{u}) (q : V ⟶ S), Etale q ∧ s ∈ Set.range q ∧
      IsSplitTorus ((baseChange q).obj G) := by
  obtain ⟨K, hK, hA, hfin, hGal, hsplit⟩ :=
    torusFiniteGaloisSplitting (S.residueField s) _ hs
  let d := Langlands.AlgebraicGeometry.etaleResidueExtension S s K
  have : Etale d.projection := d.etale
  have : Smooth ((baseChange d.projection).obj G).X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.X.hom d.projection))
  have : IsAffineHom ((baseChange d.projection).obj G).X.hom :=
    MorphismProperty.pullback_snd G.X.hom d.projection inferInstance
  have : GeometricallyConnected ((baseChange d.projection).obj G).X.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd G.X.hom d.projection))
  have hext : IsSplitTorus ((baseChange d.extensionPoint).obj G) :=
    IsSplitTorus.of_iso
      (baseChangeCompIso (S.fromSpecResidueField s)
        (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) K))) G) hsplit
  have hnew : IsSplitTorus (RelativeIdentityComponent.residueFiber
      ((baseChange d.projection).obj G) d.point) :=
    IsSplitTorus.of_iso (d.groupFibreIso G).symm (hext.baseChange d.inverseResiduePoint)
  obtain ⟨V, q, hq, ht, hV⟩ :=
    exists_etale_split_of_split_residueFibre ((baseChange d.projection).obj G) d.point hnew
  let : Etale q := hq
  refine ⟨V, q ≫ d.projection, inferInstance, ?_, ?_⟩
  · obtain ⟨v, hv⟩ := ht
    refine ⟨v, ?_⟩
    change d.projection (q v) = s
    rw [hv, d.point_over]
  · exact IsSplitTorus.of_iso (baseChangeCompIso d.projection q G) hV

/-- The relative-torus property descends from an etale map to its open image. -/
theorem relativeTorus_etaleImage_of_split {S V : Scheme.{u}}
    (G : GroupScheme S) (q : V ⟶ S) [Etale q]
    (h : IsSplitTorus ((baseChange q).obj G)) :
    ∃ U : S.Opens, (U : Set S) = Set.range q ∧
      RelativeTorus.IsTorus ((baseChange U.ι).obj G) := by
  let U : S.Opens := ⟨Set.range q, q.isOpenMap.isOpen_range⟩
  let q' : V ⟶ U := IsOpenImmersion.lift U.ι q (by simp [U])
  have hq' : q' ≫ U.ι = q := IsOpenImmersion.lift_fac _ _ _
  have : Surjective q' := ⟨fun ⟨x, ⟨y, hy⟩⟩ =>
    ⟨y, by
      apply U.ι.injective
      change (q' ≫ U.ι) y = x
      rw [hq']
      exact hy⟩⟩
  have : Etale (q' ≫ U.ι) := by rw [hq']; infer_instance
  have : Etale q' := Etale.of_comp q' U.ι
  refine ⟨U, rfl, RelativeTorus.IsTorus.of_baseChange_of_etale q' ?_⟩
  apply RelativeTorus.IsTorus.of_isSplitTorus
  apply IsSplitTorus.of_iso (baseChangeCompIso U.ι q' G).symm
  change IsSplitTorus ((baseChange (q' ≫ U.ι)).obj G)
  rwa [hq']

/-- A torus fibre of a smooth affine group with geometrically connected fibres
spreads to a Zariski neighbourhood. -/
theorem exists_open_torus_of_smooth_torus_residueFibre
    {S : Scheme.{u}} (G : GroupScheme S) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [GeometricallyConnected G.X.hom] (s : S)
    (hs : IsTorus (RelativeIdentityComponent.residueFiber G s)) :
    ∃ U : S.Opens, s ∈ U ∧ RelativeTorus.IsTorus ((baseChange U.ι).obj G) := by
  obtain ⟨V, q, hq, hsV, hsplit⟩ := exists_etale_split_of_torus_residueFibre G s hs
  let : Etale q := hq
  obtain ⟨U, hU, ht⟩ := relativeTorus_etaleImage_of_split G q hsplit
  exact ⟨U, by rw [← SetLike.mem_coe, hU]; exact hsV, ht⟩

end Langlands.GroupScheme
