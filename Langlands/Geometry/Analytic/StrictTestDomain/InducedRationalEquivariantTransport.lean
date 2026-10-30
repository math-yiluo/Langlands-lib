import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalAtlasAction

/-! # Equivariant bounded transport on actual induced affinoid families -/

noncomputable section

universe u v

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory Topology

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}

namespace OpenSubgroupTransport

/-- The action pullback has the actual inverse ambient operator as its base map. -/
theorem strictActionPullback_comp_baseMap (X : ρ.OpenSubgroupTransport)
    (g : G) (c : G ⧸ X.subgroup.toSubgroup) :
    (X.strictActionPullback g c).comp X.domain.obj.baseMap =
      X.domain.obj.baseMap.comp (ρ.toMonoidHom (X.actionChartElement g c : G)).inv := by
  have h := X.chartSectionAction_comp_baseMap (X.actionChartElement g c)⁻¹
  simpa only [strictActionPullback, map_inv, InvMemClass.coe_inv,
    Aut.Aut_inv_def, Iso.symm] using h

namespace Hom

variable {X Y Z : ρ.OpenSubgroupTransport}

/-- Right translation by the inverse transport label commutes with left translation. -/
@[simp]
theorem cosetMap_smul (f : X ⟶ Y) (g : G) (c : G ⧸ X.subgroup.toSubgroup) :
    f.cosetMap (g • c) = g • f.cosetMap c := by
  induction c using Quotient.inductionOn with
  | h a =>
    change ((g * a) * f.label⁻¹ : G ⧸ Y.subgroup.toSubgroup) =
      (g * (a * f.label⁻¹) : G ⧸ Y.subgroup.toSubgroup)
    rw [mul_assoc]

private theorem ambientInv_comp_equivariance (r s : G) :
    (ρ.toMonoidHom r).inv.comp (ρ.toMonoidHom s).inv =
      (ρ.toMonoidHom (s * r)).inv := by
  rw [map_mul]
  rfl

/-- Equivariance holds for the bounded rational quotient maps themselves. -/
theorem cosetChartPullback_equivariant (f : X ⟶ Y) (g : G)
    (c : G ⧸ X.subgroup.toSubgroup) :
    (X.strictActionPullback g c).comp (f.cosetChartPullback (g • c)) =
      (f.cosetChartPullback c).comp (Y.strictActionPullback g (f.cosetMap c)) := by
  apply Y.domain.obj.hom_ext
  conv_lhs =>
    rw [BoundedAlgHom.comp_assoc, cosetChartPullback_comp_baseMap,
      ← BoundedAlgHom.comp_assoc, strictActionPullback_comp_baseMap,
      BoundedAlgHom.comp_assoc, ambientInv_comp_equivariance]
  conv_rhs =>
    rw [BoundedAlgHom.comp_assoc, strictActionPullback_comp_baseMap,
      ← BoundedAlgHom.comp_assoc, cosetChartPullback_comp_baseMap,
      BoundedAlgHom.comp_assoc, ambientInv_comp_equivariance]
  simp only [cosetMap_smul, actionChartElement_coe, mul_assoc, mul_inv_cancel_left]

/-- The published bounded radius-one comparison carries the strict transport map. -/
theorem affinoidChartPullback_eq_ofStrictMap (f : X ⟶ Y)
    (c : G ⧸ X.subgroup.toSubgroup) :
    f.affinoidChartPullback c =
      PresentedAffinoidAlgebra.ofStrictMap K (f.cosetChartPullback c) := rfl

/-- Algebra equivariance survives passage to the actual generalized quotient algebras. -/
theorem affinoidChartPullback_equivariant (f : X ⟶ Y) (g : G)
    (c : G ⧸ X.subgroup.toSubgroup) :
    (X.affinoidActionPullback g c).comp (f.affinoidChartPullback (g • c)) =
      (f.affinoidChartPullback c).comp (Y.affinoidActionPullback g (f.cosetMap c)) := by
  simp only [affinoidActionPullback, affinoidChartPullback_eq_ofStrictMap]
  exact ((PresentedAffinoidAlgebra.ofStrictFunctor K).map_comp
    (f.cosetChartPullback (g • c)) (X.strictActionPullback g c)).symm.trans
      ((congrArg (PresentedAffinoidAlgebra.ofStrictMap K)
        (f.cosetChartPullback_equivariant g c)).trans
          ((PresentedAffinoidAlgebra.ofStrictFunctor K).map_comp
            (Y.strictActionPullback g (f.cosetMap c)) (f.cosetChartPullback c)))

/-- The full family morphisms commute, retaining indices and bounded pullbacks. -/
theorem affinoidFamilyMap_equivariant (f : X ⟶ Y) (g : G) :
    X.affinoidActionMap g ≫ f.affinoidFamilyMap =
      f.affinoidFamilyMap ≫ Y.affinoidActionMap g := by
  apply AffinoidFamily.Hom.ext (funext (f.cosetMap_smul g))
  exact heq_of_eq (funext (f.affinoidChartPullback_equivariant g))

/-- The actual nonempty target components commute with the group action. -/
theorem atlasTarget_action (f : X ⟶ Y) (g : G) (c : X.inducedAffinoidAtlas.Index) :
    f.atlasTarget (X.actionAtlasTarget g c) =
      Y.actionAtlasTarget g (f.atlasTarget c) :=
  Subtype.ext (f.cosetMap_smul g c.val)

/-- Every admissible square of atlas charts has equal bounded composite pullbacks. -/
theorem atlasPullback_equivariant (f : X ⟶ Y) (g : G)
    (c cg : X.inducedAffinoidAtlas.Index) (d dg : Y.inducedAffinoidAtlas.Index)
    (hX : (fun z => g • z) '' Set.range (X.inducedAffinoidAtlas.chart c) ⊆
      Set.range (X.inducedAffinoidAtlas.chart cg))
    (hf : f.inducedMap '' Set.range (X.inducedAffinoidAtlas.chart c) ⊆
      Set.range (Y.inducedAffinoidAtlas.chart d))
    (hfg : f.inducedMap '' Set.range (X.inducedAffinoidAtlas.chart cg) ⊆
      Set.range (Y.inducedAffinoidAtlas.chart dg))
    (hY : (fun z => g • z) '' Set.range (Y.inducedAffinoidAtlas.chart d) ⊆
      Set.range (Y.inducedAffinoidAtlas.chart dg)) :
    (X.actionAtlasPullback g c cg hX).comp (f.atlasPullback cg dg hfg) =
      (f.atlasPullback c d hf).comp (Y.actionAtlasPullback g d dg hY) := by
  have hcg : cg.val = g • c.val :=
    congrArg Subtype.val (X.actionAtlasTarget_eq g c cg hX).symm
  have hd : d.val = f.cosetMap c.val :=
    congrArg Subtype.val (f.atlasTarget_eq c d hf).symm
  change (X.affinoidActionPullback g c.val).comp (f.affinoidChartPullback cg.val) =
    (f.affinoidChartPullback c.val).comp (Y.affinoidActionPullback g d.val)
  rw [hcg, hd]
  exact f.affinoidChartPullback_equivariant g c.val

/-- Transport lifted to a morphism of the constructed bounded group actions. -/
def equivariantAffinoidMap (f : X ⟶ Y) :
    X.inducedAffinoidAction ⟶ Y.inducedAffinoidAction where
  hom := f.affinoidFamilyMap
  comm := f.affinoidFamilyMap_equivariant

@[simp]
theorem equivariantAffinoidMap_id (X : ρ.OpenSubgroupTransport) :
    (𝟙 X : X ⟶ X).equivariantAffinoidMap = 𝟙 X.inducedAffinoidAction :=
  Action.Hom.ext (affinoidFamilyMap_id X)

theorem equivariantAffinoidMap_comp (f : X ⟶ Y) (h : Y ⟶ Z) :
    (f ≫ h).equivariantAffinoidMap =
      f.equivariantAffinoidMap ≫ h.equivariantAffinoidMap :=
  Action.Hom.ext (f.affinoidFamilyMap_comp h)

end Hom

/-- Actual bounded group actions and equivariant transport form a functor. -/
def inducedEquivariantAffinoidFunctor :
    ρ.OpenSubgroupTransport ⥤ Action (AffinoidFamily.{u, v} K) G where
  obj X := X.inducedAffinoidAction
  map := Hom.equivariantAffinoidMap
  map_id := Hom.equivariantAffinoidMap_id
  map_comp := Hom.equivariantAffinoidMap_comp

/-- Forgetting the actions recovers the already constructed bounded transport. -/
theorem inducedEquivariantAffinoidFunctor_forget :
    inducedEquivariantAffinoidFunctor (ρ := ρ) ⋙
        Action.forget (AffinoidFamily.{u, v} K) G =
      inducedAffinoidTransportFunctor := rfl

/-- The realized bounded equivariant functor is naturally the balanced-quotient diagram. -/
def inducedEquivariantSpectrumComparison :
    inducedEquivariantAffinoidFunctor (ρ := ρ) ⋙
        (AffinoidFamily.spectrumFunctor (K := K)).mapAction G ≅
      inducedSpectrumFunctor ⋙ forget₂ _ (Action TopCat.{max u v} G) :=
  NatIso.ofComponents (fun X => X.inducedAffinoidSpectrumIso) (fun {X Y} f => by
    apply Action.Hom.ext
    apply TopCat.ext
    intro p
    exact (f.affinoidFamilyMap_realization p).symm)

/-- The realized bounded equivariant transport has jointly continuous actions. -/
def inducedAffinoidContinuousSpectrumFunctor :
    ρ.OpenSubgroupTransport ⥤ ContAction TopCat.{max u v} G where
  obj X := X.inducedAffinoidContinuousSpectrum
  map f := ObjectProperty.homMk
    (((AffinoidFamily.spectrumFunctor (K := K)).mapAction G).map
      f.equivariantAffinoidMap)
  map_id X := by
    apply ObjectProperty.hom_ext _
    exact (inducedEquivariantAffinoidFunctor (ρ := ρ) ⋙
      (AffinoidFamily.spectrumFunctor (K := K)).mapAction G).map_id X
  map_comp f h := by
    apply ObjectProperty.hom_ext _
    exact (inducedEquivariantAffinoidFunctor (ρ := ρ) ⋙
      (AffinoidFamily.spectrumFunctor (K := K)).mapAction G).map_comp f h

/-- The comparison preserves the jointly continuous group actions and every transport map. -/
def inducedContinuousSpectrumComparison :
    inducedAffinoidContinuousSpectrumFunctor (ρ := ρ) ≅ inducedSpectrumFunctor :=
  NatIso.ofComponents (fun X =>
    { hom := ObjectProperty.homMk X.inducedAffinoidSpectrumIso.hom
      inv := ObjectProperty.homMk X.inducedAffinoidSpectrumIso.inv
      hom_inv_id := by
        apply ObjectProperty.hom_ext _
        exact X.inducedAffinoidSpectrumIso.hom_inv_id
      inv_hom_id := by
        apply ObjectProperty.hom_ext _
        exact X.inducedAffinoidSpectrumIso.inv_hom_id })
    (fun {X Y} f => by
      apply ObjectProperty.hom_ext _
      apply Action.Hom.ext
      apply TopCat.ext
      intro p
      exact (f.affinoidFamilyMap_realization p).symm)

end OpenSubgroupTransport

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
