import Langlands.Geometry.Analytic.GeneralizedAffinoid.NormContinuousAction
import Langlands.Geometry.Analytic.GeneralizedAffinoid.StrictComparisonFunctor
import Langlands.Geometry.Analytic.NormContinuousAction

/-! # Radius-one comparison of norm-continuous affinoid actions -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open CategoryTheory

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (G : Type v) [Group G] [TopologicalSpace G]

/-- Conjugating through the actual radius-one equivalence preserves continuous
element orbits in the quotient norm. -/
theorem normContinuousAction_ofStrict
    (X : Langlands.Analytic.NormContinuousAffinoidAction K G) :
    normContinuousActionProperty K G (((ofStrictFunctor K).mapAction G).obj X.obj) := by
  intro a
  change Continuous (fun g : G =>
    (strictEquiv K X.obj.V).symm ((X.obj.ρ g).toAlgHom (strictEquiv K X.obj.V a)))
  exact (strictEquiv K X.obj.V).symm.toBoundedAlgHom.continuous.comp
    (X.property (strictEquiv K X.obj.V a))

/-- The strict continuous-orbit action category embeds through the actual
radius-one quotient comparison, retaining all equivariant bounded maps. -/
def ofStrictActionFunctor :
    Langlands.Analytic.NormContinuousAffinoidAction K G ⥤ NormContinuousAction K G :=
  (normContinuousActionProperty K G).lift
    (Langlands.Analytic.NormContinuousAffinoidAction.inclusion ⋙
      (ofStrictFunctor K).mapAction G)
    (normContinuousAction_ofStrict K G)

@[simp]
theorem ofStrictActionFunctor_obj_algebra
    (X : Langlands.Analytic.NormContinuousAffinoidAction K G) :
    ((ofStrictActionFunctor K G).obj X).obj.V = ofStrict K X.obj.V :=
  rfl

@[simp]
theorem ofStrictActionFunctor_obj_apply
    (X : Langlands.Analytic.NormContinuousAffinoidAction K G)
    (g : G) (a : ofStrict K X.obj.V) :
    (((ofStrictActionFunctor K G).obj X).obj.ρ g).toAlgHom a =
      (strictEquiv K X.obj.V).symm ((X.obj.ρ g).toAlgHom (strictEquiv K X.obj.V a)) :=
  rfl

@[simp]
theorem homMap_ofStrictActionFunctor_map
    {X Y : Langlands.Analytic.NormContinuousAffinoidAction K G} (f : X ⟶ Y) :
    NormContinuousAction.homMap ((ofStrictActionFunctor K G).map f) =
      ofStrictMap K (Langlands.Analytic.NormContinuousAffinoidAction.homMap f) :=
  rfl

/-- The inverse on equivariant arrows uses the actual bounded-map inverse,
with equivariance reflected by full faithfulness. -/
def fromStrictActionMap
    {X Y : Langlands.Analytic.NormContinuousAffinoidAction K G}
    (f : (ofStrictActionFunctor K G).obj X ⟶ (ofStrictActionFunctor K G).obj Y) :
    X ⟶ Y :=
  ObjectProperty.homMk (((ofStrictFullyFaithful K).mapAction G).preimage f.hom)

@[simp]
theorem homMap_fromStrictActionMap
    {X Y : Langlands.Analytic.NormContinuousAffinoidAction K G}
    (f : (ofStrictActionFunctor K G).obj X ⟶ (ofStrictActionFunctor K G).obj Y) :
    Langlands.Analytic.NormContinuousAffinoidAction.homMap (fromStrictActionMap K G f) =
      fromStrictMap K (NormContinuousAction.homMap f) :=
  rfl

/-- Every equivariant bounded arrow between embedded actions has a unique
equivariant bounded preimage between the strict actions. -/
def strictActionFullyFaithful : (ofStrictActionFunctor K G).FullyFaithful where
  preimage := fromStrictActionMap K G
  map_preimage f := by
    apply NormContinuousAction.hom_ext
    exact ofStrictMap_fromStrictMap K (NormContinuousAction.homMap f)
  preimage_map f := by
    apply Langlands.Analytic.NormContinuousAffinoidAction.hom_ext
    exact fromStrictMap_ofStrictMap K
      (Langlands.Analytic.NormContinuousAffinoidAction.homMap f)

instance : (ofStrictActionFunctor K G).Full :=
  (strictActionFullyFaithful K G).full

instance : (ofStrictActionFunctor K G).Faithful :=
  (strictActionFullyFaithful K G).faithful

/-- Forgetting the action commutes with the original radius-one comparison. -/
def strictActionForgetComparison :
    ofStrictActionFunctor K G ⋙ NormContinuousAction.forget ≅
      Langlands.Analytic.NormContinuousAffinoidAction.forget ⋙ ofStrictFunctor K :=
  Iso.refl _

section Restriction

variable {H : Type w} [Group H] [TopologicalSpace H]

/-- Changing the acting group commutes with the actual radius-one embedding. -/
def strictActionRestrictionComparison (f : H →ₜ* G) :
    Langlands.Analytic.NormContinuousAffinoidAction.restrict f ⋙
        ofStrictActionFunctor K H ≅
      ofStrictActionFunctor K G ⋙ NormContinuousAction.restrict f :=
  Iso.refl _

end Restriction

section Spectrum

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

/-- The concrete radius-one spectrum homeomorphism intertwines the actual
inverse-pullback actions. No continuity of group operations is needed here. -/
theorem strictActionSpectrumHomeomorph_equivariant
    (X : Langlands.Analytic.NormContinuousAffinoidAction K G)
    (g : G) (x : BanachSpectrum X.obj.V) :
    strictSpectrumHomeomorph K X.obj.V ((X.actionAut g) • x) =
      BanachSpectrum.comap
        (((ofStrictActionFunctor K G).obj X).actionAut g).inv.toBoundedRingHom
        (strictSpectrumHomeomorph K X.obj.V x) :=
  strictSpectrumHomeomorph_naturality K (X.obj.ρ (g⁻¹)) x

variable [IsTopologicalGroup G]

/-- The actual homeomorphism gives an isomorphism in the category of continuous
topological group actions. -/
def strictActionSpectrumIso
    (X : Langlands.Analytic.NormContinuousAffinoidAction K G) :
    Langlands.Analytic.NormContinuousAffinoidAction.spectrum X ≅
      NormContinuousAction.spectrum ((ofStrictActionFunctor K G).obj X) :=
  ObjectProperty.isoMk _ (Action.mkIso
    (TopCat.isoOfHomeo (strictSpectrumHomeomorph K X.obj.V))
    (fun g => by
      apply TopCat.ext
      intro x
      exact strictActionSpectrumHomeomorph_equivariant K G X g x))

@[simp]
theorem strictActionSpectrumIso_hom_apply
    (X : Langlands.Analytic.NormContinuousAffinoidAction K G)
    (x : BanachSpectrum X.obj.V) (a : ofStrict K X.obj.V) :
    BanachSpectrum.toMulRingSeminorm
      ((strictActionSpectrumIso K G X).hom.hom.hom x) a =
        x (strictEquiv K X.obj.V a) :=
  rfl

@[simp]
theorem strictActionSpectrumIso_inv_apply
    (X : Langlands.Analytic.NormContinuousAffinoidAction K G)
    (x : BanachSpectrum (ofStrict K X.obj.V)) (a : X.obj.V) :
    BanachSpectrum.toMulRingSeminorm
      ((strictActionSpectrumIso K G X).inv.hom.hom x) a =
        x ((strictEquiv K X.obj.V).symm a) :=
  rfl

/-- The induced radius-one comparison in the geometric direction. -/
def ofStrictActionSpaceFunctor :
    Langlands.Analytic.NormContinuousAffinoidSpace K G ⥤ NormContinuousSpace K G :=
  (ofStrictActionFunctor K G).op

/-- The strict and positive-polyradius continuous spectrum functors agree by
the actual equivariant radius-one homeomorphisms, naturally in every arrow. -/
def strictActionSpectrumComparison :
    Langlands.Analytic.NormContinuousAffinoidAction.spectrumFunctor (K := K) (G := G) ≅
      ofStrictActionSpaceFunctor K G ⋙
        NormContinuousAction.spectrumFunctor (K := K) (G := G) :=
  NatIso.ofComponents (fun X => strictActionSpectrumIso K G X.unop)
    (fun {X Y} f => by
      apply ObjectProperty.hom_ext _
      apply Action.Hom.ext
      apply TopCat.ext
      intro x
      exact strictSpectrumHomeomorph_naturality K
        (Langlands.Analytic.NormContinuousAffinoidAction.homMap f.unop) x)

end Spectrum

end Langlands.Analytic.PresentedAffinoidAlgebra
