import Langlands.Geometry.Analytic.GeneralizedAffinoid.StrictActionComparison
import Langlands.Geometry.Analytic.GeneralizedAffinoid.EquivariantFiniteEtaleUnder
import Langlands.Geometry.Analytic.EquivariantFiniteEtaleUnder

/-! # Radius-one comparison of relative finite étale actions -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open CategoryTheory

variable (K : Type u) [NormedField K] [IsUltrametricDist K]

/-- The explicit radius-one conjugation preserves algebraic finite étaleness. -/
theorem algebraicallyFiniteEtale_ofStrictMap
    {P Q : PresentedStrictAffinoidAlgebra K} {f : BoundedAlgHom K P Q}
    (hf : f.AlgebraicallyFiniteEtale) :
    (ofStrictMap K f).AlgebraicallyFiniteEtale :=
  (BoundedAlgHom.AlgebraicallyFiniteEtale.of_bijective
    (strictEquiv K Q).symm.toBoundedAlgHom (strictEquiv K Q).symm.bijective).comp
      (hf.comp (BoundedAlgHom.AlgebraicallyFiniteEtale.of_bijective
        (strictEquiv K P).toBoundedAlgHom (strictEquiv K P).bijective))

/-- The radius-one map comparison also reflects algebraic finite étaleness. -/
theorem algebraicallyFiniteEtale_ofStrictMap_iff
    {P Q : PresentedStrictAffinoidAlgebra K} (f : BoundedAlgHom K P Q) :
    (ofStrictMap K f).AlgebraicallyFiniteEtale ↔ f.AlgebraicallyFiniteEtale := by
  constructor
  · intro hf
    have h := (BoundedAlgHom.AlgebraicallyFiniteEtale.of_bijective
      (strictEquiv K Q).toBoundedAlgHom (strictEquiv K Q).bijective).comp
        (hf.comp (BoundedAlgHom.AlgebraicallyFiniteEtale.of_bijective
          (strictEquiv K P).symm.toBoundedAlgHom (strictEquiv K P).symm.bijective))
    change (fromStrictMap K (ofStrictMap K f)).AlgebraicallyFiniteEtale at h
    simpa only [fromStrictMap_ofStrictMap] using h
  · exact algebraicallyFiniteEtale_ofStrictMap K

variable (G : Type v) [Group G] [TopologicalSpace G]

namespace AlgebraicallyFiniteEtaleActionUnder

/-- Embed strict relative finite étale actions using the actual radius-one
quotient comparison on their structural maps and every relative arrow. -/
def ofStrictFunctor (X : Langlands.Analytic.NormContinuousAffinoidAction K G) :
    Langlands.Analytic.AlgebraicallyFiniteEtaleAffinoidActionUnder X ⥤
      AlgebraicallyFiniteEtaleActionUnder ((ofStrictActionFunctor K G).obj X) :=
  (algebraicallyFiniteEtaleActionUnderProperty
    ((ofStrictActionFunctor K G).obj X)).lift
      (Langlands.Analytic.AlgebraicallyFiniteEtaleAffinoidActionUnder.inclusion X ⋙
        Under.post (ofStrictActionFunctor K G))
      (fun Y => algebraicallyFiniteEtale_ofStrictMap K Y.property)

@[simp]
theorem ofStrictFunctor_obj_baseMap
    {X : Langlands.Analytic.NormContinuousAffinoidAction K G}
    (Y : Langlands.Analytic.AlgebraicallyFiniteEtaleAffinoidActionUnder X) :
    ((ofStrictFunctor K G X).obj Y).baseMap =
      ofStrictMap K
        (Langlands.Analytic.AlgebraicallyFiniteEtaleAffinoidActionUnder.baseMap Y) :=
  rfl

@[simp]
theorem ofStrictFunctor_map_homMap
    {X : Langlands.Analytic.NormContinuousAffinoidAction K G}
    {Y Z : Langlands.Analytic.AlgebraicallyFiniteEtaleAffinoidActionUnder X}
    (h : Y ⟶ Z) :
    homMap ((ofStrictFunctor K G X).map h) =
      ofStrictMap K
        (Langlands.Analytic.AlgebraicallyFiniteEtaleAffinoidActionUnder.homMap h) :=
  rfl

/-- The inverse on relative arrows reflects the triangle through the fully
faithful action comparison; no additional bound or equivariance is assumed. -/
def fromStrictRelativeMap
    {X : Langlands.Analytic.NormContinuousAffinoidAction K G}
    {Y Z : Langlands.Analytic.AlgebraicallyFiniteEtaleAffinoidActionUnder X}
    (h : (ofStrictFunctor K G X).obj Y ⟶ (ofStrictFunctor K G X).obj Z) :
    Y ⟶ Z :=
  ObjectProperty.homMk (((strictActionFullyFaithful K G).under X).preimage h.hom)

@[simp]
theorem homMap_fromStrictRelativeMap
    {X : Langlands.Analytic.NormContinuousAffinoidAction K G}
    {Y Z : Langlands.Analytic.AlgebraicallyFiniteEtaleAffinoidActionUnder X}
    (h : (ofStrictFunctor K G X).obj Y ⟶ (ofStrictFunctor K G X).obj Z) :
    Langlands.Analytic.AlgebraicallyFiniteEtaleAffinoidActionUnder.homMap
        (fromStrictRelativeMap K G h) =
      fromStrictMap K (homMap h) :=
  rfl

/-- Every generalized relative arrow between image objects has exactly one
strict bounded equivariant preimage over the original base. -/
def strictRelativeFullyFaithful
    (X : Langlands.Analytic.NormContinuousAffinoidAction K G) :
    (ofStrictFunctor K G X).FullyFaithful where
  preimage := fromStrictRelativeMap K G
  map_preimage h := by
    apply hom_ext
    exact ofStrictMap_fromStrictMap K (homMap h)
  preimage_map h := by
    apply Langlands.Analytic.AlgebraicallyFiniteEtaleAffinoidActionUnder.hom_ext
    exact fromStrictMap_ofStrictMap K
      (Langlands.Analytic.AlgebraicallyFiniteEtaleAffinoidActionUnder.homMap h)

instance (X : Langlands.Analytic.NormContinuousAffinoidAction K G) :
    (ofStrictFunctor K G X).Full :=
  (strictRelativeFullyFaithful K G X).full

instance (X : Langlands.Analytic.NormContinuousAffinoidAction K G) :
    (ofStrictFunctor K G X).Faithful :=
  (strictRelativeFullyFaithful K G X).faithful

/-- Forgetting the structural map commutes exactly with radius-one transport. -/
theorem ofStrictFunctor_forget
    (X : Langlands.Analytic.NormContinuousAffinoidAction K G) :
    ofStrictFunctor K G X ⋙ forget ((ofStrictActionFunctor K G).obj X) =
      Langlands.Analytic.AlgebraicallyFiniteEtaleAffinoidActionUnder.forget X ⋙
        ofStrictActionFunctor K G :=
  rfl

section Spectrum

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

variable [IsTopologicalGroup G]

/-- The actual equivariant radius-one spectrum comparisons commute over the
identified base spectrum, naturally in every relative bounded map. -/
def strictRelativeSpectrumComparison
    (X : Langlands.Analytic.NormContinuousAffinoidAction K G) :
    Langlands.Analytic.AlgebraicallyFiniteEtaleAffinoidActionUnder.spectrumOverFunctor X ⋙
        Over.map (strictActionSpectrumIso K G X).hom ≅
      (ofStrictFunctor K G X).op ⋙
        spectrumOverFunctor ((ofStrictActionFunctor K G).obj X) :=
  NatIso.ofComponents
    (fun Y => Over.isoMk (strictActionSpectrumIso K G Y.unop.obj.right) (by
      apply ObjectProperty.hom_ext
      apply Action.Hom.ext
      apply TopCat.ext
      intro x
      exact (strictSpectrumHomeomorph_naturality K
        (Langlands.Analytic.AlgebraicallyFiniteEtaleAffinoidActionUnder.baseMap
          Y.unop) x).symm))
    (by
      intro Y Z h
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      apply Action.Hom.ext
      apply TopCat.ext
      intro x
      exact strictSpectrumHomeomorph_naturality K
        (Langlands.Analytic.AlgebraicallyFiniteEtaleAffinoidActionUnder.homMap
          h.unop) x)

@[simp]
theorem strictRelativeSpectrumComparison_hom_apply
    {X : Langlands.Analytic.NormContinuousAffinoidAction K G}
    (Y : Langlands.Analytic.AlgebraicallyFiniteEtaleAffinoidActionUnder X)
    (x : BanachSpectrum Y.obj.right.obj.V) (a : ofStrict K Y.obj.right.obj.V) :
    BanachSpectrum.toMulRingSeminorm
        (((strictRelativeSpectrumComparison K G X).hom.app
          (Opposite.op Y)).left.hom.hom x) a =
      x (strictEquiv K Y.obj.right.obj.V a) :=
  rfl

@[simp]
theorem strictRelativeSpectrumComparison_inv_apply
    {X : Langlands.Analytic.NormContinuousAffinoidAction K G}
    (Y : Langlands.Analytic.AlgebraicallyFiniteEtaleAffinoidActionUnder X)
    (x : BanachSpectrum (ofStrict K Y.obj.right.obj.V)) (a : Y.obj.right.obj.V) :
    BanachSpectrum.toMulRingSeminorm
        (((strictRelativeSpectrumComparison K G X).inv.app
          (Opposite.op Y)).left.hom.hom x) a =
      x ((strictEquiv K Y.obj.right.obj.V).symm a) :=
  rfl

end Spectrum

end AlgebraicallyFiniteEtaleActionUnder

end Langlands.Analytic.PresentedAffinoidAlgebra
