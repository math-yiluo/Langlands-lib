import Langlands.AbelianScheme.PolarizedFiniteLevel.ZariskiGluingCover
import Langlands.AbelianScheme.PolarizedFiniteLevel.ZariskiGluingTransition

/-! # Gluing the underlying schemes of rigid data along the cover by small opens -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.PolarizedFiniteLevel.ZariskiGluing

variable {P : Prerequisites.{u}} {g d n : ℕ} {S : Scheme.{u}} {ι : Type*} {U : ι → S.Opens}
  (hU : iSup U = ⊤) (c : ∀ W : SubOpens U, Datum P W.1.toScheme g d n)
  (hrig : ∀ (W : SubOpens U) (α : PolarizedIso (c W) (c W)), α = PolarizedIso.refl (c W))
  (θ : ∀ (W W' : SubOpens U) (h : W.1 ≤ W'.1),
    PolarizedIso (c W) ((c W').pullback (S.homOfLE h)))

/-- The diagram of underlying schemes of the data `c W`, with the transition maps of the
polarized isomorphisms `θ`. Functoriality follows from rigidity. -/
def gluingFunctor : (subCover hU).I₀ ⥤ Scheme.{u} where
  obj W := (c W).abelian.X.left
  map {W W'} h := (θ W W' (leOfHom h)).overMap
  map_id W := PolarizedIso.overMap_eq_id (hrig W) (S.homOfLE_rfl W.1) _
  map_comp {W W' W''} f h := ((θ W W' (leOfHom f)).overMap_comp (hrig W)
    (S.homOfLE_homOfLE (leOfHom f) (leOfHom h)) (θ W' W'' (leOfHom h))
    (θ W W'' (leOfHom (f ≫ h)))).symm

/-- The structure maps of the data, as a natural transformation to the diagram of opens. -/
def gluingNatTrans :
    gluingFunctor hU c hrig θ ⟶ (subCover hU).functorOfLocallyDirected where
  app W := (c W).abelian.X.hom
  naturality {W W'} h := by
    change (θ W W' (leOfHom h)).overMap ≫ (c W').abelian.X.hom =
      (c W).abelian.X.hom ≫ (subCover hU).trans h
    rw [subCover_trans]
    exact (θ W W' (leOfHom h)).overMap_w

/-- The relative gluing datum over the cover by opens contained in some member of `U`. -/
def gluingData : (subCover hU).RelativeGluingData where
  functor := gluingFunctor hU c hrig θ
  natTrans := gluingNatTrans hU c hrig θ
  equifibered {W W'} h := by
    change IsPullback (θ W W' (leOfHom h)).overMap (c W).abelian.X.hom
      (c W').abelian.X.hom ((subCover hU).trans h)
    rw [subCover_trans]
    exact (θ W W' (leOfHom h)).isPullback_overMap

/-- Each piece is the preimage of its open in the glued scheme. -/
theorem gluingData_isPullback (W : SubOpens U) :
    IsPullback (c W).abelian.X.hom (colimit.ι (gluingData hU c hrig θ).functor W) W.1.ι
      (gluingData hU c hrig θ).toBase :=
  (gluingData hU c hrig θ).isPullback_natTrans_ι_toBase W

end Langlands.AbelianScheme.PolarizedFiniteLevel.ZariskiGluing
