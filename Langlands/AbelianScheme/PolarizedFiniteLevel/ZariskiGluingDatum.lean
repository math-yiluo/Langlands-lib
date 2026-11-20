import Langlands.AbelianScheme.PolarizedFiniteLevel.ZariskiGluingPolarization
import Langlands.AbelianScheme.PolarizedFiniteLevel.ZariskiGluingLevel

/-! # Gluing rigid ordinary polarized full-level data along an open cover -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.PolarizedFiniteLevel.ZariskiGluing

open GroupScheme.Tate

variable {P : Prerequisites.{u}} {g d n : ℕ} {S : Scheme.{u}} {J : Type*} {U : J → S.Opens}
  (hU : iSup U = ⊤) (c : ∀ W : SubOpens U, Datum P W.1.toScheme g d n)
  (hrig : ∀ (W : SubOpens U) (α : PolarizedIso (c W) (c W)), α = PolarizedIso.refl (c W))
  (θ : ∀ (W W' : SubOpens U) (h : W.1 ≤ W'.1),
    PolarizedIso (c W) ((c W').pullback (S.homOfLE h)))
  [QuasiSeparatedSpace S]

/-- The transported local level sections agree on overlaps. -/
theorem localLevel_compat (W W' : SubOpens U) (h : W.1 ≤ W'.1) (i : Fin (2 * g)) :
    (Additive.toMul ((localTransport hU c hrig θ W).level.sections i)).val.left ≫
        pullback.fst (gluedAbelian hU c hrig θ).X.hom W.1.ι =
      S.homOfLE h ≫ (Additive.toMul ((localTransport hU c hrig θ W').level.sections i)).val.left ≫
        pullback.fst (gluedAbelian hU c hrig θ).X.hom W'.1.ι := by
  have hl := congrArg (fun x => (Additive.toMul x).val.left)
    ((overlapIso hU c hrig θ W W' h).level_eq i)
  change (Additive.toMul ((localTransport hU c hrig θ W).level.sections i)).val.left ≫
      hom (overlapIso hU c hrig θ W W' h).abelianIso.hom =
    (Additive.toMul (pullbackTuple (S.homOfLE h)
      (localTransport hU c hrig θ W').level.sections i)).val.left at hl
  rw [← hom_overlapIso_fst_fst hU c hrig θ W W' h, ← Category.assoc, ← Category.assoc, hl]
  have hp := pullbackTuple_fst (S.homOfLE h) (localTransport hU c hrig θ W').level.sections i
  erw [hp]
  rw [Category.assoc]

/-- The glued level sections. -/
def gluedSections : SectionTuple (gluedAbelian hU c hrig θ) g n :=
  gluedTuple hU (fun W => (localTransport hU c hrig θ W).level.sections)
    (localLevel_compat hU c hrig θ)

theorem pullbackTuple_gluedSections (W : SubOpens U) :
    pullbackTuple W.1.ι (gluedSections hU c hrig θ) =
      (localTransport hU c hrig θ W).level.sections :=
  pullbackTuple_gluedTuple hU _ _ W

/-- The glued datum, given the four local-to-global properties of its fields. -/
def gluedDatum (hdim : (gluedAbelian hU c hrig θ).HasRelativeDimension g)
    (hpol : (gluedDualWitness hU c hrig θ).IsPolarization P (gluedPolarization hU c hrig θ))
    (hdeg : HasDegreeSquare (gluedPolarization hU c hrig θ) d)
    (hfull : IsFull (gluedSections hU c hrig θ)) : Datum P S g d n where
  abelian := gluedAbelian hU c hrig θ
  dimension := hdim
  dualWitness := gluedDualWitness hU c hrig θ
  polarization := gluedPolarization hU c hrig θ
  polarized := hpol
  degree := hdeg
  level := ⟨gluedSections hU c hrig θ, hfull⟩

/-- The restriction of the glued datum to a small open is the transported local datum. -/
def gluedDatumRestrictIso (hdim : (gluedAbelian hU c hrig θ).HasRelativeDimension g)
    (hpol : (gluedDualWitness hU c hrig θ).IsPolarization P (gluedPolarization hU c hrig θ))
    (hdeg : HasDegreeSquare (gluedPolarization hU c hrig θ) d)
    (hfull : IsFull (gluedSections hU c hrig θ)) (W : SubOpens U) :
    PolarizedIso ((gluedDatum hU c hrig θ hdim hpol hdeg hfull).pullback W.1.ι)
      (localTransport hU c hrig θ W) where
  abelianIso := Iso.refl _
  polarization_eq := by
    change (gluedDualWitness hU c hrig θ).pullbackMap P W.1.ι
        ((gluedDualWitness hU c hrig θ).pullback P W.1.ι) (gluedPolarization hU c hrig θ) =
      𝟙 _ ≫ (localTransport hU c hrig θ W).polarization ≫
        ((gluedDualWitness hU c hrig θ).pullback P W.1.ι).map P
          ((gluedDualWitness hU c hrig θ).pullback P W.1.ι) (𝟙 _)
    simp only [DualWitness.map_id, Category.id_comp]
    exact pullbackMap_gluedPolarization hU c hrig θ W
  level_eq i := by
    have hx := congrFun (pullbackTuple_gluedSections hU c hrig θ W) i
    apply toSection_injective _ (Over.mk (𝟙 W.1.toScheme)) n
    change (Additive.toMul (pullbackTuple W.1.ι (gluedSections hU c hrig θ) i)).val ≫
        𝟙 ((baseChange W.1.ι).obj (gluedAbelian hU c hrig θ)).X =
      (Additive.toMul ((localTransport hU c hrig θ W).level.sections i)).val
    rw [Category.comp_id, hx]
    rfl

/-- The restriction of the glued datum to a small open is isomorphic to the given datum. -/
theorem isomorphic_gluedDatum_restrict
    (hdim : (gluedAbelian hU c hrig θ).HasRelativeDimension g)
    (hpol : (gluedDualWitness hU c hrig θ).IsPolarization P (gluedPolarization hU c hrig θ))
    (hdeg : HasDegreeSquare (gluedPolarization hU c hrig θ) d)
    (hfull : IsFull (gluedSections hU c hrig θ)) (W : SubOpens U) :
    Isomorphic ((gluedDatum hU c hrig θ hdim hpol hdeg hfull).pullback W.1.ι) (c W) :=
  ⟨(gluedDatumRestrictIso hU c hrig θ hdim hpol hdeg hfull W).trans
    ((c W).transportIso (restrictIso hU c hrig θ W)
      ((gluedDualWitness hU c hrig θ).pullback P W.1.ι))⟩

section Input

variable {a : ∀ i, Datum P (U i).toScheme g d n}

omit [QuasiSeparatedSpace S] in
/-- A datum restricting to the local data on all small opens restricts to the given data
on every member of the cover. -/
theorem isomorphic_restrict_of_subOpens
    (h : ∀ i j, Isomorphic ((a i).pullback (S.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)))
      ((a j).pullback (S.homOfLE (inf_le_right : U i ⊓ U j ≤ U j))))
    (b : Datum P S g d n) (hb : ∀ W : SubOpens U, Isomorphic (b.pullback W.1.ι) (localDatum a W))
    (i : J) : Isomorphic (b.pullback (U i).ι) (a i) := by
  let W : SubOpens U := ⟨U i, i, le_rfl⟩
  have e1 : Isomorphic (b.pullback (U i).ι) (localDatum a W) := hb W
  have e2 : Isomorphic (localDatum a W) ((a i).pullback (S.homOfLE (le_refl (U i)))) :=
    isomorphic_restrict h (U i) (le_index W) (le_refl (U i))
  have e3 : Isomorphic ((a i).pullback (S.homOfLE (le_refl (U i)))) (a i) :=
    (Isomorphic.pullback_congr (a i) (S.homOfLE_rfl (U i))).trans' ⟨(a i).pullbackIdIso⟩
  exact e1.trans' (e2.trans' e3)

end Input

end Langlands.AbelianScheme.PolarizedFiniteLevel.ZariskiGluing
