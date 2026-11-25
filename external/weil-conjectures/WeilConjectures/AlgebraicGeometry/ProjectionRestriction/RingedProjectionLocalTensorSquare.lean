/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionRestrictionDataSupplement
import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionLocalOrdinaryTensorSquare
import WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses

/-! # Tensor coherence of the normalized localized pullback square

## References

* Stacks Project, Modules on Sites, Tag 04J0 and Cohomology on Sites, Tag 07A4
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.ProjectionRestriction

attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  HasDerivedCategory.standard DerivedCategory SheafOfModules.monoidalCategory

section Representatives

variable {C₀ C₁ C₂ : Type (u + 1)}
  [Category.{u} C₀] [Category.{u} C₁] [Category.{u} C₂]
  [EssentiallySmall.{u + 1} C₀] [EssentiallySmall.{u + 1} C₁]
  [EssentiallySmall.{u + 1} C₂]
  {J₀ : GrothendieckTopology C₀} {J₁ : GrothendieckTopology C₁}
  {J₂ : GrothendieckTopology C₂}
  {R₀ : Sheaf J₀ CommRingCat.{u + 1}} {R₁ : Sheaf J₁ CommRingCat.{u + 1}}
  {R₂ : Sheaf J₂ CommRingCat.{u + 1}}

@[irreducible] private def chain {L : Mod R₀ ⥤ Mod R₁} [L.Additive] {d : ExactModel L}
    {a : TensorModel R₀} {b : TensorModel R₁}
    {mu : ∀ M N, L.obj (((tensor R₀).obj M).obj N) ≅
      ((tensor R₁).obj (L.obj M)).obj (L.obj N)}
    (t : TensorComparison L d a b mu) (P Q : CochainComplex (Mod R₀) ℤ) :=
  totalMap a b L mu t.comm P Q

private theorem chain_summand
    {L : Mod R₀ ⥤ Mod R₁} [L.Additive] {d : ExactModel L}
    {a : TensorModel R₀} {b : TensorModel R₁}
    {mu : ∀ M N, L.obj (((tensor R₀).obj M).obj N) ≅
      ((tensor R₁).obj (L.obj M)).obj (L.obj N)}
    (t : TensorComparison L d a b mu) (P Q : CochainComplex (Mod R₀) ℤ)
    (i j n : ℤ) (hij : i + j = n) :
    HomologicalComplex.ιMapBifunctor ((L.mapHomologicalComplex (.up ℤ)).obj P)
        ((L.mapHomologicalComplex (.up ℤ)).obj Q) (tensor R₁) (.up ℤ) i j n hij ≫
      (chain t P Q).f n =
    (mu (P.X i) (Q.X j)).inv ≫
      L.map (HomologicalComplex.ιMapBifunctor P Q (tensor R₀) (.up ℤ) i j n hij) := by
  let := SheafOfModules.monoidalCategory R₀
  let := SheafOfModules.monoidalCategory R₁
  let := a.preadditive
  let := b.preadditive
  simp only [chain, totalMap, totalComponent, tensorPullbackTotalComponent,
    HomologicalComplex.ι_mapBifunctorDesc]

private theorem total_map
    {P P' Q Q' : CochainComplex (Mod R₀) ℤ} (a : P ⟶ P') (b : Q ⟶ Q') :
    (total R₀).map (Prod.mkHom a b) =
      HomologicalComplex.mapBifunctorMap a b (tensor R₀) (.up ℤ) := by
  simp only [total, Functor.uncurry_obj_map, Functor.map₂HomologicalComplex,
    HomologicalComplex.mapBifunctorMap, ← HomologicalComplex₂.total.map_comp,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.comp_id, Category.id_comp]

private theorem total_summand_map
    {P P' Q Q' : CochainComplex (Mod R₀) ℤ} (a : P ⟶ P') (b : Q ⟶ Q')
    (p q n : ℤ) (hpq : p + q = n) :
    HomologicalComplex.ιMapBifunctor P Q (tensor R₀) (.up ℤ) p q n hpq ≫
        ((total R₀).map (Prod.mkHom a b)).f n =
      (Functor.uncurry.obj (tensor R₀)).map (Prod.mkHom (a.f p) (b.f q)) ≫
        HomologicalComplex.ιMapBifunctor P' Q' (tensor R₀) (.up ℤ) p q n hpq := by
  rw [total_map, HomologicalComplex.ι_mapBifunctorMap]
  simp only [Functor.uncurry_obj_map, Category.assoc]

private theorem model_inverse
    {L : Mod R₀ ⥤ Mod R₁} [L.Additive] {d : ExactModel L}
    {a : TensorModel R₀} {b : TensorModel R₁}
    {mu : ∀ M N, L.obj (((tensor R₀).obj M).obj N) ≅
      ((tensor R₁).obj (L.obj M)).obj (L.obj N)}
    (t : TensorComparison L d a b mu)
    (P Q : CochainComplex (Mod R₀) ℤ) (hp : resolving R₀ P) (hq : resolving R₀ Q) :
    t.comparison.inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      d.functor.map (a.representative.inv.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
      d.factors.hom.app ((total R₀).obj (P, Q)) =
    b.functor.map (Prod.mkHom (d.factors.hom.app P) (d.factors.hom.app Q)) ≫
      b.representative.inv.app
        (⟨(L.mapHomologicalComplex (.up ℤ)).obj P, t.preserves P hp⟩,
          ⟨(L.mapHomologicalComplex (.up ℤ)).obj Q, t.preserves Q hq⟩) ≫
      DerivedCategory.Q.map (chain t P Q) := by
  have h := t.representative P Q hp hq
  have he := congrArg (fun z ↦
    t.comparison.inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      d.functor.map (a.representative.inv.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫ z) h
  simp only [← d.functor.map_comp_assoc, Iso.inv_hom_id_app] at he
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc] at he
  simpa only [chain] using he.symm

@[irreducible] private def twoFactors
    {F : Mod R₀ ⥤ Mod R₁} [F.Additive] {G : Mod R₁ ⥤ Mod R₂} [G.Additive]
    (d : ExactModel F) (e : ExactModel G) (P : CochainComplex (Mod R₀) ℤ) :
    e.functor.obj (d.functor.obj (DerivedCategory.Q.obj P)) ≅
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P)) :=
  e.functor.mapIso (d.factors.app P) ≪≫
    e.factors.app ((F.mapHomologicalComplex (.up ℤ)).obj P)

private theorem two_models
    {F : Mod R₀ ⥤ Mod R₁} [F.Additive] {G : Mod R₁ ⥤ Mod R₂} [G.Additive]
    {d : ExactModel F} {e : ExactModel G}
    {a : TensorModel R₀} {b : TensorModel R₁} {c : TensorModel R₂}
    {mu : ∀ M N, F.obj (((tensor R₀).obj M).obj N) ≅
      ((tensor R₁).obj (F.obj M)).obj (F.obj N)}
    {nu : ∀ M N, G.obj (((tensor R₁).obj M).obj N) ≅
      ((tensor R₂).obj (G.obj M)).obj (G.obj N)}
    (t : TensorComparison F d a b mu) (s : TensorComparison G e b c nu)
    (P Q : CochainComplex (Mod R₀) ℤ) (hp : resolving R₀ P) (hq : resolving R₀ Q) :
    s.comparison.inv.app (d.functor.obj (DerivedCategory.Q.obj P),
        d.functor.obj (DerivedCategory.Q.obj Q)) ≫
      e.functor.map (t.comparison.inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      e.functor.map (d.functor.map (a.representative.inv.app (⟨P, hp⟩, ⟨Q, hq⟩))) ≫
      (twoFactors d e ((total R₀).obj (P, Q))).hom =
    c.functor.map (Prod.mkHom (twoFactors d e P).hom (twoFactors d e Q).hom) ≫
      c.representative.inv.app
        (⟨(G.mapHomologicalComplex (.up ℤ)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj P),
          s.preserves _ (t.preserves P hp)⟩,
        ⟨(G.mapHomologicalComplex (.up ℤ)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj Q),
          s.preserves _ (t.preserves Q hq)⟩) ≫
      DerivedCategory.Q.map
        (chain s ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q) ≫
          (G.mapHomologicalComplex (.up ℤ)).map (chain t P Q)) := by
  let FP := (F.mapHomologicalComplex (.up ℤ)).obj P
  let FQ := (F.mapHomologicalComplex (.up ℤ)).obj Q
  have hF := model_inverse t P Q hp hq
  have hG := model_inverse s FP FQ (t.preserves P hp) (t.preserves Q hq)
  have hn := s.comparison.inv.naturality
    (Prod.mkHom (d.factors.hom.app P) (d.factors.hom.app Q))
  change c.functor.map (Prod.mkHom
      (e.functor.map (d.factors.hom.app P)) (e.functor.map (d.factors.hom.app Q))) ≫
      s.comparison.inv.app (DerivedCategory.Q.obj FP, DerivedCategory.Q.obj FQ) =
    s.comparison.inv.app (d.functor.obj (DerivedCategory.Q.obj P),
      d.functor.obj (DerivedCategory.Q.obj Q)) ≫
      e.functor.map (b.functor.map (Prod.mkHom
        (d.factors.hom.app P) (d.factors.hom.app Q))) at hn
  simp only [twoFactors, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  rw [← e.functor.map_comp_assoc, ← e.functor.map_comp_assoc]
  simp only [Category.assoc]
  rw [hF]
  simp only [e.functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn]
  have hg := e.factors.hom.naturality (chain t P Q)
  dsimp only [Functor.comp_map] at hg
  erw [hg]
  rw [reassoc_of% hG]
  simp only [← c.functor.map_comp_assoc, prod_comp, Functor.map_comp]
  rfl

-- On each signed-total summand the square is the inverse ordinary tensor square.
private theorem total_square
    {C₃ : Type (u + 1)} [Category.{u} C₃] [EssentiallySmall.{u + 1} C₃]
    {J₃ : GrothendieckTopology C₃} {R₃ : Sheaf J₃ CommRingCat.{u + 1}}
    {F : Mod R₀ ⥤ Mod R₁} {G : Mod R₀ ⥤ Mod R₂}
    {H : Mod R₁ ⥤ Mod R₃} {K : Mod R₂ ⥤ Mod R₃}
    [F.Additive] [G.Additive] [H.Additive] [K.Additive]
    {dF : ExactModel F} {dG : ExactModel G} {dH : ExactModel H} {dK : ExactModel K}
    {a : TensorModel R₀} {b : TensorModel R₁} {c : TensorModel R₂}
    {d : TensorModel R₃}
    {muF : ∀ M N, F.obj (((tensor R₀).obj M).obj N) ≅
      ((tensor R₁).obj (F.obj M)).obj (F.obj N)}
    {muG : ∀ M N, G.obj (((tensor R₀).obj M).obj N) ≅
      ((tensor R₂).obj (G.obj M)).obj (G.obj N)}
    {muH : ∀ M N, H.obj (((tensor R₁).obj M).obj N) ≅
      ((tensor R₃).obj (H.obj M)).obj (H.obj N)}
    {muK : ∀ M N, K.obj (((tensor R₂).obj M).obj N) ≅
      ((tensor R₃).obj (K.obj M)).obj (K.obj N)}
    (tF : TensorComparison F dF a b muF) (tG : TensorComparison G dG a c muG)
    (tH : TensorComparison H dH b d muH) (tK : TensorComparison K dK c d muK)
    (gamma : G ⋙ K ⟶ F ⋙ H)
    (ho : ∀ M N,
      gamma.app (((tensor R₀).obj M).obj N) ≫ H.map (muF M N).hom ≫
          (muH (F.obj M) (F.obj N)).hom =
        K.map (muG M N).hom ≫ (muK (G.obj M) (G.obj N)).hom ≫
          (Functor.uncurry.obj (tensor R₃)).map (Prod.mkHom (gamma.app M) (gamma.app N)))
    (P Q : CochainComplex (Mod R₀) ℤ) :
    chain tK ((G.mapHomologicalComplex (.up ℤ)).obj P)
        ((G.mapHomologicalComplex (.up ℤ)).obj Q) ≫
      (K.mapHomologicalComplex (.up ℤ)).map (chain tG P Q) ≫
      (NatTrans.mapHomologicalComplex gamma (.up ℤ)).app ((total R₀).obj (P, Q)) =
    (total R₃).map (Prod.mkHom
        ((NatTrans.mapHomologicalComplex gamma (.up ℤ)).app P)
        ((NatTrans.mapHomologicalComplex gamma (.up ℤ)).app Q)) ≫
      chain tH ((F.mapHomologicalComplex (.up ℤ)).obj P)
        ((F.mapHomologicalComplex (.up ℤ)).obj Q) ≫
      (H.mapHomologicalComplex (.up ℤ)).map (chain tF P Q) := by
  let := SheafOfModules.monoidalCategory R₃
  let := d.preadditive
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  let GP := (G.mapHomologicalComplex (.up ℤ)).obj P
  let GQ := (G.mapHomologicalComplex (.up ℤ)).obj Q
  let FP := (F.mapHomologicalComplex (.up ℤ)).obj P
  let FQ := (F.mapHomologicalComplex (.up ℤ)).obj Q
  let i0 := HomologicalComplex.ιMapBifunctor P Q (tensor R₀) (.up ℤ) p q n hpq
  let iG := HomologicalComplex.ιMapBifunctor GP GQ (tensor R₂) (.up ℤ) p q n hpq
  let iF := HomologicalComplex.ιMapBifunctor FP FQ (tensor R₁) (.up ℤ) p q n hpq
  let iK := HomologicalComplex.ιMapBifunctor
    ((K.mapHomologicalComplex (.up ℤ)).obj GP)
    ((K.mapHomologicalComplex (.up ℤ)).obj GQ) (tensor R₃) (.up ℤ) p q n hpq
  let iH := HomologicalComplex.ιMapBifunctor
    ((H.mapHomologicalComplex (.up ℤ)).obj FP)
    ((H.mapHomologicalComplex (.up ℤ)).obj FQ) (tensor R₃) (.up ℤ) p q n hpq
  let chK := (chain tK GP GQ).f n
  let chG := (chain tG P Q).f n
  let chH := (chain tH FP FQ).f n
  let chF := (chain tF P Q).f n
  let muK' := muK (G.obj (P.X p)) (G.obj (Q.X q))
  let muG' := muG (P.X p) (Q.X q)
  let muH' := muH (F.obj (P.X p)) (F.obj (Q.X q))
  let muF' := muF (P.X p) (Q.X q)
  let dt := gamma.app (((total R₀).obj (P, Q)).X n)
  let dm := gamma.app (((tensor R₀).obj (P.X p)).obj (Q.X q))
  let beta := (Functor.uncurry.obj (tensor R₃)).map
    (Prod.mkHom (gamma.app (P.X p)) (gamma.app (Q.X q)))
  let dc := NatTrans.mapHomologicalComplex gamma (.up ℤ)
  let tm := ((total R₃).map (Prod.mkHom (dc.app P) (dc.app Q))).f n
  have hK : iK ≫ chK = muK'.inv ≫ K.map iG :=
    chain_summand tK GP GQ p q n hpq
  have hG : K.map iG ≫ K.map chG = K.map muG'.inv ≫ K.map (G.map i0) := by
    have h := congrArg K.map (chain_summand tG P Q p q n hpq)
    simpa only [K.map_comp] using h
  have hH : iH ≫ chH = muH'.inv ≫ H.map iF :=
    chain_summand tH FP FQ p q n hpq
  have hF : H.map iF ≫ H.map chF = H.map muF'.inv ≫ H.map (F.map i0) := by
    have h := congrArg H.map (chain_summand tF P Q p q n hpq)
    simpa only [H.map_comp] using h
  have hn : K.map (G.map i0) ≫ dt = dm ≫ H.map (F.map i0) :=
    gamma.naturality i0
  have hm : iK ≫ tm = beta ≫ iH := total_summand_map (dc.app P) (dc.app Q) p q n hpq
  have hl : iK ≫ chK ≫ K.map chG ≫ dt =
      muK'.inv ≫ K.map muG'.inv ≫ dm ≫ H.map (F.map i0) := by
    have h1 := congrArg (fun z ↦ z ≫ K.map chG ≫ dt) hK
    have h2 := congrArg (fun z ↦ muK'.inv ≫ z ≫ dt) hG
    have h3 := congrArg (fun z ↦ muK'.inv ≫ K.map muG'.inv ≫ z) hn
    simp only [Category.assoc] at h1 h2 h3
    exact h1.trans (h2.trans h3)
  have hr : iK ≫ tm ≫ chH ≫ H.map chF =
      beta ≫ muH'.inv ≫ H.map muF'.inv ≫ H.map (F.map i0) := by
    have h1 := congrArg (fun z ↦ z ≫ chH ≫ H.map chF) hm
    have h2 := congrArg (fun z ↦ beta ≫ z ≫ H.map chF) hH
    have h3 := congrArg (fun z ↦ beta ≫ muH'.inv ≫ z) hF
    simp only [Category.assoc] at h1 h2 h3
    exact h1.trans (h2.trans h3)
  let x := K.mapIso muG' ≪≫ muK'
  let y := H.mapIso muF' ≪≫ muH'
  have hi : x.inv ≫ dm = beta ≫ y.inv := by
    apply (Iso.inv_comp_eq x).2
    rw [← Category.assoc]
    apply (Iso.eq_comp_inv y).2
    exact ho _ _
  have h := congrArg (fun z ↦ z ≫ H.map (F.map i0)) hi
  simp only [x, y, Iso.trans_inv, Functor.mapIso_inv, Category.assoc] at h
  exact hl.trans (h.trans hr.symm)

-- Keep the four-model calculation abstract, so its category algebra does not
-- unfold the concrete pro-étale pullbacks and restriction functors.
private theorem four_models_inverse
    {C₃ : Type (u + 1)} [Category.{u} C₃] [EssentiallySmall.{u + 1} C₃]
    {J₃ : GrothendieckTopology C₃} {R₃ : Sheaf J₃ CommRingCat.{u + 1}}
    {F : Mod R₀ ⥤ Mod R₁} {G : Mod R₀ ⥤ Mod R₂}
    {H : Mod R₁ ⥤ Mod R₃} {K : Mod R₂ ⥤ Mod R₃}
    [F.Additive] [G.Additive] [H.Additive] [K.Additive]
    {dF : ExactModel F} {dG : ExactModel G} {dH : ExactModel H} {dK : ExactModel K}
    {a : TensorModel R₀} {b : TensorModel R₁} {c : TensorModel R₂}
    {d : TensorModel R₃}
    {muF : ∀ M N, F.obj (((tensor R₀).obj M).obj N) ≅
      ((tensor R₁).obj (F.obj M)).obj (F.obj N)}
    {muG : ∀ M N, G.obj (((tensor R₀).obj M).obj N) ≅
      ((tensor R₂).obj (G.obj M)).obj (G.obj N)}
    {muH : ∀ M N, H.obj (((tensor R₁).obj M).obj N) ≅
      ((tensor R₃).obj (H.obj M)).obj (H.obj N)}
    {muK : ∀ M N, K.obj (((tensor R₂).obj M).obj N) ≅
      ((tensor R₃).obj (K.obj M)).obj (K.obj N)}
    (tF : TensorComparison F dF a b muF) (tG : TensorComparison G dG a c muG)
    (tH : TensorComparison H dH b d muH) (tK : TensorComparison K dK c d muK)
    (gamma : G ⋙ K ⟶ F ⋙ H)
    (ho : ∀ M N,
      gamma.app (((tensor R₀).obj M).obj N) ≫ H.map (muF M N).hom ≫
          (muH (F.obj M) (F.obj N)).hom =
        K.map (muG M N).hom ≫ (muK (G.obj M) (G.obj N)).hom ≫
          (Functor.uncurry.obj (tensor R₃)).map (Prod.mkHom (gamma.app M) (gamma.app N)))
    (theta : dG.functor ⋙ dK.functor ⟶ dF.functor ⋙ dH.functor)
    (hnorm : ∀ P : CochainComplex (Mod R₀) ℤ,
      theta.app (DerivedCategory.Q.obj P) ≫ (twoFactors dF dH P).hom =
        (twoFactors dG dK P).hom ≫ DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex gamma (.up ℤ)).app P))
    (P Q : CochainComplex (Mod R₀) ℤ) (hp : resolving R₀ P) (hq : resolving R₀ Q) :
    d.functor.map (Prod.mkHom (theta.app (DerivedCategory.Q.obj P))
        (theta.app (DerivedCategory.Q.obj Q))) ≫
      tH.comparison.inv.app (dF.functor.obj (DerivedCategory.Q.obj P),
        dF.functor.obj (DerivedCategory.Q.obj Q)) ≫
      dH.functor.map (tF.comparison.inv.app (DerivedCategory.Q.obj P,
        DerivedCategory.Q.obj Q)) =
    tK.comparison.inv.app (dG.functor.obj (DerivedCategory.Q.obj P),
        dG.functor.obj (DerivedCategory.Q.obj Q)) ≫
      dK.functor.map (tG.comparison.inv.app (DerivedCategory.Q.obj P,
        DerivedCategory.Q.obj Q)) ≫
      theta.app (a.functor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) := by
  let D := d.functor
  let gammaC := NatTrans.mapHomologicalComplex gamma (.up ℤ)
  let FP := (F.mapHomologicalComplex (.up ℤ)).obj P
  let FQ := (F.mapHomologicalComplex (.up ℤ)).obj Q
  let GP := (G.mapHomologicalComplex (.up ℤ)).obj P
  let GQ := (G.mapHomologicalComplex (.up ℤ)).obj Q
  let HFP := (H.mapHomologicalComplex (.up ℤ)).obj FP
  let HFQ := (H.mapHomologicalComplex (.up ℤ)).obj FQ
  let KGP := (K.mapHomologicalComplex (.up ℤ)).obj GP
  let KGQ := (K.mapHomologicalComplex (.up ℤ)).obj GQ
  let Tot := (total R₀).obj (P, Q)
  let bGK := twoFactors dG dK
  let bFH := twoFactors dF dH
  let r0 := a.representative.app (⟨P, hp⟩, ⟨Q, hq⟩)
  let rGK := d.representative.app
    (⟨KGP, tK.preserves _ (tG.preserves P hp)⟩,
      ⟨KGQ, tK.preserves _ (tG.preserves Q hq)⟩)
  let rFH := d.representative.app
    (⟨HFP, tH.preserves _ (tF.preserves P hp)⟩,
      ⟨HFQ, tH.preserves _ (tF.preserves Q hq)⟩)
  let cGK := chain tK GP GQ ≫
    (K.mapHomologicalComplex (.up ℤ)).map (chain tG P Q)
  let cFH := chain tH FP FQ ≫
    (H.mapHomologicalComplex (.up ℤ)).map (chain tF P Q)
  have hGK := two_models tG tK P Q hp hq
  have hFH := two_models tF tH P Q hp hq
  change _ = D.map (Prod.mkHom (bGK P).hom (bGK Q).hom) ≫
    rGK.inv ≫ DerivedCategory.Q.map cGK at hGK
  change _ = D.map (Prod.mkHom (bFH P).hom (bFH Q).hom) ≫
    rFH.inv ≫ DerivedCategory.Q.map cFH at hFH
  have hp' := hnorm P
  have hq' := hnorm Q
  have ht := hnorm Tot
  have hn := d.representative.hom.naturality
    (Prod.mkHom
      (ObjectProperty.homMk
        (X := ⟨KGP, tK.preserves _ (tG.preserves P hp)⟩)
        (Y := ⟨HFP, tH.preserves _ (tF.preserves P hp)⟩)
        (gammaC.app P))
      (ObjectProperty.homMk
        (X := ⟨KGQ, tK.preserves _ (tG.preserves Q hq)⟩)
        (Y := ⟨HFQ, tH.preserves _ (tF.preserves Q hq)⟩)
        (gammaC.app Q)))
  change DerivedCategory.Q.map
      ((total R₃).map
        (Prod.mkHom (gammaC.app P) (gammaC.app Q))) ≫ rFH.hom =
    rGK.hom ≫ D.map (Prod.mkHom (DerivedCategory.Q.map (gammaC.app P))
      (DerivedCategory.Q.map (gammaC.app Q))) at hn
  have hinv := congrArg (fun z ↦ rGK.inv ≫ z ≫ rFH.inv) hn
  simp only [Category.assoc, Iso.hom_inv_id, Iso.inv_hom_id_assoc,
    Category.comp_id] at hinv
  have hc := total_square tF tG tH tK gamma ho P Q
  change cGK ≫ gammaC.app Tot =
    (total R₃).map
      (Prod.mkHom (gammaC.app P) (gammaC.app Q)) ≫ cFH at hc
  let z := dH.functor.mapIso (dF.functor.mapIso r0.symm) ≪≫ bFH Tot
  apply (cancel_mono z.hom).1
  simp only [z, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  have htheta := theta.naturality r0.inv
  change dK.functor.map (dG.functor.map r0.inv) ≫
      theta.app (DerivedCategory.Q.obj Tot) =
    theta.app (a.functor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      dH.functor.map (dF.functor.map r0.inv) at htheta
  erw [← reassoc_of% htheta]
  erw [ht]
  erw [reassoc_of% hGK]
  erw [hFH]
  rw [← D.map_comp_assoc]
  simp only [prod_comp]
  erw [hp', hq']
  erw [← prod_comp (Prod.mkHom (bGK P).hom (bGK Q).hom)
    (Prod.mkHom (DerivedCategory.Q.map (gammaC.app P))
      (DerivedCategory.Q.map (gammaC.app Q))), D.map_comp]
  simp only [Category.assoc]
  erw [← reassoc_of% hinv]
  simp only [← DerivedCategory.Q.map_comp, ← Category.assoc]
  erw [← hc]

end Representatives

-- Specialize the abstract calculation using the canonical cochain normalization.
private theorem inverse_on_representatives
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {R_Y : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {R_X : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R_Y ≅ R_X}
    {g : Global f R_Y R_X c} {V : Y.ProEt}
    (l : Local f R_Y R_X c g V)
    (P Q : CochainComplex (Mod R_Y) ℤ) (hp : resolving R_Y P) (hq : resolving R_Y Q) :
    letI := l.restrictionYAdditive
    letI := l.restrictionXAdditive
    l.tensorX.functor.map (Prod.mkHom
        (l.pullback.inv.app (DerivedCategory.Q.obj P))
        (l.pullback.inv.app (DerivedCategory.Q.obj Q))) ≫
      l.restrictionTensorX.comparison.inv.app
        (g.operation.left.obj (DerivedCategory.Q.obj P),
          g.operation.left.obj (DerivedCategory.Q.obj Q)) ≫
      l.restrictionX.model.functor.map
        (g.tensorComparison.comparison.inv.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) =
    l.tensorComparison.comparison.inv.app
        (l.restrictionY.model.functor.obj (DerivedCategory.Q.obj P),
          l.restrictionY.model.functor.obj (DerivedCategory.Q.obj Q)) ≫
      l.operation.left.map
        (l.restrictionTensorY.comparison.inv.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      l.pullback.inv.app
        (g.tensorY.functor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) := by
  let := l.restrictionYAdditive
  let := l.restrictionXAdditive
  apply four_models_inverse g.tensorComparison l.restrictionTensorY
    l.restrictionTensorX l.tensorComparison (localOrdinaryPullbackSquare l)
    (localOrdinaryTensorSquare f R_Y R_X c g V l) l.pullback.inv
    (P := P) (Q := Q) (hp := hp) (hq := hq)
  intro T
  simpa only [twoFactors, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Category.assoc] using localPullbackNormalization f R_Y R_X c g V l T

-- The two routes are natural transformations; resolving-pair faithfulness
-- therefore permits a componentwise representative calculation below.
/-- The localized pullback square respects the four canonical tensor comparisons. -/
theorem localTensorSquare
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R_Y : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (R_X : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R_Y ≅ R_X)
    (g : Global f R_Y R_X c) (V : Y.ProEt)
    (l : Local f R_Y R_X c g V) :
    letI := l.restrictionYAdditive
    letI := l.restrictionXAdditive
    ∀ P Q : Der R_Y,
    l.pullback.inv.app (g.tensorY.functor.obj (P, Q)) ≫
        l.restrictionX.model.functor.map (g.tensorComparison.comparison.hom.app (P, Q)) ≫
        l.restrictionTensorX.comparison.hom.app
          (g.operation.left.obj P, g.operation.left.obj Q) =
      l.operation.left.map (l.restrictionTensorY.comparison.hom.app (P, Q)) ≫
        l.tensorComparison.comparison.hom.app
          (l.restrictionY.model.functor.obj P, l.restrictionY.model.functor.obj Q) ≫
        l.tensorX.functor.map (CategoryTheory.Prod.mkHom
          (l.pullback.inv.app P) (l.pullback.inv.app Q)) := by
  let := l.restrictionYAdditive
  let := l.restrictionXAdditive
  let F := g.operation.left
  let G := l.restrictionY.model.functor
  let H := l.restrictionX.model.functor
  let K := l.operation.left
  let A := g.tensorY.functor
  let D := l.tensorX.functor
  let tF := g.tensorComparison.comparison
  let tG := l.restrictionTensorY.comparison
  let tH := l.restrictionTensorX.comparison
  let tK := l.tensorComparison.comparison
  let theta := l.pullback.inv
  let a : (G.prod G) ⋙ (K.prod K) ⋙ D ⟶ A ⋙ F ⋙ H :=
    Functor.whiskerRight (theta.prod theta) D ≫
      Functor.whiskerLeft (F.prod F) tH.inv ≫ Functor.whiskerRight tF.inv H
  let b : (G.prod G) ⋙ (K.prod K) ⋙ D ⟶ A ⋙ F ⋙ H :=
    Functor.whiskerLeft (G.prod G) tK.inv ≫ Functor.whiskerRight tG.inv K ≫
      Functor.whiskerLeft A theta
  have he : a = b := by
    obtain ⟨_, _, _, hd⟩ := SheafOfModules.cochain_tensor_model_rigidity
      (ProEt.topology Y) R_Y
    apply (hd (Der (R_X.over ((proEtaleBaseChange f).obj V))) inferInstance _ _).1
    apply NatTrans.ext
    funext Z
    rcases Z with ⟨P, Q⟩
    exact inverse_on_representatives l P.obj Q.obj P.property Q.property
  intro P Q
  have hi := congrArg (fun t ↦ t.app (P, Q)) he
  change D.map (Prod.mkHom (theta.app P) (theta.app Q)) ≫
      tH.inv.app (F.obj P, F.obj Q) ≫ H.map (tF.inv.app (P, Q)) =
    tK.inv.app (G.obj P, G.obj Q) ≫ K.map (tG.inv.app (P, Q)) ≫
      theta.app (A.obj (P, Q)) at hi
  let v := K.mapIso (tG.app (P, Q)) ≪≫ tK.app (G.obj P, G.obj Q)
  let w := H.mapIso (tF.app (P, Q)) ≪≫ tH.app (F.obj P, F.obj Q)
  have hi' : D.map (Prod.mkHom (theta.app P) (theta.app Q)) ≫ w.inv =
      v.inv ≫ theta.app (A.obj (P, Q)) := by
    simpa only [v, w, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc]
      using hi
  have hf : v.hom ≫ D.map (Prod.mkHom (theta.app P) (theta.app Q)) =
      theta.app (A.obj (P, Q)) ≫ w.hom := by
    apply (Iso.comp_inv_eq w).1
    rw [Category.assoc, hi', Iso.hom_inv_id_assoc]
  simpa only [v, w, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc]
    using hf.symm

end AlgebraicGeometry.Scheme.ProjectionRestriction
