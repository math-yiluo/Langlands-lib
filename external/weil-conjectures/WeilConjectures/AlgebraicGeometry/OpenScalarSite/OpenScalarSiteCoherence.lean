/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensor
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantExact
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.CategoryTheory.RingedSliceExtensionTensorHomData
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import all WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensorDefs
import all WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsPullbackSquare
import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
import WeilConjectures.AlgebraicGeometry.Etale.Constant.EtaleConstantModuleFlat
import WeilConjectures.AlgebraicGeometry.OpenScalarFlatModel.OpenScalarFlatModelRealization
import all WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
import all WeilConjectures.AlgebraicGeometry.Comparison.ComparisonOpenTensorCoherence
import all WeilConjectures.AlgebraicGeometry.Derived.DerivedScalarExtensionLocalSystems
import all WeilConjectures.AlgebraicGeometry.Open.OpenComparisonUnitNormalization

/-! # Open extension, scalar extension, and site comparison

## Main declarations

* `scalarOpen`: the canonical pro-etale scalar/open adjunction mate.
* `extension_flat_kflat`: preservation of the required flat models on both sites.
* `scalar_site_square`: the specified B-linear derived square.
* `etale_scalar_comp`, `proetale_scalar_comp`: scalar composition coherence.
* `etale_scalar_id`, `proetale_scalar_id`: scalar identity normalization.
* `site_comp`, `site_id`: derived site composition and identity coherence.

## References

* Stacks Project, Tags 0GL1, 0E8I, 09AF, 06YQ and 0G7E
* Stacks 03EL, 03EK
* Stacks 0GL1, 0E8I, 06YY
* Stacks 03DI, 0E8I, 0GL1
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
private theorem uniq_eq_conjugate
    {C D : Type*} [Category C] [Category D]
    {F F' : C ⥤ D} {G G' : D ⥤ C}
    (a : F ⊣ G) (b : F' ⊣ G') (e : G' ≅ G) :
    a.leftAdjointUniq (b.ofNatIsoRight e) = (conjugateIsoEquiv b a).symm e := by
  ext X
  simp [Adjunction.leftAdjointUniq, conjugateEquiv_symm_apply_app]

private theorem exact_identity_square
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (E : C ⥤ C) (N : C ⥤ D) (P : D ⥤ D)
    [E.Additive] [N.Additive] [P.Additive]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits N] [PreservesFiniteColimits N]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (q : E ⋙ N ≅ N ⋙ P) (e : E ≅ 𝟭 C) (p : P ≅ 𝟭 D)
    (hq : ∀ X, q.hom.app X ≫ p.hom.app (N.obj X) = N.map (e.hom.app X))
    (K : DerivedCategory C) :
    (Functor.mapDerivedCategorySquareIso q).hom.app K ≫
        (Functor.mapDerivedCategoryNatIso p ≪≫ Functor.mapDerivedCategoryIdIso D).hom.app
          (N.mapDerivedCategory.obj K) =
      N.mapDerivedCategory.map
        ((Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso C).hom.app K) := by
  have heq : q ≪≫ Functor.isoWhiskerLeft N p ≪≫ N.rightUnitor =
      Functor.isoWhiskerRight e N ≪≫ N.leftUnitor := by
    ext X
    simpa using hq X
  have hd := congrArg (fun z ↦ (Functor.mapDerivedCategoryNatIso z).hom.app K) heq
  simp only [Functor.mapDerivedCategoryNatIso_trans, NatTrans.comp_app] at hd
  have hleft := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft N p) K
  have hright := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight e N) K
  have hu : (Functor.mapDerivedCategoryNatIso N.rightUnitor).hom = 𝟙 _ :=
    Functor.mapDerivedCategoryNatIso_refl
  have hv : (Functor.mapDerivedCategoryNatIso N.leftUnitor).hom = 𝟙 _ :=
    Functor.mapDerivedCategoryNatIso_refl
  rw [hu, hv] at hd
  simp only [NatTrans.id_app, Category.comp_id] at hd
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso E N).inv.app K)).mp
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
  have hp := congr_app (Functor.mapDerivedCategoryCompIso_comp_id N) K
  have he := congr_app (Functor.mapDerivedCategoryCompIso_id_comp N) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.id_app] at hp he
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app] at hleft hright
  calc
    _ = (Functor.mapDerivedCategoryNatIso q).hom.app K ≫
        (Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerLeft N p)).hom.app K ≫
        (Functor.mapDerivedCategoryCompIso N (𝟭 D)).inv.app K ≫
        (Functor.mapDerivedCategoryIdIso D).hom.app (N.mapDerivedCategory.obj K) := by
      rw [reassoc_of% hleft]
    _ = (Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerRight e N)).hom.app K := by
      rw [hp]
      erw [Category.comp_id]
      exact hd
    _ = (Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerRight e N)).hom.app K ≫
        (Functor.mapDerivedCategoryCompIso (𝟭 C) N).inv.app K ≫
        N.mapDerivedCategory.map ((Functor.mapDerivedCategoryIdIso C).hom.app K) := by
      rw [he]
      erw [Category.comp_id]
    _ = _ := by rw [← Category.assoc, hright, Category.assoc]

private theorem scalar_composition
    {A B C D E F : Type*}
    [Category* A] [Category* B] [Category* C]
    [Category* D] [Category* E] [Category* F]
    {La : A ⥤ D} {Ra : D ⥤ A} {Lb : B ⥤ E} {Rb : E ⥤ B}
    {Lc : C ⥤ F} {Rc : F ⥤ C}
    {H : A ⥤ B} {S : B ⥤ A} {I : B ⥤ C} {T : C ⥤ B}
    {J : A ⥤ C} {U : C ⥤ A}
    {P : D ⥤ E} {Rp : E ⥤ D} {Q : E ⥤ F} {Rq : F ⥤ E}
    {R : D ⥤ F} {Rr : F ⥤ D}
    (a : La ⊣ Ra) (b : Lb ⊣ Rb) (c : Lc ⊣ Rc)
    (h : H ⊣ S) (i : I ⊣ T) (j : J ⊣ U)
    (p : P ⊣ Rp) (q : Q ⊣ Rq) (r : R ⊣ Rr)
    (α01 : Rp ⋙ Ra ≅ Rb ⋙ S) (α12 : Rq ⋙ Rb ≅ Rc ⋙ T)
    (α02 : Rr ⋙ Ra ≅ Rc ⋙ U) (β : U ≅ T ⋙ S) (γ : Rq ⋙ Rp ≅ Rr)
    (μ : J ≅ H ⋙ I) (κ : R ≅ P ⋙ Q)
    (hμ : conjugateIsoEquiv (h.comp i) j μ = β.symm)
    (hκ : conjugateIsoEquiv (p.comp q) r κ = γ)
    (hr : α02 = Functor.isoWhiskerRight γ.symm Ra ≪≫
      Functor.associator Rq Rp Ra ≪≫ Functor.isoWhiskerLeft Rq α01 ≪≫
      (Functor.associator Rq Rb S).symm ≪≫ Functor.isoWhiskerRight α12 S ≪≫
      Functor.associator Rc T S ≪≫ Functor.isoWhiskerLeft Rc β.symm)
    (K : A) :
    Lc.map (μ.hom.app K) ≫
        ((i.comp c).leftAdjointUniq ((b.comp q).ofNatIsoRight α12)).hom.app (H.obj K) ≫
        Q.map (((h.comp b).leftAdjointUniq ((a.comp p).ofNatIsoRight α01)).hom.app K) ≫
        κ.inv.app (La.obj K) =
      ((j.comp c).leftAdjointUniq ((a.comp r).ofNatIsoRight α02)).hom.app K := by
  let t01 := (h.comp b).leftAdjointUniq ((a.comp p).ofNatIsoRight α01)
  let t12 := (i.comp c).leftAdjointUniq ((b.comp q).ofNatIsoRight α12)
  let t02 := (j.comp c).leftAdjointUniq ((a.comp r).ofNatIsoRight α02)
  have he := adjunctionSquareComposition a b c h i j p q r
    α01 α12 α02 β γ t01.symm t12.symm t02.symm μ κ.symm
    (by rw [conjugateIsoEquiv_iso_symm, CategoryTheory.conj_uniq_transport])
    (by rw [conjugateIsoEquiv_iso_symm, CategoryTheory.conj_uniq_transport])
    (by rw [conjugateIsoEquiv_iso_symm, CategoryTheory.conj_uniq_transport]) hμ
    (by rw [conjugateIsoEquiv_iso_symm, hκ]) hr
  have he' := congrArg (fun z ↦ z.inv.app K) he
  simp only [Iso.trans_inv, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app, Iso.symm_inv,
    Category.id_comp, Category.comp_id] at he'
  exact CategoryTheory.paste_cancel (Lc.mapIso (μ.app K)) _ _ (κ.app (La.obj K)) _ he'

private theorem scalar_identity
    {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} {E S : C ⥤ C} {P T : D ⥤ D}
    (a : L ⊣ R) (b : E ⊣ S) (c : P ⊣ T)
    (q : T ⋙ R ≅ R ⋙ S) (s : S ≅ 𝟭 C) (t : T ≅ 𝟭 D)
    (hq : ∀ X, q.hom.app X ≫ s.hom.app (R.obj X) = R.map (t.hom.app X))
    (K : C) :
    ((b.comp a).leftAdjointUniq ((a.comp c).ofNatIsoRight q)).hom.app K ≫
        (Adjunction.leftAdjointIdIso c t).hom.app (L.obj K) =
      L.map ((Adjunction.leftAdjointIdIso b s).hom.app K) := by
  have h := CategoryTheory.identity_square a b c
    ((b.comp a).leftAdjointUniq ((a.comp c).ofNatIsoRight q))
    (Adjunction.leftAdjointIdIso b s) (Adjunction.leftAdjointIdIso c t) q.symm s t
    (by
      rw [conjugateIsoEquiv_iso_symm, CategoryTheory.conj_uniq_transport])
    (Equiv.apply_symm_apply _ _) (Equiv.apply_symm_apply _ _) (by
      apply Iso.ext
      ext X
      simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom,
        Functor.isoWhiskerLeft_hom, Iso.symm_hom, Iso.symm_inv,
        NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Functor.leftUnitor_inv_app, Functor.rightUnitor_inv_app,
        Category.id_comp]
      apply (cancel_mono (s.hom.app (R.obj X))).mp
      rw [Category.assoc, hq, ← R.map_comp, Iso.inv_hom_id_app, R.map_id,
        Iso.inv_hom_id_app]
      rfl)
  simpa using congrArg (fun z ↦ z.hom.app K) h

private theorem scalar_open_inverse_mate
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {LA : C ⥤ D} {JA : D ⥤ C} {LB : E ⥤ F} {JB : F ⥤ E}
    {SX : D ⥤ F} {RX : F ⥤ D} {SU : C ⥤ E} {RU : E ⥤ C}
    (a : LA ⊣ JA) (b : LB ⊣ JB) (x : SX ⊣ RX) (u : SU ⊣ RU)
    (q : JB ⋙ RU ≅ RX ⋙ JA) :
    ((mateEquiv a b).symm
      ((mateEquiv x u).symm (TwoSquare.mk _ _ _ _ q.inv))) =
      ((a.comp x).leftAdjointUniq ((u.comp b).ofNatIsoRight q)).inv := by
  rw [uniq_eq_conjugate]
  exact
    (iterated_mateEquiv_conjugateEquiv_symm a b u x (TwoSquare.mk _ _ _ _ q.inv))

private theorem open_mate_cube
    {C D E F Cb Db Eb Fb : Type*}
    [Category C] [Category D] [Category E] [Category F]
    [Category Cb] [Category Db] [Category Eb] [Category Fb]
    {LA : C ⥤ D} {JA : D ⥤ C} {LA' : E ⥤ F} {JA' : F ⥤ E}
    {LB : Cb ⥤ Db} {JB : Db ⥤ Cb} {LB' : Eb ⥤ Fb} {JB' : Fb ⥤ Eb}
    (a : LA ⊣ JA) (a' : LA' ⊣ JA') (b : LB ⊣ JB) (b' : LB' ⊣ JB')
    {HA : C ⥤ E} {GA : D ⥤ F} {HB : Cb ⥤ Eb} {GB : Db ⥤ Fb}
    {S : C ⥤ Cb} {Q : D ⥤ Db} {S' : E ⥤ Eb} {Q' : F ⥤ Fb}
    (β : LA ⋙ Q ≅ S ⋙ LB) (β' : LA' ⋙ Q' ≅ S' ⋙ LB')
    (dA : HA ⋙ LA' ≅ LA ⋙ GA) (dB : HB ⋙ LB' ≅ LB ⋙ GB)
    (lj : JA ⋙ S ⟶ Q ⋙ JB) (lj' : JA' ⋙ S' ⟶ Q' ⋙ JB')
    (lh : S ⋙ HB ≅ HA ⋙ S') (lg : Q ⋙ GB ≅ GA ⋙ Q')
    (cA : JA ⋙ HA ≅ GA ⋙ JA') (cB : JB ⋙ HB ≅ GB ⋙ JB')
    (hi : ∀ M, b.unit.app (S.obj M) ≫ JB.map (β.inv.app M) =
      S.map (a.unit.app M) ≫ lj.app (LA.obj M))
    (hi' : ∀ M, b'.unit.app (S'.obj M) ≫ JB'.map (β'.inv.app M) =
      S'.map (a'.unit.app M) ≫ lj'.app (LA'.obj M))
    (hdA : ∀ M, a'.unit.app (HA.obj M) ≫ JA'.map (dA.hom.app M) =
      HA.map (a.unit.app M) ≫ cA.hom.app (LA.obj M))
    (hdB : ∀ M, b'.unit.app (HB.obj M) ≫ JB'.map (dB.hom.app M) =
      HB.map (b.unit.app M) ≫ cB.hom.app (LB.obj M))
    (hc : ∀ N, S'.map (cA.hom.app N) ≫ lj'.app (GA.obj N) ≫
        JB'.map (lg.inv.app N) =
      lh.inv.app (JA.obj N) ≫ HB.map (lj.app N) ≫ cB.hom.app (Q.obj N))
    (M : C) :
    LB'.map (lh.inv.app M) ≫ dB.hom.app (S.obj M) ≫ GB.map (β.inv.app M) =
      β'.inv.app (HA.obj M) ≫ Q'.map (dA.hom.app M) ≫ lg.inv.app (LA.obj M) := by
  set_option backward.isDefEq.respectTransparency false in
    apply (b'.homEquiv _ _).injective
    simp only [Adjunction.homEquiv_unit, Functor.map_comp, Functor.comp_obj]
    have hn := b'.unit.naturality (lh.inv.app M)
    dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at hn
    rw [← reassoc_of% hn, reassoc_of% hdB]
    have hn := cB.hom.naturality (β.inv.app M)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    rw [← hn, ← HB.map_comp_assoc, hi, HB.map_comp, Category.assoc]
    have hn := lh.inv.naturality (a.unit.app M)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    rw [← reassoc_of% hn]
    rw [reassoc_of% hi']
    have hn := lj'.naturality (dA.hom.app M)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    rw [← reassoc_of% hn, ← S'.map_comp_assoc, hdA, S'.map_comp, Category.assoc]
    rw [hc]

namespace AlgebraicGeometry.ProEtale.OpenScalarSite

private def site_pullback (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) :
    Etale.upperStar (ModuleCat.{u + 1} A) j ⋙
      comparisonUpperStar (ModuleCat.{u + 1} A) U ≅
    comparisonUpperStar (ModuleCat.{u + 1} A) X ⋙ upperStar (ModuleCat.{u + 1} A) j :=
  supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) j

/-- The sectionwise coefficient identification for pro-etale open restriction. -/
def restrictScalarsIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    upperStar (ModuleCat.{u + 1} B) j ⋙
        Sheaf.restrictScalars (Scheme.ProEt.topology U) φ ≅
      Sheaf.restrictScalars (Scheme.ProEt.topology X) φ ⋙
        upperStar (ModuleCat.{u + 1} A) j :=
  Functor.isoWhiskerRight (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} B) j) _ ≪≫
    (show openImmersionRestriction (ModuleCat.{u + 1} B) j ⋙
        Sheaf.restrictScalars (Scheme.ProEt.topology U) φ ≅
      Sheaf.restrictScalars (Scheme.ProEt.topology X) φ ⋙
        openImmersionRestriction (ModuleCat.{u + 1} A) j from
      NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)) ≪≫
    Functor.isoWhiskerLeft _
      (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).symm

/-- The canonical pro-etale scalar/open comparison. This is the mate of the literal
coefficient/restriction identification under the derived scalar and exact open
adjunctions. Thus it specifies the summand-preserving map, rather than choosing an
arbitrary isomorphism. -/
def scalarOpen {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory ⋙
        pbcFixedScalarExtension (Scheme.ProEt.topology X) φ ≅
      pbcFixedScalarExtension (Scheme.ProEt.topology U) φ ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory :=
  ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).comp
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ))).leftAdjointUniq
    (((Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology U) φ)).comp
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)).ofNatIsoRight
      (Functor.mapDerivedCategorySquareIso (restrictScalarsIso φ j)))

/-- Exact descent of the recorded pro-etale extension compositor. -/
def extensionComp (A : Type (u + 1)) [CommRing A] {V U X : Scheme.{u}}
    (k : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion k] [IsOpenImmersion j] :=
  Functor.mapDerivedCategoryNatIso (proEtaleOpenExtensionComp A k j) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

private theorem et_restrict_comp {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {V U X : Scheme.{u}} (k : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j]
    (M : Sheaf (X.smallEtaleTopology) (ModuleCat.{u + 1} B)) :
    (Sheaf.restrictScalars (V.smallEtaleTopology) φ).map
        ((Etale.upperStarComp (ModuleCat.{u + 1} B) k j).hom.app M) ≫
      (Etale.openRestrictScalarsIso φ k).hom.app ((Etale.upperStar (ModuleCat.{u + 1} B) j).obj M) ≫
      (Etale.upperStar (ModuleCat.{u + 1} A) k).map ((Etale.openRestrictScalarsIso φ j).hom.app M) =
    (Etale.openRestrictScalarsIso φ (k ≫ j)).hom.app M ≫
      (Etale.upperStarComp (ModuleCat.{u + 1} A) k j).hom.app
        ((Sheaf.restrictScalars (X.smallEtaleTopology) φ).obj M) := by
  have h := (Etale.coefficient_comp_app φ k j (k ≫ j) rfl M).symm
  rw [← Etale.openRestrictScalarsIso_inv_eq, ← Etale.openRestrictScalarsIso_inv_eq,
    ← Etale.openRestrictScalarsIso_inv_eq] at h
  apply (cancel_epi ((Etale.openRestrictScalarsIso φ (k ≫ j)).inv.app M)).mp
  rw [← Category.assoc, ← Category.assoc, h]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  erw [Category.id_comp]
  rw [← (Etale.upperStar (ModuleCat.{u + 1} A) k).map_comp,
    Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

private theorem et_derived_restrict_comp {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {V U X : Scheme.{u}} (k : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion k] [IsOpenImmersion j]
    (hq : ∀ M : Sheaf (X.smallEtaleTopology) (ModuleCat.{u + 1} B),
      (Sheaf.restrictScalars (V.smallEtaleTopology) φ).map
          ((Etale.upperStarComp (ModuleCat.{u + 1} B) k j).hom.app M) ≫
        (Etale.openRestrictScalarsIso φ k).hom.app
          ((Etale.upperStar (ModuleCat.{u + 1} B) j).obj M) ≫
        (Etale.upperStar (ModuleCat.{u + 1} A) k).map
          ((Etale.openRestrictScalarsIso φ j).hom.app M) =
      (Etale.openRestrictScalarsIso φ (k ≫ j)).hom.app M ≫
        (Etale.upperStarComp (ModuleCat.{u + 1} A) k j).hom.app
          ((Sheaf.restrictScalars (X.smallEtaleTopology) φ).obj M)) :
    let RA (T : Scheme.{u}) := Sheaf.derivedRestrictScalars (T.smallEtaleTopology) φ
    let UB {S T : Scheme.{u}} (f : S ⟶ T) :=
      (Etale.upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategory
    let UA {S T : Scheme.{u}} (f : S ⟶ T) :=
      (Etale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory
    let β := Functor.mapDerivedCategoryNatIso (Etale.upperStarComp (ModuleCat.{u + 1} A) k j) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm
    let γ := Functor.mapDerivedCategoryNatIso (Etale.upperStarComp (ModuleCat.{u + 1} B) k j) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm
    Functor.mapDerivedCategorySquareIso (Etale.openRestrictScalarsIso φ (k ≫ j)) =
      Functor.isoWhiskerRight γ (RA V) ≪≫
      Functor.associator (UB j) (UB k) (RA V) ≪≫
      Functor.isoWhiskerLeft (UB j)
        (Functor.mapDerivedCategorySquareIso (Etale.openRestrictScalarsIso φ k)) ≪≫
      (Functor.associator (UB j) (RA U) (UA k)).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapDerivedCategorySquareIso (Etale.openRestrictScalarsIso φ j)) (UA k) ≪≫
      Functor.associator (RA X) (UA j) (UA k) ≪≫
      Functor.isoWhiskerLeft (RA X) β.symm := by
  dsimp only
  apply Iso.ext
  ext K
  have hc :
      (Sheaf.derivedRestrictScalars (V.smallEtaleTopology) φ).map
          ((Functor.mapDerivedCategoryNatIso (Etale.upperStarComp (ModuleCat.{u + 1} B) k j) ≪≫
            (Functor.mapDerivedCategoryCompIso _ _).symm).hom.app K) ≫
        (Functor.mapDerivedCategorySquareIso (Etale.openRestrictScalarsIso φ k)).hom.app
          ((Etale.upperStar (ModuleCat.{u + 1} B) j).mapDerivedCategory.obj K) ≫
        (Etale.upperStar (ModuleCat.{u + 1} A) k).mapDerivedCategory.map
          ((Functor.mapDerivedCategorySquareIso (Etale.openRestrictScalarsIso φ j)).hom.app K) =
      (Functor.mapDerivedCategorySquareIso (Etale.openRestrictScalarsIso φ (k ≫ j))).hom.app K ≫
        (Functor.mapDerivedCategoryNatIso (Etale.upperStarComp (ModuleCat.{u + 1} A) k j) ≪≫
          (Functor.mapDerivedCategoryCompIso _ _).symm).hom.app
            ((Sheaf.derivedRestrictScalars (X.smallEtaleTopology) φ).obj K) := by
    simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id] using congrArg (fun e ↦ e.hom.app K)
      (Functor.mapDerivedCategorySquareIso_comp
        (C₀ := Sheaf (X.smallEtaleTopology) (ModuleCat.{u + 1} B))
        (C₁ := Sheaf (U.smallEtaleTopology) (ModuleCat.{u + 1} B))
        (C₂ := Sheaf (V.smallEtaleTopology) (ModuleCat.{u + 1} B))
        (D₀ := Sheaf (X.smallEtaleTopology) (ModuleCat.{u + 1} A))
        (D₁ := Sheaf (U.smallEtaleTopology) (ModuleCat.{u + 1} A))
        (D₂ := Sheaf (V.smallEtaleTopology) (ModuleCat.{u + 1} A))
        (Etale.upperStar (ModuleCat.{u + 1} B) j) (Etale.upperStar (ModuleCat.{u + 1} B) k)
        (Etale.upperStar (ModuleCat.{u + 1} B) (k ≫ j))
        (Etale.upperStar (ModuleCat.{u + 1} A) j) (Etale.upperStar (ModuleCat.{u + 1} A) k)
        (Etale.upperStar (ModuleCat.{u + 1} A) (k ≫ j))
        (Sheaf.restrictScalars (X.smallEtaleTopology) φ)
        (Sheaf.restrictScalars (U.smallEtaleTopology) φ)
        (Sheaf.restrictScalars (V.smallEtaleTopology) φ)
        (Etale.openRestrictScalarsIso φ j) (Etale.openRestrictScalarsIso φ k)
        (Etale.openRestrictScalarsIso φ (k ≫ j))
        (Etale.upperStarComp (ModuleCat.{u + 1} B) k j)
        (Etale.upperStarComp (ModuleCat.{u + 1} A) k j) hq)
  have he := congrArg (fun t ↦ t ≫
    (Functor.mapDerivedCategoryNatIso (Etale.upperStarComp (ModuleCat.{u + 1} A) k j) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm).inv.app
        ((Sheaf.derivedRestrictScalars (X.smallEtaleTopology) φ).obj K)) hc
  simp only [Category.assoc, Iso.hom_inv_id_app] at he
  erw [Category.comp_id] at he
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] using he.symm

private theorem et_restrict_id {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u})
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    (Etale.openRestrictScalarsIso φ (𝟙 X)).hom.app M ≫
      (Etale.upperStarId (ModuleCat.{u + 1} A) X).hom.app
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj M) =
      (Sheaf.restrictScalars X.smallEtaleTopology φ).map
        ((Etale.upperStarId (ModuleCat.{u + 1} B) X).hom.app M) := by
  rw [← et_up_res_id (ModuleCat.{u + 1} A) X, ← et_up_res_id (ModuleCat.{u + 1} B) X]
  simp only [Etale.openRestrictScalarsIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, NatIso.ofComponents_hom_app,
    Iso.refl_hom, Category.id_comp, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_app_assoc, Functor.map_comp]
  rfl

private theorem etale_identity_normalized (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) :
    Etale.mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) X =
      Adjunction.leftAdjointIdIso
        (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X))
        (Functor.mapDerivedCategoryNatIso (Etale.upperStarId (ModuleCat.{u + 1} A) X) ≪≫
          Functor.mapDerivedCategoryIdIso _) := by
  dsimp only [Etale.mapDerivedCategoryOpenImmersionLowerShriekId,
    Etale.openImmersionLowerShriekId]
  rw [uniq_eq_conjugate]
  apply Iso.ext
  apply (conjugateEquiv Adjunction.id _).injective
  rw [Adjunction.conjugateEquiv_leftAdjointIdIso_hom]
  exact Etale.derived_open_id_conjugate A X

private theorem comparison_restriction_mate (A : Type (u + 1)) [CommRing A]
    [Finite A] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (mateEquiv (comparisonAdjunction (ModuleCat.{u + 1} A) X)
      (comparisonAdjunction (ModuleCat.{u + 1} A) U)
      (TwoSquare.mk _ _ _ _ (openComparisonRestrictionIso A j).hom)) = 𝟙 _ := by
  let B := ModuleCat.{u + 1} A
  let cX := comparisonAdjunction B X
  let cU := comparisonAdjunction B U
  let r := Etale.openImmersionRestrictionLowerStarAdjunction B j
  let s := openImmersionRestrictionLowerStarAdjunction B j
  apply (mateEquiv s r).injective
  change (mateEquiv s r (mateEquiv cX cU
    (TwoSquare.mk _ _ _ _ (openComparisonRestrictionIso A j).hom))) =
    (mateEquiv s r (TwoSquare.mk _ _ _ _
      (comparisonLowerStarOpenImmersionRestrictionIso B j).hom))
  rw [iterated_mateEquiv_conjugateEquiv]
  exact (openComparisonRestrictionIso_conjugate A j).trans
    (openComparisonRestriction_directImage_mate A j).symm

private theorem comparison_restriction_left (A : Type (u + 1)) [CommRing A]
    [Finite A] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    ((mateEquiv (comparisonAdjunction (ModuleCat.{u + 1} A) X)
      (comparisonAdjunction (ModuleCat.{u + 1} A) U)).symm
      (TwoSquare.mk _ _ _ _
        (comparisonLowerStarOpenImmersionRestrictionIso (ModuleCat.{u + 1} A) j).hom)) =
      (openComparisonRestrictionIso A j).hom := by
  apply (mateEquiv (comparisonAdjunction (ModuleCat.{u + 1} A) X)
    (comparisonAdjunction (ModuleCat.{u + 1} A) U)).injective
  rw [Equiv.apply_symm_apply]
  exact (comparison_restriction_mate A j).symm

private theorem restriction_coefficient_cube {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    (openComparisonRestrictionIso A j).hom.app
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj M) ≫
      (openImmersionRestriction (ModuleCat.{u + 1} A) j).map
        ((pbcComparisonRestrict X φ).inv.app M) =
    (pbcComparisonRestrict U φ).inv.app
        ((Etale.openImmersionRestriction (ModuleCat.{u + 1} B) j).obj M) ≫
      (Sheaf.restrictScalars (Scheme.ProEt.topology U) φ).map
        ((openComparisonRestrictionIso B j).hom.app M) := by
  let aX := comparisonAdjunction (ModuleCat.{u + 1} B) X
  let aU := comparisonAdjunction (ModuleCat.{u + 1} B) U
  let dX := comparisonAdjunction (ModuleCat.{u + 1} A) X
  let dU := comparisonAdjunction (ModuleCat.{u + 1} A) U
  have hu (T : Scheme.{u}) (N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) :
      (comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app
          ((Sheaf.restrictScalars T.smallEtaleTopology φ).obj N) ≫
        (comparisonLowerStar (ModuleCat.{u + 1} A) T).map
          ((pbcComparisonRestrict T φ).inv.app N) =
      (Sheaf.restrictScalars T.smallEtaleTopology φ).map
        ((comparisonAdjunction (ModuleCat.{u + 1} B) T).unit.app N) := by
    have hm := comparison_restrict_mate T φ
    have ht := unit_mateEquiv
      (comparisonAdjunction (ModuleCat.{u + 1} B) T)
      (comparisonAdjunction (ModuleCat.{u + 1} A) T)
      (TwoSquare.mk _ _ _ _ (pbcComparisonRestrict T φ).inv) N
    change (Sheaf.restrictScalars T.smallEtaleTopology φ).map
      ((comparisonAdjunction (ModuleCat.{u + 1} B) T).unit.app N) ≫
      (mateEquiv (comparisonAdjunction (ModuleCat.{u + 1} B) T)
        (comparisonAdjunction (ModuleCat.{u + 1} A) T)
        (TwoSquare.mk _ _ _ _ (pbcComparisonRestrict T φ).inv)).app
          ((comparisonUpperStar (ModuleCat.{u + 1} B) T).obj N) = _ at ht
    rw [hm] at ht
    simp only [NatTrans.id_app] at ht
    erw [Category.comp_id] at ht
    exact ht.symm
  have h := left_mate_normalization aX aU dX dU
    (Sheaf.restrictScalars X.smallEtaleTopology φ)
    (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ)
    (Sheaf.restrictScalars U.smallEtaleTopology φ)
    (Sheaf.restrictScalars (Scheme.ProEt.topology U) φ)
    (pbcComparisonRestrict X φ).inv (pbcComparisonRestrict U φ).inv
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (comparisonLowerStarOpenImmersionRestrictionIso (ModuleCat.{u + 1} B) j).hom
    (comparisonLowerStarOpenImmersionRestrictionIso (ModuleCat.{u + 1} A) j).hom
    (fun N ↦ by
      simp only [Iso.refl_hom, NatTrans.id_app]
      erw [Category.comp_id]
      exact hu X N)
    (fun N ↦ by
      simp only [Iso.refl_hom, NatTrans.id_app]
      erw [Category.comp_id]
      exact hu U N)
    (fun N ↦ by simp only [Iso.refl_hom]; rfl) M
  simp only [aX, aU, dX, dU, comparison_restriction_left, Iso.refl_hom,
    NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp] at h
  erw [Category.comp_id] at h
  exact h

private theorem upper_coefficient_cube {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) U).map
        ((Etale.openRestrictScalarsIso φ j).inv.app M) ≫
      (pbcComparisonRestrict U φ).inv.app ((Etale.upperStar (ModuleCat.{u + 1} B) j).obj M) ≫
      (Sheaf.restrictScalars (Scheme.ProEt.topology U) φ).map
        ((site_pullback B j).hom.app M) =
    (site_pullback A j).hom.app
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj M) ≫
      (upperStar (ModuleCat.{u + 1} A) j).map ((pbcComparisonRestrict X φ).inv.app M) ≫
      (restrictScalarsIso φ j).inv.app
        ((comparisonUpperStar (ModuleCat.{u + 1} B) X).obj M) := by
  let eA := Etale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j
  let eB := Etale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} B) j
  let pA : upperStar (ModuleCat.{u + 1} A) j ≅
      openImmersionRestriction (ModuleCat.{u + 1} A) j :=
    upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j
  let pB : upperStar (ModuleCat.{u + 1} B) j ≅
      openImmersionRestriction (ModuleCat.{u + 1} B) j :=
    upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} B) j
  let νA := comparisonUpperStar (ModuleCat.{u + 1} A) U
  let νB := comparisonUpperStar (ModuleCat.{u + 1} B) U
  let ρ : Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} B) ⥤
      Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} A) :=
    Sheaf.restrictScalars (Scheme.ProEt.topology U) φ
  have hsite (C : Type (u + 1)) [CommRing C] [Finite C]
      (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} C)) :
      (site_pullback C j).hom.app N ≫
          (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} C) j).hom.app
            ((comparisonUpperStar (ModuleCat.{u + 1} C) X).obj N) =
        (comparisonUpperStar (ModuleCat.{u + 1} C) U).map
          ((Etale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} C) j).hom.app N) ≫
          (openComparisonRestrictionIso C j).hom.app N := by
    simp only [site_pullback, openComparisonRestrictionIso, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app]
    rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  have hqp (N : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) :
      (restrictScalarsIso φ j).inv.app N =
        pA.hom.app ((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).obj N) ≫
          ρ.map (pB.inv.app N) := by
    simp only [restrictScalarsIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatIso.ofComponents_inv_app,
      Iso.refl_inv]
    erw [Category.comp_id]
  have hqe : (Etale.openRestrictScalarsIso φ j).inv.app M =
      eA.hom.app ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj M) ≫
        (Sheaf.restrictScalars U.smallEtaleTopology φ).map (eB.inv.app M) := by
    simp only [Etale.openRestrictScalarsIso, Iso.trans_inv, Iso.symm_inv,
      NatTrans.comp_app, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatIso.ofComponents_inv_app,
      Iso.refl_inv]
    erw [Category.comp_id]
  let z := ρ.mapIso (pB.app ((comparisonUpperStar (ModuleCat.{u + 1} B) X).obj M))
  apply (cancel_mono z.hom).mp
  simp only [z, Functor.mapIso_hom, Iso.app_hom]
  simp only [Category.assoc]
  rw [← ρ.map_comp, hsite, hqp]
  simp only [Category.assoc]
  erw [← ρ.map_comp, Iso.inv_hom_id_app, ρ.map_id, Category.comp_id]
  have hn := pA.hom.naturality ((pbcComparisonRestrict X φ).inv.app M)
  erw [hn]
  erw [reassoc_of% (hsite A ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj M))]
  rw [hqe]
  simp only [Functor.map_comp, Category.assoc]
  have hd := (pbcComparisonRestrict U φ).inv.naturality
    ((Etale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} B) j).inv.app M)
  rw [reassoc_of% hd]
  erw [← ρ.map_comp_assoc, ← νB.map_comp, Iso.inv_hom_id_app]
  erw [νB.map_id, ρ.map_id, Category.id_comp]
  rw [restriction_coefficient_cube φ j M]

private theorem derived_coefficient_cube {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory.map
        ((Functor.mapDerivedCategorySquareIso (Etale.openRestrictScalarsIso φ j)).inv.app M) ≫
      (pbcDerivedComparisonRestrict U φ).inv.app
        ((Etale.upperStar (ModuleCat.{u + 1} B) j).mapDerivedCategory.obj M) ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology U) φ).map
        ((Functor.mapDerivedCategorySquareIso
          (site_pullback B j)).hom.app M) =
    (Functor.mapDerivedCategorySquareIso
        (site_pullback A j)).hom.app
        ((Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).obj M) ≫
      (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.map
        ((pbcDerivedComparisonRestrict X φ).inv.app M) ≫
      (Functor.mapDerivedCategorySquareIso (restrictScalarsIso φ j)).inv.app
        ((comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.obj M) := by
  have h := derived_cube
    (Sheaf.restrictScalars X.smallEtaleTopology φ)
    (Sheaf.restrictScalars U.smallEtaleTopology φ)
    (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ)
    (Sheaf.restrictScalars (Scheme.ProEt.topology U) φ)
    (Etale.upperStar (ModuleCat.{u + 1} A) j)
    (Etale.upperStar (ModuleCat.{u + 1} B) j)
    (upperStar (ModuleCat.{u + 1} A) j)
    (upperStar (ModuleCat.{u + 1} B) j)
    (comparisonUpperStar (ModuleCat.{u + 1} A) X)
    (comparisonUpperStar (ModuleCat.{u + 1} B) X)
    (comparisonUpperStar (ModuleCat.{u + 1} A) U)
    (comparisonUpperStar (ModuleCat.{u + 1} B) U)
    (Etale.openRestrictScalarsIso φ j).symm (pbcComparisonRestrict U φ).symm
    (pbcComparisonRestrict X φ).symm (restrictScalarsIso φ j).symm
    (site_pullback A j)
    (site_pullback B j)
    (upper_coefficient_cube φ j) M
  simpa only [pbcDerivedComparisonRestrict, Functor.mapDerivedCategorySquareIso,
    Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Functor.map_comp, Category.assoc] using h

private theorem scalar_pullback_cube {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (M : Etale.DerivedCategoryModule A X) :
    (pbcFixedScalarExtension (Scheme.ProEt.topology U) φ).map
        ((Functor.mapDerivedCategorySquareIso
          (site_pullback A j)).hom.app M) ≫
      ((mateEquiv
        (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ))
        (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology U)
      φ))).symm
          (TwoSquare.mk _ _ _ _
            (Functor.mapDerivedCategorySquareIso (restrictScalarsIso φ j)).inv)).app
              ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj M) ≫
      (upperStar (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
        ((pbcComparisonReduction X φ).hom.app M) =
    (pbcComparisonReduction U φ).hom.app
        ((Etale.upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} B) U).mapDerivedCategory.map
        ((Etale.openScalarRestriction φ j).hom.app M) ≫
      (Functor.mapDerivedCategorySquareIso
        (site_pullback B j)).hom.app
          ((Etale.scalarExtension φ X).obj M) := by
  let a := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
  let al := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ)
  let am := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ)
  let ad := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology U) φ)
  let t := TwoSquare.mk _ _ _ _
    (Functor.mapDerivedCategorySquareIso (Etale.openRestrictScalarsIso φ j)).inv
  let k := TwoSquare.mk _ _ _ _ (pbcDerivedComparisonRestrict U φ).inv
  let c := TwoSquare.mk _ _ _ _ (pbcDerivedComparisonRestrict X φ).inv
  let q := TwoSquare.mk _ _ _ _
    (Functor.mapDerivedCategorySquareIso (restrictScalarsIso φ j)).inv
  let b := Functor.mapDerivedCategorySquareIso
    (site_pullback A j)
  let b' := Functor.mapDerivedCategorySquareIso
    (site_pullback B j)
  have hp : TwoSquare.vComp t k = TwoSquare.mk _ _ _ _
      (Functor.whiskerLeft (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ) b.hom ≫
        (TwoSquare.vComp c q) ≫ Functor.whiskerRight b'.inv
          (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology U) φ)) := by
    ext N
    simp only [TwoSquare.vComp, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc]
    dsimp only [t, k, c, q, b, b']
    apply (cancel_mono ((Sheaf.derivedRestrictScalars
      (Scheme.ProEt.topology U) φ).map
        ((Functor.mapDerivedCategorySquareIso
          (site_pullback B j)).hom.app N))).mp
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id]
    erw [Category.comp_id]
    exact derived_coefficient_cube φ j N
  have h := inverse_mate_cube a al am ad t k c q b b' hp M
  simpa only [a, al, am, ad, t, k, c, q, b, b', pbcComparisonReduction, asIso_hom,
    pbcComparisonReductionMap, Etale.openScalarRestriction, asIso_hom,
    Etale.openScalarRestrictionMap, Etale.openDerivedRestrictScalarsIso,
    pbcFixedScalarExtension, Etale.scalarExtension,
    Category.assoc,
    TwoSquare, TwoSquare.mk] using h

private theorem scalar_site_square_aux {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (L : Etale.DerivedCategoryModule A U) :
    (pbcFixedScalarExtension (Scheme.ProEt.topology X) φ).map
        ((mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
          (ModuleCat.{u + 1} A) j).hom.app L) ≫
      (scalarOpen φ j).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory.obj L) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
        ((pbcComparisonReduction U φ).hom.app L) =
    (pbcComparisonReduction X φ).hom.app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj L) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.map
        ((Etale.openScalarExtension φ j).hom.app L) ≫
      (mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} B) j).hom.app
          ((Etale.scalarExtension φ U).obj L) := by
  let ae := Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) j
  let ap := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j
  let be := Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} B) j
  let bp := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j
  let xe := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
  let ue := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ)
  let xp := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ)
  let up := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology U) φ)
  let qe := Functor.mapDerivedCategorySquareIso (Etale.openRestrictScalarsIso φ j)
  let qp := Functor.mapDerivedCategorySquareIso (restrictScalarsIso φ j)
  let le := ((mateEquiv xe ue).symm (TwoSquare.mk _ _ _ _ qe.inv))
  let lp := ((mateEquiv xp up).symm (TwoSquare.mk _ _ _ _ qp.inv))
  have he (N : Etale.DerivedCategoryModule A U) :
      be.unit.app ((Etale.scalarExtension φ U).obj N) ≫
        (Etale.upperStar (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
          ((Etale.openScalarExtension φ j).inv.app N) =
      (Etale.scalarExtension φ U).map (ae.unit.app N) ≫ le.app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj N) := by
    have h := unit_mateEquiv_symm ae be
      ((mateEquiv xe ue).symm (TwoSquare.mk _ _ _ _ qe.inv)) N
    have hm := scalar_open_inverse_mate ae be xe ue qe
    change (Etale.scalarExtension φ U).map (ae.unit.app N) ≫ le.app
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj N) =
      be.unit.app ((Etale.scalarExtension φ U).obj N) ≫ (Etale.upperStar (ModuleCat.{u + 1} B)
      j).mapDerivedCategory.map
        (((mateEquiv ae be).symm ((mateEquiv xe ue).symm
          (TwoSquare.mk _ _ _ _ qe.inv))).app N) at h
    rw [hm] at h
    exact h.symm
  have hp (N : DerivedCategory (Sheaf (Scheme.ProEt.topology U) (ModuleCat.{u + 1} A))) :
      bp.unit.app ((pbcFixedScalarExtension (Scheme.ProEt.topology U) φ).obj N) ≫
        (upperStar (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
          ((scalarOpen φ j).inv.app N) =
      (pbcFixedScalarExtension (Scheme.ProEt.topology U) φ).map (ap.unit.app N) ≫ lp.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj N) := by
    have h := unit_mateEquiv_symm ap bp
      ((mateEquiv xp up).symm (TwoSquare.mk _ _ _ _ qp.inv)) N
    have hm := scalar_open_inverse_mate ap bp xp up qp
    change (pbcFixedScalarExtension (Scheme.ProEt.topology U) φ).map (ap.unit.app N) ≫ lp.app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj N) =
      bp.unit.app ((pbcFixedScalarExtension (Scheme.ProEt.topology U) φ).obj N) ≫ (upperStar
      (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
        (((mateEquiv ap bp).symm ((mateEquiv xp up).symm
          (TwoSquare.mk _ _ _ _ qp.inv))).app N) at h
    rw [hm] at h
    exact h.symm
  have h := open_mate_cube ae ap be bp
    (Etale.openScalarExtension φ j) (scalarOpen φ j)
    (mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
      (ModuleCat.{u + 1} A) j).symm
    (mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
      (ModuleCat.{u + 1} B) j).symm
    le lp (pbcComparisonReduction U φ).symm (pbcComparisonReduction X φ).symm
    (Functor.mapDerivedCategorySquareIso
      (site_pullback A j))
    (Functor.mapDerivedCategorySquareIso
      (site_pullback B j))
    he hp (comparison_derived_extension_mate A j) (comparison_derived_extension_mate B j)
    (scalar_pullback_cube φ j) L
  simp only [Iso.symm_hom, Iso.symm_inv] at h
  let eA := mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
    (ModuleCat.{u + 1} A) j
  let eB := mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
    (ModuleCat.{u + 1} B) j
  let SX := pbcFixedScalarExtension (Scheme.ProEt.topology X) φ
  let NX := (comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory
  let J := (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory
  let a := SX.mapIso (eA.app L) ≪≫
    (scalarOpen φ j).app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory.obj L)
  let b := NX.mapIso ((Etale.openScalarExtension φ j).app L) ≪≫
    eB.app ((Etale.scalarExtension φ U).obj L)
  let d := J.mapIso ((pbcComparisonReduction U φ).app L)
  let c := (pbcComparisonReduction X φ).app
    ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj L)
  have hi : d ≪≫ b.symm = a.symm ≪≫ c := by
    apply Iso.ext
    simpa only [d, b, a, c, J, NX, SX, eA, eB, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom,
      Iso.app_inv, Category.assoc] using h
  have hr : a ≪≫ d = c ≪≫ b := by
    calc
      a ≪≫ d = a ≪≫ (d ≪≫ b.symm) ≪≫ b := by simp
      _ = a ≪≫ (a.symm ≪≫ c) ≪≫ b := by rw [hi]
      _ = c ≪≫ b := by simp
  simpa only [d, b, a, c, J, NX, SX, eA, eB, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, Category.assoc] using congrArg Iso.hom hr

/-- Scalar/open composition coherence on the etale site, with the canonical
open compositors. -/
theorem etale_scalar_comp {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {V U X : Scheme.{u}}
    (k : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion k] [IsOpenImmersion j]
    (L : Etale.DerivedCategoryModule A V) :
    (Etale.scalarExtension φ X).map
        ((Etale.mapDerivedCategoryOpenImmersionLowerShriekComp
          (ModuleCat.{u + 1} A) k j).hom.app L) ≫
      (Etale.openScalarExtension φ j).hom.app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) k).mapDerivedCategory.obj L) ≫
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
        ((Etale.openScalarExtension φ k).hom.app L) ≫
      (Etale.mapDerivedCategoryOpenImmersionLowerShriekComp
        (ModuleCat.{u + 1} B) k j).inv.app ((Etale.scalarExtension φ V).obj L) =
    (Etale.openScalarExtension φ (k ≫ j)).hom.app L := by
  exact scalar_composition
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (V.smallEtaleTopology) φ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (U.smallEtaleTopology) φ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (X.smallEtaleTopology) φ))
    (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) k)
    (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
    (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (k ≫ j))
    (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) k)
    (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
    (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) (k ≫ j))
    (Functor.mapDerivedCategorySquareIso (Etale.openRestrictScalarsIso φ k))
    (Functor.mapDerivedCategorySquareIso (Etale.openRestrictScalarsIso φ j))
    (Functor.mapDerivedCategorySquareIso (Etale.openRestrictScalarsIso φ (k ≫ j)))
    (Functor.mapDerivedCategoryNatIso (Etale.upperStarComp (ModuleCat.{u + 1} A) k j) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm)
    (Functor.mapDerivedCategoryNatIso (Etale.upperStarComp (ModuleCat.{u + 1} B) k j) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm).symm
    (Etale.mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A) k j)
    (Etale.mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} B) k j)
    (Iso.ext (Etale.derived_open_comp_conjugate (ModuleCat.{u + 1} A) k j))
    (Iso.ext (Etale.derived_open_comp_conjugate (ModuleCat.{u + 1} B) k j))
    (et_derived_restrict_comp φ k j (et_restrict_comp φ k j)) L

/-- The scalar/open comparison for the identity open is the identity after the
canonical identity identifications. -/
theorem etale_scalar_id {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (X : Scheme.{u})
    (L : Etale.DerivedCategoryModule A X) :
    (Etale.openScalarExtension φ (𝟙 X)).hom.app L ≫
      (Etale.mapDerivedCategoryOpenImmersionLowerShriekId
        (ModuleCat.{u + 1} B) X).hom.app ((Etale.scalarExtension φ X).obj L) =
    (Etale.scalarExtension φ X).map
      ((Etale.mapDerivedCategoryOpenImmersionLowerShriekId
        (ModuleCat.{u + 1} A) X).hom.app L) := by
  rw [etale_identity_normalized B X, etale_identity_normalized A X]
  exact scalar_identity
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ))
    (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X))
    (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) (𝟙 X))
    (Functor.mapDerivedCategorySquareIso (Etale.openRestrictScalarsIso φ (𝟙 X)))
    (Functor.mapDerivedCategoryNatIso (Etale.upperStarId (ModuleCat.{u + 1} A) X) ≪≫
      Functor.mapDerivedCategoryIdIso _)
    (Functor.mapDerivedCategoryNatIso (Etale.upperStarId (ModuleCat.{u + 1} B) X) ≪≫
      Functor.mapDerivedCategoryIdIso _)
    (fun M ↦ exact_identity_square
      (Etale.upperStar (ModuleCat.{u + 1} B) (𝟙 X))
      (Sheaf.restrictScalars X.smallEtaleTopology φ)
      (Etale.upperStar (ModuleCat.{u + 1} A) (𝟙 X))
      (Etale.openRestrictScalarsIso φ (𝟙 X))
      (Etale.upperStarId (ModuleCat.{u + 1} B) X)
      (Etale.upperStarId (ModuleCat.{u + 1} A) X) (et_restrict_id φ X) M) L

end AlgebraicGeometry.ProEtale.OpenScalarSite
