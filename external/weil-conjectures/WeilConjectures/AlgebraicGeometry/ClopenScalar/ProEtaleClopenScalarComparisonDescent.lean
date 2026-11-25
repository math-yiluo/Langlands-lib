/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClopenScalar.ProEtaleClopenDerivedScalarData
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement
import WeilConjectures.AlgebraicGeometry.ClopenScalar.ProEtaleClopenOrdinaryScalarComparison

/-! # Normalized clopen scalar comparison

Source: Stacks Project, Tags 06YY and 0D6D.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t u w
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules SheafOfModules.SuccessiveDerivedQuotient
namespace AlgebraicGeometry.Scheme.ProEt.ClopenScalar
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] ClopenLocalization.modulesAbelian ClopenLocalization.hasDerived
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_hasSheafify
  AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective

universe a₁ b₁ a₂ b₂ d₁

private noncomputable def cochainRepresentativeWhiskering
    {A : Type a₁} [Category.{b₁} A] [Abelian A] [HasDerivedCategory.{d₁} A]
    (good : CochainComplex A ℤ → Prop)
    (res : ∀ K, ∃ (L : CochainComplex A ℤ) (p : L ⟶ K), good L ∧ QuasiIso p)
    (E : Type a₂) [Category.{b₂} E] :
    ((Functor.whiskeringLeft _ _ E).obj
      (ObjectProperty.ι good ⋙ DerivedCategory.Q)).FullyFaithful := by
  let q := HomotopyCategory.quotient A (.up ℤ)
  let P : ObjectProperty (CochainComplex A ℤ) := good
  let S : ObjectProperty (HomotopyCategory A (.up ℤ)) := fun X ↦ good X.as
  let f := S.lift (P.ι ⋙ q) (fun X ↦ X.property)
  have : f.Full := ⟨by
    intro X Y g
    obtain ⟨a, ha⟩ := q.map_surjective g.hom
    refine ⟨ObjectProperty.homMk a, ?_⟩
    exact ObjectProperty.hom_ext _ ha⟩
  have : f.EssSurj := ⟨by
    intro X
    obtain ⟨Y, hy⟩ := HomotopyCategory.quotient_obj_surjective X.obj
    refine ⟨⟨Y, ?_⟩, ⟨ObjectProperty.isoMk S (eqToIso hy)⟩⟩
    change S (q.obj Y)
    rw [hy]
    exact X.property⟩
  have hres : ∀ X : HomotopyCategory A (.up ℤ),
      ∃ (Y : S.FullSubcategory) (s : Y.obj ⟶ X), HomotopyCategory.quasiIso A (.up ℤ) s := by
    intro X
    obtain ⟨L, p, hL, hp⟩ := res X.as
    exact ⟨⟨q.obj L, hL⟩, q.map p,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff p).2 hp⟩
  have : (S.ι ⋙ DerivedCategory.Qh).IsLocalization
      ((HomotopyCategory.quasiIso A (.up ℤ)).inverseImage S.ι) :=
    CategoryTheory.restriction_localization _ _ S hres
  let ff := (Localization.fullyFaithfulWhiskeringLeft (S.ι ⋙ DerivedCategory.Qh)
    ((HomotopyCategory.quasiIso A (.up ℤ)).inverseImage S.ι) E).comp
      (CategoryTheory.fullyFaithfulWhiskeringOfFullEssSurj f E)
  exact ff.ofIso ((Functor.whiskeringLeft _ _ E).mapIso
    (Functor.isoWhiskerLeft P.ι (DerivedCategory.quotientCompQhIso A)))

attribute [local irreducible] computation SheafOfModules.monoidalCategory
  HasDerivedCategory.standard Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors

private theorem descendComparison
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{d₁} A] [HasDerivedCategory.{d₁} B]
    [HasDerivedCategory.{d₁} C] [HasDerivedCategory.{d₁} D]
    (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (N : C ⥤ D) [N.Additive] [PreservesFiniteLimits N] [PreservesFiniteColimits N]
    (E : A ⥤ C) [E.Additive] (F : B ⥤ D) [F.Additive]
    (T : DerivedCategory A ⥤ DerivedCategory C)
    (U : DerivedCategory B ⥤ DerivedCategory D)
    (ε : DerivedCategory.Q ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (δ : DerivedCategory.Q ⋙ U ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (good : CochainComplex A ℤ → Prop)
    (res : ∀ K, ∃ (P : CochainComplex A ℤ) (f : P ⟶ K), good P ∧ QuasiIso f)
    (hε : ∀ P, good P → IsIso (ε.app P))
    (hδ : ∀ P, good P → IsIso (δ.app ((L.mapHomologicalComplex (.up ℤ)).obj P)))
    (c : E ⋙ N ≅ L ⋙ F) :
    ∃ e : T ⋙ N.mapDerivedCategory ≅ L.mapDerivedCategory ⋙ U,
      (∀ P, good P → e.hom.app (DerivedCategory.Q.obj P) ≫
        U.map (L.mapDerivedCategoryFactors.hom.app P) ≫
          δ.app ((L.mapHomologicalComplex (.up ℤ)).obj P) =
        N.mapDerivedCategory.map (ε.app P) ≫
          N.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app P)) ∧
      ∀ e' : T ⋙ N.mapDerivedCategory ⟶ L.mapDerivedCategory ⋙ U,
        (∀ P, good P → e'.app (DerivedCategory.Q.obj P) ≫
          U.map (L.mapDerivedCategoryFactors.hom.app P) ≫
            δ.app ((L.mapHomologicalComplex (.up ℤ)).obj P) =
          N.mapDerivedCategory.map (ε.app P) ≫
            N.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app P)) →
        e' = e.hom := by
  let P : ObjectProperty (CochainComplex A ℤ) := good
  let l := P.ι ⋙ DerivedCategory.Q
  let EC := E.mapHomologicalComplex (.up ℤ)
  let LC := L.mapHomologicalComplex (.up ℤ)
  let FC := F.mapHomologicalComplex (.up ℤ)
  let H := LC ⋙ FC ⋙ (DerivedCategory.Q : CochainComplex D ℤ ⥤ _)
  let a : DerivedCategory.Q ⋙ (T ⋙ N.mapDerivedCategory) ⟶ H :=
    Functor.whiskerRight ε N.mapDerivedCategory ≫
      Functor.whiskerLeft EC N.mapDerivedCategoryFactors.hom ≫
      Functor.whiskerRight (NatIso.mapHomologicalComplex c (.up ℤ)).hom DerivedCategory.Q
  let b : DerivedCategory.Q ⋙ (L.mapDerivedCategory ⋙ U) ⟶ H :=
    Functor.whiskerRight L.mapDerivedCategoryFactors.hom U ≫ Functor.whiskerLeft LC δ
  let a' : l ⋙ (T ⋙ N.mapDerivedCategory) ⟶ P.ι ⋙ H := Functor.whiskerLeft P.ι a
  let b' : l ⋙ (L.mapDerivedCategory ⋙ U) ⟶ P.ι ⋙ H := Functor.whiskerLeft P.ι b
  have (K : P.FullSubcategory) : IsIso (a'.app K) := by
    have hK : IsIso (ε.app (P.ι.obj K)) := hε K.obj K.property
    dsimp only [a', a, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
    infer_instance
  have (K : P.FullSubcategory) : IsIso (b'.app K) := by
    have hK : IsIso (δ.app (LC.obj (P.ι.obj K))) := hδ K.obj K.property
    dsimp only [b', b, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
    infer_instance
  have : IsIso a' := NatIso.isIso_of_isIso_app a'
  have : IsIso b' := NatIso.isIso_of_isIso_app b'
  let ff := cochainRepresentativeWhiskering good res (DerivedCategory D)
  let e := ff.preimageIso
    (show ((Functor.whiskeringLeft _ _ _).obj l).obj (T ⋙ N.mapDerivedCategory) ≅
      ((Functor.whiskeringLeft _ _ _).obj l).obj (L.mapDerivedCategory ⋙ U) from
      asIso a' ≪≫ (asIso b').symm)
  have he : Functor.whiskerLeft l e.hom ≫ b' = a' := by
    rw [show Functor.whiskerLeft l e.hom =
      (asIso a' ≪≫ (asIso b').symm).hom from ff.map_preimage _]
    simp
  refine ⟨e, fun K hK ↦ NatTrans.congr_app he ⟨K, hK⟩, ?_⟩
  intro e' he'
  apply ff.map_injective
  apply (cancel_mono b').1
  ext K
  exact (he' K.obj K.property).trans (NatTrans.congr_app he K).symm

end AlgebraicGeometry.Scheme.ProEt.ClopenScalar
