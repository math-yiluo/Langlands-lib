/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.CategoryTheory.RingedExtendedCech
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Adjunction.Additive
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Homology.Localization

/-! # Pullback transports augmented models on flat K-flat representatives

Source: Stacks Project, Cohomology on Sites, Tags 06YY, 0G7E, 06XN.
(blueprint: lem-weil-pbc-ringed-pullback-augmented-models).
-/

@[expose] public section
set_option autoImplicit false
universe u wR wS
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

private theorem transport_augmented_iso
    {A B E : Type*} [Category A] [Category B] [Category E]
    (Q : A ⥤ B) (L : B ⥤ E) (T : A ⥤ E) (τ : Q ⋙ L ⟶ T)
    {X Y Z : A} (a : X ⟶ Z) (b : Y ⟶ Z)
    (e : Q.obj X ≅ Q.obj Y) (he : e.hom ≫ Q.map b = Q.map a)
    [IsIso (τ.app X)] [IsIso (τ.app Y)] :
    ∃ d : T.obj X ≅ T.obj Y, d.hom ≫ T.map b = T.map a := by
  refine ⟨(asIso (τ.app X)).symm ≪≫ L.mapIso e ≪≫ asIso (τ.app Y), ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, Functor.mapIso_hom,
    Category.assoc]
  rw [← τ.naturality b]
  simp only [Functor.comp_map, ← L.map_comp_assoc, he]
  have hn := τ.naturality a
  dsimp only [Functor.comp_map] at hn
  rw [hn, IsIso.inv_hom_id_assoc]

/-- Ringed module pullback carries an augmented derived isomorphism between
flat-term K-flat complexes to the corresponding ordinary pulled-back complexes.
The target of the augmentation need not be K-flat.

Source: Stacks Project, Cohomology on Sites, Tags 06YY, 0G7E, 06XN.
(blueprint: lem-weil-pbc-ringed-pullback-augmented-models).

Proof: compare the given left adjoint with the supplied tensor pullback by uniqueness
of left adjoints. Tensor pullback preserves quasi-isomorphisms between flat-term K-flat
complexes. Transport that property through the comparison. The class of flat-term
K-flat complexes resolves every homotopy-category object, so the resolving-class theorem
constructs a left derived functor, with its comparison invertible on both source
complexes. Apply this derived functor to the augmented isomorphism and compose the
comparison isomorphisms. Naturality at the two augmentation arrows proves the required
equation, without any assumption on their common target. The resolving-class theorem
allows the two derived categories to have independent localization universes. -/
theorem ringed_pullback_augmented_models
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
    [HasDerivedCategory.{wR} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [HasDerivedCategory.{wS} (ringedSiteModules.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))]
    (h : RingedToposMorphism
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (F : ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      ringedSiteModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
    [F.Additive] (hF : F ⊣ h.modules)
    (X Y Z : ringedSiteComplex R) (a : X ⟶ Z) (b : Y ⟶ Z)
    (hX : X.IsKFlatIndependentCoefficients)
    (hfX : ∀ n : ℤ, SheafOfModules.IsFlat (X.X n))
    (hY : Y.IsKFlatIndependentCoefficients)
    (hfY : ∀ n : ℤ, SheafOfModules.IsFlat (Y.X n))
    (e : DerivedCategory.Q.obj X ≅ DerivedCategory.Q.obj Y)
    (he : e.hom ≫ DerivedCategory.Q.map b = DerivedCategory.Q.map a) :
    ∃ d : DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj X) ≅
        DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj Y),
      d.hom ≫ DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map b) =
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map a) := by
  classical
  let A := ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let B := ringedSiteModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
  let H := HomotopyCategory.quotient A (.up ℤ)
  let Fc := F.mapHomologicalComplex (.up ℤ)
  obtain ⟨G, hGadd, hG, _, hGqi⟩ := h.exists_kFlatPullback K J S R
  let := hGadd
  let α := NatIso.mapHomologicalComplex (Adjunction.leftAdjointUniq hF hG) (.up ℤ)
  have hpres {P Q : ringedSiteComplex R} (s : P ⟶ Q)
      (hP : P.IsKFlatIndependentCoefficients) (hfP : ∀ n, SheafOfModules.IsFlat (P.X n))
      (hQ : Q.IsKFlatIndependentCoefficients) (hfQ : ∀ n, SheafOfModules.IsFlat (Q.X n))
      (hs : QuasiIso s) : QuasiIso (Fc.map s) := by
    have ht := hGqi P Q s
      ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).1 hP) hfP
      ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat Q).1 hQ) hfQ hs
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (α.app P) (α.app Q) (α.hom.naturality s).symm)).2 ht
  let W : Set (HomotopyCategory A (.up ℤ)) :=
    {T | ∃ P : ringedSiteComplex R, H.obj P = T ∧
      P.IsKFlatIndependentCoefficients ∧ ∀ n : ℤ, SheafOfModules.IsFlat (P.X n)}
  have hres : ∀ T : HomotopyCategory A (.up ℤ),
      ∃ (T' : HomotopyCategory A (.up ℤ)) (s : T' ⟶ T),
        T' ∈ W ∧ HomotopyCategory.quasiIso A (.up ℤ) s := by
    intro T
    obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective T
    obtain ⟨Q, q, hQ, hfQ, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients P
    exact ⟨H.obj Q, H.map q, ⟨Q, rfl, hQ, hfQ⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff q).2 hq⟩
  let T := F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  have hinv : ∀ (P Q : HomotopyCategory A (.up ℤ)) (s : P ⟶ Q),
      P ∈ W → Q ∈ W → HomotopyCategory.quasiIso A (.up ℤ) s → IsIso (T.map s) := by
    intro P Q s hP hQ hs
    obtain ⟨P, rfl, hP, hfP⟩ := hP
    obtain ⟨Q, rfl, hQ, hfQ⟩ := hQ
    obtain ⟨s, rfl⟩ := H.map_surjective s
    have hq := (HomotopyCategory.quotient_map_mem_quasiIso_iff s).1 hs
    have ht := hpres s hP hfP hQ hfQ hq
    change IsIso (DerivedCategory.Qh.map ((F.mapHomotopyCategory (.up ℤ)).map (H.map s)))
    rw [Functor.mapHomotopyCategory_map]
    exact Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso B (.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff (Fc.map s)).2 ht)
  obtain ⟨_, LF, ε, _, _, hε⟩ :=
    Functor.leftDerived_from_resolvingClass A (DerivedCategory B) T W hres hinv
  let τ : DerivedCategory.Q ⋙ LF ⟶ Fc ⋙ DerivedCategory.Q := Functor.whiskerLeft H ε
  have : IsIso (τ.app X) := hε (H.obj X) ⟨X, rfl, hX, hfX⟩
  have : IsIso (τ.app Y) := hε (H.obj Y) ⟨Y, rfl, hY, hfY⟩
  exact transport_augmented_iso DerivedCategory.Q LF (Fc ⋙ DerivedCategory.Q) τ a b e he

end CategoryTheory
