/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.RingedSitePoint
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.Bifunctor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Mathlib.CategoryTheory.PUnit
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainModuleAdjunction
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor

/-! # Total tensor products and module stalks at a topos point -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CategoryTheory.RingedSitePoint

private abbrev point : (Discrete PUnit.{w + 1})ᵒᵖ := Opposite.op ⟨PUnit.unit⟩

private def constant (A : Type*) [Category A] :
    A ⥤ Sheaf (⊥ : GrothendieckTopology (Discrete PUnit.{w + 1})) A :=
  Functor.const _ ⋙ (sheafBotEquivalence A).inverse

private def setEquivalence :
    Sheaf (⊥ : GrothendieckTopology (Discrete PUnit.{w + 1})) (Type w) ≌ Type w where
  functor := sheafToPresheaf _ _ ⋙ (evaluation _ _).obj point
  inverse := constant (Type w)
  unitIso := NatIso.ofComponents (fun F ↦ ObjectProperty.isoMk _ <|
    NatIso.ofComponents (fun U ↦ by
      obtain rfl : U = point := Subsingleton.elim _ _
      exact Iso.refl _) (by
        intro U V f
        obtain rfl : U = point := Subsingleton.elim _ _
        obtain rfl : V = point := Subsingleton.elim _ _
        obtain rfl : f = 𝟙 point := Subsingleton.elim _ _
        simp [constant])) (by
    intro F G f
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    obtain rfl : U = point := Subsingleton.elim _ _
    rfl)
  counitIso := Iso.refl _

private def pointRing (A : CommRingCat.{w}) := (constant CommRingCat.{w}).obj A

private abbrev pointModules (A : CommRingCat.{w}) := SheafOfModules.{w}
  ((sheafCompose ⊥ (forget₂ CommRingCat.{w} RingCat.{w})).obj (pointRing A))

private def moduleConstant (A : CommRingCat.{w}) : ModuleCat.{w} A ⥤ pointModules A where
  obj M := ⟨{ obj := fun _ ↦ M
              map := fun _ ↦ ModuleCat.ofHom LinearMap.id }, Presheaf.isSheaf_bot _⟩
  map f := ⟨{ app := fun _ ↦ f }⟩

private instance (A : CommRingCat.{w}) : (moduleConstant A).Additive where
  map_add := by intros; rfl

private abbrev moduleEval (A : CommRingCat.{w}) : pointModules A ⥤ ModuleCat.{w} A :=
  SheafOfModules.evaluation _ point

private def moduleUnitIso {A : CommRingCat.{w}} (M : pointModules A) :
    M ≅ (moduleConstant A).obj ((moduleEval A).obj M) := by
  let e : M.val ≅ ((moduleConstant A).obj ((moduleEval A).obj M)).val :=
    PresheafOfModules.isoMk (fun U ↦ by
      obtain rfl : U = point := Subsingleton.elim _ _
      exact Iso.refl _) (by
        intro U V g
        obtain rfl : U = point := Subsingleton.elim _ _
        obtain rfl : V = point := Subsingleton.elim _ _
        obtain rfl : g = 𝟙 point := Subsingleton.elim _ _
        ext x
        simp [moduleConstant, moduleEval]
        rfl)
  exact (SheafOfModules.fullyFaithfulForget _).preimageIso e

private def moduleEquivalence (A : CommRingCat.{w}) : pointModules A ≌ ModuleCat.{w} A where
  functor := moduleEval A
  inverse := moduleConstant A
  unitIso := NatIso.ofComponents moduleUnitIso (by
    intro M N f
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    obtain rfl : U = point := Subsingleton.elim _ _
    rfl)
  counitIso := Iso.refl _

private instance (A : CommRingCat.{w}) : (moduleEval A).IsEquivalence :=
  (moduleEquivalence A).isEquivalence_functor

private instance (A : CommRingCat.{w}) : (moduleEval A).Additive where
  map_add := by intros; rfl

private def tensorMap {A : CommRingCat.{w}} (M N : pointModules A) :
    M.val ⊗ N.val ⟶
      (letI := SheafOfModules.monoidalCategory (pointRing A)
       M ⊗ N).val := by
  let := SheafOfModules.monoidalCategory (pointRing A)
  exact (PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app (M.val ⊗ N.val) ≫
    (SheafOfModules.tensorObjIsoSheafification (R := pointRing A) M N).inv.val

private theorem tensorMap_isIso {A : CommRingCat.{w}} (M N : pointModules A) :
    IsIso (tensorMap M N) := by
  let := SheafOfModules.monoidalCategory (pointRing A)
  let adj := PresheafOfModules.sheafificationAdjunction.{w} (𝟙
    ((sheafCompose ⊥ (forget₂ CommRingCat.{w} RingCat.{w})).obj (pointRing A)).obj)
  have : IsIso (adj.unit.app (M.val ⊗ N.val)) :=
    adj.isIso_unit_app_of_iso (X := ⟨M.val ⊗ N.val, Presheaf.isSheaf_bot _⟩) (Iso.refl _)
  have : IsIso (SheafOfModules.tensorObjIsoSheafification
      (R := pointRing A) M N).inv.val :=
    inferInstanceAs (IsIso ((SheafOfModules.forget _).map
      (SheafOfModules.tensorObjIsoSheafification (R := pointRing A) M N).inv))
  change IsIso (adj.unit.app (M.val ⊗ N.val) ≫ _)
  infer_instance

private theorem tensorMap_natural {A : CommRingCat.{w}} {M M' N N' : pointModules A}
    (f : M ⟶ M') (g : N ⟶ N') :
    letI := SheafOfModules.monoidalCategory (pointRing A)
    (f.val ⊗ₘ g.val) ≫ tensorMap M' N' = tensorMap M N ≫ (f ⊗ₘ g).val := by
  let R := pointRing A
  let := SheafOfModules.monoidalCategory R
  let S := PresheafOfModules.sheafification.{w}
    (𝟙 ((sheafCompose ⊥ (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj)
  have h : (f ⊗ₘ g) ≫ (SheafOfModules.tensorObjIsoSheafification (R := R) M' N').hom =
      (SheafOfModules.tensorObjIsoSheafification (R := R) M N).hom ≫
        S.map (f.val ⊗ₘ g.val) := by
    rw [tensorHom_def, Category.assoc,
      SheafOfModules.whiskerLeft_tensorObjIsoSheafification_hom (R := R) M' g,
      ← Category.assoc, SheafOfModules.whiskerRight_tensorObjIsoSheafification_hom (R := R) f N,
      Category.assoc, ← Functor.map_comp, ← tensorHom_def]
  have hi : (SheafOfModules.tensorObjIsoSheafification (R := R) M N).inv ≫
      (f ⊗ₘ g) = S.map (f.val ⊗ₘ g.val) ≫
        (SheafOfModules.tensorObjIsoSheafification (R := R) M' N').inv := by
    rw [← cancel_mono (SheafOfModules.tensorObjIsoSheafification (R := R) M' N').hom]
    simp [Category.assoc, h]
  have hu := (PresheafOfModules.sheafificationAdjunction.{w}
    (𝟙 ((sheafCompose ⊥ (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj)).unit.naturality
      (f.val ⊗ₘ g.val)
  dsimp at hu
  dsimp only [tensorMap]
  rw [← Category.assoc, hu, Category.assoc]
  exact congrArg (fun z ↦ _ ≫ z) (congrArg SheafOfModules.Hom.val hi.symm)

private def tensorIso {A : CommRingCat.{w}} (M N : pointModules A) :
    letI := SheafOfModules.monoidalCategory (pointRing A)
    (moduleEval A).obj M ⊗ (moduleEval A).obj N ≅ (moduleEval A).obj (M ⊗ N) := by
  have := tensorMap_isIso M N
  exact (PresheafOfModules.evaluation _ point).mapIso (asIso (tensorMap M N))

private def evalTensorNatIso (A : CommRingCat.{w}) :
    letI := SheafOfModules.monoidalCategory (pointRing A)
    (((Functor.whiskeringLeft₂ _).obj (moduleEval A)).obj
      (moduleEval A)).obj (curriedTensor _) ≅
      (Functor.postcompose₂.obj (moduleEval A)).obj (curriedTensor _) := by
  let := SheafOfModules.monoidalCategory (pointRing A)
  refine NatIso.ofComponents (fun M ↦ NatIso.ofComponents (fun N ↦ tensorIso M N)
    (fun {N N'} g ↦ ?_)) (fun {M M'} f ↦ ?_)
  · change whiskerLeft (C := ModuleCat A) (M.val.obj point) (g.val.app point) ≫
      (tensorMap M N').app point =
      (tensorMap M N).app point ≫ (M ◁ g).val.app point
    have h := congrArg (fun z ↦ z.app point) (tensorMap_natural (𝟙 M) g)
    simp only [SheafOfModules.id_val, id_tensorHom, PresheafOfModules.comp_app] at h
    exact h
  · apply NatTrans.ext
    funext N
    change whiskerRight (C := ModuleCat A) (f.val.app point) (N.val.obj point) ≫
      (tensorMap M' N).app point =
      (tensorMap M N).app point ≫ (f ▷ N).val.app point
    have h := congrArg (fun z ↦ z.app point) (tensorMap_natural f (𝟙 N))
    simp only [SheafOfModules.id_val, tensorHom_id, PresheafOfModules.comp_app] at h
    exact h

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{w}}
  {p : GeometricMorphism (Type w) (Sheaf J (Type w))}

private def pointInverse (s : RingedSitePoint R p) :
    SheafOfModules.AlgebraicInverseImage
      (p.inverse ⋙ constant (Type w)) R (pointRing s.ring) where
  ringUnderlying := (constant (Type w)).mapIso s.ringUnderlying
  ringAdd T a b z h _ x := s.ringAdd T a b z h x
  ringMul T a b z h _ x := s.ringMul T a b z h x
  ringZero T a h _ x := s.ringZero T a h x
  ringOne T a h _ x := s.ringOne T a h x
  modules := s.modules ⋙ moduleConstant s.ring
  moduleUnderlying := Functor.isoWhiskerRight s.moduleUnderlying (constant (Type w))
  moduleAdd M T a b z h _ x := s.moduleAdd M T a b z h x
  moduleZero M T a h _ x := s.moduleZero M T a h x
  moduleSMul M T a b z h _ x := s.moduleSMul M T a b z h x

private theorem preservesColimits (s : RingedSitePoint R p) : PreservesColimits s.modules := by
  have : PreservesFiniteLimits p.inverse := p.leftExact
  have : (constant (Type w)).IsEquivalence := setEquivalence.isEquivalence_inverse
  have : PreservesFiniteLimits (p.inverse ⋙ constant (Type w)) :=
    comp_preservesFiniteLimits _ _
  let adj : (p.inverse ⋙ constant (Type w)) ⊣ (setEquivalence.functor ⋙ p.direct) :=
    p.adj.comp setEquivalence.symm.toAdjunction
  obtain ⟨V, ⟨hV⟩⟩ := SheafOfModules.CochainInversePairing.inverseImageModuleAdjunction_exists
    R (pointRing s.ring) _ _ adj (pointInverse s)
  have : PreservesColimits (pointInverse s).modules := hV.leftAdjoint_preservesColimits
  have : PreservesColimits ((pointInverse s).modules ⋙ moduleEval s.ring) :=
    comp_preservesColimits _ _
  exact inferInstanceAs (PreservesColimits ((pointInverse s).modules ⋙ moduleEval s.ring))

private theorem moduleTensor (s : RingedSitePoint R p) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients R
    letI := SheafOfModules.monoidalCategory R
    ∃ e : ∀ M N, s.modules.obj (M ⊗ N) ≅ s.modules.obj M ⊗ s.modules.obj N,
      ∀ {M M' N N'} (f : M ⟶ M') (g : N ⟶ N'),
        s.modules.map (f ⊗ₘ g) ≫ (e M' N').hom =
          (e M N).hom ≫ (s.modules.map f ⊗ₘ s.modules.map g) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory (pointRing s.ring)
  have : PreservesFiniteLimits p.inverse := p.leftExact
  have : (constant (Type w)).IsEquivalence := setEquivalence.isEquivalence_inverse
  have : PreservesFiniteLimits (p.inverse ⋙ constant (Type w)) :=
    comp_preservesFiniteLimits _ _
  let adj : (p.inverse ⋙ constant (Type w)) ⊣ (setEquivalence.functor ⋙ p.direct) :=
    p.adj.comp setEquivalence.symm.toAdjunction
  let I := pointInverse s
  obtain ⟨e, hn, _⟩ :=
    SheafOfModules.CochainInversePairing.exists_inverseImageTensorComparison R
      (pointRing s.ring) _ I _ adj
  refine ⟨fun M N ↦ (moduleEval s.ring).mapIso (e M N) ≪≫
    (tensorIso (I.modules.obj M) (I.modules.obj N)).symm, ?_⟩
  intro M M' N N' f g
  have h := congrArg ((moduleEval s.ring).map) (hn f g)
  simp only [Functor.map_comp] at h
  change s.modules.map (f ⊗ₘ g) ≫ (moduleEval s.ring).map (e M' N').hom =
    (moduleEval s.ring).map (e M N).hom ≫
      (moduleEval s.ring).map (I.modules.map f ⊗ₘ I.modules.map g) at h
  dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [Category.assoc]
  rw [← Category.assoc, h, Category.assoc]
  congr 1
  apply (cancel_mono (tensorIso (I.modules.obj M') (I.modules.obj N')).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply (cancel_epi (tensorIso (I.modules.obj M) (I.modules.obj N)).hom).1
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  exact congrArg (fun z ↦ z.app point)
    (tensorMap_natural (I.modules.map f) (I.modules.map g)).symm

/-- Taking a module stalk commutes with the unbounded direct-sum total tensor.
Source: Stacks Project, Cohomology on Sites, Tag 07A4 and Tag 0DEN.
(auxiliary; not a blueprint node)

Proof: encode modules over the stalk ring as constant module sheaves on the
one-object site with bottom topology. The prescribed operation graphs give an
algebraic inverse-image presentation on that site. Apply the ordinary inverse-image
tensor comparison, then evaluate at its sole object; sheafification on the bottom
topology is an equivalence. The module adjunction proves preservation of direct sums.
The resulting natural module comparison therefore induces an isomorphism of total
complexes, commuting with both signed differential components in every degree. -/
theorem tensor (s : RingedSitePoint R p) :
    letI := SheafOfModules.isMonoidal_W_independentCoefficients R
    letI := SheafOfModules.monoidalCategory R
    letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
    letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
    ∀ F K : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ,
      Nonempty (((s.modules.mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mapBifunctor F K (curriedTensor _))) ≅
        CochainComplex.mapBifunctor
          ((s.modules.mapHomologicalComplex (.up ℤ)).obj F)
          ((s.modules.mapHomologicalComplex (.up ℤ)).obj K) (curriedTensor _)) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  have : PreservesColimits s.modules := preservesColimits s
  have : PreservesColimitsOfSize.{0, 0} s.modules := preservesColimitsOfSize_shrink _
  obtain ⟨e, hn⟩ := moduleTensor s
  let t : (Functor.postcompose₂.obj s.modules).obj (curriedTensor _) ≅
      (((Functor.whiskeringLeft₂ _).obj s.modules).obj s.modules).obj (curriedTensor _) :=
    NatIso.ofComponents (fun M ↦ NatIso.ofComponents (fun N ↦ e M N) (by
      intro N N' g
      change s.modules.map (M ◁ g) ≫ (e M N').hom =
        (e M N).hom ≫ (s.modules.obj M ◁ s.modules.map g)
      simpa only [id_tensorHom, Functor.map_id] using hn (𝟙 M) g)) (by
        intro M M' f
        apply NatTrans.ext
        funext N
        change s.modules.map (f ▷ N) ≫ (e M' N).hom =
          (e M N).hom ≫ (s.modules.map f ▷ s.modules.obj N)
        simpa only [tensorHom_id, Functor.map_id] using hn f (𝟙 N))
  intro F K
  exact ⟨asIso (HomologicalComplex.mapBifunctorComparison t.hom (.up ℤ) F K)⟩

end CategoryTheory.RingedSitePoint
