/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomDataSupplement
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.ScalarHomOrdinaryTensorComparison

/-! # The ordinary normalized scalar tensor comparison

Source: Stacks Project, Modules on Sites, Tags 03EL and 0GMW.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped ChangeOfRings
namespace SheafOfModules.ScalarHomOrdinary
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}}
attribute [local instance] isMonoidal_W_independentCoefficients
attribute [local irreducible] monoidalCategory

private noncomputable def extensionPresheafIso (a : R ⟶ S) (M : scalarModules J R) :
    changeOfRingsPresheaf a M ≅ changeOfRingsPresheafOfUniverses a M :=
  PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by
      intro V W i
      apply ModuleCat.hom_ext
      ext t
      induction t using TensorProduct.inductionOn with
      | add z z' hz hz' => simp only [map_add, hz, hz']
      | tmul s x =>
        change changeOfRingsMap a M i (s ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x) =
          changeOfRingsMapOfUniverses a M i (s ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x)
        exact (Classical.choose_spec (exists_changeOfRingsMap a M i) s x).trans
          (changeOfRingsMap_tmulOfUniverses a M i s x).symm)

private noncomputable def extensionIso (a : R ⟶ S) (M : scalarModules J R) :
    changeOfRings a M ≅ changeOfRingsOfUniverses a M :=
  (PresheafOfModules.sheafification (𝟙 _)).mapIso (extensionPresheafIso a M)

private noncomputable def tensorIsoSite (A : Sheaf J CommRingCat.{r})
    (M N : scalarModules J A) :
    (monoidalCategory A).tensorObj M N ≅ (siteSheafTensorRight N).obj M :=
  tensorObjIsoSheafification M N ≪≫
    (PresheafOfModules.sheafification (𝟙 _)).mapIso
      ((siteTensorRightIso A N.val).app M.val).symm

private theorem tensorIsoSite_pure (A : Sheaf J CommRingCat.{r})
    (M N : scalarModules J A) (V : Cᵒᵖ) (x : M.val.obj V) (y : N.val.obj V) :
    (tensorIsoSite A M N).hom.val.app V (pure A M N V x y) =
      siteSheafTensorTmul M N V x y := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A).obj)
  let q := ((siteTensorRightIso A N.val).app M.val).inv
  have hn := adj.unit.naturality q
  have hh := congrArg (fun f ↦ f.app V (x ⊗ₜ[A.obj.obj V] y)) hn
  dsimp only [tensorIsoSite, pure, Iso.trans_hom]
  change ((PresheafOfModules.sheafification (𝟙 _)).map q).val.app V
    ((tensorObjIsoSheafification M N).hom.val.app V
      ((tensorObjIsoSheafification M N).inv.val.app V
        ((adj.unit.app (M.val ⊗ N.val)).app V (x ⊗ₜ[A.obj.obj V] y)))) = _
  have hi := congrArg (fun f ↦ f.val.app V
    ((adj.unit.app (M.val ⊗ N.val)).app V (x ⊗ₜ[A.obj.obj V] y)))
    (tensorObjIsoSheafification M N).inv_hom_id
  change (tensorObjIsoSheafification M N).hom.val.app V
    ((tensorObjIsoSheafification M N).inv.val.app V _) = _ at hi
  rw [hi]
  exact hh.symm

private noncomputable def extensionFunctor (a : R ⟶ S) :
    scalarModules J R ⥤ scalarModules J S where
  obj M := changeOfRingsOfUniverses a M
  map f := changeOfRingsHomOfUniverses a _ f
  map_id M := scalarExtension_map_id a M
  map_comp f g := scalarExtension_map_comp a f g

omit [EssentiallySmall.{r} C] in
private theorem extensionIso_unit (a : R ⟶ S) (M : scalarModules J R)
    (V : Cᵒᵖ) (x : M.val.obj V) :
    (extensionIso a M).hom.val.app V
      (((PresheafOfModules.sheafificationAdjunction (𝟙 _)).unit.app
        (changeOfRingsPresheaf a M)).app V
          ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x)) =
      scalarExtensionSection a M V 1 x := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj S).obj)
  dsimp only [extensionIso, Functor.mapIso_hom]
  have hn := adj.unit.naturality (extensionPresheafIso a M).hom
  exact (congrArg (fun f ↦ f.app V
    ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] x)) hn).symm

private theorem pure_map (A : Sheaf J CommRingCat.{r})
    {M M' N N' : scalarModules J A} (f : M ⟶ M') (g : N ⟶ N')
    (V : Cᵒᵖ) (x : M.val.obj V) (y : N.val.obj V) :
    ((monoidalCategory A).tensorHom f g).val.app V (pure A M N V x y) =
      pure A M' N' V (f.val.app V x) (g.val.app V y) := by
  let := monoidalCategory A
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A).obj)
  have ht : (f ⊗ₘ g) ≫ (tensorObjIsoSheafification M' N').hom =
      (tensorObjIsoSheafification M N).hom ≫
        (PresheafOfModules.sheafification (𝟙 _)).map (f.val ⊗ₘ g.val) := by
    let sh := PresheafOfModules.sheafification (𝟙
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A).obj)
    let ε := asIso adj.counit
    have hf : f ≫ (ε.app M').inv = (ε.app M).inv ≫ sh.map f.val :=
      ε.inv.naturality f
    have hg : g ≫ (ε.app N').inv = (ε.app N).inv ≫ sh.map g.val :=
      ε.inv.naturality g
    change (f ⊗ₘ g) ≫ ((ε.app M').inv ⊗ₘ (ε.app N').inv) ≫
        Functor.LaxMonoidal.μ sh M'.val N'.val =
      ((ε.app M).inv ⊗ₘ (ε.app N).inv) ≫
        Functor.LaxMonoidal.μ sh M.val N.val ≫ sh.map (f.val ⊗ₘ g.val)
    rw [← Functor.LaxMonoidal.μ_natural]
    simp only [← Category.assoc, tensorHom_comp_tensorHom, hf, hg]
  have hi : (tensorObjIsoSheafification M N).inv ≫ (f ⊗ₘ g) =
      (PresheafOfModules.sheafification (𝟙 _)).map (f.val ⊗ₘ g.val) ≫
        (tensorObjIsoSheafification M' N').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← ht, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hh := congrArg (fun h ↦ h.val.app V
    ((adj.unit.app (M.val ⊗ N.val)).app V (x ⊗ₜ[A.obj.obj V] y))) hi
  have hη := congrArg (fun h ↦ h.app V (x ⊗ₜ[A.obj.obj V] y))
    (adj.unit.naturality (f.val ⊗ₘ g.val))
  exact hh.trans (congrArg ((tensorObjIsoSheafification M' N').inv.val.app V) hη.symm)

private theorem pure_hom_ext (A : Sheaf J CommRingCat.{r})
    (M N H : scalarModules J A)
    {f g : (monoidalCategory A).tensorObj M N ⟶ H}
    (h : ∀ V x y, f.val.app V (pure A M N V x y) =
      g.val.app V (pure A M N V x y)) : f = g := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A).obj)
  apply (cancel_epi (tensorObjIsoSheafification M N).inv).mp
  apply (adj.homEquiv (M.val ⊗ N.val) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  exact h V x y

variable [HasDerivedCategory.{w} (scalarModules J R)]
  [HasDerivedCategory.{w} (scalarModules J S)] (a : R ⟶ S) (s : ScalarDerivedPair a)

private noncomputable def extensionPairIso (M : scalarModules J R) :
    s.extension.obj M ≅ changeOfRingsOfUniverses a M :=
  eqToIso (s.extension_obj M) ≪≫ extensionIso a M

private theorem extensionPairIso_unit (M : scalarModules J R) (V : Cᵒᵖ)
    (x : M.val.obj V) :
    (extensionPairIso a s M).hom.val.app V
      (((s.ordinaryAdjunction.unit.app M).val.app V) x) =
      scalarExtensionSection a M V 1 x := by
  change (extensionIso a M).hom.val.app V
    ((eqToHom (s.extension_obj M)).val.app V
      (((s.ordinaryAdjunction.unit.app M).val.app V) x)) = _
  rw [s.ordinaryUnit]
  exact extensionIso_unit a M V x

private noncomputable def ordinaryTensorIso
    (k : ScalarExtensionTensorCore R S a) (M N : scalarModules J R) :
    s.extension.obj ((monoidalCategory R).tensorObj M N) ≅
      (monoidalCategory S).tensorObj (s.extension.obj M) (s.extension.obj N) :=
  extensionPairIso a s _ ≪≫ (extensionFunctor a).mapIso (tensorIsoSite R M N) ≪≫
    k.tensorComparison M N ≪≫
      (tensorIsoSite S (changeOfRingsOfUniverses a M) (changeOfRingsOfUniverses a N)).symm ≪≫
        @tensorIso _ _ (monoidalCategory S) _ _ _ _
          (extensionPairIso a s M).symm (extensionPairIso a s N).symm

private theorem extensionPairIso_inv_unit (M : scalarModules J R) (V : Cᵒᵖ)
    (x : M.val.obj V) :
    (extensionPairIso a s M).inv.val.app V (scalarExtensionSection a M V 1 x) =
      ((s.ordinaryAdjunction.unit.app M).val.app V) x := by
  rw [← extensionPairIso_unit a s M V x]
  exact congrArg (fun f ↦ f.val.app V
    (((s.ordinaryAdjunction.unit.app M).val.app V) x))
      (extensionPairIso a s M).hom_inv_id

private theorem tensorIsoSite_inv_pure (A : Sheaf J CommRingCat.{r})
    (M N : scalarModules J A) (V : Cᵒᵖ) (x : M.val.obj V) (y : N.val.obj V) :
    (tensorIsoSite A M N).inv.val.app V (siteSheafTensorTmul M N V x y) =
      pure A M N V x y := by
  rw [← tensorIsoSite_pure A M N V x y]
  exact congrArg (fun f ↦ f.val.app V (pure A M N V x y))
    (tensorIsoSite A M N).hom_inv_id

private theorem ordinaryTensorIso_unit
    (k : ScalarExtensionTensorCore R S a) (M N : scalarModules J R)
    (V : Cᵒᵖ) (x : M.val.obj V) (y : N.val.obj V) :
    (ordinaryTensorIso a s k M N).hom.val.app V
      (((s.ordinaryAdjunction.unit.app _).val.app V) (pure R M N V x y)) =
    pure S _ _ V (((s.ordinaryAdjunction.unit.app M).val.app V) x)
      (((s.ordinaryAdjunction.unit.app N).val.app V) y) := by
  change ((monoidalCategory S).tensorHom (extensionPairIso a s M).inv
    (extensionPairIso a s N).inv).val.app V
    ((tensorIsoSite S _ _).inv.val.app V
      ((k.tensorComparison M N).hom.val.app V
        ((changeOfRingsHomOfUniverses a _ (tensorIsoSite R M N).hom).val.app V
          ((extensionPairIso a s _).hom.val.app V _)))) = _
  rw [extensionPairIso_unit, scalarExtension_map_tmul, tensorIsoSite_pure,
    k.tensor_tmul, tensorIsoSite_inv_pure, pure_map,
    extensionPairIso_inv_unit, extensionPairIso_inv_unit]

private theorem extendedTensor_hom_ext (M N : scalarModules J R)
    (H : scalarModules J S)
    {f g : s.extension.obj ((monoidalCategory R).tensorObj M N) ⟶ H}
    (h : ∀ V x y, f.val.app V
        (((s.ordinaryAdjunction.unit.app _).val.app V) (pure R M N V x y)) =
      g.val.app V (((s.ordinaryAdjunction.unit.app _).val.app V) (pure R M N V x y))) :
    f = g := by
  apply (s.ordinaryAdjunction.homEquiv _ H).injective
  apply pure_hom_ext R M N ((scalarRestriction a).obj H)
  intro V x y
  exact h V x y

/-- Scalar extension preserves the sheaf tensor product with its unit normalization.
Source: Stacks Project, Modules on Sites, Tag 03EL, and Tag 0GMW for sheafification.
(blueprint: lem-sfb-scalar-ordinary-tensor-comparison).

Proof: transport the existing binary scalar-extension tensor core along its identity
sectionwise identification with the ordinary extension presheaf. Identify both sheaf
tensors with their sheafifications; their unit formulas identify all pure sections.
Naturality follows from the extension adjunction and generation of tensors by pure
sections. No flatness hypothesis is required. -/
theorem scalarOrdinaryTensorComparison_exists :
    ∃ e : ∀ M N : scalarModules J R,
      s.extension.obj ((monoidalCategory R).tensorObj M N) ≅
        (monoidalCategory S).tensorObj (s.extension.obj M) (s.extension.obj N),
      (∀ {M M' N N' : scalarModules J R} (f : M ⟶ M') (g : N ⟶ N'),
        s.extension.map ((monoidalCategory R).tensorHom f g) ≫ (e M' N').hom =
          (e M N).hom ≫ (monoidalCategory S).tensorHom
            (s.extension.map f) (s.extension.map g)) ∧
      ∀ M N V x y, (e M N).hom.val.app V
        (((s.ordinaryAdjunction.unit.app _).val.app V) (pure R M N V x y)) =
      pure S _ _ V (((s.ordinaryAdjunction.unit.app M).val.app V) x)
        (((s.ordinaryAdjunction.unit.app N).val.app V) y) := by
  classical
  obtain ⟨k⟩ := exists_scalarExtensionTensorCore R S a
  let e := ordinaryTensorIso a s k
  have he := ordinaryTensorIso_unit a s k
  refine ⟨e, ?_, he⟩
  intro M M' N N' f g
  apply extendedTensor_hom_ext a s M N
  intro V x y
  have hu (P Q : scalarModules J R) (h : P ⟶ Q) (z : P.val.obj V) :
      (s.extension.map h).val.app V (((s.ordinaryAdjunction.unit.app P).val.app V) z) =
        ((s.ordinaryAdjunction.unit.app Q).val.app V) (h.val.app V z) :=
    (congrArg (fun k ↦ k.val.app V z) (s.ordinaryAdjunction.unit.naturality h)).symm
  change (e M' N').hom.val.app V
      ((s.extension.map ((monoidalCategory R).tensorHom f g)).val.app V _) =
    ((monoidalCategory S).tensorHom (s.extension.map f) (s.extension.map g)).val.app V
      ((e M N).hom.val.app V _)
  rw [hu, pure_map, he, he, pure_map, hu, hu]

end SheafOfModules.ScalarHomOrdinary
