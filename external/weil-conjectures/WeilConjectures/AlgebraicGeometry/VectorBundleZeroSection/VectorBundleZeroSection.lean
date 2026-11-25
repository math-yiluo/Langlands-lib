/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.QuasiCoherentSymmetricAlgebraCore
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.QuasiCoherentSymmetricAlgebraAffine
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Topology.Sheaves.Functors
public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.SymmetricAlgebraSheafConstruction

/-!
# The vector bundle Spec Sym(F), its augmentation and zero section

Source: blueprint, `sec-smooth-purity/sk-prop-an`, order 1968;
Stacks Project, Constructions, Tags 01M2, 01LW and 01LX
(blueprint: proposition-purity-vector-bundles).

The relative-spectrum anti-equivalence is the one characterized by its structure-algebra
functor in `affine_morphism_relative_spec`. Its inverse determines the bundle up to the
unique algebra-compatible isomorphism. The augmentation is chosen from a unique extension
of the zero linear map, and the zero section is its fully faithful inverse image.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

noncomputable section

namespace AlgebraicGeometry.VectorBundleZeroSection

/-- The concrete structure-algebra functor, with sectionwise pullback on morphisms.
Source: Stacks Tag 01LX (blueprint: proposition-purity-vector-bundles). -/
def structureAlgebraFunctor (S : Scheme.{u}) :
    (ObjectProperty.FullSubcategory (fun Y : Over S ↦ IsAffineHom Y.hom))ᵒᵖ ⥤
      ObjectProperty.FullSubcategory
        (fun A : S.CommAlgebraSheaf ↦ A.toModule.IsQuasicoherent) := by
  refine {
    obj := fun Y ↦ ⟨Under.mk (⟨Y.unop.obj.hom.c⟩ : S.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat.{u} Y.unop.obj.hom.base).obj
          Y.unop.obj.left.sheaf), (affine_morphism_relative_spec S).1
      Y.unop.obj.hom Y.unop.property⟩
    map := fun {Y Y'} h ↦ ⟨Under.homMk ⟨{
      app := fun V ↦ h.unop.hom.left.appLE (Y.unop.obj.hom ⁻¹ᵁ V.unop)
        (Y'.unop.obj.hom ⁻¹ᵁ V.unop)
        (by rw [← Over.w h.unop.hom, Scheme.Hom.comp_preimage])
      naturality := ?_ }⟩ ?_⟩
    map_id := ?_
    map_comp := ?_ }
  · intro U V i
    change Y.unop.obj.left.presheaf.map
        ((Opens.map Y.unop.obj.hom.base).map i.unop).op ≫ _ = _ ≫
      Y'.unop.obj.left.presheaf.map ((Opens.map Y'.unop.obj.hom.base).map i.unop).op
    simp only [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
  · apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    change Y.unop.obj.hom.app V.unop ≫ h.unop.hom.left.appLE _ _ _ =
      Y'.unop.obj.hom.app V.unop
    rw [← Scheme.Hom.comp_appLE]
    exact (Scheme.Hom.congr_app (Over.w h.unop.hom).symm V.unop).symm
  · intro Y
    apply InducedCategory.hom_ext
    apply StructuredArrow.hom_ext
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    change Scheme.Hom.appLE (𝟙 Y.unop.obj.left) _ _ _ = 𝟙 _
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_base, Scheme.Hom.id_app,
      homOfLE_refl, op_id, Category.id_comp]
    exact CategoryTheory.Functor.map_id _ _
  · intro Y Y' Y'' h k
    apply InducedCategory.hom_ext
    apply StructuredArrow.hom_ext
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    change (k.unop.hom.left ≫ h.unop.hom.left).appLE _ _ _ =
      h.unop.hom.left.appLE _ _ _ ≫ k.unop.hom.left.appLE _ _ _
    rw [Scheme.Hom.appLE_comp_appLE]

/-- The structure-algebra functor is an equivalence. Source: Stacks Tag 01LX
(blueprint: proposition-purity-vector-bundles).
Proof: the relative-spectrum theorem provides an equivalence whose object and morphism
characterizations give a natural isomorphism to this concrete functor. -/
theorem structureAlgebraFunctor_isEquivalence (S : Scheme.{u}) :
    (structureAlgebraFunctor S).IsEquivalence := by
  obtain ⟨E, hobj, ρ, hmap, _⟩ := (affine_morphism_relative_spec S).2
  let η : E.functor ≅ structureAlgebraFunctor S :=
    NatIso.ofComponents (fun Y ↦ ObjectProperty.isoMk _ (eqToIso (hobj Y.unop))) (by
      intro Y Y' f
      apply InducedCategory.hom_ext
      apply StructuredArrow.hom_ext
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      have htransport {C D : TopCat.Sheaf CommRingCat.{u} S} (e : C = D) :
          (eqToHom e).hom.app U =
            eqToHom (congrArg (fun G ↦ G.obj.obj U) e) := by cases e; rfl
      change (E.functor.map f).hom.right.hom.app U ≫
        (eqToHom (hobj Y'.unop)).right.hom.app U =
        (eqToHom (hobj Y.unop)).right.hom.app U ≫
          f.unop.hom.left.appLE _ _ _
      erw [hmap Y'.unop Y.unop f.unop U.unop]
      simp only [Under.eqToHom_right, htransport, Category.assoc, eqToHom_trans,
        eqToHom_refl, Category.comp_id])
  exact Functor.isEquivalence_of_iso η

/-- The relative-spectrum equivalence with its concrete structure-algebra functor.
Source: Stacks Tag 01LX (blueprint: proposition-purity-vector-bundles). -/
def antiEquivalence (S : Scheme.{u}) :
    (ObjectProperty.FullSubcategory (fun Y : Over S ↦ IsAffineHom Y.hom))ᵒᵖ ≌
      ObjectProperty.FullSubcategory
        (fun A : S.CommAlgebraSheaf ↦ A.toModule.IsQuasicoherent) := by
  letI := structureAlgebraFunctor_isEquivalence S
  exact (structureAlgebraFunctor S).asEquivalence

/-- The base itself as an affine scheme over itself, Stacks Tag 01LX
(blueprint: proposition-purity-vector-bundles). -/
def baseObject (S : Scheme.{u}) :
    ObjectProperty.FullSubcategory (fun Y : Over S ↦ IsAffineHom Y.hom) :=
  ⟨Over.mk (𝟙 S), inferInstanceAs (IsAffineHom (𝟙 S))⟩

/-- The constructed symmetric algebra, with the quasi-coherence provided by the affine
comparison. Source: Stacks Tag 01CL (blueprint: proposition-purity-vector-bundles). -/
def algebraObject (S : Scheme.{u}) (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] :
    ObjectProperty.FullSubcategory
      (fun A : S.CommAlgebraSheaf ↦ A.toModule.IsQuasicoherent) := by
  letI := SheafOfModules.IsFiniteLocallyFreeOfRank.isLocallyFree F d
  exact ⟨SymmetricAlgebraSheaf.algebra F,
    (quasiCoherentSymmetricAlgebra_affine_comparison S F).1⟩

/-- The relative affine scheme Spec_S Sym(F) as an object over S.
Source: Stacks Tag 01M2 (blueprint: proposition-purity-vector-bundles). -/
def over (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] :
    ObjectProperty.FullSubcategory (fun Y : Over S ↦ IsAffineHom Y.hom) :=
  ((antiEquivalence S).inverse.obj (algebraObject S d F)).unop

/-- The total space of the vector bundle of constant rank d.
Source: Stacks Tag 01M2 (blueprint: proposition-purity-vector-bundles). -/
def scheme (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] : Scheme.{u} :=
  (over S d F).obj.left

/-- The structural projection of Spec_S Sym(F).
Source: Stacks Tag 01M2 (blueprint: proposition-purity-vector-bundles). -/
def π (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] : scheme S d F ⟶ S :=
  (over S d F).obj.hom

/-- The unique algebra morphism to O_S killing the degree-one generators.
Source: Stacks Tag 01M2 (blueprint: proposition-purity-vector-bundles). -/
def augmentation (S : Scheme.{u}) (F : S.Modules) :
    SymmetricAlgebraSheaf.algebra F ⟶ Under.mk (𝟙 S.sheaf) :=
  (exists_quasiCoherentSymmetricAlgebra_core S F (Under.mk (𝟙 S.sheaf)) 0).exists.choose

/-- The same zero-generator extension into the structure algebra of the identity S-scheme.
This is the augmentation transported to the anti-equivalence's chosen base object.
Source: Stacks Tags 01M2 and 01LX (blueprint: proposition-purity-vector-bundles). -/
def augmentationToBase (S : Scheme.{u}) (F : S.Modules) :
    SymmetricAlgebraSheaf.algebra F ⟶
      ((antiEquivalence S).functor.obj (op (baseObject S))).obj :=
  (exists_quasiCoherentSymmetricAlgebra_core S F
    ((antiEquivalence S).functor.obj (op (baseObject S))).obj 0).exists.choose

/-- The zero section: the fully faithful inverse image of the augmentation, after the
counit identifies the bundle's structure algebra with Sym(F).
Source: Stacks Tag 01M2 (blueprint: proposition-purity-vector-bundles). -/
def zero (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] : S ⟶ scheme S d F :=
  ((antiEquivalence S).functor.preimage
    (((antiEquivalence S).counitIso.app (algebraObject S d F)).hom ≫
    (ObjectProperty.homMk (augmentationToBase S F)))).unop.hom.left

/-- The canonical symmetric-algebra identification with the direct-image structure algebra.
Source: Stacks Tag 01LX (blueprint: proposition-purity-vector-bundles). -/
def algebraIso (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] :
    SymmetricAlgebraSheaf.algebra F ≅
      Under.mk (⟨(π S d F).c⟩ : S.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat.{u} (π S d F).base).obj
          (scheme S d F).sheaf) :=
  ((ObjectProperty.ι (fun A : S.CommAlgebraSheaf ↦ A.toModule.IsQuasicoherent)).mapIso
    ((antiEquivalence S).counitIso.app (algebraObject S d F))).symm

/-- The chart over an affine open is induced by the sheafification unit and the
symmetric-algebra identification. Source: Stacks Tag 01LX
(blueprint: proposition-purity-vector-bundles). -/
def affineChart (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] (U : S.affineOpens) :
    ((π S d F) ⁻¹ᵁ U.1).toScheme ⟶
      Spec (.of (SymmetricAlgebraSheaf.sections F (op U.1))) :=
  ((π S d F) ⁻¹ᵁ U.1).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom
      (((algebraIso S d F).hom.right.hom.app (op U.1)).hom.comp
        (SymmetricAlgebraSheaf.sectionMap F (op U.1))))

/-- The augmentation is the unique map killing every degree-one section, and on sectionwise
symmetric algebras is the identity on scalars and zero on generators.
Source: Stacks Tag 01M2 (blueprint: proposition-purity-vector-bundles).
Proof: the core symmetric-algebra universal property with the zero linear map gives
existence and uniqueness. Before sheafification the map is SymmetricAlgebra.algebraMapInv;
uniqueness on scalars and generators identifies the composite with the sheafification unit.
The under-category compatibility supplies the identity on scalars. -/
theorem augmentation_spec (S : Scheme.{u}) (F : S.Modules) :
    (∀ (U : S.Opens) (x : F.val.obj (op U)),
      (augmentation S F).right.hom.app (op U)
        ((SymmetricAlgebraSheaf.inclusion F).val.app (op U) x) = 0) ∧
    (∀ t : SymmetricAlgebraSheaf.algebra F ⟶ Under.mk (𝟙 S.sheaf),
      (∀ (U : S.Opens) (x : F.val.obj (op U)),
        t.right.hom.app (op U) ((SymmetricAlgebraSheaf.inclusion F).val.app (op U) x) = 0) →
      t = augmentation S F) ∧
    (∀ (U : S.Opens) (a : SymmetricAlgebraSheaf.sections F (op U)),
      (augmentation S F).right.hom.app (op U) (SymmetricAlgebraSheaf.sectionMap F (op U) a) =
        SymmetricAlgebra.algebraMapInv a) := by
  have h := (exists_quasiCoherentSymmetricAlgebra_core S F (Under.mk (𝟙 S.sheaf))
    0).exists.choose_spec
  have hz : ∀ (U : S.Opens) (x : F.val.obj (op U)),
      (augmentation S F).right.hom.app (op U)
        ((SymmetricAlgebraSheaf.inclusion F).val.app (op U) x) = 0 := by
    intro U x
    exact h U x
  refine ⟨hz, ?_, ?_⟩
  · intro t ht
    exact ExistsUnique.unique
      (exists_quasiCoherentSymmetricAlgebra_core S F (Under.mk (𝟙 S.sheaf)) 0) ht hz
  · intro U a
    induction a using SymmetricAlgebra.induction with
    | algebraMap r =>
        rw [AlgHom.commutes]
        exact congrArg (fun q ↦ q.hom.app (op U) r) (Under.w (augmentation S F))
    | ι x =>
        exact (hz U x).trans (SymmetricAlgebra.algebraMapInv_ι x).symm
    | mul a b ha hb => simp only [map_mul, ha, hb]
    | add a b ha hb => simp only [map_add, ha, hb]

/-- The zero section is a section and a closed immersion.
Source: Stacks Tag 01M2 (blueprint: proposition-purity-vector-bundles).
Proof: the augmentation is an O_S-algebra map, so its spectrum lies over S, giving the
section identity. On each relative-spectrum affine chart it is induced by the
augmentation Sym_R(F(U)) → R, which is surjective because it fixes scalars. It is therefore
the quotient closed subscheme for the augmentation kernel, by the affine closed-immersion
criterion. These charts cover the total space, so the morphism is a closed immersion. -/
theorem zero_spec (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] :
    zero S d F ≫ π S d F = 𝟙 S ∧ IsClosedImmersion (zero S d F) := by
  have hs : zero S d F ≫ π S d F = 𝟙 S := by
    exact Over.w
      (((antiEquivalence S).functor.preimage
        (((antiEquivalence S).counitIso.app (algebraObject S d F)).hom ≫
          ObjectProperty.homMk (augmentationToBase S F))).unop.hom)
  have : IsAffineHom (π S d F) := (over S d F).property
  have : IsClosedImmersion (zero S d F ≫ π S d F) := hs ▸ inferInstance
  exact ⟨hs, IsClosedImmersion.of_comp (zero S d F) (π S d F)⟩

/-- Restriction of the zero section to an open of the base.
Source: Stacks Tag 01M2 (blueprint: proposition-purity-vector-bundles). -/
def zeroRestricted (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] (V : S.Opens) :
    V.toScheme ⟶ ((π S d F) ⁻¹ᵁ V).toScheme :=
  (zero S d F).resLE ((π S d F) ⁻¹ᵁ V) V
    (by rw [← Scheme.Hom.comp_preimage, (zero_spec S d F).1]; simp)

private def zeroOver (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] : baseObject S ⟶ over S d F :=
  ((antiEquivalence S).functor.preimage
    (((antiEquivalence S).counitIso.app (algebraObject S d F)).hom ≫
      ObjectProperty.homMk (augmentationToBase S F))).unop

private theorem zeroOver_map (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] :
    (antiEquivalence S).functor.map (zeroOver S d F).op =
      ((antiEquivalence S).counitIso.app (algebraObject S d F)).hom ≫
        ObjectProperty.homMk (augmentationToBase S F) :=
  (antiEquivalence S).functor.map_preimage _

private theorem zero_pullback (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] (U : S.Opens) :
    (algebraIso S d F).hom.right.hom.app (op U) ≫
      (zero S d F).appLE ((π S d F) ⁻¹ᵁ U) U
        (by rw [← Scheme.Hom.comp_preimage, (zero_spec S d F).1]; simp) =
      (augmentation S F).right.hom.app (op U) := by
  have hn := congrArg (fun t ↦ t.hom.right.hom.app (op U)) (zeroOver_map S d F)
  simp only [ObjectProperty.FullSubcategory.comp_hom, Under.comp_right,
    TopCat.Sheaf.comp_app] at hn
  change (zero S d F).appLE ((π S d F) ⁻¹ᵁ U) U _ =
    ((antiEquivalence S).counitIso.app (algebraObject S d F)).hom.hom.right.hom.app (op U) ≫
      (augmentation S F).right.hom.app (op U) at hn
  have hc := congrArg (fun t ↦ t.hom.right.hom.app (op U))
    ((antiEquivalence S).counitIso.app (algebraObject S d F)).inv_hom_id
  simp only [ObjectProperty.FullSubcategory.comp_hom, Under.comp_right,
    TopCat.Sheaf.comp_app, ObjectProperty.FullSubcategory.id_hom, Under.id_right,
    TopCat.Sheaf.id_app] at hc
  change ((antiEquivalence S).counitIso.app (algebraObject S d F)).inv.hom.right.hom.app
    (op U) ≫ _ = _
  rw [hn, ← Category.assoc, hc, Category.id_comp]

-- Geometry uses the equivalence API, not the choice of its quasi-inverse.
attribute [local irreducible] antiEquivalence

/-- The two compatibility equations for the affine relative-spectrum chart.
This is the equation portion of `affineChart_spec`; it is split out because the
relative-spectrum construction and the zero-section comparison are independent of
chart invertibility. Source: Stacks Project, Constructions, Tags 01LX and 01M2.
Proof: use the affine symmetric-algebra section bijection and the relative-spectrum chart
characterization. Scalar compatibility gives the first equation, and augmentation_spec gives
the second.
(blueprint: lem-asd-vector-bundle-affine-chart-equations). -/
theorem affineChart_equations (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] (U : S.affineOpens) :
    (affineChart S d F U ≫
      Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.obj (op U.1))
        (SymmetricAlgebraSheaf.sections F (op U.1)))) ≫ U.2.isoSpec.inv = (π S d F) ∣_ U.1) ∧
    (zeroRestricted S d F U.1 ≫ affineChart S d F U =
      U.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
        (SymmetricAlgebra.algebraMapInv (R := S.presheaf.obj (op U.1))
          (M := F.val.obj (op U.1))).toRingHom)) := by
  constructor
  · have hscalar : CommRingCat.ofHom (algebraMap (S.presheaf.obj (op U.1))
        (SymmetricAlgebraSheaf.sections F (op U.1))) ≫
        CommRingCat.ofHom (SymmetricAlgebraSheaf.sectionMap F (op U.1)) ≫
        (algebraIso S d F).hom.right.hom.app (op U.1) = (π S d F).app U.1 := by
      exact congrArg (fun q ↦ q.hom.app (op U.1)) (Under.w (algebraIso S d F).hom)
    change (((π S d F) ⁻¹ᵁ U.1).toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (SymmetricAlgebraSheaf.sectionMap F (op U.1)) ≫
        (algebraIso S d F).hom.right.hom.app (op U.1))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.obj (op U.1))
        (SymmetricAlgebraSheaf.sections F (op U.1)))) ≫ U.2.isoSpec.inv = _
    simp only [Category.assoc, ← Spec.map_comp_assoc]
    rw [hscalar, Scheme.Opens.toSpecΓ_naturality_assoc]
    simp
  · have hzero : CommRingCat.ofHom (SymmetricAlgebraSheaf.sectionMap F (op U.1)) ≫
        (algebraIso S d F).hom.right.hom.app (op U.1) ≫
        (zero S d F).appLE ((π S d F) ⁻¹ᵁ U.1) U.1
          (by rw [← Scheme.Hom.comp_preimage, (zero_spec S d F).1]; simp) =
        CommRingCat.ofHom (SymmetricAlgebra.algebraMapInv
          (R := S.presheaf.obj (op U.1)) (M := F.val.obj (op U.1))).toRingHom := by
      rw [zero_pullback]
      apply CommRingCat.hom_ext
      exact RingHom.ext ((augmentation_spec S F).2.2 U.1)
    change (zero S d F).resLE ((π S d F) ⁻¹ᵁ U.1) U.1 _ ≫
      ((π S d F) ⁻¹ᵁ U.1).toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (SymmetricAlgebraSheaf.sectionMap F (op U.1)) ≫
          (algebraIso S d F).hom.right.hom.app (op U.1)) = _
    rw [← Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc]
    simp only [← Spec.map_comp, Category.assoc] at hzero ⊢
    rw [hzero]
    rfl

set_option linter.style.haveILetI false in
/-- The affine charts are isomorphisms over the corresponding base affine opens, and the
zero section in these charts is exactly the spectrum of the augmentation.
Source: Stacks Tags 01LX and 01M2 (blueprint: proposition-purity-vector-bundles).
Proof: quasiCoherentSymmetricAlgebra_affine_comparison identifies affine algebra sections
with Sym_R(F(U)). Since the structural projection is affine, its inverse image of an affine
open is affine. Its toSpecΓ map, the counit on sections, and the section comparison are
isomorphisms, so their spectra give the chart isomorphism. The two compatibility equations
are exactly affineChart_equations, using scalar compatibility and the augmentation. -/
theorem affineChart_spec (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] (U : S.affineOpens) :
    IsIso (affineChart S d F U) ∧
    (affineChart S d F U ≫
      Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.obj (op U.1))
        (SymmetricAlgebraSheaf.sections F (op U.1)))) ≫ U.2.isoSpec.inv = (π S d F) ∣_ U.1) ∧
    (zeroRestricted S d F U.1 ≫ affineChart S d F U =
      U.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
        (SymmetricAlgebra.algebraMapInv (R := S.presheaf.obj (op U.1))
          (M := F.val.obj (op U.1))).toRingHom))   := by
  letI := SheafOfModules.IsFiniteLocallyFreeOfRank.isLocallyFree F d
  have hq := quasiCoherentSymmetricAlgebra_affine_comparison S F
  have hsec : IsIso (CommRingCat.ofHom (SymmetricAlgebraSheaf.sectionMap F (op U.1))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (hq.2 U)
  letI := hsec
  haveI : IsAffineHom (π S d F) := (over S d F).property
  haveI : IsIso (((π S d F) ⁻¹ᵁ U.1).toSpecΓ) :=
    (U.2.preimage (π S d F)).isoSpec.isIso_hom
  haveI : IsIso ((algebraIso S d F).hom.right.hom) := by infer_instance
  haveI : IsIso ((algebraIso S d F).hom.right.hom.app (op U.1)) := by infer_instance
  have hi : IsIso (affineChart S d F U) := by
    change IsIso (((π S d F) ⁻¹ᵁ U.1).toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (SymmetricAlgebraSheaf.sectionMap F (op U.1)) ≫
        (algebraIso S d F).hom.right.hom.app (op U.1)))
    infer_instance
  have heq := affineChart_equations S d F U
  exact ⟨hi, heq.1, heq.2⟩

/-- On an inclusion of affine opens, the chart change is the spectrum of the
symmetric-algebra restriction, so these are exactly the affine pieces glued in the node.
Source: Stacks Tag 01LX (blueprint: proposition-purity-vector-bundles).
Proof: naturality of the counit algebra isomorphism and of the sheafification unit
identifies the maps on section rings with SymmetricAlgebraSheaf.restriction. Apply
naturality of toSpecΓ and contravariant functoriality of Spec. -/
theorem affineChart_naturality (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] (U V : S.affineOpens) (h : U.1 ≤ V.1) :
    Scheme.Hom.resLE (𝟙 (scheme S d F)) ((π S d F) ⁻¹ᵁ V.1) ((π S d F) ⁻¹ᵁ U.1)
        ((π S d F).preimage_mono h) ≫ affineChart S d F V =
      affineChart S d F U ≫
        Spec.map (CommRingCat.ofHom (SymmetricAlgebraSheaf.restriction F (homOfLE h).op)) := by
  simp only [Scheme.Hom.resLE_id, affineChart, Category.assoc]
  rw [← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc]
  simp only [← Spec.map_comp]
  congr 1
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  have hA := (algebraIso S d F).hom.right.hom.naturality (homOfLE h).op
  have hθ := (toSheafify (Opens.grothendieckTopology S)
    (SymmetricAlgebraSheaf.presheaf F)).naturality (homOfLE h).op
  exact (CategoryTheory.congr_fun hA
    (SymmetricAlgebraSheaf.sectionMap F (op V.1) a)).symm.trans
      (congrArg ((algebraIso S d F).hom.right.hom.app (op U.1))
        (CategoryTheory.congr_fun hθ a).symm)

/-- A Zariski trivialization is a frame of the given module, not an arbitrary isomorphism
of schemes. Source: blueprint order 1968 (blueprint: proposition-purity-vector-bundles). -/
def Trivialization (S : Scheme.{u}) (d : ℕ) (F : S.Modules) (V : S.Opens) :=
  F.restrict V.ι ≅ SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin d))

/-- The i-th frame section over V, obtained by the inverse frame map on its standard basis.
Source: blueprint order 1968 (blueprint: proposition-purity-vector-bundles). -/
def frameSection (S : Scheme.{u}) (d : ℕ) (F : S.Modules) (V : S.Opens)
    (e : Trivialization S d F V) (i : Fin d) : F.val.obj (op V) :=
  F.presheaf.map (eqToHom V.ι_image_top.symm).op
    ((F.restrictAppIso V.ι ⊤).hom
      (e.inv.val.app (op ⊤) ((SheafOfModules.ιFree (R := V.toScheme.ringCatSheaf)
        (ULift.up i)).val.app (op ⊤)
          (1 : V.toScheme.ringCatSheaf.obj.obj (op ⊤)))))

private def frameBasis (S : Scheme.{u}) (d : ℕ) (F : S.Modules) (V : S.Opens)
    (e : Trivialization S d F V) :
    Module.Basis (Fin d) Γ(V.toScheme, ⊤) Γ(F.restrict V.ι, ⊤) :=
  ((((Pi.basisFun Γ(V.toScheme, ⊤) (ULift.{u} (Fin d))).map
    (Scheme.Modules.freeSectionsEquiv (X := V.toScheme) (ULift.{u} (Fin d))).symm).reindex
      Equiv.ulift).map (Scheme.Modules.appLinearEquivOfIso e.symm ⊤))

private theorem frameBasis_apply (S : Scheme.{u}) (d : ℕ) (F : S.Modules) (V : S.Opens)
    (e : Trivialization S d F V) (i : Fin d) :
    frameBasis S d F V e i = e.inv.val.app (op ⊤)
      ((SheafOfModules.ιFree (R := V.toScheme.ringCatSheaf) (ULift.up i)).val.app (op ⊤)
        (1 : Γ(V.toScheme, ⊤))) := by
  classical
  unfold frameBasis
  erw [Module.Basis.map_apply, Module.Basis.reindex_apply, Module.Basis.map_apply,
    Pi.basisFun_apply]
  change e.inv.val.app (op ⊤) (∑ j : ULift.{u} (Fin d),
    (SheafOfModules.ιFree (R := V.toScheme.ringCatSheaf) j).val.app (op ⊤)
      ((Pi.single (ULift.up i) 1 : ULift.{u} (Fin d) → Γ(V.toScheme, ⊤)) j)) = _
  congr 1
  simp only [Pi.single_apply]
  rw [Finset.sum_eq_single (ULift.up i)]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

private def frameTransport (S : Scheme.{u}) (F : S.Modules) (V : S.Opens) :
    Γ(F.restrict V.ι, ⊤) →ₛₗ[V.topIso.hom.hom] Γ(F, V) where
  toFun x := F.presheaf.map (eqToHom V.ι_image_top.symm).op
    ((F.restrictAppIso V.ι ⊤).hom x)
  map_add' x y := by simp
  map_smul' r x := by
    rw [Scheme.Modules.smul_restrictAppIso_hom_apply]
    simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
    exact F.val.map_smul (eqToHom V.ι_image_top.symm).op r
      ((F.restrictAppIso V.ι ⊤).hom x)

private theorem frameTransport_basis (S : Scheme.{u}) (d : ℕ) (F : S.Modules)
    (V : S.Opens) (e : Trivialization S d F V) (i : Fin d) :
    frameTransport S F V (frameBasis S d F V e i) = frameSection S d F V e i := by
  rw [frameBasis_apply]
  rfl

private def freeSectionEquivAt (T : Scheme.{u}) (I : Type u) [Fintype I] [DecidableEq I]
    (U : T.Opens) :
    Γ(SheafOfModules.free (R := T.ringCatSheaf) I, U) ≃ₗ[Γ(T, U)] (I → Γ(T, U)) where
  toFun x i := (Scheme.Modules.freeπ i).val.app (op U) x
  map_add' x y := by ext i; exact map_add _ _ _
  map_smul' r x := by ext i; exact (Scheme.Modules.freeπ i).val.app (op U) |>.hom.map_smul r x
  invFun c := ∑ i, (SheafOfModules.ιFree (R := T.ringCatSheaf) i).val.app (op U) (c i)
  left_inv x := by
    change ∑ i : I, (Scheme.Modules.Hom.app
      (Scheme.Modules.freeπ i ≫ SheafOfModules.ιFree i) U) x = x
    rw [← Scheme.Modules.Hom.sum_app_apply, Scheme.Modules.sum_freeπ_ιFree]
    rfl
  right_inv c := by
    ext j
    change (Scheme.Modules.freeπ j).val.app (op U) (∑ i,
      (SheafOfModules.ιFree (R := T.ringCatSheaf) i).val.app (op U) (c i)) = c j
    rw [map_sum, Finset.sum_eq_single j _ (by simp)]
    · have h := congrArg (fun f ↦ f.val.app (op U) (c j))
        (Scheme.Modules.ιFree_freeπ (X := T) j j)
      rw [ite_eq_left rfl] at h
      exact h
    · intro i _ hij
      have h := congrArg (fun f ↦ f.val.app (op U) (c i))
        (Scheme.Modules.ιFree_freeπ (X := T) i j)
      rw [ite_eq_right hij] at h
      exact h

section LocalFrames

private local instance restrictedSectionsModule (S : Scheme.{u}) (F : S.Modules) (V : S.Opens)
    (U : V.toScheme.Opens) : Module Γ(V.toScheme, U) Γ(F, V.ι ''ᵁ U) := by
  change Module Γ(S, V.ι ''ᵁ U) Γ(F, V.ι ''ᵁ U)
  infer_instance

private def restrictedSectionsEquiv (S : Scheme.{u}) (F : S.Modules) (V : S.Opens)
    (U : V.toScheme.Opens) :
    Γ(F.restrict V.ι, U) ≃ₗ[Γ(V.toScheme, U)] Γ(F, V.ι ''ᵁ U) where
  toFun := (F.restrictAppIso V.ι U).hom
  invFun := (F.restrictAppIso V.ι U).inv
  left_inv := Iso.hom_inv_id_apply _
  right_inv := Iso.inv_hom_id_apply _
  map_add' := map_add _
  map_smul' r x := by
    rw [Scheme.Modules.smul_restrictAppIso_hom_apply]
    simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
    rfl

private def frameBasisAt (S : Scheme.{u}) (d : ℕ) (F : S.Modules) (V : S.Opens)
    (e : Trivialization S d F V) (U : V.toScheme.Opens) :
    Module.Basis (ULift.{u} (Fin d)) Γ(S, V.ι ''ᵁ U) Γ(F, V.ι ''ᵁ U) := by
  classical
  change Module.Basis (ULift.{u} (Fin d)) Γ(V.toScheme, U) Γ(F, V.ι ''ᵁ U)
  exact (((Pi.basisFun Γ(V.toScheme, U) (ULift.{u} (Fin d))).map
    (freeSectionEquivAt V.toScheme (ULift.{u} (Fin d)) U).symm).map
      (Scheme.Modules.appLinearEquivOfIso e.symm U)).map (restrictedSectionsEquiv S F V U)

private theorem frameBasisAt_apply (S : Scheme.{u}) (d : ℕ) (F : S.Modules) (V : S.Opens)
    (e : Trivialization S d F V) (U : V.toScheme.Opens) (i : ULift.{u} (Fin d)) :
    frameBasisAt S d F V e U i = (F.restrictAppIso V.ι U).hom
      (e.inv.val.app (op U)
        ((SheafOfModules.ιFree (R := V.toScheme.ringCatSheaf) i).val.app (op U)
          (1 : Γ(V.toScheme, U)))) := by
  classical
  unfold frameBasisAt
  erw [Module.Basis.map_apply, Module.Basis.map_apply, Module.Basis.map_apply,
    Pi.basisFun_apply]
  change (F.restrictAppIso V.ι U).hom
    (e.inv.val.app (op U) (∑ j : ULift.{u} (Fin d),
      (SheafOfModules.ιFree (R := V.toScheme.ringCatSheaf) j).val.app (op U)
        ((Pi.single i 1 : ULift.{u} (Fin d) → Γ(V.toScheme, U)) j))) = _
  congr 2
  simp only [Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

set_option backward.isDefEq.respectTransparency false in
private theorem frameSection_restrict (S : Scheme.{u}) (d : ℕ) (F : S.Modules)
    (V : S.Opens) (e : Trivialization S d F V) (U : V.toScheme.Opens)
    (i : ULift.{u} (Fin d)) :
    F.presheaf.map (homOfLE (V.ι_image_le U)).op (frameSection S d F V e i.down) =
      frameBasisAt S d F V e U i := by
  rw [frameBasisAt_apply]
  dsimp only [frameSection]
  rw [← ConcreteCategory.comp_apply, ← F.presheaf.map_comp]
  have he := PresheafOfModules.naturality_apply e.inv.val (homOfLE (le_top : U ≤ ⊤)).op
    ((SheafOfModules.ιFree (R := V.toScheme.ringCatSheaf) i).val.app (op ⊤)
      (1 : Γ(V.toScheme, ⊤)))
  have hi := PresheafOfModules.naturality_apply
    (SheafOfModules.ιFree (R := V.toScheme.ringCatSheaf) i).val
    (homOfLE (le_top : U ≤ ⊤)).op (1 : Γ(V.toScheme, ⊤))
  change (SheafOfModules.ιFree (R := V.toScheme.ringCatSheaf) i).val.app (op U)
    (V.toScheme.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op 1) = _ at hi
  rw [map_one] at hi
  have h := congrArg ((F.restrictAppIso V.ι U).hom) he
  rw [← hi] at h
  exact h.symm

end LocalFrames

/-- The coordinate x_i = j(e_i), transported to the restricted total space's global ring.
Source: blueprint order 1968 (blueprint: proposition-purity-vector-bundles). -/
def coordinate (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] (V : S.Opens) (e : Trivialization S d F V) (i : Fin d) :
    Γ(((π S d F) ⁻¹ᵁ V).toScheme, ⊤) :=
  ((π S d F) ⁻¹ᵁ V).topIso.inv
    ((algebraIso S d F).hom.right.hom.app (op V)
      ((SymmetricAlgebraSheaf.inclusion F).val.app (op V) (frameSection S d F V e i)))

set_option backward.isDefEq.respectTransparency false in
private theorem homOfLE_topIso_inv {X : Scheme.{u}} {U V : X.Opens} (h : U ≤ V)
    (r : Γ(X, V)) :
    (X.homOfLE h).appTop (V.topIso.inv r) =
      U.topIso.inv (X.presheaf.map (homOfLE h).op r) := by
  simp only [Scheme.homOfLE_appTop, Scheme.Opens.topIso_inv]
  simp only [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem coordinate_restrict (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] (V : S.Opens)
    (e : Trivialization S d F V) (U : V.toScheme.Opens) (i : ULift.{u} (Fin d)) :
    ((scheme S d F).homOfLE ((π S d F).preimage_mono (V.ι_image_le U))).appTop
      (coordinate S d F V e i.down) =
    ((π S d F) ⁻¹ᵁ (V.ι ''ᵁ U)).topIso.inv
      ((algebraIso S d F).hom.right.hom.app (op (V.ι ''ᵁ U))
        ((SymmetricAlgebraSheaf.inclusion F).val.app (op (V.ι ''ᵁ U))
          (frameBasisAt S d F V e U i))) := by
  rw [coordinate, homOfLE_topIso_inv]
  have ha := CategoryTheory.congr_fun
    ((algebraIso S d F).hom.right.hom.naturality (homOfLE (V.ι_image_le U)).op)
    ((SymmetricAlgebraSheaf.inclusion F).val.app (op V) (frameSection S d F V e i.down))
  have hj := PresheafOfModules.naturality_apply (SymmetricAlgebraSheaf.inclusion F).val
    (homOfLE (V.ι_image_le U)).op (frameSection S d F V e i.down)
  change (SymmetricAlgebraSheaf.inclusion F).val.app (op (V.ι ''ᵁ U))
    (F.presheaf.map (homOfLE (V.ι_image_le U)).op (frameSection S d F V e i.down)) =
    (SymmetricAlgebraSheaf.algebra F).right.obj.map (homOfLE (V.ι_image_le U)).op
      ((SymmetricAlgebraSheaf.inclusion F).val.app (op V)
        (frameSection S d F V e i.down)) at hj
  rw [frameSection_restrict] at hj
  exact congrArg (((π S d F) ⁻¹ᵁ (V.ι ''ᵁ U)).topIso.inv)
    (ha.symm.trans (congrArg ((algebraIso S d F).hom.right.hom.app (op (V.ι ''ᵁ U))) hj.symm))

set_option backward.isDefEq.respectTransparency false in
private theorem affineChart_appTop (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] (U : S.affineOpens)
    (a : SymmetricAlgebraSheaf.sections F (op U.1)) :
    (affineChart S d F U).appTop
      ((Scheme.ΓSpecIso (.of (SymmetricAlgebraSheaf.sections F (op U.1)))).inv a) =
    ((π S d F) ⁻¹ᵁ U.1).topIso.inv
      ((algebraIso S d F).hom.right.hom.app (op U.1)
        (SymmetricAlgebraSheaf.sectionMap F (op U.1) a)) := by
  dsimp only [affineChart]
  rw [Scheme.Hom.comp_appTop]
  change (π S d F ⁻¹ᵁ U.1).toSpecΓ.appTop
    ((Spec.map (CommRingCat.ofHom (((algebraIso S d F).hom.right.hom.app (op U.1)).hom.comp
      (SymmetricAlgebraSheaf.sectionMap F (op U.1))))).appTop
      ((Scheme.ΓSpecIso (.of (SymmetricAlgebraSheaf.sections F (op U.1)))).inv a)) = _
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality,
    CommRingCat.comp_apply, Scheme.Opens.toSpecΓ_appTop]
  change (π S d F ⁻¹ᵁ U.1).topIso.inv
    ((Scheme.ΓSpecIso _).hom ((Scheme.ΓSpecIso _).inv _)) = _
  rw [Iso.inv_hom_id_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem projection_appTop (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] (V : S.Opens)
    (r : S.presheaf.obj (op V)) :
    ((π S d F) ∣_ V).appTop (V.topIso.inv r) =
      ((π S d F) ⁻¹ᵁ V).topIso.inv ((π S d F).app V r) := by
  have h := Scheme.Hom.resLE_app_top (π S d F)
    (le_rfl : (π S d F) ⁻¹ᵁ V ≤ (π S d F) ⁻¹ᵁ V)
  rw [Scheme.Hom.resLE_eq_morphismRestrict] at h
  simp only [Scheme.Hom.appLE, homOfLE_refl, op_id] at h
  rw [(scheme S d F).presheaf.map_id, Category.comp_id] at h
  simp only [Scheme.Hom.appTop, h, CommRingCat.comp_apply, Iso.inv_hom_id_apply]

set_option backward.isDefEq.respectTransparency false in
private def coordinateMap (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] (V : S.Opens) :
    Γ(F, V) →ₛₗ[((π S d F) ∣_ V).appTop.hom.comp V.topIso.inv.hom]
      Γ(((π S d F) ⁻¹ᵁ V).toScheme, ⊤) where
  toFun x := ((π S d F) ⁻¹ᵁ V).topIso.inv
    ((algebraIso S d F).hom.right.hom.app (op V)
      ((SymmetricAlgebraSheaf.inclusion F).val.app (op V) x))
  map_add' x y := by simp only [map_add]
  map_smul' r x := by
    rw [RingHom.comp_apply, projection_appTop]
    have hs := congrArg (fun q ↦ q.hom.app (op V) r) (Under.w (algebraIso S d F).hom)
    change (algebraIso S d F).hom.right.hom.app (op V)
      ((SymmetricAlgebraSheaf.algebra F).hom.hom.app (op V) r) =
      (π S d F).app V r at hs
    change ((π S d F) ⁻¹ᵁ V).topIso.inv
      ((algebraIso S d F).hom.right.hom.app (op V)
        ((SymmetricAlgebraSheaf.inclusion F).val.app (op V) (r • x))) = _
    rw [map_smul]
    let jx : (SymmetricAlgebraSheaf.algebra F).right.obj.obj (op V) :=
      (SymmetricAlgebraSheaf.inclusion F).val.app (op V) x
    change ((π S d F) ⁻¹ᵁ V).topIso.inv
      ((algebraIso S d F).hom.right.hom.app (op V)
        ((SymmetricAlgebraSheaf.algebra F).hom.hom.app (op V) r * jx)) = _
    simp only [map_mul]
    rw [hs]
    rfl

private theorem coordinateMap_frame (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] (V : S.Opens)
    (e : Trivialization S d F V) (i : Fin d) :
    coordinateMap S d F V (frameSection S d F V e i) = coordinate S d F V e i := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem zero_coordinateMap (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] (V : S.Opens) (x : Γ(F, V)) :
    (zeroRestricted S d F V).appTop (coordinateMap S d F V x) = 0 := by
  have hp := congrArg (fun q ↦ q ((SymmetricAlgebraSheaf.inclusion F).val.app (op V) x))
    (zero_pullback S d F V)
  change (zero S d F).appLE ((π S d F) ⁻¹ᵁ V) V _
    ((algebraIso S d F).hom.right.hom.app (op V)
      ((SymmetricAlgebraSheaf.inclusion F).val.app (op V) x)) = _ at hp
  have h0 := hp.trans ((augmentation_spec S F).1 V x)
  change ((zero S d F).resLE _ _ _).app ⊤ _ = 0
  rw [Scheme.Hom.resLE_app_top]
  change V.topIso.inv ((zero S d F).appLE _ _ _
    (((π S d F) ⁻¹ᵁ V).topIso.hom (((π S d F) ⁻¹ᵁ V).topIso.inv _))) = 0
  rw [Iso.inv_hom_id_apply, h0, map_zero]

/-- The map to affine space induced by a module frame and its degree-one coordinates.
Source: Stacks Tag 01M2 (blueprint: proposition-purity-vector-bundles). -/
def trivializationMap (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] (V : S.Opens) (e : Trivialization S d F V) :
    ((π S d F) ⁻¹ᵁ V).toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) V.toScheme :=
  AffineSpace.homOfVector ((π S d F) ∣_ V) (fun i ↦ coordinate S d F V e i.down)

private def frameChart (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] (V : S.Opens) (e : Trivialization S d F V)
    (U : V.toScheme.affineOpens) :
    ((π S d F) ⁻¹ᵁ (V.ι ''ᵁ U.1)).toScheme ⟶
      AffineSpace (ULift.{u} (Fin d)) (Spec Γ(V.toScheme, U.1)) :=
  affineChart S d F ⟨V.ι ''ᵁ U.1, U.2.image_of_isOpenImmersion V.ι⟩ ≫
    Spec.map (CommRingCat.ofHom
      (SymmetricAlgebra.equivMvPolynomial (frameBasisAt S d F V e U.1)).symm.toRingHom) ≫
      (AffineSpace.SpecIso (ULift.{u} (Fin d)) Γ(V.toScheme, U.1)).inv

private theorem frameChart_isIso (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] (V : S.Opens) (e : Trivialization S d F V)
    (U : V.toScheme.affineOpens) : IsIso (frameChart S d F V e U) := by
  have : IsIso (affineChart S d F
      ⟨V.ι ''ᵁ U.1, U.2.image_of_isOpenImmersion V.ι⟩) := (affineChart_spec S d F _).1
  have : IsIso (CommRingCat.ofHom
      (SymmetricAlgebra.equivMvPolynomial (frameBasisAt S d F V e U.1)).symm.toRingHom) :=
    (RingEquiv.toCommRingCatIso
      (SymmetricAlgebra.equivMvPolynomial (frameBasisAt S d F V e U.1)).symm.toRingEquiv).isIso_hom
  dsimp only [frameChart]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem frameChart_comp_map (S : Scheme.{u}) [IsNoetherian S] (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] (V : S.Opens)
    (e : Trivialization S d F V) (U : V.toScheme.affineOpens) :
    (scheme S d F).homOfLE ((π S d F).preimage_mono (V.ι_image_le U.1)) ≫
      trivializationMap S d F V e =
    frameChart S d F V e U ≫ AffineSpace.map (ULift.{u} (Fin d)) U.2.fromSpec := by
  let W : S.affineOpens := ⟨V.ι ''ᵁ U.1, U.2.image_of_isOpenImmersion V.ι⟩
  let b := frameBasisAt S d F V e U.1
  have hc : CommRingCat.ofHom (MvPolynomial.C : Γ(S, W.1) →+* _) ≫
      CommRingCat.ofHom (SymmetricAlgebra.equivMvPolynomial b).symm.toRingHom =
      CommRingCat.ofHom (algebraMap Γ(S, W.1) (SymmetricAlgebraSheaf.sections F (op W.1))) := by
    apply CommRingCat.hom_ext
    exact RingHom.ext (SymmetricAlgebra.equivMvPolynomial b).symm.commutes
  have hbase : U.2.fromSpec ≫ V.ι = W.2.fromSpec := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec V.ι W.2 U.2
      ((V.ι.preimage_image_eq U.1).ge)
    have ha : V.ι.appLE W.1 U.1 ((V.ι.preimage_image_eq U.1).ge) = 𝟙 _ := by
      rw [Scheme.Opens.ι_appLE]
      change S.presheaf.map (𝟙 (op W.1)) = 𝟙 _
      exact S.presheaf.map_id _
    rw [ha, Spec.map_id] at h
    change 𝟙 (Spec Γ(S, W.1)) ≫ W.2.fromSpec = U.2.fromSpec ≫ V.ι at h
    rw [Category.id_comp] at h
    exact h.symm
  apply AffineSpace.hom_ext
  · dsimp only [trivializationMap, frameChart]
    simp only [Category.assoc, AffineSpace.map_over, AffineSpace.homOfVector_over,
      AffineSpace.SpecIso_inv_over_assoc, ← Spec.map_comp_assoc]
    rw [hc]
    apply (cancel_mono V.ι).mp
    simp only [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc]
    rw [hbase]
    have h := congrArg (fun q ↦ q ≫ W.1.ι) (affineChart_spec S d F W).2.1
    simpa only [Category.assoc, IsAffineOpen.isoSpec_inv_ι, morphismRestrict_ι] using h.symm
  · intro i
    dsimp only [trivializationMap, frameChart]
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AffineSpace.homOfVector_appTop_coord, AffineSpace.map_appTop_coord]
    rw [coordinate_restrict]
    change _ = (affineChart S d F W).appTop
      ((Spec.map (CommRingCat.ofHom (SymmetricAlgebra.equivMvPolynomial b).symm.toRingHom)).appTop
        ((AffineSpace.SpecIso (ULift.{u} (Fin d)) Γ(V.toScheme, U.1)).inv.appTop
          (AffineSpace.coord _ i)))
    rw [AffineSpace.SpecIso_inv_appTop_coord]
    have hn := CategoryTheory.congr_fun (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (SymmetricAlgebra.equivMvPolynomial b).symm.toRingHom))
        (MvPolynomial.X i)
    change (Scheme.ΓSpecIso (.of (SymmetricAlgebraSheaf.sections F (op W.1)))).inv
        ((SymmetricAlgebra.equivMvPolynomial b).symm (MvPolynomial.X i)) =
      (Spec.map (CommRingCat.ofHom (SymmetricAlgebra.equivMvPolynomial b).symm.toRingHom)).appTop
        ((Scheme.ΓSpecIso (.of (MvPolynomial (ULift.{u} (Fin d)) Γ(S, W.1)))).inv
          (MvPolynomial.X i)) at hn
    refine Eq.trans ?_ (congrArg ((affineChart S d F W).appTop) hn)
    rw [SymmetricAlgebra.equivMvPolynomial_symm_X, affineChart_appTop]
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem affineSpaceChartRange {T : Scheme.{u}} (I : Type u) (U : T.affineOpens) :
    (AffineSpace.map I U.2.fromSpec).opensRange =
      (AffineSpace I T ↘ T) ⁻¹ᵁ U.1 := by
  have h := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    (AffineSpace.isPullback_map (n := I) U.2.fromSpec).flip (⊤ : (Spec Γ(T, U.1)).Opens)
  simpa only [Scheme.Hom.preimage_top, Scheme.Hom.image_top_eq_opensRange,
    IsAffineOpen.opensRange_fromSpec] using h

set_option backward.isDefEq.respectTransparency false in
private theorem isIso_of_affineSpace_charts {T X : Scheme.{u}} (I : Type u)
    (f : X ⟶ T) (h : X ⟶ AffineSpace I T) (w : h ≫ AffineSpace I T ↘ T = f)
    (ht : ∀ U : T.affineOpens,
      ∃ t : (f ⁻¹ᵁ U.1).toScheme ⟶ AffineSpace I (Spec Γ(T, U.1)),
        IsIso t ∧ (f ⁻¹ᵁ U.1).ι ≫ h = t ≫ AffineSpace.map I U.2.fromSpec) : IsIso h := by
  let 𝒰 : (AffineSpace I T).OpenCover := Scheme.Cover.mkOfCovers
    T.affineOpens (fun U ↦ AffineSpace I (Spec Γ(T, U.1)))
    (fun U ↦ AffineSpace.map I U.2.fromSpec) (by
      intro y
      obtain ⟨U, hU, hy, _⟩ := exists_isAffineOpen_mem_and_subset
        (show (AffineSpace I T ↘ T) y ∈ (⊤ : T.Opens) from trivial)
      have hm : y ∈ (AffineSpace.map I hU.fromSpec).opensRange := by
        rw [affineSpaceChartRange I ⟨U, hU⟩]
        exact hy
      exact ⟨⟨U, hU⟩, hm⟩)
  apply IsZariskiLocalAtTarget.of_openCover (P := MorphismProperty.isomorphisms Scheme) 𝒰
  intro U
  obtain ⟨t, hi, he⟩ := ht U
  have hp : IsPullback t (f ⁻¹ᵁ U.1).ι (AffineSpace.map I U.2.fromSpec) h := by
    apply IsOpenImmersion.isPullback _ _ _ _ he
    rw [affineSpaceChartRange, ← Scheme.Hom.comp_preimage, w, Scheme.Opens.opensRange_ι]
  change IsIso (pullback.snd h (AffineSpace.map I U.2.fromSpec))
  rw [← hp.flip.isoPullback_inv_snd]
  infer_instance

/-- The frame induces an affine-space isomorphism over V with the zero section at the origin.
Source: blueprint order 1968 and Stacks Tag 01M2
(blueprint: proposition-purity-vector-bundles).
Proof: on every affine open inside V the frame gives a module basis. The basis-preserving
isomorphism SymmetricAlgebra.equivMvPolynomial identifies its symmetric algebra with the
polynomial algebra and its generators with the variables. The affine relative-spectrum
charts therefore identify trivializationMap with an isomorphism over V. These maps agree
on overlaps because their coordinates are the restrictions of j(e_i), so they glue.
The augmentation kills each e_i, hence all coordinates of the zero section vanish;
AffineSpace.homOfVector identifies this with the standard affine-space zero section. -/
theorem trivializationMap_spec (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] (V : S.Opens) (e : Trivialization S d F V) :
    IsIso (trivializationMap S d F V e) ∧
    (trivializationMap S d F V e ≫
      AffineSpace (ULift.{u} (Fin d)) V.toScheme ↘ V.toScheme = (π S d F) ∣_ V) ∧
    (zeroRestricted S d F V ≫ trivializationMap S d F V e =
      AffineSpace.zeroSection (ULift.{u} (Fin d)) V.toScheme) := by
  have ho : trivializationMap S d F V e ≫
      AffineSpace (ULift.{u} (Fin d)) V.toScheme ↘ V.toScheme = (π S d F) ∣_ V :=
    AffineSpace.homOfVector_over _ _
  refine ⟨?_, ho, ?_⟩
  · apply isIso_of_affineSpace_charts (ULift.{u} (Fin d)) ((π S d F) ∣_ V) _ ho
    intro U
    let eX := (((π S d F) ⁻¹ᵁ V).ι.isoImage (((π S d F) ∣_ V) ⁻¹ᵁ U.1)).trans
      ((scheme S d F).isoOfEq (image_morphismRestrict_preimage (π S d F) V U.1))
    have hi : eX.hom ≫ (scheme S d F).homOfLE
        ((π S d F).preimage_mono (V.ι_image_le U.1)) =
        (((π S d F) ∣_ V) ⁻¹ᵁ U.1).ι := by
      apply (cancel_mono ((π S d F) ⁻¹ᵁ V).ι).mp
      dsimp only [eX, Iso.trans_hom]
      simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.isoOfEq_hom_ι,
        Scheme.Hom.isoImage_hom_ι]
    refine ⟨eX.hom ≫ frameChart S d F V e U, ?_, ?_⟩
    · have := frameChart_isIso S d F V e U
      infer_instance
    · rw [← hi, Category.assoc, frameChart_comp_map, Category.assoc]
  · apply AffineSpace.hom_ext
    · rw [Category.assoc, ho, AffineSpace.zeroSection_over]
      apply (cancel_mono V.ι).mp
      simp only [morphismRestrict_ι, zeroRestricted,
        Scheme.Hom.resLE_comp_ι_assoc, Category.assoc, (zero_spec S d F).1,
        Category.comp_id, Category.id_comp]
    · intro i
      dsimp only [trivializationMap]
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        AffineSpace.homOfVector_appTop_coord, AffineSpace.zeroSection_appTop_coord]
      exact zero_coordinateMap S d F V (frameSection S d F V e i.down)

/-- Two frames on an overlap differ by an invertible matrix of regular functions, and the
same matrix changes their degree-one coordinates (with no transpose or dual convention).
Source: blueprint order 1968 (blueprint: proposition-purity-vector-bundles).
Proof: the composite of the two frame isomorphisms is an automorphism of the finite free
module sheaf. Its values on the standard global basis have global coefficient sections,
giving G. The inverse automorphism gives H. Applying their composites to each basis
vector proves GH = HG = I. These coefficients give the displayed equation for frame
sections on W, whether or not W is affine. The degree-one map j is O_S-linear; applying
it and the algebra isomorphism to that equation gives the coordinate equation, with
coefficients pulled back along the restricted projection. For d = 0 all sums are empty
and the unique empty matrices are mutual inverses. -/
theorem transition_spec (S : Scheme.{u}) [IsNoetherian S] (d : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank d] (W : S.Opens) (e e' : Trivialization S d F W) :
    ∃ G H : Matrix (Fin d) (Fin d) (S.presheaf.obj (op W)),
      G * H = 1 ∧ H * G = 1 ∧
      (∀ j : Fin d,
        frameSection S d F W e' j = ∑ i : Fin d, G i j • frameSection S d F W e i) ∧
      (∀ j : Fin d,
        coordinate S d F W e' j = ∑ i : Fin d,
          ((π S d F) ∣_ W).appTop (W.topIso.inv (G i j)) * coordinate S d F W e i) := by
  classical
  let b := frameBasis S d F W e
  let b' := frameBasis S d F W e'
  let G := (b.toMatrix b').map W.topIso.hom
  let H := (b'.toMatrix b).map W.topIso.hom
  have hG : G * H = 1 := by
    rw [← Matrix.map_mul, Module.Basis.toMatrix_mul_toMatrix_flip]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hH : H * G = 1 := by
    rw [← Matrix.map_mul, Module.Basis.toMatrix_mul_toMatrix_flip]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hf (j : Fin d) :
      frameSection S d F W e' j = ∑ i : Fin d, G i j • frameSection S d F W e i := by
    have h := congrArg (frameTransport S F W) (b.sum_toMatrix_smul_self b' j)
    simpa only [map_sum, map_smulₛₗ, b, b', frameTransport_basis, G, Matrix.map_apply] using h.symm
  refine ⟨G, H, hG, hH, hf, ?_⟩
  intro j
  have h := congrArg (coordinateMap S d F W) (hf j)
  simpa only [map_sum, map_smulₛₗ, RingHom.comp_apply, smul_eq_mul,
    coordinateMap_frame] using h

end AlgebraicGeometry.VectorBundleZeroSection
