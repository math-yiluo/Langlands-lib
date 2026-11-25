/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImagePairing
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all WeilConjectures.CategoryTheory.RingedToposKFlatPullback

/-! # Universality of the transported tensor pairing
Source: Stacks Project, Modules on Sites, Tag 03EL.
(blueprint: lem-weil-pbc-algebraic-inverse-image-pairing-isIso).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open SheafOfModules SheafOfModules.GeometricConstruction
namespace SheafOfModules.RingedTensor
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

private noncomputable def radd
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) := fromProd (rset R) (rset R) ≫ ringAdd R

private noncomputable def rmul
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) := fromProd (rset R) (rset R) ≫ ringMul R

private noncomputable def madd
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (M : SheafOfModules.{u, u, u, u} (base R)) :=
  fromProd ((mset R).obj M) ((mset R).obj M) ≫ addition R M
private noncomputable def msmul
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (M : SheafOfModules.{u, u, u, u} (base R)) :=
  fromProd (rset R) ((mset R).obj M) ≫ action R M

variable (R : Sheaf J CommRingCat.{u}) (RI : Sheaf K CommRingCat.{u})
  (F : Sheaf J (Type u) ⥤ Sheaf K (Type u))
  (V : Sheaf K (Type u) ⥤ Sheaf J (Type u))
  (adj : F ⊣ V) [PreservesFiniteLimits F]
  (I : AlgebraicInverseImage F R RI)

private theorem ringOperations :
    F.map (radd R) = prodComparison F (rset R) (rset R) ≫
        prod.map I.ringUnderlying.hom I.ringUnderlying.hom ≫ radd RI ≫
          I.ringUnderlying.inv ∧
    F.map (rmul R) = prodComparison F (rset R) (rset R) ≫
        prod.map I.ringUnderlying.hom I.ringUnderlying.hom ≫ rmul RI ≫
          I.ringUnderlying.inv := by
  constructor
  · apply (cancel_mono I.ringUnderlying.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact binary_of_graph F I.ringUnderlying.hom I.ringUnderlying.hom
      I.ringUnderlying.hom (radd R) (radd RI)
      (fun U x y ↦ @Add.add (R.obj.obj U) inferInstance x y)
      (fun U x y ↦ @Add.add (RI.obj.obj U) inferInstance x y)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      (fun T x y z hz U t ↦ I.ringAdd T x y z hz U t)
  · apply (cancel_mono I.ringUnderlying.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact binary_of_graph F I.ringUnderlying.hom I.ringUnderlying.hom
      I.ringUnderlying.hom (rmul R) (rmul RI)
      (fun U x y ↦ @Mul.mul (R.obj.obj U) inferInstance x y)
      (fun U x y ↦ @Mul.mul (RI.obj.obj U) inferInstance x y)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      (fun T x y z hz U t ↦ I.ringMul T x y z hz U t)

variable [PreservesFiniteLimits V]

omit [PreservesFiniteLimits F] in
private theorem pairMate
    {X : Sheaf J (Type u)} {A B : Sheaf K (Type u)}
    (a : F.obj X ⟶ A) (b : F.obj X ⟶ B) :
    adj.homEquiv X (A ⨯ B) (prod.lift a b) =
      prod.lift (adj.homEquiv X A a) (adj.homEquiv X B b) ≫
        inv (prodComparison V A B) := by
  have : PreservesLimits V := adj.rightAdjoint_preservesLimits
  apply (cancel_mono (prodComparison V A B)).mp
  apply prod.hom_ext
  · simp only [Category.assoc, IsIso.inv_hom_id_assoc, prod.lift_fst]
    rw [prodComparison_fst]
    rw [← adj.homEquiv_naturality_right]
    simp only [prod.lift_fst]
  · simp only [Category.assoc, IsIso.inv_hom_id_assoc, prod.lift_snd]
    rw [prodComparison_snd]
    rw [← adj.homEquiv_naturality_right]
    simp only [prod.lift_snd]

omit [PreservesFiniteLimits F] in
private theorem mateAdd
    (H : SheafOfModules.{u} (RingedTensor.ringSheaf RI))
    (P : SheafOfModules.{u} (RingedTensor.ringSheaf R))
    (e : (RingedTensor.underlying R).obj P ≅ V.obj ((RingedTensor.underlying RI).obj H))
    (hadd : madd R P ≫ e.hom = prod.map e.hom e.hom ≫
      inv (prodComparison V ((RingedTensor.underlying RI).obj H)
          ((RingedTensor.underlying RI).obj H)) ≫
        V.map (madd RI H))
    {X : Sheaf J (Type u)} (a b : F.obj X ⟶ (RingedTensor.underlying RI).obj H) :
    mateIsoEquiv adj (Iso.refl (F.obj X)) e (prod.lift a b ≫ madd RI H) =
      prod.lift (mateIsoEquiv adj (Iso.refl (F.obj X)) e a)
        (mateIsoEquiv adj (Iso.refl (F.obj X)) e b) ≫ madd R P := by
  apply (cancel_mono e.hom).mp
  rw [← mateIsoEquiv_equation]
  simp only [Iso.refl_inv, Category.id_comp, Category.assoc]
  rw [hadd, adj.homEquiv_naturality_right, pairMate]
  simp only [Category.assoc, prod.lift_map_assoc]
  rw [← mateIsoEquiv_equation, ← mateIsoEquiv_equation]
  simp only [Iso.refl_inv, Category.id_comp]

omit [PreservesFiniteLimits F] in
private theorem mateSMul
    (H : SheafOfModules.{u} (RingedTensor.ringSheaf RI))
    (P : SheafOfModules.{u} (RingedTensor.ringSheaf R))
    (e : (RingedTensor.underlying R).obj P ≅ V.obj ((RingedTensor.underlying RI).obj H))
    (hsmul : msmul R P ≫ e.hom =
      prod.map (adj.homEquiv _ _ I.ringUnderlying.hom) e.hom ≫
        inv (prodComparison V (rset RI) ((RingedTensor.underlying RI).obj H)) ≫ V.map (msmul RI H))
    {X : Sheaf J (Type u)} (a : X ⟶ rset R) (b : F.obj X ⟶ (RingedTensor.underlying RI).obj H) :
    mateIsoEquiv adj (Iso.refl (F.obj X)) e
      (prod.lift (F.map a ≫ I.ringUnderlying.hom) b ≫ msmul RI H) =
      prod.lift a (mateIsoEquiv adj (Iso.refl (F.obj X)) e b) ≫ msmul R P := by
  apply (cancel_mono e.hom).mp
  rw [← mateIsoEquiv_equation]
  simp only [Iso.refl_inv, Category.id_comp, Category.assoc]
  rw [hsmul, adj.homEquiv_naturality_right, pairMate]
  simp only [Category.assoc, prod.lift_map_assoc]
  rw [← mateIsoEquiv_equation]
  simp only [Iso.refl_inv, Category.id_comp]
  rw [adj.homEquiv_naturality_left]

private theorem fromProd_lift
    {E : Type u} [Category.{u} E] {T : GrothendieckTopology E}
    {X Y Z : Sheaf T (Type u)} (a : Z ⟶ X) (b : Z ⟶ Y) :
    prod.lift a b ≫ fromProd X Y = CartesianMonoidalCategory.lift a b := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [Category.assoc, fromProd_fst, fromProd_snd,
      prod.lift_fst, prod.lift_snd, CartesianMonoidalCategory.lift_fst,
      CartesianMonoidalCategory.lift_snd]

omit [PreservesFiniteLimits F] in
private theorem mateAdd_cartesian
    (H : SheafOfModules.{u} (RingedTensor.ringSheaf RI))
    (P : SheafOfModules.{u} (RingedTensor.ringSheaf R))
    (e : (RingedTensor.underlying R).obj P ≅ V.obj ((RingedTensor.underlying RI).obj H))
    (hadd : madd R P ≫ e.hom = prod.map e.hom e.hom ≫
      inv (prodComparison V ((RingedTensor.underlying RI).obj H)
        ((RingedTensor.underlying RI).obj H)) ≫ V.map (madd RI H))
    {X : Sheaf J (Type u)} (a b : F.obj X ⟶ (RingedTensor.underlying RI).obj H) :
    mateIsoEquiv adj (Iso.refl (F.obj X)) e
      (CartesianMonoidalCategory.lift a b ≫ addition RI H) =
      CartesianMonoidalCategory.lift (mateIsoEquiv adj (Iso.refl (F.obj X)) e a)
        (mateIsoEquiv adj (Iso.refl (F.obj X)) e b) ≫ addition R P := by
  have hh := mateAdd R RI F V adj H P e hadd a b
  simpa only [madd, ← Category.assoc, fromProd_lift] using hh

omit [PreservesFiniteLimits F] in
private theorem mateSMul_cartesian
    (H : SheafOfModules.{u} (RingedTensor.ringSheaf RI))
    (P : SheafOfModules.{u} (RingedTensor.ringSheaf R))
    (e : (RingedTensor.underlying R).obj P ≅ V.obj ((RingedTensor.underlying RI).obj H))
    (hsmul : msmul R P ≫ e.hom =
      prod.map (adj.homEquiv _ _ I.ringUnderlying.hom) e.hom ≫
        inv (prodComparison V (rset RI) ((RingedTensor.underlying RI).obj H)) ≫
          V.map (msmul RI H))
    {X : Sheaf J (Type u)} (a : X ⟶ rset R)
    (b : F.obj X ⟶ (RingedTensor.underlying RI).obj H) :
    mateIsoEquiv adj (Iso.refl (F.obj X)) e
      (CartesianMonoidalCategory.lift (F.map a ≫ I.ringUnderlying.hom) b ≫ action RI H) =
      CartesianMonoidalCategory.lift a (mateIsoEquiv adj (Iso.refl (F.obj X)) e b) ≫
        action R P := by
  have hh := mateSMul R RI F V adj I H P e hsmul a b
  simpa only [msmul, ← Category.assoc, fromProd_lift] using hh

omit [PreservesFiniteLimits F] [PreservesFiniteLimits V] in
private theorem mate_naturalLeft
    {X Y : Sheaf J (Type u)} {H : Sheaf K (Type u)} {P : Sheaf J (Type u)}
    (e : P ≅ V.obj H) (a : X ⟶ Y) (b : F.obj Y ⟶ H) :
    mateIsoEquiv adj (Iso.refl (F.obj X)) e (F.map a ≫ b) =
      a ≫ mateIsoEquiv adj (Iso.refl (F.obj Y)) e b := by
  change adj.homEquiv X H (F.map a ≫ b) ≫ e.inv =
    a ≫ (adj.homEquiv Y H b ≫ e.inv)
  rw [adj.homEquiv_naturality_left, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem imageLift
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) [F.Monoidal]
    {X Y Z : Sheaf J (Type u)} (x : Z ⟶ X) (y : Z ⟶ Y) :
    F.map (CartesianMonoidalCategory.lift x y) ≫ inv (Functor.LaxMonoidal.μ F X Y) =
      CartesianMonoidalCategory.lift (F.map x) (F.map y) := by
  rw [← Functor.Monoidal.lift_μ]
  simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
omit [PreservesFiniteLimits F] [PreservesFiniteLimits V] in
private theorem transposePair_lift [F.Monoidal]
    (M N : SheafOfModules.{u} (RingedTensor.ringSheaf R))
    (H : SheafOfModules.{u} (RingedTensor.ringSheaf RI))
    (P : SheafOfModules.{u} (RingedTensor.ringSheaf R))
    (e : (RingedTensor.underlying R).obj P ≅ V.obj ((RingedTensor.underlying RI).obj H))
    (β : (RingedTensor.underlying RI).obj (I.modules.obj M) ⊗
      (RingedTensor.underlying RI).obj (I.modules.obj N) ⟶
        (RingedTensor.underlying RI).obj H)
    (Z : Sheaf J (Type u)) (x : Z ⟶ (RingedTensor.underlying R).obj M)
    (y : Z ⟶ (RingedTensor.underlying R).obj N) :
    CartesianMonoidalCategory.lift x y ≫
      mateIsoEquiv adj (Iso.refl _) e
        (inv (Functor.LaxMonoidal.μ F _ _) ≫
          (I.moduleUnderlying.inv.app M ⊗ₘ I.moduleUnderlying.inv.app N) ≫ β) =
      mateIsoEquiv adj (Iso.refl _) e
        (CartesianMonoidalCategory.lift
          (F.map x ≫ I.moduleUnderlying.inv.app M)
          (F.map y ≫ I.moduleUnderlying.inv.app N) ≫ β) := by
  rw [← mate_naturalLeft]
  congr 1
  rw [← Category.assoc, ← Category.assoc, imageLift]
  rw [Category.assoc, CartesianMonoidalCategory.lift_map_assoc]

-- Specify the mate by its equation, keeping both underlying maps abstract.
private theorem mate_linear_iff
    (M0 : SheafOfModules.{u} (ringSheaf R))
    (H0 : SheafOfModules.{u} (ringSheaf RI))
    (P0 : SheafOfModules.{u} (ringSheaf R))
    (e : (RingedTensor.underlying R).obj P0 ≅ V.obj ((RingedTensor.underlying RI).obj H0))
    (hadd : madd R P0 ≫ e.hom = prod.map e.hom e.hom ≫
      inv (prodComparison V ((RingedTensor.underlying RI).obj H0)
        ((RingedTensor.underlying RI).obj H0)) ≫ V.map (madd RI H0))
    (hsmul : msmul R P0 ≫ e.hom =
      prod.map (adj.homEquiv _ _ I.ringUnderlying.hom) e.hom ≫
        inv (prodComparison V (rset RI) ((RingedTensor.underlying RI).obj H0)) ≫
          V.map (msmul RI H0))
    (α : (RingedTensor.underlying RI).obj (I.modules.obj M0) ⟶
      (RingedTensor.underlying RI).obj H0)
    (α' : (RingedTensor.underlying R).obj M0 ⟶ (RingedTensor.underlying R).obj P0)
    (hm : adj.homEquiv _ _ (I.moduleUnderlying.inv.app M0 ≫ α) = α' ≫ e.hom) :
    (∃ a : I.modules.obj M0 ⟶ H0, (RingedTensor.underlying RI).map a = α) ↔
      ∃ b : M0 ⟶ P0, (RingedTensor.underlying R).map b = α' := by
  let eR := I.ringUnderlying.symm
  let eI := I.moduleUnderlying
  have hLA : F.map (madd R M0) =
      prodComparison F ((RingedTensor.underlying R).obj M0)
        ((RingedTensor.underlying R).obj M0) ≫
        prod.map (eI.inv.app M0) (eI.inv.app M0) ≫
          madd RI (I.modules.obj M0) ≫ eI.hom.app M0 := by
    apply (cancel_mono (eI.inv.app M0)).mp
    simp only [Category.assoc, Iso.hom_inv_id_app]
    exact binary_of_graph F (eI.inv.app M0) (eI.inv.app M0) (eI.inv.app M0)
      (madd R M0) (madd RI (I.modules.obj M0))
      (fun U x y ↦ @Add.add (M0.val.obj U) inferInstance x y)
      (fun U x y ↦ @Add.add ((I.modules.obj M0).val.obj U) inferInstance x y)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      (fun T x y z hz U t ↦ I.moduleAdd M0 T x y z hz U t)
  have hLS : F.map (msmul R M0) =
      prodComparison F (rset R) ((RingedTensor.underlying R).obj M0) ≫
        prod.map eR.inv (eI.inv.app M0) ≫
          msmul RI (I.modules.obj M0) ≫ eI.hom.app M0 := by
    apply (cancel_mono (eI.inv.app M0)).mp
    simp only [Category.assoc, Iso.hom_inv_id_app]
    exact binary_of_graph F eR.inv (eI.inv.app M0) (eI.inv.app M0)
      (msmul R M0) (msmul RI (I.modules.obj M0))
      (fun U x y ↦ @SMul.smul (R.obj.obj U) (M0.val.obj U) inferInstance x y)
      (fun U x y ↦ @SMul.smul (RI.obj.obj U) ((I.modules.obj M0).val.obj U)
        inferInstance x y)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
      (fun T a x z hz U t ↦ I.moduleSMul M0 T a x z hz U t)
  have hAdd := binary_mate_iso_iff adj (eI.app M0) (eI.app M0) (eI.app M0)
    e.hom e.hom e (madd R M0)
    (madd RI (I.modules.obj M0)) (madd RI H0) (madd R P0)
    hLA hadd α α α α' α' α' hm hm hm
  have hSmul := binary_mate_iso_iff adj eR (eI.app M0) (eI.app M0)
    (adj.homEquiv _ _ eR.inv) e.hom e
    (msmul R M0) (msmul RI (I.modules.obj M0)) (msmul RI H0) (msmul R P0)
    hLS hsmul (𝟙 (rset RI)) α α (𝟙 (rset R))
    α' α' (by simp) hm hm
  have hSame := linear_iff (𝟙 R) M0 P0
    (madd R M0) (madd R P0) (msmul R M0) (msmul R P0)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) α'
  exact (linear_iff (𝟙 RI) (I.modules.obj M0) H0 (madd RI (I.modules.obj M0))
    (madd RI H0) (msmul RI (I.modules.obj M0)) (msmul RI H0)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) α).trans
      ((and_congr hAdd hSmul).trans hSame.symm)

-- Keep the tensor construction folded while checking its universal property.
attribute [local irreducible] monoidalCategory

-- Work with an arbitrary bilinear target, so checking the four laws does not
-- repeatedly unfold the target tensor construction or the transported module functor.
omit [PreservesFiniteLimits F] in
private theorem transpose_bilinear
    (M N : SheafOfModules.{u} (ringSheaf R))
    (H : SheafOfModules.{u} (ringSheaf RI)) (P0 : SheafOfModules.{u} (ringSheaf R))
    (e : (RingedTensor.underlying R).obj P0 ≅ V.obj ((RingedTensor.underlying RI).obj H))
    (hadd : madd R P0 ≫ e.hom = prod.map e.hom e.hom ≫
      inv (prodComparison V ((RingedTensor.underlying RI).obj H)
        ((RingedTensor.underlying RI).obj H)) ≫ V.map (madd RI H))
    (hsmul : msmul R P0 ≫ e.hom =
      prod.map (adj.homEquiv _ _ I.ringUnderlying.hom) e.hom ≫
        inv (prodComparison V (rset RI) ((RingedTensor.underlying RI).obj H)) ≫
          V.map (msmul RI H))
    (β : (RingedTensor.underlying RI).obj (I.modules.obj M) ⊗
      (RingedTensor.underlying RI).obj (I.modules.obj N) ⟶ (RingedTensor.underlying RI).obj H)
    (βb : ∀ W : Dᵒᵖ, (I.modules.obj M).val.obj W →ₗ[RI.obj.obj W]
      (I.modules.obj N).val.obj W →ₗ[RI.obj.obj W] H.val.obj W)
    (hβ : ∀ W m n, β.hom.app W (m, n) = βb W m n)
    (φ : (RingedTensor.underlying R).obj M ⊗ (RingedTensor.underlying R).obj N ⟶
      (RingedTensor.underlying R).obj P0)
    (hφ : ∀ Z (x : Z ⟶ (RingedTensor.underlying R).obj M)
      (y : Z ⟶ (RingedTensor.underlying R).obj N),
      CartesianMonoidalCategory.lift x y ≫ φ = mateIsoEquiv adj (Iso.refl _) e
        (CartesianMonoidalCategory.lift (F.map x ≫ I.moduleUnderlying.inv.app M)
          (F.map y ≫ I.moduleUnderlying.inv.app N) ≫ β)) :
    ∃ f : (monoidalCategory R).tensorObj M N ⟶ P0,
      pureSheaf R M N ≫ (RingedTensor.underlying R).map f = φ := by
  have hAdd Z (x y : Z ⟶ (RingedTensor.underlying R).obj M)
      (n : Z ⟶ (RingedTensor.underlying R).obj N)
      (s : Z ⟶ (RingedTensor.underlying R).obj M)
      (hs : ∀ W t, s.hom.app W t =
        (show M.val.obj W from x.hom.app W t) +
          (show M.val.obj W from y.hom.app W t)) :
      CartesianMonoidalCategory.lift s n ≫ φ =
        CartesianMonoidalCategory.lift
          (CartesianMonoidalCategory.lift x n ≫ φ)
          (CartesianMonoidalCategory.lift y n ≫ φ) ≫ addition R P0 := by
    rw [hφ, hφ, hφ]
    refine Eq.trans ?_ (mateAdd_cartesian R RI F V adj H P0 e hadd _ _)
    apply congrArg (mateIsoEquiv adj (Iso.refl _) e)
    ext W t
    change β.hom.app W ((F.map s ≫ I.moduleUnderlying.inv.app M).hom.app W t,
        (F.map n ≫ I.moduleUnderlying.inv.app N).hom.app W t) =
      (show H.val.obj W from β.hom.app W ((F.map x ≫ I.moduleUnderlying.inv.app M).hom.app W t,
        (F.map n ≫ I.moduleUnderlying.inv.app N).hom.app W t)) +
      (show H.val.obj W from β.hom.app W ((F.map y ≫ I.moduleUnderlying.inv.app M).hom.app W t,
        (F.map n ≫ I.moduleUnderlying.inv.app N).hom.app W t))
    simp only [hβ]
    have ht : (F.map s ≫ I.moduleUnderlying.inv.app M).hom.app W t =
        (show (I.modules.obj M).val.obj W from
          (F.map x ≫ I.moduleUnderlying.inv.app M).hom.app W t) +
        (show (I.modules.obj M).val.obj W from
          (F.map y ≫ I.moduleUnderlying.inv.app M).hom.app W t) :=
      I.moduleAdd M Z x y s hs W t
    exact (congrArg (fun v : (I.modules.obj M).val.obj W ↦
      βb W v ((F.map n ≫ I.moduleUnderlying.inv.app N).hom.app W t)) ht).trans
        ((βb W).map_add₂ _ _ _)
  have hAddR Z (x y : Z ⟶ (RingedTensor.underlying R).obj N)
      (n : Z ⟶ (RingedTensor.underlying R).obj M)
      (s : Z ⟶ (RingedTensor.underlying R).obj N)
      (hs : ∀ W t, s.hom.app W t =
        (show N.val.obj W from x.hom.app W t) +
          (show N.val.obj W from y.hom.app W t)) :
      CartesianMonoidalCategory.lift n s ≫ φ =
        CartesianMonoidalCategory.lift
          (CartesianMonoidalCategory.lift n x ≫ φ)
          (CartesianMonoidalCategory.lift n y ≫ φ) ≫ addition R P0 := by
    rw [hφ, hφ, hφ]
    refine Eq.trans ?_ (mateAdd_cartesian R RI F V adj H P0 e hadd _ _)
    apply congrArg (mateIsoEquiv adj (Iso.refl _) e)
    ext W t
    change β.hom.app W ((F.map n ≫ I.moduleUnderlying.inv.app M).hom.app W t,
        (F.map s ≫ I.moduleUnderlying.inv.app N).hom.app W t) =
      (show H.val.obj W from β.hom.app W ((F.map n ≫ I.moduleUnderlying.inv.app M).hom.app W t,
        (F.map x ≫ I.moduleUnderlying.inv.app N).hom.app W t)) +
      (show H.val.obj W from β.hom.app W ((F.map n ≫ I.moduleUnderlying.inv.app M).hom.app W t,
        (F.map y ≫ I.moduleUnderlying.inv.app N).hom.app W t))
    simp only [hβ]
    have ht : (F.map s ≫ I.moduleUnderlying.inv.app N).hom.app W t =
        (show (I.modules.obj N).val.obj W from
          (F.map x ≫ I.moduleUnderlying.inv.app N).hom.app W t) +
        (show (I.modules.obj N).val.obj W from
          (F.map y ≫ I.moduleUnderlying.inv.app N).hom.app W t) :=
      I.moduleAdd N Z x y s hs W t
    exact (congrArg (fun v : (I.modules.obj N).val.obj W ↦
      βb W ((F.map n ≫ I.moduleUnderlying.inv.app M).hom.app W t) v) ht).trans
        ((βb W _).map_add _ _)
  have hSmul Z (a : Z ⟶ rset R) (x : Z ⟶ (RingedTensor.underlying R).obj M)
      (n : Z ⟶ (RingedTensor.underlying R).obj N)
      (s : Z ⟶ (RingedTensor.underlying R).obj M)
      (hs : ∀ W t, s.hom.app W t =
        (show R.obj.obj W from a.hom.app W t) •
          (show M.val.obj W from x.hom.app W t)) :
      CartesianMonoidalCategory.lift s n ≫ φ =
        CartesianMonoidalCategory.lift a
          (CartesianMonoidalCategory.lift x n ≫ φ) ≫ action R P0 := by
    rw [hφ, hφ]
    refine Eq.trans ?_ (mateSMul_cartesian R RI F V adj I H P0 e hsmul a _)
    apply congrArg (mateIsoEquiv adj (Iso.refl _) e)
    ext W t
    change β.hom.app W ((F.map s ≫ I.moduleUnderlying.inv.app M).hom.app W t,
        (F.map n ≫ I.moduleUnderlying.inv.app N).hom.app W t) =
      (show RI.obj.obj W from (F.map a ≫ I.ringUnderlying.hom).hom.app W t) •
      (show H.val.obj W from β.hom.app W ((F.map x ≫ I.moduleUnderlying.inv.app M).hom.app W t,
        (F.map n ≫ I.moduleUnderlying.inv.app N).hom.app W t))
    simp only [hβ]
    have ht : (F.map s ≫ I.moduleUnderlying.inv.app M).hom.app W t =
        (show RI.obj.obj W from (F.map a ≫ I.ringUnderlying.hom).hom.app W t) •
        (show (I.modules.obj M).val.obj W from
          (F.map x ≫ I.moduleUnderlying.inv.app M).hom.app W t) :=
      I.moduleSMul M Z a x s hs W t
    exact (congrArg (fun v : (I.modules.obj M).val.obj W ↦
      βb W v ((F.map n ≫ I.moduleUnderlying.inv.app N).hom.app W t)) ht).trans
        ((βb W).map_smul₂ _ _ _)
  have hSmulR Z (a : Z ⟶ rset R) (x : Z ⟶ (RingedTensor.underlying R).obj N)
      (n : Z ⟶ (RingedTensor.underlying R).obj M)
      (s : Z ⟶ (RingedTensor.underlying R).obj N)
      (hs : ∀ W t, s.hom.app W t =
        (show R.obj.obj W from a.hom.app W t) •
          (show N.val.obj W from x.hom.app W t)) :
      CartesianMonoidalCategory.lift n s ≫ φ =
        CartesianMonoidalCategory.lift a
          (CartesianMonoidalCategory.lift n x ≫ φ) ≫ action R P0 := by
    rw [hφ, hφ]
    refine Eq.trans ?_ (mateSMul_cartesian R RI F V adj I H P0 e hsmul a _)
    apply congrArg (mateIsoEquiv adj (Iso.refl _) e)
    ext W t
    change β.hom.app W ((F.map n ≫ I.moduleUnderlying.inv.app M).hom.app W t,
        (F.map s ≫ I.moduleUnderlying.inv.app N).hom.app W t) =
      (show RI.obj.obj W from (F.map a ≫ I.ringUnderlying.hom).hom.app W t) •
      (show H.val.obj W from β.hom.app W ((F.map n ≫ I.moduleUnderlying.inv.app M).hom.app W t,
        (F.map x ≫ I.moduleUnderlying.inv.app N).hom.app W t))
    simp only [hβ]
    have ht : (F.map s ≫ I.moduleUnderlying.inv.app N).hom.app W t =
        (show RI.obj.obj W from (F.map a ≫ I.ringUnderlying.hom).hom.app W t) •
        (show (I.modules.obj N).val.obj W from
          (F.map x ≫ I.moduleUnderlying.inv.app N).hom.app W t) :=
      I.moduleSMul N Z a x s hs W t
    exact (congrArg (fun v : (I.modules.obj N).val.obj W ↦
      βb W ((F.map n ≫ I.moduleUnderlying.inv.app M).hom.app W t) v) ht).trans
        ((βb W _).map_smul _ _)
  have hAddSections W (x y : M.val.obj W) (n : N.val.obj W) :
      φ.hom.app W (x + y, n) =
        (show P0.val.obj W from φ.hom.app W (x, n)) +
        (show P0.val.obj W from φ.hom.app W (y, n)) := by
    let X := (RingedTensor.underlying R).obj M
    let Y := (RingedTensor.underlying R).obj M
    let Z := (RingedTensor.underlying R).obj N
    let Z' := (X ⊗ Y) ⊗ Z
    let a : Z' ⟶ X := CartesianMonoidalCategory.fst (X ⊗ Y) Z ≫
      CartesianMonoidalCategory.fst X Y
    let b : Z' ⟶ Y := CartesianMonoidalCategory.fst (X ⊗ Y) Z ≫
      CartesianMonoidalCategory.snd X Y
    let c : Z' ⟶ Z := CartesianMonoidalCategory.snd (X ⊗ Y) Z
    have hh := hAdd Z' a b c (CartesianMonoidalCategory.lift a b ≫ addition R M)
      (fun _ _ ↦ rfl)
    exact congrArg (fun f : Z' ⟶ (RingedTensor.underlying R).obj P0 ↦
      f.hom.app W ((x, y), n)) hh
  have hAddRSections W (x y : N.val.obj W) (n : M.val.obj W) :
      φ.hom.app W (n, x + y) =
        (show P0.val.obj W from φ.hom.app W (n, x)) +
        (show P0.val.obj W from φ.hom.app W (n, y)) := by
    let X := (RingedTensor.underlying R).obj N
    let Y := (RingedTensor.underlying R).obj N
    let Z := (RingedTensor.underlying R).obj M
    let Z' := (X ⊗ Y) ⊗ Z
    let a : Z' ⟶ X := CartesianMonoidalCategory.fst (X ⊗ Y) Z ≫
      CartesianMonoidalCategory.fst X Y
    let b : Z' ⟶ Y := CartesianMonoidalCategory.fst (X ⊗ Y) Z ≫
      CartesianMonoidalCategory.snd X Y
    let c : Z' ⟶ Z := CartesianMonoidalCategory.snd (X ⊗ Y) Z
    have hh := hAddR Z' a b c (CartesianMonoidalCategory.lift a b ≫ addition R N)
      (fun _ _ ↦ rfl)
    exact congrArg (fun f : Z' ⟶ (RingedTensor.underlying R).obj P0 ↦
      f.hom.app W ((x, y), n)) hh
  have hSmulSections W (x : R.obj.obj W) (y : M.val.obj W)
      (n : N.val.obj W) :
      φ.hom.app W (x • y, n) =
        x • (show P0.val.obj W from φ.hom.app W (y, n)) := by
    let X := rset R
    let Y := (RingedTensor.underlying R).obj M
    let Z := (RingedTensor.underlying R).obj N
    let Z' := (X ⊗ Y) ⊗ Z
    let a : Z' ⟶ X := CartesianMonoidalCategory.fst (X ⊗ Y) Z ≫
      CartesianMonoidalCategory.fst X Y
    let b : Z' ⟶ Y := CartesianMonoidalCategory.fst (X ⊗ Y) Z ≫
      CartesianMonoidalCategory.snd X Y
    let c : Z' ⟶ Z := CartesianMonoidalCategory.snd (X ⊗ Y) Z
    have hh := hSmul Z' a b c (CartesianMonoidalCategory.lift a b ≫ action R M)
      (fun _ _ ↦ rfl)
    exact congrArg (fun f : Z' ⟶ (RingedTensor.underlying R).obj P0 ↦
      f.hom.app W ((x, y), n)) hh
  have hSmulRSections W (x : R.obj.obj W) (y : N.val.obj W)
      (n : M.val.obj W) :
      φ.hom.app W (n, x • y) =
        x • (show P0.val.obj W from φ.hom.app W (n, y)) := by
    let X := rset R
    let Y := (RingedTensor.underlying R).obj N
    let Z := (RingedTensor.underlying R).obj M
    let Z' := (X ⊗ Y) ⊗ Z
    let a : Z' ⟶ X := CartesianMonoidalCategory.fst (X ⊗ Y) Z ≫
      CartesianMonoidalCategory.fst X Y
    let b : Z' ⟶ Y := CartesianMonoidalCategory.fst (X ⊗ Y) Z ≫
      CartesianMonoidalCategory.snd X Y
    let c : Z' ⟶ Z := CartesianMonoidalCategory.snd (X ⊗ Y) Z
    have hh := hSmulR Z' a b c (CartesianMonoidalCategory.lift a b ≫ action R N)
      (fun _ _ ↦ rfl)
    exact congrArg (fun f : Z' ⟶ (RingedTensor.underlying R).obj P0 ↦
      f.hom.app W ((x, y), n)) hh
  let β' (W : Cᵒᵖ) : M.val.obj W →ₗ[R.obj.obj W]
      N.val.obj W →ₗ[R.obj.obj W] P0.val.obj W :=
    LinearMap.mk₂ _ (fun m n ↦ φ.hom.app W (m, n))
      (hAddSections W) (hSmulSections W)
      (fun m n n' ↦ hAddRSections W n n' m)
      (fun r m n ↦ hSmulRSections W r n m)
  have hβ' : ∀ {U W : Cᵒᵖ} (i : U ⟶ W) (m : M.val.obj U) (n : N.val.obj U),
      β' W (M.val.map i m) (N.val.map i n) = P0.val.map i (β' U m n) := by
    intro U W i m n
    exact congrArg (fun k ↦ k (m, n)) (φ.hom.naturality i)
  obtain ⟨f, hf, _⟩ := tensor_bilinear_universal R M N P0 β' hβ'
  refine ⟨f, ?_⟩
  ext W t
  exact hf W t.1 t.2

-- The proof checks transported module structures in four bilinear identities and two inverses.
/-- The map representing the transported pure pairing is invertible.
Source: Stacks Project, Modules on Sites, Tag 03EL, the third equality of the Hom chain.
(blueprint: lem-weil-pbc-algebraic-inverse-image-pairing-isIso).

Proof: transport the product-preserving right adjoint on set sheaves to modules over R,
using the adjoint of I.ringUnderlying as the structural ring map. The graph identities for
I.moduleAdd and I.moduleSMul, and the corresponding right-adjoint operations, show that
the sheaf adjunction restricts to linear maps for the specified I. This also proves that
maps out of I(M tensor N) are determined by the transported pure pairing: transpose two
such maps, test their mates on pure source tensors, then use the tensor universal property.

For H = I(M) tensor I(N), transpose its pure pairing along the inverse product comparison.
For each of the four bilinearity identities, use the adjunction's naturality, its formulas
for addition and scalar multiplication, and the corresponding graph identity of I. Evaluate
on the universal triple of operands to obtain sectionwise bilinearity. The source tensor
universal property gives a linear map M tensor N into the module direct image of H.
The restricted adjunction transposes this map to gamma : I(M tensor N) → H.

Naturality of the adjunction and the source tensor's pairing formula show that gamma
composed with the transported pure pairing is the pure pairing of H. The normalization
of b and tensor extensionality give b followed by gamma equal to the identity on H.
The extensionality for maps out of I(M tensor N), proved above, then gives gamma followed
by b equal to the identity. These are the two inverse identities. All constructions use
the specified I. No points or nonzero-ring assumption is needed; zero modules, zero rings
and empty sites satisfy the same argument. -/
theorem inverseImageTensorPairing_isIso
    (R : Sheaf J CommRingCat.{u}) (RI : Sheaf K CommRingCat.{u})
    (F : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (adj : F ⊣ V) [PreservesFiniteLimits F]
    (I : AlgebraicInverseImage F R RI)
    (M N : SheafOfModules.{u} (ringSheaf R))
    (b : (monoidalCategory RI).tensorObj (I.modules.obj M) (I.modules.obj N) ⟶
      I.modules.obj ((monoidalCategory R).tensorObj M N))
    (hb : ∀ W m n, b.val.app W (pure RI _ _ W m n) =
      (inverseImagePurePairing R RI F I M N).hom.app W (m, n)) : IsIso b := by
  let : PreservesLimits V := adj.rightAdjoint_preservesLimits
  have hR := ringOperations R RI F I
  obtain ⟨I', P, eI, eP, hI, hP, B, hBL, hBR, hB⟩ := geometric_module_transport J K F V adj
    R RI RI I.ringUnderlying.symm (radd R) (rmul R) (radd RI) (rmul RI)
    ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl, hR⟩ (𝟙 RI)
  clear hB hBR hBL B hI eI I'
  have hOps H :
      madd R (P.obj H) ≫ eP.hom.app H = prod.map (eP.hom.app H) (eP.hom.app H) ≫
        inv (prodComparison V ((RingedTensor.underlying RI).obj H)
          ((RingedTensor.underlying RI).obj H)) ≫
          V.map (madd RI H) ∧
      msmul R (P.obj H) ≫ eP.hom.app H =
        prod.map (adj.homEquiv _ _ I.ringUnderlying.hom) (eP.hom.app H) ≫
          inv (prodComparison V (rset RI) ((RingedTensor.underlying RI).obj H)) ≫
            V.map (msmul RI H) := by
    have : PreservesLimits V := adj.rightAdjoint_preservesLimits
    obtain ⟨aH, sH, aP, sP, k, haH, hsH, haP, hsP, hVA, hk₁, hk₂, hk⟩ := hP H
    have h₁ : aH = madd RI H := by ext U t; exact haH U t
    have h₂ : sH = msmul RI H := by ext U t; exact hsH U t
    have h₃ : aP = madd R (P.obj H) := by ext U t; exact haP U t
    have h₄ : sP = msmul R (P.obj H) := by ext U t; exact hsP U t
    subst aH sH aP sP
    constructor
    · exact right_operation V (eP.app H) _ _ hVA
    · rw [hk]
      simp only [Iso.symm_inv] at hk₁
      have he := right_pair V k (adj.homEquiv _ _ I.ringUnderlying.hom)
        (eP.hom.app H) hk₁ hk₂
      rw [he]
      rfl
  let eI := I.moduleUnderlying
  obtain ⟨E, hE⟩ : ∃ E : ∀ M0 H0,
      ((RingedTensor.underlying RI).obj (I.modules.obj M0) ⟶
        (RingedTensor.underlying RI).obj H0) ≃
      ((RingedTensor.underlying R).obj M0 ⟶ (RingedTensor.underlying R).obj (P.obj H0)),
      E = fun M0 H0 ↦ mateIsoEquiv adj (eI.app M0) (eP.app H0) := ⟨_, rfl⟩
  have hImage M0 H0 (α : (RingedTensor.underlying RI).obj (I.modules.obj M0) ⟶
      (RingedTensor.underlying RI).obj H0) :
      (∃ a : I.modules.obj M0 ⟶ H0, (RingedTensor.underlying RI).map a = α) ↔
        ∃ b : M0 ⟶ P.obj H0, (RingedTensor.underlying R).map b = E M0 H0 α := by
    apply mate_linear_iff R RI F V adj I M0 H0 (P.obj H0) (eP.app H0)
      (hOps H0).1 (hOps H0).2 α (E M0 H0 α)
    rw [hE]
    exact mateIsoEquiv_equation adj (eI.app M0) (eP.app H0) α
  let : F.Monoidal := by
    set_option backward.isDefEq.respectTransparency false in
      exact (Functor.Braided.ofChosenFiniteProducts F).toMonoidal
  have hExt H0 (a a' : I.modules.obj ((monoidalCategory R).tensorObj M N) ⟶ H0)
      (hh : inverseImagePurePairing R RI F I M N ≫ (RingedTensor.underlying RI).map a =
        inverseImagePurePairing R RI F I M N ≫ (RingedTensor.underlying RI).map a') :
      a = a' := by
    let T := (monoidalCategory R).tensorObj M N
    obtain ⟨f0, hf0⟩ := (hImage T H0 ((RingedTensor.underlying RI).map a)).mp ⟨a, rfl⟩
    obtain ⟨g0, hg0⟩ := (hImage T H0 ((RingedTensor.underlying RI).map a')).mp ⟨a', rfl⟩
    have hq : F.map (pureSheaf R M N) ≫ I.moduleUnderlying.inv.app T ≫
        (RingedTensor.underlying RI).map a =
        F.map (pureSheaf R M N) ≫ I.moduleUnderlying.inv.app T ≫
          (RingedTensor.underlying RI).map a' := by
      apply (cancel_epi (Functor.LaxMonoidal.μ F _ _)).mp
      apply (cancel_epi (I.moduleUnderlying.hom.app M ⊗ₘ I.moduleUnderlying.hom.app N)).mp
      simpa only [inverseImagePurePairing, Category.assoc] using hh
    have hm := congrArg (adj.homEquiv _ _) hq
    rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_left] at hm
    have hma : adj.homEquiv _ _ (I.moduleUnderlying.inv.app T ≫
        (RingedTensor.underlying RI).map a) =
        E T H0 ((RingedTensor.underlying RI).map a) ≫ eP.hom.app H0 :=
      by rw [hE]; exact mateIsoEquiv_equation adj (eI.app T) (eP.app H0) _
    have hma' : adj.homEquiv _ _ (I.moduleUnderlying.inv.app T ≫
        (RingedTensor.underlying RI).map a') =
        E T H0 ((RingedTensor.underlying RI).map a') ≫ eP.hom.app H0 :=
      by rw [hE]; exact mateIsoEquiv_equation adj (eI.app T) (eP.app H0) _
    rw [hma, hma', ← hf0, ← hg0] at hm
    have he : pureSheaf R M N ≫ (RingedTensor.underlying R).map f0 =
        pureSheaf R M N ≫ (RingedTensor.underlying R).map g0 := by
      apply (cancel_mono (eP.hom.app H0)).mp
      simpa only [Category.assoc] using hm
    have hfg : f0 = g0 := by
      apply pure_hom_ext R M N (P.obj H0)
      intro W m n
      exact congrArg (fun k ↦ k.hom.app W (m, n)) he
    apply (RingedTensor.underlying RI).map_injective
    apply (E T H0).injective
    rw [← hf0, ← hg0, hfg]
  let H := (monoidalCategory RI).tensorObj (I.modules.obj M) (I.modules.obj N)
  let β := pureSheaf RI (I.modules.obj M) (I.modules.obj N)
  let α := inv (Functor.LaxMonoidal.μ F _ _) ≫
    (I.moduleUnderlying.inv.app M ⊗ₘ I.moduleUnderlying.inv.app N) ≫ β
  obtain ⟨φ, hφdef⟩ : ∃ φ :
      (RingedTensor.underlying R).obj M ⊗ (RingedTensor.underlying R).obj N ⟶
        (RingedTensor.underlying R).obj (P.obj H),
      φ = mateIsoEquiv adj (Iso.refl _) (eP.app H) α := ⟨_, rfl⟩
  have hφ Z (x : Z ⟶ (RingedTensor.underlying R).obj M)
      (y : Z ⟶ (RingedTensor.underlying R).obj N) :
      CartesianMonoidalCategory.lift x y ≫ φ =
        mateIsoEquiv adj (Iso.refl _) (eP.app H)
          (CartesianMonoidalCategory.lift
            (F.map x ≫ I.moduleUnderlying.inv.app M)
            (F.map y ≫ I.moduleUnderlying.inv.app N) ≫ β) := by
    rw [hφdef]
    exact transposePair_lift R RI F V adj I M N H (P.obj H) (eP.app H) β Z x y
  obtain ⟨f, hf'⟩ := transpose_bilinear R RI F V adj I M N H (P.obj H) (eP.app H)
    (hOps H).1 (hOps H).2 β (pureBilin RI (I.modules.obj M) (I.modules.obj N))
    (fun _ _ _ ↦ rfl) φ hφ
  obtain ⟨γ, hγ⟩ := (hImage _ H ((E _ H).symm ((RingedTensor.underlying R).map f))).mpr
    ⟨f, (E _ H).apply_symm_apply _ |>.symm⟩
  have hγ' : E _ H ((RingedTensor.underlying RI).map γ) =
      (RingedTensor.underlying R).map f := by
    rw [hγ, Equiv.apply_symm_apply]
  have hq : F.map (pureSheaf R M N) ≫ I.moduleUnderlying.inv.app
      ((monoidalCategory R).tensorObj M N) ≫ (RingedTensor.underlying RI).map γ = α := by
    apply (adj.homEquiv _ _).injective
    have hm : adj.homEquiv _ _ (I.moduleUnderlying.inv.app
        ((monoidalCategory R).tensorObj M N) ≫ (RingedTensor.underlying RI).map γ) =
        E _ H ((RingedTensor.underlying RI).map γ) ≫ eP.hom.app H :=
      by rw [hE]; exact mateIsoEquiv_equation adj (eI.app _) (eP.app H) _
    rw [adj.homEquiv_naturality_left, hm, hγ', ← Category.assoc, hf']
    rw [hφdef]
    exact (mateIsoEquiv_equation adj (Iso.refl _) (eP.app H) α).symm
  have hB : inverseImagePurePairing R RI F I M N ≫
      (RingedTensor.underlying RI).map γ = β := by
    change (I.moduleUnderlying.hom.app M ⊗ₘ I.moduleUnderlying.hom.app N) ≫
      Functor.LaxMonoidal.μ F _ _ ≫ F.map (pureSheaf R M N) ≫
        I.moduleUnderlying.inv.app ((monoidalCategory R).tensorObj M N) ≫
          (RingedTensor.underlying RI).map γ = β
    rw [hq]
    dsimp only [α]
    simp only [IsIso.hom_inv_id_assoc, tensorHom_comp_tensorHom_assoc,
      Iso.hom_inv_id_app, id_tensorHom_id, Category.id_comp]
  have hb' : β ≫ (RingedTensor.underlying RI).map b =
      inverseImagePurePairing R RI F I M N := by
    ext W t
    exact hb W t.1 t.2
  have hleft : b ≫ γ = 𝟙 H := by
    apply pure_hom_ext RI (I.modules.obj M) (I.modules.obj N) H
    intro W m n
    exact (congrArg (γ.val.app W) (hb W m n)).trans
      (congrArg (fun k ↦ k.hom.app W (m, n)) hB)
  have hright : γ ≫ b = 𝟙 (I.modules.obj ((monoidalCategory R).tensorObj M N)) := by
    apply hExt
    rw [Functor.map_comp, ← Category.assoc, hB, hb']
    rfl
  exact ⟨⟨γ, hleft, hright⟩⟩

end SheafOfModules.RingedTensor
