/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
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
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.HomCongr

/-! # The trilinear universal property of the sheaf tensor product

Source: Stacks Project, Modules on Sites, Sections 03EK, 04TT and Lemma 03EO.
(blueprint: lem-pd-sheaf-trilinear-universal)

The trilinear maps are expressed directly as restriction-compatible families of
separately linear functions, without introducing a second notion of sheaf morphism.
The tensor objects and pure tensors are the existing sheafifications of the
sectionwise balanced tensor product, including the inner sheafification.
-/

@[expose] public section

universe uC vC u

open CategoryTheory

namespace SheafOfModules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

section Helpers
variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})

private noncomputable abbrev sheafify :=
  PresheafOfModules.sheafification.{u}
    (R := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) (𝟙 _)

private noncomputable abbrev adj :=
  PresheafOfModules.sheafificationAdjunction.{u}
    (R := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) (𝟙 _)

private noncomputable def unitMap
    (P : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})) :
    P ⟶ ((sheafify R).obj P).val := (adj R).unit.app P

private instance unitMap_injective
    (P : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})) :
    PresheafOfModules.IsLocallyInjective J (unitMap R P) := by
  change PresheafOfModules.IsLocallyInjective J (PresheafOfModules.toSheafify
    (R := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) (𝟙 _)
    (CategoryTheory.toSheafify J P.presheaf))
  infer_instance

private instance unitMap_surjective
    (P : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})) :
    PresheafOfModules.IsLocallySurjective J (unitMap R P) := by
  change PresheafOfModules.IsLocallySurjective J (PresheafOfModules.toSheafify
    (R := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) (𝟙 _)
    (CategoryTheory.toSheafify J P.presheaf))
  infer_instance

private noncomputable def tripleHomEquiv (A B T H : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
    ((siteSheafTensorRight (A := R) T).obj
      ((siteSheafTensorRight (A := R) B).obj A) ⟶ H) ≃
    (siteTensorPresheaf (siteTensorPresheaf A.val B.val) T.val ⟶ H.val) := by
  let P := siteTensorPresheaf A.val B.val
  let q := siteTensorHom (unitMap R P) T.val
  have : IsIso ((sheafify R).map q) :=
    PresheafOfModules.sheafification_tensorHom_isIso (R := R.obj) (J := J)
      (f := unitMap R P) (N := T.val)
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).property
  exact (Iso.homCongr (asIso ((sheafify R).map q)).symm (Iso.refl H)).trans
    ((adj R).homEquiv _ H)

private theorem tripleHomEquiv_apply (A B T H : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (f : (siteSheafTensorRight (A := R) T).obj
      ((siteSheafTensorRight (A := R) B).obj A) ⟶ H)
    (U : Cᵒᵖ) (x : A.val.obj U) (y : B.val.obj U) (z : T.val.obj U) :
    (tripleHomEquiv R A B T H f).app U ((x ⊗ₜ[R.obj.obj U] y) ⊗ₜ[R.obj.obj U] z) =
      f.val.app U (siteSheafTensorTmul (A := R) _ T U
        (siteSheafTensorTmul (A := R) A B U x y) z) := by
  change ((adj R).homEquiv _ H
    ((sheafify R).map (siteTensorHom
      (unitMap R (siteTensorPresheaf A.val B.val)) T.val) ≫ f ≫ 𝟙 H)).app U _ = _
  rw [Category.comp_id, (adj R).homEquiv_naturality_left]
  rfl

private abbrev Families (A B T H : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :=
  { β : ∀ U : Cᵒᵖ, A.val.obj U → B.val.obj U → T.val.obj U → H.val.obj U //
    (∀ U y z, IsLinearMap (R.obj.obj U) (fun x ↦ β U x y z)) ∧
    (∀ U x z, IsLinearMap (R.obj.obj U) (fun y ↦ β U x y z)) ∧
    (∀ U x y, IsLinearMap (R.obj.obj U) (fun z ↦ β U x y z)) ∧
    (∀ {U V : Cᵒᵖ} (i : U ⟶ V) (x : A.val.obj U)
      (y : B.val.obj U) (z : T.val.obj U),
      β V (A.val.map i x) (B.val.map i y) (T.val.map i z) =
        H.val.map i (β U x y z)) }

private noncomputable def evaluate (A B T H : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (k : siteTensorPresheaf (siteTensorPresheaf A.val B.val) T.val ⟶ H.val) :
    Families R A B T H :=
  ⟨fun U x y z ↦ k.app U ((x ⊗ₜ[R.obj.obj U] y) ⊗ₜ[R.obj.obj U] z), by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro U y z
      constructor
      · intro x x'
        simp only [TensorProduct.add_tmul, map_add]
      · intro r x
        simp only [← TensorProduct.smul_tmul', map_smul]
    · intro U x z
      constructor
      · intro y y'
        simp only [TensorProduct.tmul_add, TensorProduct.add_tmul, map_add]
      · intro r y
        simp only [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', map_smul]
    · intro U x y
      constructor
      · intro z z'
        simp only [TensorProduct.tmul_add, map_add]
      · intro r z
        simp only [TensorProduct.tmul_smul, map_smul]
    · intro U V i x y z
      exact PresheafOfModules.naturality_apply k i
        ((x ⊗ₜ[R.obj.obj U] y) ⊗ₜ[R.obj.obj U] z)⟩

private theorem evaluate_injective (A B T H : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
    Function.Injective (evaluate R A B T H) := by
  intro f g h
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro q z
  induction q using TensorProduct.inductionOn with
  | tmul x y => exact congrArg (fun b ↦ b.1 U x y z) h
  | add q q' hq hq' => simp only [TensorProduct.add_tmul, map_add, hq, hq']

private def curry (A B T H : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (β : Families R A B T H) (U : Cᵒᵖ) :
    A.val.obj U →ₗ[R.obj.obj U]
      B.val.obj U →ₗ[R.obj.obj U] T.val.obj U →ₗ[R.obj.obj U] H.val.obj U where
  toFun x :=
    { toFun := fun y ↦ IsLinearMap.mk' (β.1 U x y) (β.2.2.2.1 U x y)
      map_add' := fun y y' ↦ LinearMap.ext (fun z ↦ (β.2.2.1 U x z).map_add y y')
      map_smul' := fun r y ↦ LinearMap.ext (fun z ↦ (β.2.2.1 U x z).map_smul r y) }
  map_add' x x' := LinearMap.ext (fun y ↦ LinearMap.ext
    (fun z ↦ (β.2.1 U y z).map_add x x'))
  map_smul' r x := LinearMap.ext (fun y ↦ LinearMap.ext
    (fun z ↦ (β.2.1 U y z).map_smul r x))

private noncomputable def liftTriple (A B T H : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (β : Families R A B T H) :
    siteTensorPresheaf (siteTensorPresheaf A.val B.val) T.val ⟶ H.val where
  app U := ModuleCat.ofHom (TensorProduct.lift (TensorProduct.lift (curry R A B T H β U)))
  naturality {U V} i := by
    apply ModuleCat.hom_ext
    ext q
    change TensorProduct.lift (TensorProduct.lift (curry R A B T H β V))
        ((siteTensorPresheaf (siteTensorPresheaf A.val B.val) T.val).map i q) =
      H.val.map i (TensorProduct.lift (TensorProduct.lift (curry R A B T H β U)) q)
    induction q using TensorProduct.inductionOn with
    | tmul q z =>
      induction q using TensorProduct.inductionOn with
      | tmul x y => exact β.2.2.2.2 i x y z
      | add q q' hq hq' =>
        simp only [TensorProduct.add_tmul, map_add, hq, hq']
    | add q q' hq hq' => simp only [map_add, hq, hq']

private theorem evaluate_surjective (A B T H : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
    Function.Surjective (evaluate R A B T H) := by
  intro β
  refine ⟨liftTriple R A B T H β, ?_⟩
  apply Subtype.ext
  rfl

private noncomputable def trilinearEquiv (A B T H : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
    ((siteSheafTensorRight (A := R) T).obj
      ((siteSheafTensorRight (A := R) B).obj A) ⟶ H) ≃ Families R A B T H :=
  (tripleHomEquiv R A B T H).trans
    (Equiv.ofBijective (evaluate R A B T H)
      ⟨evaluate_injective R A B T H, evaluate_surjective R A B T H⟩)

private theorem trilinearEquiv_apply (A B T H : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (f : (siteSheafTensorRight (A := R) T).obj
      ((siteSheafTensorRight (A := R) B).obj A) ⟶ H)
    (U : Cᵒᵖ) (x : A.val.obj U) (y : B.val.obj U) (z : T.val.obj U) :
    (trilinearEquiv R A B T H f).1 U x y z =
      f.val.app U (siteSheafTensorTmul (A := R) _ T U
        (siteSheafTensorTmul (A := R) A B U x y) z) :=
  tripleHomEquiv_apply R A B T H f U x y z

private theorem map_tmul_first {A A' B : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)} (a : A' ⟶ A)
    (U : Cᵒᵖ) (x : A'.val.obj U) (y : B.val.obj U) :
    ((siteSheafTensorRight (A := R) B).map a).val.app U
      (siteSheafTensorTmul (A := R) A' B U x y) =
    siteSheafTensorTmul (A := R) A B U (a.val.app U x) y := by
  exact (congrArg (fun q ↦ q.app U (x ⊗ₜ[R.obj.obj U] y))
    ((adj R).unit.naturality (siteTensorHom a.val B.val))).symm

private theorem map_tmul_second {A B B' : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)} (b : B' ⟶ B)
    (U : Cᵒᵖ) (x : A.val.obj U) (y : B'.val.obj U) :
    (siteSheafTensorSecondMap (A := R) A b).val.app U
      (siteSheafTensorTmul (A := R) A B' U x y) =
    siteSheafTensorTmul (A := R) A B U x (b.val.app U y) := by
  exact (congrArg (fun q ↦ q.app U (x ⊗ₜ[R.obj.obj U] y))
    ((adj R).unit.naturality (siteTensorSecondMap A.val b.val))).symm

private theorem map_tmul_both {A A' B B' : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)}
    (a : A' ⟶ A) (b : B' ⟶ B)
    (U : Cᵒᵖ) (x : A'.val.obj U) (y : B'.val.obj U) :
    (((siteSheafTensorRight (A := R) B').map a ≫
      siteSheafTensorSecondMap (A := R) A b).val.app U)
      (siteSheafTensorTmul (A := R) A' B' U x y) =
    siteSheafTensorTmul (A := R) A B U (a.val.app U x) (b.val.app U y) := by
  exact (congrArg ((siteSheafTensorSecondMap (A := R) A b).val.app U)
    (map_tmul_first R a U x y)).trans (map_tmul_second R b U (a.val.app U x) y)

end Helpers

/-- The natural trilinear bijection and its pure-triple equality criterion.
Source: Stacks Project, Modules on Sites, Sections 03EK, 04TT and Lemma 03EO
(blueprint: lem-pd-sheaf-trilinear-universal).

The three IsLinearMap conditions express linearity in each variable. The
subtype's restriction equation says precisely that the maps form a morphism of
underlying sheaves of sets. The first clause normalizes the equivalences on
canonical local pure triples. The second is contravariant naturality in all
three factors and covariant naturality in the target. The third detects equality
on pure triples over every object, without asserting sectionwise generation
of the sheafified tensor.

Proof: (1) Put P = homObj T H. The slice description of def-pur-sheaf-hom
and lem-pur-sheaf-hom-is-sheaf sends a trilinear family beta to the bilinear
family c_U(x,y)_v(z) = beta_V(x|V,y|V,z). Restriction compatibility makes
these slice morphisms and makes c bilinear with the restricted scalar action.
(2) Apply lem-pc-sites-sheaf-tensor-bilinear-universal with target P to get
a : A tensor B -> P. Evaluation b_U(q,z) = a_U(q)_id(z) is bilinear and
restriction-compatible. Apply the binary property again to obtain f.
(3) Evaluating f on a pure triple returns beta, proving surjectivity; the
canonical tensor maps and f are separately linear and restriction-compatible.
(4) For any f define a^f_U(q)_v(z) = f_V(q|V tensor z). Semilinearity of
restrictions and linearity of f give a module morphism A tensor B -> P.
(5) If f and g agree on all pure triples, their a^f and a^g agree on pure
pairs after testing every slice component. Binary uniqueness first gives
a^f = a^g, and a second application gives f = g. This proves injectivity
and the equality criterion. (6) Tensor maps send pure tensors to tensors
of their images. Evaluating on pure triples gives the four-variable
naturality equation; bijectivity also makes the inverse natural. -/
theorem tensor_trilinear_universal
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u}) :
    ∃ e : ∀ (A B T H : CategoryTheory.ringedSiteModules.{u, u, vC, uC}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)),
      ((siteSheafTensorRight (A := R) T).obj
        ((siteSheafTensorRight (A := R) B).obj A) ⟶ H) ≃
        { β : ∀ U : Cᵒᵖ, A.val.obj U → B.val.obj U → T.val.obj U → H.val.obj U //
          (∀ (U : Cᵒᵖ) (y : B.val.obj U) (z : T.val.obj U),
            IsLinearMap (R.obj.obj U) (fun x ↦ β U x y z)) ∧
          (∀ (U : Cᵒᵖ) (x : A.val.obj U) (z : T.val.obj U),
            IsLinearMap (R.obj.obj U) (fun y ↦ β U x y z)) ∧
          (∀ (U : Cᵒᵖ) (x : A.val.obj U) (y : B.val.obj U),
            IsLinearMap (R.obj.obj U) (fun z ↦ β U x y z)) ∧
          (∀ {U V : Cᵒᵖ} (i : U ⟶ V) (x : A.val.obj U)
            (y : B.val.obj U) (z : T.val.obj U),
            β V (A.val.map i x) (B.val.map i y) (T.val.map i z) =
              H.val.map i (β U x y z)) },
      (∀ (A B T H : CategoryTheory.ringedSiteModules.{u, u, vC, uC}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
        (f : (siteSheafTensorRight (A := R) T).obj
          ((siteSheafTensorRight (A := R) B).obj A) ⟶ H)
        (U : Cᵒᵖ) (x : A.val.obj U) (y : B.val.obj U) (z : T.val.obj U),
        ((e A B T H).toFun f).1 U x y z = f.val.app U
          (siteSheafTensorTmul (A := R) ((siteSheafTensorRight (A := R) B).obj A) T U
            (siteSheafTensorTmul (A := R) A B U x y) z)) ∧
      (∀ (A B T H A' B' T' H' : CategoryTheory.ringedSiteModules.{u, u, vC, uC}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
        (a : A' ⟶ A) (b : B' ⟶ B) (t : T' ⟶ T) (h : H ⟶ H')
        (f : (siteSheafTensorRight (A := R) T).obj
          ((siteSheafTensorRight (A := R) B).obj A) ⟶ H)
        (U : Cᵒᵖ) (x : A'.val.obj U) (y : B'.val.obj U) (z : T'.val.obj U),
        ((e A' B' T' H').toFun
          ((siteSheafTensorRight (A := R) T').map
              ((siteSheafTensorRight (A := R) B').map a ≫
                siteSheafTensorSecondMap (A := R) A b) ≫
            siteSheafTensorSecondMap (A := R)
              ((siteSheafTensorRight (A := R) B).obj A) t ≫ f ≫ h)).1 U x y z =
          h.val.app U (((e A B T H).toFun f).1 U
            (a.val.app U x) (b.val.app U y) (t.val.app U z))) ∧
      (∀ (A B T H : CategoryTheory.ringedSiteModules.{u, u, vC, uC}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
        (f g : (siteSheafTensorRight (A := R) T).obj
          ((siteSheafTensorRight (A := R) B).obj A) ⟶ H),
        f = g ↔ ∀ (U : Cᵒᵖ) (x : A.val.obj U) (y : B.val.obj U) (z : T.val.obj U),
          f.val.app U
            (siteSheafTensorTmul (A := R) ((siteSheafTensorRight (A := R) B).obj A) T U
              (siteSheafTensorTmul (A := R) A B U x y) z) =
          g.val.app U
            (siteSheafTensorTmul (A := R) ((siteSheafTensorRight (A := R) B).obj A) T U
              (siteSheafTensorTmul (A := R) A B U x y) z)) := by
  refine ⟨trilinearEquiv R, ?_, ?_, ?_⟩
  · exact trilinearEquiv_apply R
  · intro A B T H A' B' T' H' a b t h f U x y z
    let ab := (siteSheafTensorRight (A := R) B').map a ≫
      siteSheafTensorSecondMap (A := R) A b
    let outerMap :=  (siteSheafTensorRight (A := R) T').map ab ≫
      siteSheafTensorSecondMap (A := R) ((siteSheafTensorRight (A := R) B).obj A) t
    have hab := map_tmul_both R a b U x y
    have hat := map_tmul_both R ab t U (siteSheafTensorTmul (A := R) A' B' U x y) z
    have hp := hat.trans (congrArg
      (fun q ↦ siteSheafTensorTmul (A := R) _ T U q (t.val.app U z)) hab)
    exact (trilinearEquiv_apply R A' B' T' H' (outerMap ≫ f ≫ h) U x y z).trans
      ((congrArg (fun q ↦ h.val.app U (f.val.app U q)) hp).trans
        (congrArg (h.val.app U)
          (trilinearEquiv_apply R A B T H f U
            (a.val.app U x) (b.val.app U y) (t.val.app U z)).symm))
  · intro A B T H f g
    constructor
    · rintro rfl
      intros
      rfl
    · intro h
      apply (trilinearEquiv R A B T H).injective
      apply Subtype.ext
      funext U x y z
      simpa only [trilinearEquiv_apply] using h U x y z

end SheafOfModules
