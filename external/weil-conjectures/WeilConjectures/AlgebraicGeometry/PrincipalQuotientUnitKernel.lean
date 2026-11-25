/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitKernel
import WeilConjectures.AlgebraicGeometry.FlatInvertibleSectionsTorsionFree
import WeilConjectures.AlgebraicGeometry.PrincipalQuotientMultiplicationImage

/-! # Multiplication is the kernel of restriction to a principal quotient

Source: Stacks Project, More on Morphisms, Tag 0EX8, the divisibility step in both
proofs; Modules, Tag 08KS, the description of pullback to a closed subscheme.
(blueprint: lem-sc-principal-quotient-unit-kernel)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem mono_baseScalar_of_flat
    (A : Type u) [CommRing A] [IsDomain A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [Flat f]
    (L : X.Modules) [L.IsInvertible] (π : A) (hπ : π ≠ 0) :
    Mono (L.smulHom (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom π)) := by
  classical
  let r := ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom π
  have hinj (U : X.Opens) : Function.Injective ((L.smulHom r).app U) := by
    have : (L.restrict U.ι).IsInvertible :=
      IsInvertible.of_iso ((restrictFunctorIsoPullback U.ι).app L).symm
    have h := injective_smul_sections_of_flat A (U.ι ≫ f) (L.restrict U.ι) π hπ
    let e := L.restrictAppIso U.ι ⊤
    have hm (s : Γ(L.restrict U.ι, ⊤)) :
        e.hom (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
          (U.ι ≫ f).appTop).hom π • s) =
        X.presheaf.map (homOfLE (show U.ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op r • e.hom s := by
      dsimp only [e]
      rw [smul_restrictAppIso_hom_apply]
      simp only [Scheme.Hom.comp_appTop, Scheme.Opens.ι_appTop,
        Scheme.Opens.ι_appIso, Iso.refl_inv, r]
      rfl
    have h' : Function.Injective (fun s : Γ(L, U.ι ''ᵁ ⊤) ↦
        X.presheaf.map (homOfLE (show U.ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op r • s) := by
      intro s t he
      have he' : e.hom (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
            (U.ι ≫ f).appTop).hom π • e.inv s) =
          e.hom (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
            (U.ι ≫ f).appTop).hom π • e.inv t) := by
        simpa only [hm, Iso.inv_hom_id_apply] using he
      have he'' := h ((ConcreteCategory.bijective_of_isIso e.hom).1 he')
      exact (ConcreteCategory.bijective_of_isIso e.inv).1 he''
    change Function.Injective (fun s : Γ(L, U) ↦
      X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r • s)
    dsimp only [Scheme.Modules.presheaf] at h'
    rw [U.ι_image_top] at h'
    exact h'
  constructor
  intro Z g h he
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext s
  apply hinj V.unop
  exact congrArg (fun q ↦ q.app V.unop s) he

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Comparing the two chosen tensor adjunctions needs extra definitional reductions.
/-- Over a domain, for a flat scheme and an invertible module, multiplication by a
nonzero base scalar is the kernel of the unit restricting to its principal quotient.

Source: Stacks Project, Tag 0EX8, the step asserting that a section which vanishes
modulo pi can be divided by pi; Modules, Tag 08KS, pullback to a closed subscheme.
(blueprint: lem-sc-principal-quotient-unit-kernel)

Proof:
1. The quotient map A -> A/(pi) is surjective, so its spectrum and its base change
   i to X are closed immersions. On an affine chart Spec B of X, the closed
   subscheme is Spec(B/pi B); consequently its ideal sheaf is pi O_X.
2. Apply injective_smul_sections_of_flat on each open restriction of X and L.
   The composite of the open immersion with f is flat and the restricted line
   bundle is invertible. Thus multiplication by pi is injective on every open's
   sections, hence is a monomorphism of sheaves. Equivalently, the stalk argument
   tensors the injective map A --pi--> A with flat local rings of X and uses the
   local rank-one trivializations of L.
3. Apply closedImmersion_unit_kernel: the kernel of its adjunction unit is the
   image of multiplication J tensor L -> L, where J = pi O_X. This image equals
   the image of L.smulHom(pi): on each trivializing neighbourhood both consist
   precisely of the multiples pi l. Since multiplication is a monomorphism, L
   itself with this multiplication map is a kernel object.
4. The kernel theorem chooses an adjunction via nonempty_tensorPullbackAdjunction,
   whereas the statement uses exists_tensorPullbackAdjunction. Uniqueness of left
   adjoints compares these units by an invertible map on their targets. Composing
   with an isomorphism preserves the kernel fork, proving the displayed limit.

Edge cases: a unit pi gives an empty quotient scheme and invertible multiplication;
the kernel is all of L. The zero module and the empty scheme give zero kernel
objects. The assumption pi != 0 is essential for multiplication to be a kernel
monomorphism on a nonzero module. Neither properness nor integrality of a fibre
nor the valuation-ring condition is used. -/
theorem principal_quotient_unit_kernel
    (A : Type u) [CommRing A] [IsDomain A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [Flat f]
    (L : X.Modules) [L.IsInvertible] (π : A) (hπ : π ≠ 0) :
    let i := pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.span {π}))))
    let η := (Classical.choose (exists_tensorPullbackAdjunction i)).unit.app L
    let μ := L.smulHom (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom π)
    ∃ w : μ ≫ η = 0, Nonempty (IsLimit (KernelFork.ofι μ w)) := by
  classical
  let i := pullback.fst f (Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (Ideal.span {π}))))
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (Ideal.span {π})))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : IsClosedImmersion i := by
    dsimp only [i]
    infer_instance
  let μ := L.smulHom (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom π)
  let m : MonoidalCategory.tensorObj i.ker.toModules L ⟶ L :=
    MonoidalCategory.whiskerRight i.ker.toModulesι L ≫ (MonoidalCategory.leftUnitor L).hom
  have : Mono μ := mono_baseScalar_of_flat A f L π hπ
  have himage : ∃ e : image μ ≅ image m, e.hom ≫ image.ι m = image.ι μ :=
    principal_quotient_multiplication_image A f L π
  obtain ⟨e, he⟩ := himage
  let d : L ≅ image m := (imageMonoIsoSource μ).symm ≪≫ e
  have hd : d.hom ≫ image.ι m = μ := by
    dsimp only [d, Iso.trans_hom, Iso.symm_hom]
    rw [Category.assoc, he, imageMonoIsoSource_inv_ι]
  let adj₁ := Classical.choice (nonempty_tensorPullbackAdjunction i)
  let adj₂ := Classical.choose (exists_tensorPullbackAdjunction i)
  let t := (pushforward i).mapIso ((Adjunction.leftAdjointUniq adj₁ adj₂).app L)
  change ∃ w : μ ≫ adj₂.unit.app L = 0, Nonempty (IsLimit (KernelFork.ofι μ w))
  have ht : adj₁.unit.app L ≫ t.hom = adj₂.unit.app L :=
    Adjunction.unit_leftAdjointUniq_hom_app adj₁ adj₂ L
  have hkernel : ∃ w : image.ι m ≫ adj₁.unit.app L = 0,
      Nonempty (IsLimit (KernelFork.ofι (image.ι m) w)) :=
    (closedImmersion_unit_kernel i L).2
  obtain ⟨w, ⟨hk⟩⟩ := hkernel
  have hw : μ ≫ adj₂.unit.app L = 0 := by
    rw [← ht, ← hd, Category.assoc, ← Category.assoc (image.ι m), w]
    simp
  refine ⟨hw, ⟨KernelFork.IsLimit.ofι' μ hw ?_⟩⟩
  intro K k h
  have h' : k ≫ adj₁.unit.app L = 0 := by
    apply (cancel_mono t.hom).mp
    simpa only [Category.assoc, ht, zero_comp] using h
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hk k h'
  refine ⟨l ≫ d.inv, ?_⟩
  rw [Category.assoc, ← hd, Iso.inv_hom_id_assoc]
  exact hl

end AlgebraicGeometry.Scheme.Modules
