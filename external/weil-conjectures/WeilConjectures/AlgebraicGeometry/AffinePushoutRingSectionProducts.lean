/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.AlgebraicGeometry.AffinePushoutRingSectionComm
import WeilConjectures.Topology.InverseImageRegularExtension
import WeilConjectures.AlgebraicGeometry.AffineModuleTensorBaseChange
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable {U X : Scheme.{u}} (f : U ⟶ X)
/-- Affine pushout sections are finite sums of products of the two section legs.
Source: Stacks Project, Morphisms, Tag 01SB, affine reduction; Schemes, Tags 01IA and 01HV.
(blueprint: stage3-affine-pushout-ring-section-products).

Proof: Let W = f⁻¹V, D = Γ(X,V), C = Γ(U,W), and A = f_*O_U. Since f is
affine, W is affine and f_*O_U is quasi-coherent as an O_X-module. Use
pushout scalar-extension cancellation on the regular A-module. Its inverse
image is the regular module of f⁻¹A, since the inverse-image unit respects
ring operations. Extension along t identifies this with the regular B-module:
the maps z ⊗ a ↦ z*t(a) and z ↦ z ⊗ 1 are inverse by the balancing relation,
and descend through sheafification. The affine pullback section theorem now
gives a surjective linear map C ⊗[D] C → B(W). The cancellation unit formula
and O_U-linearity show that its pure-tensor value is b(c)*t(η(d)). Every tensor
is a finite sum of pure tensors: prove this by tensor induction, using the
empty list for zero, a singleton for a pure tensor, and concatenation for
addition. A preimage of a given section therefore gives the required list.
This uses only surjectivity of the linear comparison and makes no assertion
about uniqueness or tensor relations among the products. The zero ring and
empty W are covered by the empty-list case. -/
theorem affinePushoutSection_products [IsAffineHom f]
    (B : U.toTopCat.Sheaf CommRingCat.{u}) (b : U.sheaf ⟶ B)
    (t : TopCat.Sheaf.inverseImageRing f.base
      ((TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj U.sheaf) ⟶ B)
    (hpushout : IsPushout (tensorPullbackRingMap f)
      ((TopCat.Sheaf.inverseImageConstruction f.base CommRingCat.{u}).map
        (show X.sheaf ⟶
          (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj U.sheaf from ⟨f.c⟩)) b t)
    (V : X.Opens) (hV : IsAffineOpen V) :
    ∀ z : B.obj.obj (op (f ⁻¹ᵁ V)),
      ∃ l : List (Γ(U, f ⁻¹ᵁ V) × Γ(U, f ⁻¹ᵁ V)),
        z = (l.map fun x ↦ (b.hom.app (op (f ⁻¹ᵁ V))).hom x.1 *
          affinePushoutSectionDelta f B t V x.2).sum := by
  classical
  let A := (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj U.sheaf
  let ρ : X.sheaf ⟶ A := ⟨f.c⟩
  let RA := (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj A
  let RB := (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj B
  let S := SheafOfModules.restrictScalars
    ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map ρ)
  let G := SheafOfModules.unit RA
  let M := S.obj G
  let := IsSeparated.of_isAffineHom f
  have : (SheafOfModules.unit U.ringCatSheaf).IsQuasicoherent :=
    SheafOfModules.isQuasicoherent_unit.{u, u, u}
  have hM : M.IsQuasicoherent :=
    isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated f
      (SheafOfModules.unit U.ringCatSheaf)
  obtain ⟨P, pobj, κ, _, hu⟩ := affine_module_tensor_baseChange f B b t hpushout
  obtain ⟨e, he⟩ := SheafOfModules.inverseImageRegularExtension f.base A B t
  let k : P.obj G ≅ SheafOfModules.unit RB := eqToIso (pobj G) ≪≫ e
  let j : (tensorPullback f).obj M ≅
      (SheafOfModules.restrictScalars
        ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map b)).obj
          (SheafOfModules.unit RB) :=
    (κ.app G).symm ≪≫ (SheafOfModules.restrictScalars
      ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map b)).mapIso k
  let W := f ⁻¹ᵁ V
  have hW : IsAffineOpen W := hV.preimage f
  let : Algebra Γ(X, V) Γ(U, W) := (f.appLE V W le_rfl).hom.toAlgebra
  obtain ⟨c, hc, _, hp, _⟩ :=
    exists_tensorPullback_affine_sections f ⟨V, hV⟩ ⟨W, hW⟩ le_rfl
  have hj (d : Γ(U, W)) :
      j.hom.val.app (op W)
        (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app M).val.app
          (op V) d) = affinePushoutSectionDelta f B t V d := by
    exact (congrArg (fun x ↦ e.hom.val.app (op W) x) (hu G (op V) d)).trans
      (he (op V) d)
  intro z
  obtain ⟨y, hy⟩ := (hc M hM).2 (j.inv.val.app (op W) z)
  have hsurj : j.hom.val.app (op W) (c M hM y) = z := by
    rw [hy]
    have h := congrArg (fun q ↦ q.val.app (op W) z) j.inv_hom_id
    exact h
  have hprod : ∀ y : Γ(M, V) ⊗[Γ(X, V)] Γ(U, W),
      ∃ l : List (Γ(U, W) × Γ(U, W)),
        j.hom.val.app (op W) (c M hM y) =
          (l.map fun x ↦ (b.hom.app (op W)).hom x.1 *
            affinePushoutSectionDelta f B t V x.2).sum := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul d a =>
      refine ⟨[(a, d)], ?_⟩
      rw [hp]
      simp only [homOfLE_refl, op_id]
      rw [CategoryTheory.Functor.map_id]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      change j.hom.val.app (op W) (a • _) = _
      rw [(j.hom.val.app (op W)).hom.map_smul]
      change (b.hom.app (op W)).hom a *
        (show B.obj.obj (op W) from j.hom.val.app (op W)
          (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app M).val.app
            (op V) d)) = _
      rw [hj]
    | add y y' hy hy' =>
      obtain ⟨l, hl⟩ := hy
      obtain ⟨l', hl'⟩ := hy'
      refine ⟨l ++ l', ?_⟩
      simp only [map_add, List.map_append, List.sum_append, hl, hl']
  obtain ⟨l, hl⟩ := hprod y
  exact ⟨l, hsurj.symm.trans hl⟩
end
end AlgebraicGeometry.Scheme.Modules
