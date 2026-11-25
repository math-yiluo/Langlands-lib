/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.AlgebraicGeometry.ChangeOfRingsTensorBalancingExists
import WeilConjectures.AlgebraicGeometry.ChangeOfRingsTensorBalancingUnique

/-! # Universal property of the change-of-rings balancing map

Source: Stacks Project, Morphisms, proof of Lemma 01SB; Sheaves, Lemma 0089.
(blueprint: lem-weil-pbc-change-of-rings-tensor-balancing-universal).
-/

@[expose] public section

universe u

open CategoryTheory Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

set_option hygiene false in
local notation "𝓡" S => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj S
set_option hygiene false in
local notation "𝓻" a => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map a

/-- Maps out of change of rings are exactly maps equalizing the two algebra actions.
Source: Stacks Project, Morphisms, proof of Lemma 01SB (change of rings), and
Sheaves, Lemma 0089 (sheafification universal property).
(blueprint: lem-weil-pbc-change-of-rings-tensor-balancing-universal).

Proof: precompose f with the tensor presheaf sheafification unit. Its sectionwise
bilinear map h(c,p) = f(c tensor p) satisfies h(c,bp) = h(φ(b)c,p), by the
assumed equality of the action composites evaluated on b tensor (c tensor p).
The universal property of the sectionwise B-tensor product therefore factors h
uniquely through C tensor_B P as an O-linear map. These maps commute with
restrictions, since both composites do so and pure tensors generate. A target
O-module Q need not have a C-action: sheafification here is applied to the
underlying O-module presheaf of C tensor_B P. Restricting the C-module
sheafification to O identifies it with that O-module sheafification, by the
universal property (or by the common associated additive sheaf and induced
scalar action). Extend the sectionwise map to T using this identification.
The formula for g and uniqueness of sheafification show g ≫ t = f.
For uniqueness, if g ≫ t' = f, the two maps from the presheaf C tensor_B P
agree on every c tensor_B p by the formula for g. Pure tensors generate, so
they agree as presheaf maps. The sheafification universal property gives t'=t.
This works for zero modules and empty opens, and requires no quasi-coherence.
-/
theorem changeOfRings_tensor_balancing_universal (Y : Scheme.{u})
    (B C : Y.CommAlgebraSheaf) (φ : B ⟶ C)
    (P : SheafOfModules.{u} (𝓡 B.right)) :
    let P₀ := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P
    let S := tensorObj C.toModule P₀
    let T := (SheafOfModules.restrictScalars (𝓻 C.hom)).obj
      (SheafOfModules.changeOfRings.{u, u, u} φ.right P)
    ∀ (a d : tensorObj B.toModule S ⟶ S) (g : S ⟶ T),
      (∀ (W : Y.Opens) (b : B.right.obj.obj (op W))
          (c : C.right.obj.obj (op W)) (p : P.val.obj (op W)),
        a.app W (tmulSection (M := B.toModule) b
          (tmulSection (M := C.toModule) (N := P₀) c p)) =
          tmulSection (M := C.toModule) (N := P₀) c (b • p)) →
      (∀ (W : Y.Opens) (b : B.right.obj.obj (op W))
          (c : C.right.obj.obj (op W)) (p : P.val.obj (op W)),
        d.app W (tmulSection (M := B.toModule) b
          (tmulSection (M := C.toModule) (N := P₀) c p)) =
          tmulSection (M := C.toModule) (N := P₀) (φ.right.hom.app (op W) b * c) p) →
      (∀ (W : Y.Opens) (c : C.right.obj.obj (op W)) (p : P.val.obj (op W)),
        g.app W (tmulSection (M := C.toModule) (N := P₀) c p) =
          (((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 C.right).obj)).unit.app
            (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ.right P)).app (op W))
              (c ⊗ₜ[B.right.obj.obj (op W), (φ.right.hom.app (op W)).hom] p)) →
      ∀ (Q : Y.Modules) (f : S ⟶ Q), a ≫ f = d ≫ f →
        ∃! t : T ⟶ Q, g ≫ t = f := by
  dsimp
  intro a d g ha hd hg Q f hfd
  obtain ⟨t, ht⟩ := changeOfRings_tensor_balancing_universal_exists
    Y B C φ P a d g ha hd hg Q f hfd
  refine ⟨t, ht, ?_⟩
  intro t' ht'
  exact (changeOfRings_tensor_balancing_universal_unique
    Y B C φ P a d g ha hd hg Q f t t' ht ht'
    ).symm

end AlgebraicGeometry.Scheme.Modules
