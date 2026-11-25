/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.HomTensor

/-!
# Evaluation for finite locally free module sheaves

Source: blueprint `lem-sc-ext-locally-free.md`, Proof, first sentence
(blueprint: lem-sc-ext-evaluation).
-/

@[expose] public section

universe u

open CategoryTheory
open scoped MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- For a finite locally free module sheaf, the canonical evaluation identifies tensoring
with the dual and internal sheaf Hom, naturally in the coefficient module.

Source: blueprint `lem-sc-ext-locally-free.md`, Proof, first sentence
(blueprint: lem-sc-ext-evaluation).

Proof: (1) Form the presheaf tensor product and the internal Hom sheaf
[def-pur-sheaf-tensor-product, def-pur-sheaf-hom]. The existing `dualTensorHom` is induced
by the restriction-compatible bilinear formula `φ ⊗ g ↦ (x ↦ φ(x) • g)`
[situation-conventions, def-pur-sheaf-modules-hom-module]. On each open
contained in a trivializing member of the finite locally free cover
[def-amb-finite-locally-free-module, allowing varying local ranks], maps from the finite
free sheaf are determined by the images of the standard basis. Both presheaf tensor and
internal Hom sections identify with finite tuples of sections of `G`; evaluation is the
identity under these identifications.
(2) These opens cover every open, so presheaf evaluation is locally injective and locally
surjective. Its sheafification is an isomorphism by
[lem-weil-pbc-site-sheafification-iso-locally-bijective]. The internal Hom target is already
a sheaf, and the module sheafification factorization
[def-weil-presheaf-modules-sheafification] is precisely `dualTensorHom F G`. Its inverse
is again module-linear, so this is an isomorphism of module sheaves.
(3) A map of coefficient modules commutes with the displayed evaluation formula on every
open. It therefore commutes with the sheafified evaluation maps and their inverses,
giving naturality in `G` [def-pur-sheaf-tensor-product, def-pur-sheaf-hom,
def-pur-sheaf-modules-hom-module]. -/
theorem dual_tensor_hom_iso (X : Scheme.{u}) (F : X.Modules)
    [F.IsFiniteLocallyFree] :
    ∃ e : (∀ G : X.Modules, Scheme.Modules.tensorObj (dual F) G ≅ homObj F G),
      (∀ G : X.Modules, (e G).hom = dualTensorHom F G) ∧
      ∀ {G H : X.Modules} (g : G ⟶ H),
        (e G).hom ≫ SheafOfModules.homObjMap (R := X.sheaf) (𝟙 F) g =
          (dual F ◁ g) ≫ (e H).hom := by
  refine ⟨fun G ↦ asIso (dualTensorHom F G), fun G ↦ rfl, ?_⟩
  intro G H g
  exact (dualTensorHom_naturality_right F g).symm

end AlgebraicGeometry.Scheme.Modules
