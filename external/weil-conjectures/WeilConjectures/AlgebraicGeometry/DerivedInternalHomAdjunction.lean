/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
import WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom
import WeilConjectures.AlgebraicGeometry.DerivedTensorSymmetry

/-! # Derived internal-Hom adjunction on a scheme

Source: Stacks Project, Cohomology, Tags 08DJ and 0FPB
(blueprint: lem-sc-derived-internal-hom-adjunction).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry

private theorem tensorHomSymmetryReduction {D : Type*} [Category D]
    [MonoidalCategory D] (H : Dᵒᵖ × D ⥤ D)
    (e : ∀ K L M : D, (K ⟶ H.obj (op L, M)) ≃ (K ⊗ L ⟶ M))
    (hn : (∀ (K K' L L' M M' : D)
        (a : K' ⟶ K) (b : L' ⟶ L) (c : M ⟶ M')
        (f : K ⟶ H.obj (op L, M)),
        e K' L' M' (a ≫ f ≫
          H.map (b.op, c)) =
          (a ⊗ₘ b) ≫ e K L M f ≫ c))
    (s : ∀ K L : D, K ⊗ L ≅ L ⊗ K)
    (hs : (∀ (K K' L L' : D) (a : K ⟶ K') (b : L ⟶ L'),
        (a ⊗ₘ b) ≫ (s K' L').hom = (s K L).hom ≫ (b ⊗ₘ a))) :
    ∃ (e : ∀ K L M : D,
        (K ⟶ H.obj (op L, M)) ≃ (K ⊗ L ⟶ M))
      (s : ∀ K L : D, K ⊗ L ≅ L ⊗ K)
      (e' : ∀ K L M : D,
        (K ⟶ H.obj (op L, M)) ≃ (L ⊗ K ⟶ M)),
      (∀ (K K' L L' M M' : D)
        (a : K' ⟶ K) (b : L' ⟶ L) (c : M ⟶ M')
        (f : K ⟶ H.obj (op L, M)),
        e K' L' M' (a ≫ f ≫
          H.map (b.op, c)) =
          (a ⊗ₘ b) ≫ e K L M f ≫ c) ∧
      (∀ (K K' L L' : D) (a : K ⟶ K') (b : L ⟶ L'),
        (a ⊗ₘ b) ≫ (s K' L').hom = (s K L).hom ≫ (b ⊗ₘ a)) ∧
      (∀ (K L M : D)
        (f : K ⟶ H.obj (op L, M)),
        e' K L M f = (s K L).inv ≫ e K L M f) ∧
      (∀ (K K' L L' M M' : D)
        (a : K' ⟶ K) (b : L' ⟶ L) (c : M ⟶ M')
        (f : K ⟶ H.obj (op L, M)),
        e' K' L' M' (a ≫ f ≫
          H.map (b.op, c)) =
          (b ⊗ₘ a) ≫ e' K L M f ≫ c) := by
  let e' (K L M : D) := (e K L M).trans (Iso.homCongr (s K L) (Iso.refl M))
  refine ⟨e, s, e', hn, hs, ?_, ?_⟩
  · intro K L M f
    simp [e', Iso.homCongr]
  · intro K K' L L' M M' a b c f
    simp only [e', Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_hom,
      Category.comp_id]
    rw [hn]
    have hi : (s K' L').inv ≫ (a ⊗ₘ b) = (b ⊗ₘ a) ≫ (s K L).inv := by
      apply (cancel_mono (s K L).hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [hs, Iso.inv_hom_id_assoc]
    simpa only [Category.assoc] using congrArg (fun g ↦ g ≫ e K L M f ≫ c) hi

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The derived tensor-internal-Hom bijection and tensor symmetry, natural in all variables.
The second bijection is obtained from the first by precomposing with the inverse symmetry.
The tensor is the shared K-flat derived tensor, and RHom is the shared K-injective model.
Source: Stacks Project, Cohomology, Tags 08DJ and 0FPB
(blueprint: lem-sc-derived-internal-hom-adjunction).

Proof:
1. Choose K-flat representatives P of K and L' of L using lem-pc-kflat-resolution and
   the K-injective representative I of M from def-pur-derived-internal-hom and
   prop-pur-kinjective-resolutions-exist. Use the closed sheaf tensor of
   lem-pc-sheaf-modules-tensor-closed.
2. By lem-pur-rhom-well-defined, Hom(L,I) and Hom(L',I) are quasi-isomorphic.
   By lem-pur-hom-kflat-into-kinjective the latter and Hom(P,Hom(L',I)) are K-injective.
   The complex isomorphism of lem-sc-derived-hom-tensor-total identifies this last complex
   with Hom(Tot(P tensor L'),I), representing RHom(K tensor^L L,M).
   Taking H^0 of global sections and using lem-pur-rhom-global-sections gives the bijection.
3. The comparisons in lem-pur-rhom-well-defined, lem-pur-hom-kflat-into-kinjective,
   lem-sc-derived-hom-tensor-total and lem-pur-rhom-global-sections are canonical and
   natural, proving independence of representatives and the displayed naturality equation.
4. The sheaf tensor symmetry with sign (-1)^(pq) gives an isomorphism of total complexes
   Tot(P tensor L') and Tot(L' tensor P). Both compute the shared derived tensors.
   A quasi-isomorphism tensored with a K-flat complex remains a quasi-isomorphism: its
   cone is the tensor with the acyclic cone, acyclic by def-pc-kflat-complex.
   Common K-flat resolutions from lem-pc-kflat-resolution therefore make the symmetry
   independent of choices and natural. Precomposition gives the final natural bijection. -/
theorem scheme_derivedInternalHom_adjunction (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    ∃ (e : ∀ K L M : schemeDerivedCategory X,
        (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).obj (op L, M)) ≃ (K ⊗ L ⟶ M))
      (s : ∀ K L : schemeDerivedCategory X, K ⊗ L ≅ L ⊗ K)
      (e' : ∀ K L M : schemeDerivedCategory X,
        (K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).obj (op L, M)) ≃ (L ⊗ K ⟶ M)),
      (∀ (K K' L L' M M' : schemeDerivedCategory X)
        (a : K' ⟶ K) (b : L' ⟶ L) (c : M ⟶ M')
        (f : K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).obj (op L, M)),
        e K' L' M' (a ≫ f ≫
          (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
            X.toRingedSpace.sheaf).map (b.op, c)) =
          (a ⊗ₘ b) ≫ e K L M f ≫ c) ∧
      (∀ (K K' L L' : schemeDerivedCategory X) (a : K ⟶ K') (b : L ⟶ L'),
        (a ⊗ₘ b) ≫ (s K' L').hom = (s K L).hom ≫ (b ⊗ₘ a)) ∧
      (∀ (K L M : schemeDerivedCategory X)
        (f : K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).obj (op L, M)),
        e' K L M f = (s K L).inv ≫ e K L M f) ∧
      (∀ (K K' L L' M M' : schemeDerivedCategory X)
        (a : K' ⟶ K) (b : L' ⟶ L) (c : M ⟶ M')
        (f : K ⟶ (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).obj (op L, M)),
        e' K' L' M' (a ≫ f ≫
          (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
            X.toRingedSpace.sheaf).map (b.op, c)) =
          (b ⊗ₘ a) ≫ e' K L M f ≫ c) := by
  apply Exists.elim (exists_canonicalDerivedTensorHom.{u, w} X)
  intro e he
  apply Exists.elim (exists_schemeDerivedTensorSymmetry.{u, w} X)
  intro s hs
  exact @tensorHomSymmetryReduction (schemeDerivedCategory X) inferInstance
    (schemeDerivedTensorMonoidal X)
    (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
      X.toRingedSpace.sheaf) e he.1 s hs

end AlgebraicGeometry
