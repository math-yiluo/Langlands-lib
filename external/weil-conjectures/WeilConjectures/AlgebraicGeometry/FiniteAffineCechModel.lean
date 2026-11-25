/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineAlternatingCechModel
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # The explicit finite affine Čech model over a base

The section complex is formed before associating sheaves. In particular its data depend
on the coefficient module and the chosen cover, rather than on an existence theorem.
Source: Stacks Project, Tag 02KE, finite affine section/base-change calculation.
-/

@[expose] public section

universe u
open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Associate the alternating section complex to the base, after restricting scalars.
The negative terms are zero. Degree `p ≥ 0` is the sheaf associated to the product of
sections on increasing `(p+1)`-tuples, with the signed restriction differential.
Source: Stacks Project, Tag 02KE, proof's Čech construction.
(blueprint: def-pc-finite-affine-cech-model). -/
noncomputable def finiteAffineCechModel {X T : Scheme.{u}} (f : X ⟶ T) (F : X.Modules)
    {r : ℕ} (V : Fin r → X.Opens) : CochainComplex T.Modules ℤ :=
  ((Modules.pullback T.toSpecΓ).mapHomologicalComplex _).obj
    (affineAlternatingCechModel (f ≫ T.toSpecΓ) V F)

/-- The explicit model has no negative terms.
Source: Stacks Project, Tag 02KE, finite Čech construction.
(blueprint: def-pc-finite-affine-cech-model).
Proof: extension from natural degrees is zero in negative degrees, and each of the
additive functors used in the construction preserves zero objects. -/
theorem finiteAffineCechModel_ge {X T : Scheme.{u}} (f : X ⟶ T) (F : X.Modules)
    {r : ℕ} (V : Fin r → X.Opens) : (finiteAffineCechModel f F V).IsStrictlyGE 0 := by
  unfold finiteAffineCechModel affineAlternatingCechModel
  infer_instance

/-- There are no increasing tuples above the size of the finite cover.
Source: Stacks Project, Tags 02KE and 01FK, finite Čech construction.
(blueprint: def-pc-finite-affine-cech-model).
Proof: an order embedding Fin (n+1) into Fin r forces n+1 ≤ r. Thus above r the
product has empty index type and is a zero module. Extension and additive functors
preserve this zero object. -/
theorem finiteAffineCechModel_le {X T : Scheme.{u}} (f : X ⟶ T) (F : X.Modules)
    {r : ℕ} (V : Fin r → X.Opens) : (finiteAffineCechModel f F V).IsStrictlyLE r := by
  classical
  apply (CochainComplex.isStrictlyLE_iff _ _).mpr
  intro i hi
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, (n : ℤ) = i := ⟨i.toNat, by omega⟩
  let C := alternatingCechComplex V F.presheafModuleCat
  have : IsEmpty (Fin (n + 1) ↪o Fin r) := ⟨fun t ↦ by
    have hcard := Fintype.card_le_of_injective t t.injective
    simp only [Fintype.card_fin] at hcard
    omega⟩
  have hz : IsZero (C.X n) := by
    change IsZero (ModuleCat.of _ (∀ t : Fin (n + 1) ↪o Fin r,
      F.presheafModuleCat.obj (Opposite.op (alternatingCechIntersection V t))))
    exact ModuleCat.isZero_of_subsingleton _
  have hext : IsZero ((C.extend ComplexShape.embeddingUpNat).X (n : ℤ)) :=
    hz.of_iso (C.extendXIso ComplexShape.embeddingUpNat (i := n) rfl)
  exact Functor.map_isZero (Modules.pullback T.toSpecΓ)
    (Functor.map_isZero
      (ModuleCat.restrictScalars
        (((Scheme.ΓSpecIso Γ(T, ⊤)).inv ≫ (f ≫ T.toSpecΓ).appTop).hom) ⋙
          tilde.functor Γ(T, ⊤)) hext)

/-- The terms are pullbacks of associated modules, hence quasi-coherent.
Source: Stacks Project, Tags 01I6 and 02KE.
(blueprint: def-pc-finite-affine-cech-model).
Proof: the tilde functor produces quasi-coherent modules, and pullback preserves
quasi-coherence. This also covers negative and empty-product terms. -/
theorem finiteAffineCechModel_quasicoherent {X T : Scheme.{u}} (f : X ⟶ T)
    (F : X.Modules) {r : ℕ} (V : Fin r → X.Opens) (n : ℤ) :
    ((finiteAffineCechModel f F V).X n).IsQuasicoherent := by
  let M := ((ModuleCat.restrictScalars
    (((Scheme.ΓSpecIso Γ(T, ⊤)).inv ≫ (f ≫ T.toSpecΓ).appTop).hom)).obj
      (((alternatingCechComplex V F.presheafModuleCat).extend
        ComplexShape.embeddingUpNat).X n))
  have hM : ((tilde.functor Γ(T, ⊤)).obj M).IsQuasicoherent := inferInstance
  exact isQuasicoherent_pullback T.toSpecΓ ((tilde.functor Γ(T, ⊤)).obj M)

end AlgebraicGeometry.Scheme.Modules
