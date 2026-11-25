/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-! # Signed module dual of a chain complex

Source: Stacks Project, duality.tex, Tag 0BQZ, displayed finite free Hom computation.
(blueprint: def-sc-signed-module-dual-complex).
-/

@[expose] public section

universe u
open CategoryTheory
namespace ModuleCat

/-- Signed precomposition has square zero.
Source: Stacks Project, duality.tex, Tag 0BQZ.
(blueprint: def-sc-signed-module-dual-complex).
Proof: the signs multiply and the remaining composite is precomposition by
K.d(n+2,n+1) followed by K.d(n+1,n), which is zero. -/
theorem signedDualBoundary_comp {A : Type u} [CommRing A]
    (K : ChainComplex (ModuleCat.{u} A) ℕ) (n : ℕ) :
    ModuleCat.ofHom ((-1 : A) ^ (n + 1) •
      Linear.leftComp A (ModuleCat.of A A) (K.d (n + 1) n)) ≫
    ModuleCat.ofHom ((-1 : A) ^ (n + 1 + 1) •
      Linear.leftComp A (ModuleCat.of A A) (K.d (n + 1 + 1) (n + 1))) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp [Linear.leftComp]

/-- The signed module dual of a natural-indexed chain complex, extended to ℤ.
In degree n≥0 its term is Hom_A(K_n,A), and the differential is
(-1)^(n+1) times precomposition by the chain boundary. Negative terms vanish.
Source: Stacks Project, duality.tex, Tag 0BQZ.
(blueprint: def-sc-signed-module-dual-complex). -/
noncomputable def signedDualCochainComplex {A : Type u} [CommRing A]
    (K : ChainComplex (ModuleCat.{u} A) ℕ) : CochainComplex (ModuleCat.{u} A) ℤ :=
  (CochainComplex.of (fun n ↦ ModuleCat.of A (K.X n ⟶ ModuleCat.of A A))
    (fun n ↦ ModuleCat.ofHom ((-1 : A) ^ (n + 1) •
      Linear.leftComp A (ModuleCat.of A A) (K.d (n + 1) n)))
    (signedDualBoundary_comp K)).extend ComplexShape.embeddingUpNat

end ModuleCat
