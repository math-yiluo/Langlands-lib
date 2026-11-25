/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.RingTheory.Ideal.Maps
public import WeilConjectures.CategoryTheory.RingedSiteModules

/-! # Presentations of towers of common quotient ring sheaves

Source: Stacks Project, proetale.tex, Tag 099L, section-derived-completion-noetherian;
sites-modules.tex, Tag 03EK, section-tensor-product.
(auxiliary; not a blueprint node).

A quotient is specified by its locally surjective projection, rather than by a
sectionwise surjection. Extension of its kernel ideal is specified by the pushout
universal property in ring sheaves. This includes quotients whose sections lift only locally.
-/

@[expose] public section
set_option autoImplicit false
universe u v r m
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R B : Sheaf J CommRingCat.{r}}

/-- A tower `S_n = R/I_n = B/I_n B`, including the quotient projections and their
transition compatibility. Its ideals are the kernels of the projections from `R`.
The pushout with bottom map the identity says precisely that the projection from `B`
is the quotient by the extended ideal. Source: Stacks 099L and 03EK
(auxiliary; not a blueprint node). -/
structure CommonQuotientTowerPresentation (φ : R ⟶ B) where
  /-- The common quotient rings; index zero denotes the first level. -/
  S : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{r}
  /-- The compatible projections from the first coefficient ring. -/
  q : (Functor.const ℕᵒᵖ).obj R ⟶ S
  /-- The compatible projections from the second coefficient ring. -/
  b : (Functor.const ℕᵒᵖ).obj B ⟶ S
  /-- Quotient projections are locally surjective, with no assertion on global sections. -/
  q_surjective : ∀ n : ℕ, Presheaf.IsLocallySurjective J (q.app (op n)).hom
  /-- The specified common quotient is induced by the original coefficient morphism. -/
  pushout : ∀ n : ℕ, IsPushout φ (q.app (op n)) (b.app (op n)) (𝟙 _)

namespace CommonQuotientTowerPresentation
variable {φ : R ⟶ B} (D : CommonQuotientTowerPresentation φ)

/-- The quotient projection with its source ring explicit.
Source: Stacks 099L (auxiliary; not a blueprint node). -/
abbrev projection (n : ℕ) : R ⟶ D.S.obj (op n) := D.q.app (op n)

/-- The projection from the second ring, with its source ring explicit.
Source: Stacks 099L (auxiliary; not a blueprint node). -/
abbrev extensionProjection (n : ℕ) : B ⟶ D.S.obj (op n) := D.b.app (op n)

end CommonQuotientTowerPresentation
end SheafOfModules
