/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.KFlatTensorQuasiIso

/-! # Shared definitions for scalar extension of ring-site Hom complexes

Source: Stacks Project, more-algebra.tex, equation-base-change-RHom, and
sites-cohomology.tex, section-hom-complexes (Tag 0A8X).
(auxiliary; not a blueprint node)

This is a chain-level construction. It requires neither derived categories nor
perfectness, and supplies only the normalized Hom map, not derived extension data.
-/

-- Keep the chosen Hom-complex witness folded during routine conversion checks.
set_option backward.isDefEq.respectTransparency true

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace CategoryTheory

/-- Modules on the one-object bottom-topology site with ring `A`. Source: Stacks,
more-algebra.tex, equation-base-change-RHom
(auxiliary; not a blueprint node). -/
abbrev RingSiteModules (A : Type u) [CommRing A] :=
  SheafOfModules.{u} ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
    (CochainComplex.onePointRingSheaf A))

/-- The map of constant ring sheaves induced by the given ring homomorphism. Source:
Stacks, equation-base-change-RHom (auxiliary; not a blueprint node). -/
def ringSiteMap {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    CochainComplex.onePointRingSheaf A ⟶ CochainComplex.onePointRingSheaf B :=
  ⟨(Functor.const _).map (CommRingCat.ofHom φ)⟩

end CategoryTheory
