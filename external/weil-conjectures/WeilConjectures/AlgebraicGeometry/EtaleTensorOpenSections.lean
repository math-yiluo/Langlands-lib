/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.EtaleTensorOpenSectionsNaturality

/-! # Tensor-pullback sections restricted to opens

Source: Stacks Project, Tag 03DR, equation defining associated quasi-coherent
sections, and Tags 0095 and 0096, module pullback and its adjunction.
(blueprint: lem-sc-etale-tensor-open-sections).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Tensor-pullback sections restricted to open subschemes recover the additive
section presheaf of the original module. Quasi-coherence is not needed.
Source: Stacks Project, Tag 03DR, equation (35.8.0.1), and Tags 0095 and 0096.
(blueprint: lem-sc-etale-tensor-open-sections).

Proof: For each open immersion j, restriction and tensor pullback are left
adjoints to the same module pushforward. Their unique unit-normalized comparison
is a natural isomorphism. Evaluate its component at the whole open scheme and
compose with the restriction section isomorphism; this identifies sections of
j^*F with F(j(open)). The functor equality hi identifies i(W) with the open
immersion W into X, so these are exactly F(W). For V included in W, the
unit equation for this comparison identifies the canonical section pullback
with ordinary restriction. The tensor composition isomorphism used in
etaleTensorSectionsRestriction is normalized by the same adjunction units.
Uniqueness of the comparison of left adjoints makes the two composition
comparisons equal. Consequently the section isomorphisms commute with every
inclusion V into W, including equality inclusions and inclusions of the empty
open. They assemble into an isomorphism of additive presheaves on X.Opens.
The presheafModuleCat construction only restricts scalars from F(W) to global
functions, so forgetting these scalars gives this same additive presheaf.
For a zero module or empty scheme all components are isomorphisms of zero groups.
No covering, affine hypothesis, separatedness or cohomology is involved. -/
theorem nonempty_etaleTensor_openSections_iso
    (X : Scheme.{u}) (i : X.Opens ⥤ X.Etale)
    (hi : i ⋙ Scheme.Etale.forget X = X.restrictFunctor) (F : X.Modules) :
    Nonempty (i.op ⋙ etaleTensorSectionsPresheaf F ≅
      F.presheafModuleCat ⋙ forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}) := by
  exact ⟨NatIso.ofComponents (etaleTensorOpenSectionIso X i hi F)
    (fun f ↦ etaleTensorOpenSectionIso_naturality X i hi F f)⟩

end AlgebraicGeometry.Scheme.Modules
