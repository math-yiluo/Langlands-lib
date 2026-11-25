/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

import WeilConjectures.AlgebraicGeometry.TorsionControlledEasyAlgebraizationBridge
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleAnnihilated
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.Algebra.Category.ModuleCat.Limits
import WeilConjectures.AlgebraicGeometry.Coherent

/-! # Construction of a torsion-controlled algebraization

Source: Stacks Project, Tag 0889(1), construction from affine limit maps.
(blueprint: lem-weil-pbc-torsion-controlled-algebraization-construction).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Construct one torsion-controlled triple from torsion of the affine limit maps.
This statement has no uniqueness conclusion and does not assert that an arbitrary
algebraization has torsion kernel and cokernel before completion.

Source: Stacks Project, Tag 0889(1), construction, using Tags 0ALK and 05EU.
(blueprint: lem-weil-pbc-torsion-controlled-algebraization-construction).

Proof:
Choose a finite affine cover of the Noetherian scheme. Restrict the formal system,
the coherent target and delta. On each affine Spec A use 087W to identify the source
with a finite module Q over the I-adic completion S of A. The affine limit map in
the hypothesis is its map to the completion of the finite module P of sections of H.
The finite-module tensor comparison identifies that target with S tensor P.
The ring map A to S is flat and induces an isomorphism modulo I, and I is finitely
generated. Apply 0ALK(1) to construct psi : T to P and a compatible completed
isomorphism, with actual kernel and cokernel identified A-linearly with those of the
limit map. These comparisons transfer the hypothesis's single annihilating exponent
on this affine to the actual kernel and cokernel of psi. Localizing at each generator
of I makes psi an isomorphism. Thus T is finite by 05EU, since both its completed
module Q and its localized modules P_f are finite. Tilde and coherence on a locally
Noetherian scheme give the local coherent triple.
On overlaps the completed comparison is the first beta inverse followed by the
second beta. Apply torsionControlled_completion_hom_lift in both directions; uniqueness
makes their composites identities, and gives the cocycle on triple overlaps. Glue the
sources by 04TN and maps by 00AL. Glue the comparison isomorphisms termwise; their
naturality and inverse identities hold locally, hence globally. Coherence is local.
The finitely many local exponents have a positive common upper bound (choose 1 for
an empty cover). Inclusion of higher ideal powers into lower ones shows that this
bound kills the actual coherent kernel and cokernel globally. The comparison equation
is likewise checked locally. For the unit ideal the construction chooses H with its
identity map, rather than an arbitrary invisible summand; for the zero ideal it
chooses the coherent module represented by the constant formal system.
-/
theorem torsionControlled_algebraization_construction
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    (H : CoherentModules X) (N : CoherentFormalModule X J)
    (δ : N ⟶ (completion X J).obj H)
    (hlocal : ∀ U : X.affineOpens, ∃ t : ℕ, 1 ≤ t ∧
      J.ideal U ^ t ≤ Module.annihilator Γ(X, U.1) (LinearMap.ker
        (lim.map (Functor.whiskerRight δ.hom
          (SheafOfModules.evaluation X.ringCatSheaf (op U.1)))).hom) ∧
      J.ideal U ^ t ≤ Module.annihilator Γ(X, U.1)
        (↥(limit (((completion X J).obj H).obj ⋙
          SheafOfModules.evaluation X.ringCatSheaf (op U.1)) :
          ModuleCat Γ(X, U.1)) ⧸ LinearMap.range
          (lim.map (Functor.whiskerRight δ.hom
            (SheafOfModules.evaluation X.ringCatSheaf (op U.1)))).hom)) :
    ∃ (F : CoherentModules X) (a : F ⟶ H) (β : N ≅ (completion X J).obj F),
      δ = β.hom ≫ (completion X J).map a ∧
      (∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (kernel a.hom)) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (cokernel a.hom))) := by
  have htorsion := ((coherentFormalModule_annihilated_iff X J J N
    ((completion X J).obj H) δ).out 2 1).mp hlocal
  obtain ⟨F, a, β, hδ, ha⟩ :=
    torsionControlled_easy_algebraization_bridge J H N δ htorsion
  exact ⟨F, a, β, hδ, ha⟩

end AlgebraicGeometry
