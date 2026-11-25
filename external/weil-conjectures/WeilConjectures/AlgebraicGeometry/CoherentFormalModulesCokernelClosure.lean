/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesCokernelCanonical
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesIsoInvariant

/-! # CoherentFormalModulesCokernelClosure

Source: Stacks Project, Lemma 087X (blueprint: lem-weil-pbc-coherent-formal-cokernel-closure).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Ambient cokernels of maps between coherent adic systems remain coherent adic.
This is an object-closure assertion; it does not assume abelianness of Coh(X,I).
Source: Stacks Project, Lemma 087X, first sentence of the proof (details omitted).
(blueprint: lem-weil-pbc-coherent-formal-cokernel-closure).

Proof: Ambient cokernels in the inverse-system category are computed termwise.
For a map alpha:F -> G set C_n=coker(alpha_n). Each term is coherent by
coherent-kernel-cokernel-locnoeth. The naturality square of alpha gives the
transition of C by the cokernel universal property. On affine sections C_n is
G_n/im(alpha_n), by quasi-coherent-module-cokernel-image. The ideal-power
annihilation of G_n passes to C_n. For the transition from level n+1 to n,
with Lean's positive levels, the kernel on G is I^(n+1)G_(n+1).
The transition on F is surjective because it is a quotient projection followed
by the specified isomorphism. Consequently the image of alpha_(n+1) maps onto
the image of alpha_n. The third isomorphism theorem gives
C_(n+1)/I^(n+1)C_(n+1) = G_(n+1)/(im(alpha_(n+1))+I^(n+1)G_(n+1))
= G_n/im(alpha_n) = C_n. This isomorphism composes with the quotient projection
to the induced transition. Ideal products and these quotients are checked on
affine sections by ideal-times-quasi-coherent-affine-sections. Therefore C has
all three object conditions. Any ambient cokernel cofork is uniquely isomorphic
to this one; transporting the conditions yields closure for every cokernel,
as required by IsClosedUnderCokernels. This includes I=0, I=O_X, and zero arrows.
-/
theorem coherentFormalModules_closedUnderCokernels (X : Scheme.{u})
    [IsNoetherian X] (I : X.IdealSheafData) :
    (IsCoherentFormalModule I).IsClosedUnderCokernels := by
  refine ⟨?_⟩
  intro _ ⟨f, k, hk, ⟨hF, hG⟩⟩
  have hc := coherentFormalModules_canonicalCokernel_isCoherent X I hF hG f
  exact coherentFormalModules_of_iso X I (
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel f) hk) hc

end AlgebraicGeometry
