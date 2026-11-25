/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.TorsionControlledAlgebraizationDescentGluing
import WeilConjectures.AlgebraicGeometry.TorsionControlledAlgebraizationDescentBound

/-! # Descent of already constructed torsion-controlled triples

Source: Stacks Project, Tag 0889(1), first sentence and uniqueness argument;
Sheaves, Tags 00AL and 00AM.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Local triples on an open cover descend. The hypothesis supplies actual local
algebraizations, not a torsion condition on the original formal map.

Source: Stacks Project, Tag 0889(1), Zariski locality by uniqueness;
Sheaves, Tags 00AL and 00AM.
(blueprint: lem-weil-pbc-torsion-controlled-algebraization-descent).

Proof: Choose the triples supplied on the covering opens. Restrict two triples to
an overlap, using the quotient/restriction comparison to compare completions.
The formal isomorphism between their completions respects the maps to H. The
torsion-controlled completion homomorphism lifting theorem lifts it and its
inverse to coherent maps. The completion extensionality theorem identifies their
composites with the identity, giving an isomorphism of triples. The same theorem
makes that isomorphism unique. On triple overlaps uniqueness proves the cocycle
identity. Glue the coherent sheaves by sheaf descent, the maps by morphism descent,
and the component isomorphisms by morphism descent at each level. Coherence is
local, and the transition equations can be checked on the cover, so the glued
component comparisons form an isomorphism of formal systems. Their factorization
equations glue to the equation for δ. Choose a finite subcover using Noetherian
quasi-compactness. Take the maximum of its bounds and 1. Higher ideal powers factor
through lower powers, and restriction is exact, so this bound kills both global
kernel and cokernel. On the empty scheme the empty subcover uses bound 1. The
argument uses uniqueness only between torsion-controlled triples, including for
the unit ideal; it asserts nothing about unrestricted triples. -/
theorem torsionControlled_algebraization_descent
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    (H : CoherentModules X) (N : CoherentFormalModule X J)
    (δ : N ⟶ (completion X J).obj H)
    (ι : Type u) (U : ι → X.Opens) (hcover : (⨆ i, U i) = ⊤)
    (Hlocal : ∀ i, CoherentModules (U i).toScheme)
    (hHlocal : ∀ i, (Hlocal i).obj = (Scheme.Modules.restrictFunctor (U i).ι).obj H.obj)
    (γ : ∀ i, ((completion X J).obj H).obj ⋙
      Scheme.Modules.restrictFunctor (U i).ι ≅
        formalCompletionSystem (J.comap (U i).ι) (Hlocal i).obj)
    (hγ : ∀ (i : ι) (n : ℕ),
      (Scheme.Modules.restrictFunctor (U i).ι).map
          (formalModuleQuotientπ J (n + 1) H.obj) ≫ (γ i).hom.app (op n) =
        eqToHom (hHlocal i).symm ≫
          formalModuleQuotientπ (J.comap (U i).ι) (n + 1) (Hlocal i).obj)
    (hlocal : ∀ i, ∃ (F : CoherentModules (U i).toScheme) (a : F ⟶ Hlocal i)
      (β : N.obj ⋙ Scheme.Modules.restrictFunctor (U i).ι ≅
        formalCompletionSystem (J.comap (U i).ι) F.obj),
      Functor.whiskerRight δ.hom (Scheme.Modules.restrictFunctor (U i).ι) ≫ (γ i).hom =
        β.hom ≫ formalCompletionMap (J.comap (U i).ι) a.hom ∧
      (∃ s : ℕ, 1 ≤ s ∧
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower (J.comap (U i).ι).toModulesι s).2 (kernel a.hom)) ∧
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower (J.comap (U i).ι).toModulesι s).2 (cokernel a.hom)))) :
    ∃ (F : CoherentModules X) (a : F ⟶ H) (β : N ≅ (completion X J).obj F),
      δ = β.hom ≫ (completion X J).map a ∧
      (∃ s : ℕ, 1 ≤ s ∧
        IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
          (kernel a.hom)) ∧
        IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
          (cokernel a.hom))) := by
  obtain ⟨F, a, β, hfactor, hbound⟩ :=
    torsionControlled_algebraization_descent_gluing J H N δ ι U hcover Hlocal hHlocal γ hγ hlocal
  obtain ⟨s, hs, hsk, hsc⟩ :=
    torsionControlled_algebraization_descent_bound J H F a ι U hcover hbound
  exact ⟨F, a, β, hfactor, ⟨s, hs, hsk, hsc⟩⟩

end AlgebraicGeometry
