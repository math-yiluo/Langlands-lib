/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.TorsionControlledLocalCocycle
import WeilConjectures.AlgebraicGeometry.TorsionControlledDescendedSourceComparisons
import WeilConjectures.Topology.GlueSheavesOfModules
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Algebraic descent with local formal comparisons

Source: Stacks Project, Tag 0889(1), Zariski locality via uniqueness;
Sheaves, Tags 00AL and 00AM.
(blueprint: new-stage3-torsion-controlled-algebraization-local-descent).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Glue the algebraic sources and their arrows, retaining local formal comparisons.
This conclusion does not glue the comparisons into a global formal isomorphism
and does not assert annihilation for the actual global kernel or cokernel.

Source: Stacks Project, Tag 0889(1), first sentence of the proof and uniqueness;
Sheaves, Tags 00AL and 00AM.
(blueprint: new-stage3-torsion-controlled-algebraization-local-descent).

Proof: Choose one supplied triple on each open. Restrict them to pairwise
intersections. Restriction preserves coherence, kernels and cokernels, and
commutes with ideal products and powers, so the restricted arrows retain their
bounds. The normalized completion-restriction comparisons identify the two
completions with the restriction of N. The resulting completed comparison
commutes with the maps to the restricted H. Lift it and its inverse using
torsion-controlled completion hom lifting. Completion extensionality with the
map to H identifies their composites with identities. The same extensionality
proves the cocycle equation on triple intersections. Glue these module sheaves
and arrows by module descent; coherence is local. The resulting local source
isomorphisms e identify the restricted global arrow with the supplied arrow ai,
with the target identification eqToHom(hHlocal.symm). Retain ai's supplied bound.
Compose each supplied beta with the inverse of the completion of e and the
canonical completion-restriction comparison. Transfer these local system
isomorphisms through the equivalence between open-subscheme modules and modules
on the over-site, obtaining epsilon. Their components agree on every open
inside an intersection by the defining completed comparisons. Naturality is
inherited from beta and completion. The supplied factorization and naturality
of the normalized comparison give delta restricted = epsilon followed by the
restricted completion of a at every level. No global epsilon is glued here.
For J = 0 the local completed comparisons are the original module comparisons.
For the unit ideal the bounded arrows are isomorphisms, so comparison is through
H even though completion is zero. For an empty cover hcover forces X empty and
module descent supplies the zero source; all comparison conditions are vacuous.
-/
theorem torsionControlled_algebraization_local_descent
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
    ∃ (F : CoherentModules X) (a : F ⟶ H)
      (ε : ∀ i, N.obj ⋙ SheafOfModules.overFunctor
        (moduleRings X.toRingedSpace) (U i) ≅
        ((completion X J).obj F).obj ⋙ SheafOfModules.overFunctor
          (moduleRings X.toRingedSpace) (U i)),
      (∀ (n : ℕᵒᵖ) (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j),
        ((ε i).hom.app n).val.app (op (Over.mk (homOfLE hi))) =
          ((ε j).hom.app n).val.app (op (Over.mk (homOfLE hj)))) ∧
      (∀ (n : ℕᵒᵖ) (i : ι), (δ.hom.app n).over (U i) =
        (ε i).hom.app n ≫ (((completion X J).map a).hom.app n).over (U i)) ∧
      (∀ i, ∃ (Fi : CoherentModules (U i).toScheme) (ai : Fi ⟶ Hlocal i)
        (e : (Scheme.Modules.restrictFunctor (U i).ι).obj F.obj ≅ Fi.obj),
        (Scheme.Modules.restrictFunctor (U i).ι).map a.hom ≫
          eqToHom (hHlocal i).symm = e.hom ≫ ai.hom ∧
        ∃ s : ℕ, 1 ≤ s ∧
          IsZero (Scheme.idealModuleProduct
            (Scheme.idealSheafPower (J.comap (U i).ι).toModulesι s).2 (kernel ai.hom)) ∧
          IsZero (Scheme.idealModuleProduct
            (Scheme.idealSheafPower (J.comap (U i).ι).toModulesι s).2
            (cokernel ai.hom))) := by
  classical
  choose Fi ai βi hfactor hbound using hlocal
  obtain ⟨Li, li, bi, qi, θ, hbi, hqi, hδ, hcoc, hbcompat, hqcompat⟩ :=
    torsionControlled_local_cocycle
      J H N δ ι U Hlocal hHlocal γ hγ Fi ai βi hfactor hbound
  obtain ⟨M, φ, hφ⟩ :=
    (glue_sheaves_of_modules.{u, u} X.toRingedSpace ι U hcover).2.2 Li θ hcoc
  obtain ⟨hM, a, ε, hε, hδε, he⟩ :=
    torsionControlled_descended_source_comparisons
      J H N δ ι U hcover Hlocal hHlocal Fi ai βi Li li bi qi θ
      hbi hqi hδ hbcompat hqcompat M φ hφ
  refine ⟨⟨M, hM⟩, a, ε, hε, hδε, ?_⟩
  intro i
  obtain ⟨e, he⟩ := he i
  exact ⟨Fi i, ai i, e, he, hbound i⟩

end AlgebraicGeometry
