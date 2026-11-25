/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import Mathlib.CategoryTheory.Preadditive.Biproducts

@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

open Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false in
private theorem ideal_map_eq_zero_of_generic_stalk (Z : Scheme.{w}) [IsIntegral Z]
    (I : Z.IdealSheafData) {F : Z.Modules} (f : F ⟶ I.toModules)
    (hf : (RingedSpace.moduleStalkFunctor Z.toRingedSpace (genericPoint Z)).map f = 0) :
    f = 0 := by
  let O := (SheafOfModules.unit Z.ringCatSheaf : Z.Modules)
  let g : F ⟶ O := f ≫ I.toModulesι
  have hg : (RingedSpace.moduleStalkFunctor Z.toRingedSpace (genericPoint Z)).map g = 0 := by
    simp [g, hf]
  have hsec (U : Z.Opens) (s : Γ(F, U)) : g.app U s = 0 := by
    apply TopCat.Presheaf.section_ext Z.sheaf U (g.app U s) 0
    intro x hx
    have hη : genericPoint Z ∈ U :=
      ((genericPoint_spec Z).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hx⟩
    let P : TopCat.Presheaf Ab Z.toTopCat := O.val.presheaf
    have he : P.germ U (genericPoint Z) hη (g.app U s) = 0 := by
      have he' := congrArg
        (fun k ↦ k.hom
          (TopCat.Presheaf.germ (X := Z.toTopCat) F.val.presheaf U (genericPoint Z) hη s)) hg
      change (TopCat.Presheaf.stalkFunctor Ab (genericPoint Z)).map
        ((PresheafOfModules.toPresheaf _).map g.val) _ = 0 at he'
      erw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at he'
      exact he'
    rw [← map_zero (P.germ U (genericPoint Z) hη).hom] at he
    obtain ⟨W, hW, iU, iV, heq⟩ := P.germ_eq (genericPoint Z) hη hη _ _ he
    change Z.presheaf.map iU.op (g.app U s) = Z.presheaf.map iV.op 0 at heq
    rw [map_zero] at heq
    have hz : g.app U s = 0 :=
      map_injective_of_isIntegral Z iU (H := ⟨⟨genericPoint Z, hW⟩⟩)
        (heq.trans (map_zero _).symm)
    rw [hz, map_zero]
  apply (cancel_mono I.toModulesι).mp
  change g = 0 ≫ I.toModulesι
  rw [zero_comp]
  ext U s
  exact hsec U s

-- Keep the existing signature; the shorter proof does not need coherence.
set_option linter.unusedVariables false in
/-- A map in the integral lattice construction is injective once it is generically an
isomorphism.  This is the coordinatewise generic-stalk argument of Stacks, Tag 01YE.
(blueprint: lem-weil-pbc-coherent-integral-generic-ideal-map-mono).

Proof sketch: take the coherent kernel of the map.  Exactness of module stalks and
the generic isomorphism show that its generic stalk is zero.  Embed this kernel in
the finite coproduct of copies of the ideal and project to each coordinate.  Each
coordinate image is a quasi-coherent ideal with zero generic stalk, hence is zero on
an integral scheme.  All coordinates of every kernel section therefore vanish, so
the kernel is zero and the map is mono.  Coherence of the kernel and the image
ideals supplies the stated finiteness hypotheses.  The formal proof is left as this
named theorem for the subsequent argument. -/
theorem mono_of_coherent_ideal_sum_generic_iso (Z : Scheme.{w}) [IsNoetherian Z]
    [IsIntegral Z] (G : Z.Modules) (hG : RingedSpace.IsCoherent Z.toRingedSpace G)
    (r : ℕ) (I : Z.IdealSheafData)
    (χ : (∐ fun _ : Fin r => I.toModules) ⟶ G)
    (hI : RingedSpace.IsCoherent Z.toRingedSpace I.toModules)
    (hSum : RingedSpace.IsCoherent Z.toRingedSpace (∐ fun _ : Fin r => I.toModules))
    (hχ : IsIso ((RingedSpace.moduleStalkFunctor Z.toRingedSpace (genericPoint Z)).map χ)) :
    Mono χ := by
  -- The ideal embeds in the structure sheaf, so no coherence argument is needed.
  let T := RingedSpace.moduleStalkFunctor Z.toRingedSpace (genericPoint Z)
  have hk : T.map (kernel.ι χ) = 0 := by
    apply (cancel_mono (T.map χ)).mp
    rw [← T.map_comp, kernel.condition, T.map_zero, zero_comp]
  apply Abelian.mono_of_kernel_ι_eq_zero
  have : HasBiproduct (fun _ : Fin r => I.toModules) :=
    HasBiproduct.of_hasCoproduct _
  let e := biproduct.isoCoproduct (fun _ : Fin r => I.toModules)
  apply (cancel_mono e.inv).mp
  rw [zero_comp]
  apply biproduct.hom_ext
  intro j
  rw [zero_comp]
  apply ideal_map_eq_zero_of_generic_stalk Z I
  change T.map ((kernel.ι χ ≫ e.inv) ≫ biproduct.π _ j) = 0
  simp only [Functor.map_comp, hk, zero_comp]

end AlgebraicGeometry.Scheme.Modules
