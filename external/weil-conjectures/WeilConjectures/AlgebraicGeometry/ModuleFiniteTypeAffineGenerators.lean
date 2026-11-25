/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.ModuleGeneratingSectionsCompactSelection
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Finite affine sections generating on a compact open

Source: Stacks Project, Properties, Lemma 01PF, finite-numerator step.
(blueprint: lem-weil-pbc-module-finite-type-affine-generators).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

private theorem exists_affine_generatingSections
    (X : Scheme.{u}) (V : X.affineOpens)
    (H : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [H.IsQuasicoherent] :
    Nonempty (H.over V.1).GeneratingSections := by
  let H' : X.Modules := H
  let M := H'.restrict V.2.fromSpec
  have : M.IsQuasicoherent := inferInstance
  have : IsIso M.fromTildeΓ := inferInstance
  let P := (presentationTilde
    ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)) .univ (by simp) _
    (Submodule.span_eq _)).ofIsIso M.fromTildeΓ
  let Q := presentationOverOfRestrict V.2.fromSpec.opensRange
    (presentationRestrictOpensRange V.2.fromSpec P)
  exact V.2.opensRange_fromSpec ▸ ⟨Q.generators⟩

/-- Finitely many sections on an affine open generate a quasi-coherent module on a
compact open where it is of finite type.

Source: Stacks Project, Properties, Lemma 01PF (label lemma-extend), final paragraph,
and Lemma 01PB (label lemma-finite-type-module).
https://stacks.math.columbia.edu/tag/01PF
(blueprint: lem-weil-pbc-module-finite-type-affine-generators).

Proof: Identify H on V with the associated sheaf of M = H(V) using the affine
counit isomorphism. Refine a finite-type generating cover on K by principal opens
D(f) inside K. The affine criterion identifies their modules of sections with
finitely generated localizations M_f. Compactness gives finitely many such opens.
For each of their finite generating families, write the generators as m/f^a and
collect the finitely many numerators m in M. Enumerate them by Fin n and map the
standard basis of the free module to these sections. On each chosen D(f), f is a
unit, so the numerators generate whenever the fractions do. The restriction of
this free-module map is therefore locally surjective on K, hence epimorphic.
Transport the map to the slice site Over V; the free-module comparison preserves
its standard basis. No submodule or monomorphism is asserted here. If K is empty,
use n = 0; every sheaf on the empty open is zero, so the restricted map is epi.
For K = V, finite generation gives the usual finite free surjection. -/
theorem exists_finiteType_affine_generators
    (X : Scheme.{u}) (V : X.affineOpens) (K : X.Opens)
    (hK : IsCompact (K : Set X)) (hKV : K ≤ V.1)
    (H : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [H.IsQuasicoherent]
    [(H.over K).IsFiniteType] :
    ∃ (n : ℕ) (φ : SheafOfModules.free
        (R := (moduleRings X.toRingedSpace).over V.1) (ULift.{u} (Fin n)) ⟶ H.over V.1),
      Epi ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
        (homOfLE hKV)).map φ) := by
  classical
  obtain ⟨σ⟩ := exists_affine_generatingSections X V H
  obtain ⟨S, hS⟩ := exists_finset_generatingSections_on_compact X V.1 K hK hKV H σ
  let e : ULift.{u} (Fin (Fintype.card S)) ≃ S :=
    Equiv.ulift.trans (Fintype.equivFin S).symm
  let R := moduleRings X.toRingedSpace
  let T := SheafOfModules.overMap R (homOfLE hKV)
  let f := SheafOfModules.freeMap (R := R.over V.1) ((↑) : S → σ.I) ≫ σ.π
  let g := ((SheafOfModules.freeFunctor (R := R.over V.1)).mapIso e.toIso).hom
  have : Epi (T.map f) := hS
  refine ⟨Fintype.card S, g ≫ f, ?_⟩
  rw [T.map_comp]
  exact epi_comp' (IsIso.epi_of_iso (T.map g)) hS

end AlgebraicGeometry.Scheme.Modules
