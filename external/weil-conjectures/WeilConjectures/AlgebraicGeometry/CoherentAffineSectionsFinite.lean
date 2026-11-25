/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.AlgebraicGeometry.Coherent
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
import all WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Finite affine sections of a coherent module

Source: Stacks Project, Modules, Tag 01BV; Properties, Tag 01PB;
Cohomology of Schemes, Tag 01Y8
(blueprint: lem-weil-pbc-coherent-affine-sections-finite).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- A coherent module has finitely generated sections on each affine open.
Source: Stacks Project, Tag 01Y8, proof, using Tags 01BV, 01BO and 01PB
(blueprint: lem-weil-pbc-coherent-affine-sections-finite).

Proof: Choose finite local generators of the coherent module and reindex each finite
family by ULift (Fin n). Coherence makes the kernel of the generator epimorphism finite
type. Choose finite local generators of that kernel. The over-site restriction preserves
cokernels, finite free modules and epimorphisms; hence restricting the original generators
and composing the relation maps gives finite presentations on the refined cover. Bind
the local data and apply locality of finite presentation. Finally the proved source-library
result finitePresentation_sections_of_isFinitePresentation gives finitely presented
sections on the given affine open, which are in particular finitely generated. -/
theorem coherent_affine_sections_finite (X : Scheme.{u}) (F : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (U : X.Opens) (hU : IsAffineOpen U) : Module.Finite Γ(X, U) Γ(F, U) := by
  classical
  have (V : X.Opens) :
      HasSheafify ((Opens.grothendieckTopology X).over V)
        AddCommGrpCat.{u} := inferInstance
  have (V : X.Opens) :
      ((Opens.grothendieckTopology X).over V).WEqualsLocallyBijective
        AddCommGrpCat.{u} := inferInstance
  have (V : X.Opens) (W : CategoryTheory.Over V) :
      HasSheafify (((Opens.grothendieckTopology X).over V).over W)
        AddCommGrpCat.{u} := inferInstance
  have (V : X.Opens) (W : CategoryTheory.Over V) :
      (((Opens.grothendieckTopology X).over V).over W).WEqualsLocallyBijective
        AddCommGrpCat.{u} := inferInstance
  have : F.IsFiniteType := hF.1
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData F
  have hfp (i : q.I) : (F.over (q.X i)).IsFinitePresentation := by
    have := hq.isFiniteType i
    let _ := Fintype.ofFinite (q.generators i).I
    let n := Fintype.card (q.generators i).I
    let e := (SheafOfModules.freeFunctor (R := X.ringCatSheaf.over (q.X i))).mapIso
      ((Equiv.ulift.trans (Fintype.equivFin (q.generators i).I).symm).toIso)
    let f := e.hom ≫ (q.generators i).π
    have : Epi f := inferInstanceAs (Epi (e.hom ≫ (q.generators i).π))
    let G := SheafOfModules.GeneratingSections.ofEpiFree f
    have : G.IsFiniteType := ⟨inferInstanceAs (Finite (ULift.{u} (Fin n)))⟩
    have : (Limits.kernel G.π).IsFiniteType := by
      simpa only [G, SheafOfModules.GeneratingSections.ofEpiFree_π]
        using hF.2 (q.X i) n f
    exact isFinitePresentation_of_generators_kernel.{u} (F.over (q.X i)) G
  have : F.IsFinitePresentation := by
    exact @SheafOfModules.IsFinitePresentation.of_coversTop _ _ _ _ _ _ _ _
      F q.I q.X q.coversTop hfp
  have := finitePresentation_sections_of_isFinitePresentation F hU
  infer_instance

end AlgebraicGeometry.Scheme.Modules
