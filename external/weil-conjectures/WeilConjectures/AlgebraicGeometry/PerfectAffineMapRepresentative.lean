/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.AffineLocalizedDerivedSheafification
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-! # Representing affine perfect derived arrows by chain maps

Source: Stacks Project, Tag 08CR, second proof; Tag 06Z0, affine derived equivalence
(blueprint: lem-pc-perfect-affine-map-representative).
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A derived arrow between strictly perfect complexes on an affine open is represented by
an actual chain map. Source: Stacks Project, Tag 08CR, second proof; Tag 06Z0
(blueprint: lem-pc-perfect-affine-map-representative).

Proof: Identify the localized site over U with the site of the affine scheme U, and
identify U with the spectrum of its ring of sections. The finite-free retract equations
show that every term of A and B is quasi-coherent. Taking global sections of the complexes
gives bounded complexes of finite projective modules: sections preserve retracts, and
sections of finite free modules on an affine scheme are finite free. The affine
sheafification/global-sections counit recovers A and B termwise, naturally in their
differentials. Thus the affine derived equivalence, followed by the fully faithful
quasi-coherent subcategory inclusion, lifts f to the module derived category. The source
complex is bounded above and projective, hence K-projective. Bijectivity of Qh on maps out
of it, followed by fullness of the homotopy quotient, gives a module chain map representing
the lifted arrow. Sheafify that chain map and conjugate by the termwise counit isomorphisms.
The factorization isomorphism for the affine equivalence and its naturality identify the
image under Q of this sheaf chain map with f. Transport back to the localized site to
obtain the claimed equality. For an empty affine open all objects and maps are zero. -/
theorem perfect_affine_map_representative (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (hU : IsAffineOpen U)
    (A B : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hA : IsStrictlyPerfect X U A) (hB : IsStrictlyPerfect X U B)
    (f : DerivedCategory.Q.obj A ⟶ DerivedCategory.Q.obj B) :
    ∃ α : A ⟶ B, DerivedCategory.Q.map α = f := by
  let R := X.presheaf.obj (.op U)
  let : HasDerivedCategory (ModuleCat.{u} R) := HasDerivedCategory.standard _
  let F := (affinePerfectSheafification X U hU).mapHomologicalComplex (.up ℤ)
  obtain ⟨P, hP, ⟨eA⟩⟩ := affine_perfect_module_model X U hU A hA
  obtain ⟨T, _, ⟨eB⟩⟩ := affine_perfect_module_model X U hU B hB
  have : P.IsKProjective := hP
  obtain ⟨G, hG, ⟨c⟩⟩ := affine_localized_derived_sheafification X U hU
  have : G.Full := hG
  let a := c.app P ≪≫ DerivedCategory.Q.mapIso eA
  let b := c.app T ≪≫ DerivedCategory.Q.mapIso eB
  let g : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj T :=
    G.preimage (a.hom ≫ f ≫ b.inv)
  obtain ⟨β, hβ⟩ := CochainComplex.IsKProjective.exists_Q_map_eq P T g
  refine ⟨eA.inv ≫ F.map β ≫ eB.hom, ?_⟩
  have hc := c.hom.naturality β
  change G.map (DerivedCategory.Q.map β) ≫ (c.app T).hom =
    (c.app P).hom ≫ DerivedCategory.Q.map (F.map β) at hc
  rw [hβ] at hc
  have hg : G.map g = a.hom ≫ f ≫ b.inv := G.map_preimage _
  rw [hg] at hc
  have hc' : DerivedCategory.Q.map (F.map β) =
      (c.app P).inv ≫ a.hom ≫ f ≫ b.inv ≫ (c.app T).hom := by
    calc
      _ = (c.app P).inv ≫ ((c.app P).hom ≫
          DerivedCategory.Q.map (F.map β)) := by simp
      _ = _ := by rw [← hc]; simp only [Category.assoc]
  simp only [Functor.map_comp, hc', Category.assoc]
  dsimp [a, b]
  simp


end AlgebraicGeometry.Scheme
