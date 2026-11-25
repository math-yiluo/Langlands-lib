/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale
public import Mathlib.CategoryTheory.Linear.FunctorCategory
import WeilConjectures.CategoryTheory.Sites.Point.Linear
import WeilConjectures.AlgebraicGeometry.FiniteEtaleUnitStalkInclusion
/-!
# Coefficient-linear finite étale trace and its degree

Source: Stacks Project, Section 03SH. We use the existing reverse adjunction
`f_* ⊣ f^*`; its counit is the trace. On geometric stalks restriction is diagonal,
trace is the sum, and their composite is multiplication by the fibre cardinality.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale
private theorem unit_stalk_component
    {X Y : Scheme.{u}} (R : Type (u + 1)) [CommRing R]
    (f : Y ⟶ X) [IsFinite f] [Etale f]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (t : f.GeometricFiber s) :
    (Scheme.pointSmallEtale s).sheafFiber.map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f).unit.app G) ≫
      stalkRestrict (ModuleCat.{u + 1} R) f s t ((f)^*[ModuleCat.{u + 1} R].obj G) =
    eqToHom (by rw [t.2]; rfl) ≫
      ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} R) f t.1).app G).inv := by
  obtain ⟨t, rfl⟩ := t
  simp only [eqToHom_refl, Category.id_comp]
  erw [stalkRestrict_eq_counit]
  have hn := (upperStarCompSheafFiberIso (ModuleCat.{u + 1} R) f t).inv.naturality
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f).unit.app G)
  dsimp only [Functor.comp_map] at hn
  erw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp]
  erw [Adjunction.left_triangle_components]
  simp

private theorem trace_stalk_component
    {X Y : Scheme.{u}} (R : Type (u + 1)) [CommRing R]
    (f : Y ⟶ X) [IsFinite f] [Etale f]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (t : f.GeometricFiber s) :
    sheafFiberToLowerStar (ModuleCat.{u + 1} R) f t ((f)^*[ModuleCat.{u + 1} R].obj G) ≫
      (Scheme.pointSmallEtale s).sheafFiber.map
        ((lowerStarUpperStarAdjunctionOfIsFinite (ModuleCat.{u + 1} R) f).counit.app G) =
    ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} R) f t.1).app G).hom ≫
      eqToHom (by rw [t.2]; rfl) := by
  obtain ⟨t, rfl⟩ := t
  erw [← finiteEtaleUnit_stalk_inclusion R f
    ((f)^*[ModuleCat.{u + 1} R].obj G) (t ≫ f) ⟨t, rfl⟩]
  simp only [eqToHom_refl, Category.comp_id]
  have hn := (upperStarCompSheafFiberIso (ModuleCat.{u + 1} R) f t).hom.naturality
    ((lowerStarUpperStarAdjunctionOfIsFinite (ModuleCat.{u + 1} R) f).counit.app G)
  dsimp only [Functor.comp_map] at hn
  erw [Category.assoc, ← hn, ← Category.assoc, ← Functor.map_comp,
    Adjunction.right_triangle_components]
  simp


/-- **The finite étale trace after pullback is multiplication by the degree.** For a finite
étale `f` all of whose geometric fibres have `d` points, the unit `G ⟶ f_* f^* G` followed by the
trace `f_* f^* G ⟶ G`, the counit of `f_* ⊣ f^*`, is multiplication by `d`. -/
theorem unit_app_comp_lowerStarUpperStarAdjunctionOfIsFinite_counit_app
    {X Y : Scheme.{u}} (R : Type (u + 1)) [CommRing R]
    (f : Y ⟶ X) [IsFinite f] [Etale f]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) (d : ℕ)
    (hdeg : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      Nat.card (f.GeometricFiber s) = d) :
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f).unit.app G ≫
      (lowerStarUpperStarAdjunctionOfIsFinite (ModuleCat.{u + 1} R) f).counit.app G =
        (d : R) • 𝟙 G := by
  classical
  let A := ModuleCat.{u + 1} R
  let H := (f)^*[A].obj G
  let η := (upperStarLowerStarAdjunction A f).unit.app G
  let tr := (lowerStarUpperStarAdjunctionOfIsFinite A f).counit.app G
  apply Scheme.sheafHom_ext_of_sheafFiber_map_algClosurePoint
  intro x
  let s := X.algClosurePoint x
  let Φ := (Scheme.pointSmallEtale s).sheafFiber (A := A)
  let : Fintype (f.GeometricFiber s) := Fintype.ofFinite _
  let ρ := fun t : f.GeometricFiber s ↦ stalkRestrict A f s t H
  let j := fun t : f.GeometricFiber s ↦ sheafFiberToLowerStar A f t H
  have htotal : ∑ t, ρ t ≫ j t = 𝟙 (Φ.obj ((f)_*[A].obj H)) := by
    apply (cancel_mono (Limits.Pi.lift ρ)).mp
    apply Limits.Pi.hom_ext
    intro t
    simp only [Category.assoc, Limits.Pi.lift_comp_π]
    erw [Preadditive.sum_comp, Category.id_comp]
    simp only [Category.assoc]
    change ∑ a, ρ a ≫ (j a ≫ ρ t) = ρ t
    erw [Finset.sum_eq_single t]
    · simp [ρ, j]
    · intro a ha hat
      erw [sheafFiberToLowerStar_stalkRestrict_of_ne A f hat H, Limits.comp_zero]
    · intro ht
      exact (ht (Finset.mem_univ t)).elim
  simp only [CategoryTheory.Functor.map_comp,
    GrothendieckTopology.Point.sheafFiber_map_smul]
  change Φ.map η ≫ Φ.map tr = (d : R) • Φ.map (𝟙 G)
  erw [Φ.map_id]
  calc
    Φ.map η ≫ Φ.map tr = Φ.map η ≫ (∑ t, ρ t ≫ j t) ≫ Φ.map tr := by
      erw [htotal, Category.id_comp]
    _ = ∑ t, (Φ.map η ≫ ρ t) ≫ (j t ≫ Φ.map tr) := by
      erw [Preadditive.sum_comp, Preadditive.comp_sum]
      simp only [Category.assoc]
    _ = ∑ _t : f.GeometricFiber s, 𝟙 (Φ.obj G) := by
      apply Finset.sum_congr rfl
      intro t ht
      erw [unit_stalk_component R f G s t, trace_stalk_component R f G s t]
      simp
    _ = (d : R) • 𝟙 _ := by
      erw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
        hdeg _ s, ← Nat.cast_smul_eq_nsmul R]
/-- A coefficient-linear trace whose composite with restriction is multiplication by
 the prescribed cardinality of every geometric fibre.

Source: Stacks Project, Section 03SH, Definition 03SE and the following degree formula.
(blueprint: lem-weil-pbc-finite-etale-module-trace-data)

Proof: take the counit of the existing reverse adjunction `f_* ⊣ f^*`. The ordinary
adjunction triangle identifies restriction on each geometric stalk with the diagonal.
The reverse-adjunction triangle and `finiteEtaleUnit_stalk_inclusion` identify the
trace on each summand with the pullback stalk comparison. The finite pushforward
stalk formula and orthogonality of extensions by zero give the resolution of the
identity as the sum of projection-inclusion composites. Consequently the composite
is the sum of one identity for each lift, hence `(d : R)` times the identity.
Geometric stalks detect equality of sheaf morphisms. Empty fibres and the empty
base are covered by the same calculation; no invertibility is used. -/
theorem finiteEtaleModuleTraceData
    {X Y : Scheme.{u}} (R : Type (u + 1)) [CommRing R]
    (f : Y ⟶ X) [IsFinite f] [Etale f]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) (d : ℕ)
    (hdeg : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      Nat.card (f.GeometricFiber s) = d) :
    (∃ t : (f)_*[ModuleCat.{u + 1} R].obj ((f)^*[ModuleCat.{u + 1} R].obj G) ⟶ G,
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f).unit.app G ≫ t =
        (d : R) • 𝟙 G) ∧ Nonempty PUnit.{0} :=
  ⟨⟨_, unit_app_comp_lowerStarUpperStarAdjunctionOfIsFinite_counit_app R f G d hdeg⟩,
    ⟨PUnit.unit⟩⟩
end AlgebraicGeometry.Etale
