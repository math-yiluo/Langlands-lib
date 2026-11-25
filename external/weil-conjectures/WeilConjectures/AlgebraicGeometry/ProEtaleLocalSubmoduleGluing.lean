/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleLocalSubmoduleGluingData
import WeilConjectures.AlgebraicGeometry.ProEtaleLocalSubsheafGluing

/-!
# Gluing compatible local submodules on the pro-etale site

Source: Stacks Project, Sites, Tag 04TR, gluing sheaves, and Modules on Sites,
Tag 03EL (auxiliary; not a blueprint node).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

section ActionLift
variable {C : Type*} [Category C] [MonoidalCategory C]
  (R : C) [MonObj R] (Q : Mod C R) (P : C) (j : P ⟶ Q.X) [Mono j]
  (a : R ⊗ P ⟶ P) (ha : a ≫ j = R ◁ j ≫ Mod.act Q.X)
@[instance_reducible] private def lift_module_structure : ModObj R P :=
  ModObj.mk' R a (by
    apply (cancel_mono j).mp
    simp only [Category.assoc, ha]
    rw [← whisker_exchange_assoc, Mod.one_act, leftUnitor_naturality]) (by
    apply (cancel_mono j).mp
    simp only [Category.assoc, ha]
    rw [← whisker_exchange_assoc, Mod.mul_act, associator_naturality_right_assoc,
      ← whiskerLeft_comp_assoc R a, ha, whiskerLeft_comp_assoc])
end ActionLift

/-- Compatible local submodules of a fixed internal module glue.

Source: Stacks Project, Sites, Tag 04TR; Modules on Sites, Tag 03EL.
(auxiliary; not a blueprint node).

Proof: glue the underlying abelian subobjects using their commuting overlap
comparisons. The local factorization property of the glued subobject lifts the
action R tensor P to P: its local factor is the action on L_i composed with the
local comparison and the tensor comparison of inverse image. Cancel the inclusion
into Q to prove the unit and associativity laws. The same cancellation proves
that each local comparison is linear. The resulting internal module, inclusion,
and local module isomorphisms give the asserted gluing data. -/
theorem exists_module_of_compatible_local_monomorphisms
    (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R]
    (Q : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (U : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (L : ∀ i, Mod (Sheaf (Scheme.ProEt.topology (U.X i)) Ab.{u + 1})
      ((upperStar Ab.{u + 1} (U.f i)).obj R))
    (q : ∀ i, L i ⟶ ((upperStar Ab.{u + 1} (U.f i)).mapMod R).obj Q)
    (hq : ∀ i, Mono (q i))
    (hcompatible : ∀ i j, ∃ c :
      (upperStar Ab.{u + 1} (pullback.fst (U.f i) (U.f j))).obj (L i).X ≅
        (upperStar Ab.{u + 1} (pullback.snd (U.f i) (U.f j))).obj (L j).X,
      c.hom ≫ (upperStar Ab.{u + 1} (pullback.snd (U.f i) (U.f j))).map (q j).hom =
        (upperStar Ab.{u + 1} (pullback.fst (U.f i) (U.f j))).map (q i).hom ≫
          (upperStarCompIso Ab.{u + 1} (pullback.condition (f := U.f i) (g := U.f j))).hom.app
            Q.X) :
    Nonempty (LocalSubmoduleGluingData X R Q U L q) := by
  have hq' (i : U.I₀) : Mono (q i).hom := by
    have := hq i
    exact (Mod.forget _).map_mono (q i)
  obtain ⟨P, j, hj, e, he, hlift⟩ :=
    exists_subsheaf_of_compatible_local_monomorphisms X Q.X U
      (fun i ↦ (L i).X) (fun i ↦ (q i).hom) hq' hcompatible
  have := hj
  let m : R ⊗ P ⟶ Q.X := R ◁ j ≫ Mod.act Q.X
  obtain ⟨a, ha⟩ := hlift (R ⊗ P) m (by
    intro i
    let B := upperStar Ab.{u + 1} (U.f i)
    refine ⟨Functor.OplaxMonoidal.δ B R P ≫
      B.obj R ◁ (e i).hom ≫ Mod.act (L i).X, ?_⟩
    simp only [Category.assoc]
    rw [Mod.act_hom, ← whiskerLeft_comp_assoc, ← he i, Functor.act_mapMod_obj]
    change Functor.OplaxMonoidal.δ B R P ≫ B.obj R ◁ B.map j ≫
      Functor.LaxMonoidal.μ B R Q.X ≫ B.map (Mod.act Q.X) = B.map m
    rw [Functor.LaxMonoidal.μ_natural_right_assoc, Functor.Monoidal.δ_μ_assoc]
    exact (B.map_comp _ _).symm)
  let := lift_module_structure R Q P j a ha
  let P' : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R := ⟨P⟩
  let t : P' ⟶ Q := Mod.homMk j ha
  let e' (i : U.I₀) : ((upperStar Ab.{u + 1} (U.f i)).mapMod R).obj P' ≅ L i :=
    Mod.isoMk (e i) (by
      have := hq' i
      apply (cancel_mono (q i).hom).mp
      rw [Category.assoc, ← he i]
      change Mod.act (((upperStar Ab.{u + 1} (U.f i)).mapMod R).obj P').X ≫
        (((upperStar Ab.{u + 1} (U.f i)).mapMod R).map t).hom = _
      rw [Mod.act_hom]
      rw [Category.assoc, Mod.act_hom, ← whiskerLeft_comp_assoc, ← he i]
      rfl)
  exact ⟨⟨P', t, e', fun i ↦ Mod.hom_ext _ _ (he i)⟩⟩

end AlgebraicGeometry.ProEtale
