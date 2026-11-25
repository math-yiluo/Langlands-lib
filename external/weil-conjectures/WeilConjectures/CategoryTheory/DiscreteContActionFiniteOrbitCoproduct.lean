/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleFieldGeometricAction
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.MulAction
import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# Orbit coproducts of discrete continuous actions

Source: Stacks Project, Tag 03QT, proof of theorem-equivalence-sheaves-point.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

attribute [local instance] AlgebraicGeometry.etaleFieldDiscreteForget₂
  AlgebraicGeometry.etaleFieldActionForget₂

set_option backward.isDefEq.respectTransparency false in
/-- Source: Stacks Project, Tag 03QT, proof of theorem-equivalence-sheaves-point;
finiteness uses Mathlib Subgroup.quotient_finite_of_isOpen.
(blueprint: lem-exc-discrete-continuous-action-finite-orbit-coproduct).

Proof: Give the underlying type of M its action specified by M.obj.obj.ρ and
let I be its quotient by the orbit equivalence relation. For each orbit take
its subtype with the restricted action and discrete topology. The restricted
action is continuous since its inclusion in M is an embedding. The stabilizer
of any point is open, as it is the inverse image of the open singleton under
the continuous orbit map. Its coset quotient is finite by compactness of G,
and the orbit-stabilizer bijection makes the orbit finite. The subtype
inclusions are equivariant. Every element belongs to exactly one orbit, so
maps out of the disjoint union are precisely families of maps out of the
orbits; if those maps are equivariant their union is equivariant. This proves
the coproduct universal property in discrete continuous actions. The same
argument with arbitrary set maps proves the underlying set coproduct property.
For empty M the quotient and family are empty and both cocones are initial. -/
theorem discreteContAction_finite_orbit_coproduct
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (M : DiscreteContAction (Type w) G) :
    let U := ObjectProperty.ι (ContAction.IsDiscrete (V := Type w) (G := G))
      ⋙ ObjectProperty.ι (Action.IsContinuous (V := Type w) (G := G))
      ⋙ Action.forget (Type w) G
    ∃ (I : Type w) (A : I → DiscreteContAction (Type w) G) (f : ∀ i, A i ⟶ M),
      (∀ i, Finite (A i).obj.obj.V) ∧
      Nonempty (IsColimit (Cofan.mk M f)) ∧
      Nonempty (IsColimit (U.mapCocone (Cofan.mk M f))) := by
  classical
  dsimp only
  let U := ObjectProperty.ι (ContAction.IsDiscrete (V := Type w) (G := G))
    ⋙ ObjectProperty.ι (Action.IsContinuous (V := Type w) (G := G))
    ⋙ Action.forget (Type w) G
  let X := (forget₂ (Action (Type w) G) TopCat).obj M.obj.obj
  let _ : MulAction G X :=
    inferInstanceAs (MulAction G ((forget₂ (Action (Type w) G) TopCat).obj M.obj.obj))
  have : ContinuousSMul G X := M.obj.property
  have : DiscreteTopology X := inferInstanceAs (DiscreteTopology ((forget₂ _ TopCat).obj M))
  let I := MulAction.orbitRel.Quotient G X
  let A (i : I) : DiscreteContAction (Type w) G :=
    ⟨⟨Action.ofMulAction G i.orbit, by
      apply (Action.isContinuous_def _).mpr
      have ht : (inferInstance : TopologicalSpace i.orbit) = ⊥ :=
        DiscreteTopology.eq_bot
      have hcont : Continuous (fun p : G × i.orbit ↦ p.1 • p.2) :=
        Continuous.subtype_mk (continuous_fst.smul
          (continuous_subtype_val.comp continuous_snd)) _
      convert hcont using 1
      all_goals first | rfl | exact ht.symm | congr 1; exact ht.symm⟩, by
      change DiscreteTopology (TopCat.discrete.obj i.orbit)
      infer_instance⟩
  let f (i : I) : A i ⟶ M := ObjectProperty.homMk
    (ObjectProperty.homMk ⟨↾Subtype.val, fun g ↦ rfl⟩)
  have hfinite (i : I) : Finite (A i).obj.obj.V := by
    change Finite i.orbit
    rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out i Quotient.out_eq']
    have : Finite (G ⧸ MulAction.stabilizer G i.out) :=
      Subgroup.quotient_finite_of_isOpen _ (stabilizer_isOpen G i.out)
    exact Finite.of_equiv _ (MulAction.orbitEquivQuotientStabilizer G i.out).symm
  let E := MulAction.selfEquivSigmaOrbits' G X
  have hE (x : X) : (E x).2.val = x := by rfl
  have hEa (i : I) (a : i.orbit) : E a.val = ⟨i, a⟩ := E.apply_symm_apply ⟨i, a⟩
  let c := Cofan.mk M f
  have hc : IsColimit c :=
    { desc := fun s ↦ ObjectProperty.homMk (ObjectProperty.homMk
        { hom := ↾fun x ↦ (s.ι.app ⟨(E x).1⟩).hom.hom.hom (E x).2
          comm := fun g ↦ by
            ext x
            change X at x
            let i := (E x).1
            let a : i.orbit := (E x).2
            have ha : a.val = x := hE x
            have he : E (g • x) = ⟨i, g • a⟩ := by
              rw [← ha]
              exact hEa i (g • a)
            change (s.ι.app ⟨(E (g • x)).1⟩).hom.hom.hom (E (g • x)).2 = _
            rw [he]
            exact ConcreteCategory.congr_hom ((s.ι.app ⟨i⟩).hom.hom.comm g) a })
      fac := fun s i ↦ by
        apply ObjectProperty.hom_ext
        apply ObjectProperty.hom_ext
        apply Action.hom_ext
        ext x
        change (s.ι.app ⟨(E x.val).1⟩).hom.hom.hom (E x.val).2 = _
        rw [hEa i.as x]
        rfl
      uniq := fun s m h ↦ by
        apply ObjectProperty.hom_ext
        apply ObjectProperty.hom_ext
        apply Action.hom_ext
        ext x
        have hh := ConcreteCategory.congr_hom
          (congrArg (fun k ↦ k.hom.hom.hom) (h ⟨(E x).1⟩)) (E x).2
        exact hh }
  have hu : Nonempty (IsColimit (U.mapCocone c)) := by
    have hbij : Function.Bijective (fun a : Σ i : I, i.orbit ↦ a.2.val) :=
      E.symm.bijective
    have h := (Cofan.nonempty_isColimit_iff_bijective_fromSigma
      (Cofan.mk (U.obj M) (fun i ↦ U.map (f i)))).2 hbij
    exact ⟨(Cofan.isColimitMapCoconeEquiv U A c).symm h.some⟩
  exact ⟨I, A, f, hfinite, ⟨hc⟩, hu⟩

end CategoryTheory
