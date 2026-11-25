/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.AlgebraicGeometry.Curve
import WeilConjectures.CategoryTheory.Sites.Point.Linear
import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenHighCohomology
import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenLowBaseChange
import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenPulledCounitHigh
import WeilConjectures.AlgebraicGeometry.Curve.PrimeTorsionNonunitCohomology

/-! # Field extension across a dense open -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry.Etale

namespace AlgebraicGeometry.IsCurve

private theorem bijective_square_iff {A B C D : Type*}
    (a : A → B) (b : C → D) (c : A → C) (d : B → D)
    (hc : Function.Bijective c) (hd : Function.Bijective d)
    (h : ∀ x, b (c x) = d (a x)) : Function.Bijective a ↔ Function.Bijective b := by
  constructor
  · intro ha
    constructor
    · intro y z hyz
      obtain ⟨x, rfl⟩ := hc.2 y
      obtain ⟨w, rfl⟩ := hc.2 z
      exact congrArg c (ha.1 (hd.1 (by rw [← h, ← h, hyz])))
    · intro z
      obtain ⟨t, rfl⟩ := hd.2 z
      obtain ⟨x, rfl⟩ := ha.2 t
      exact ⟨c x, h x⟩
  · intro hb
    constructor
    · intro x y hxy
      exact hc.1 (hb.1 (by rw [h, h, hxy]))
    · intro t
      obtain ⟨y, hy⟩ := hb.2 (d t)
      obtain ⟨x, rfl⟩ := hc.2 y
      exact ⟨x, hd.1 ((h x).symm.trans hy)⟩

private theorem dense_open_all_base_change (Λ : Type (u + 1)) [CommRing Λ]
    {k k' : Type u} [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k']
    {X X' : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f]
    {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : X' ⟶ Spec (.of k')}
    {ι' : X' ⟶ X} (h : IsPullback ι' f' f ι)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (U : X.Opens) (hU : Dense (U : Set X)) :
    let G := (U.ι)_!open[ModuleCat.{u + 1} Λ].obj
      ((U.ι)^*[ModuleCat.{u + 1} Λ].obj F)
    (∀ q : ℕ, Function.Bijective (cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q)) ↔
    (∀ q : ℕ, Function.Bijective (cohomologyMap ι'
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G) q)) := by
  dsimp
  let ε := (sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
      ((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) U.ι).counit.app F)
  have hhigh (q : ℕ) (hq : 1 < q) :=
    bijective_square_iff _ _ (Sheaf.H.map ε q)
      (Sheaf.H.map (((ι')^*[AddCommGrpCat.{u + 1}]).map ε) q)
      ((dense_open_high_cohomology Λ f F U hU).1 q hq)
      (dense_open_pulled_counit_high Λ f h F U hU q hq)
      (fun x ↦ cohomologyMap_map ι' q ε x)
  have hlow := dense_open_low_base_change Λ f h F U hU
  constructor
  · intro hF q
    by_cases hq : q ≤ 1
    · exact hlow.mp (fun n _ ↦ hF n) q hq
    · exact (hhigh q (by omega)).mpr (hF q)
  · intro hG q
    by_cases hq : q ≤ 1
    · exact hlow.mpr (fun n _ ↦ hG n) q hq
    · exact (hhigh q (by omega)).mp (hG q)

private theorem invertible_order_of_annihilator (Λ : Type (u + 1)) [CommRing Λ]
    {k : Type u} [Field k] {X : Scheme.{u}}
    (r : ℕ) [Fact r.Prime] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : r • 𝟙 F = 0) (hr : IsUnit (r : Γ(Spec (.of k), ⊤))) :
    Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F := by
  constructor
  intro Ω _ _ s x
  refine ⟨r, (Fact.out : r.Prime).pos, hr, ?_⟩
  let E := (Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)
  have hz : E.map (0 : F ⟶ F) = 0 := by
    simpa only [zero_smul] using
      (Scheme.pointSmallEtale s).sheafFiber_map_smul (0 : ℕ) (𝟙 F)
  have hm : r • 𝟙 (E.obj F) = 0 := by
    have hh := congrArg E.map hF
    rw [(Scheme.pointSmallEtale s).sheafFiber_map_smul r (𝟙 F)] at hh
    rw [hz] at hh
    simpa only [CategoryTheory.Functor.map_id] using hh
  have hx := congrArg (fun t : E.obj F ⟶ E.obj F ↦ t.hom x) hm
  simpa using hx

/-- The two conditional field-extension assertions transfer across a dense-open counit
for a constructible sheaf killed by a prime.
Source: Stacks Project, Tag 0GJA, proof, the five-term sequence and remark (c)
(blueprint: lem-pbc-s2-dense-open-base-change).

Proof: Write G=j_!j^*F and B=i_*i^*F for the reduced closed complement. The complement is
a finite union of k-rational points. Its base change to an algebraically closed extension
is the corresponding union of spectra of that field, and inverse image identifies the
geometric stalks of F at these points with the new stalks. Thus the cohomology pullback
for B is bijective in degree zero (the product of these stalk identifications) and in
positive degrees (both groups are zero). Inverse image preserves the open-closed short
exact sequence and identifies the pullback of G with extension by zero from the base
change of U. The pullback-cohomology ladder is a morphism of long exact sequences with
the canonical cohomologyMap as vertical maps. Since both boundary sheaves have zero
positive cohomology, the higher-degree counit maps are bijective on both rows. Therefore
the field-extension maps for F and G in degrees at least two are bijective together.
For degrees zero and one, use the exact five-term sequence
0 -> H^0(G) -> H^0(F) -> H^0(B) -> H^1(G) -> H^1(F) -> 0.
If all vertical maps for G are bijective, the five lemma at H^0(F) and at H^1(F), using
the bijective B map and zero end terms, makes all vertical maps for F bijective. Conversely,
if all vertical maps for F are bijective, the five lemma at H^0(G) and at H^1(G), again
using the bijective B map and zero end terms, gives the maps for G. This proves the proper
base-change assertion. For the invertible-order assertion, if r is invertible in k,
both F and G have invertible-order torsion and the same ladder applies. If r equals the
positive characteristic, any invertible-order hypothesis on either r-torsion sheaf makes
that sheaf zero, since each stalk element is killed by coprime integers. Its pullback is
zero and every comparison is bijective. Constructibility and r-torsion of G follow from
its stalks, which equal those of F on U and vanish off U. These cases prove both conditional
implications, including the empty scheme, the zero sheaf, and the full open. -/
theorem dense_open_base_change (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (r : ℕ) [Fact r.Prime] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsConstructibleSheaf F] (hF : r • 𝟙 F = 0)
    (U : X.Opens) (hU : Dense (U : Set X)) :
    let G := (U.ι)_!open[ModuleCat.{u + 1} Λ].obj
      ((U.ι)^*[ModuleCat.{u + 1} Λ].obj F)
    (BaseChangeOfInvertibleOrder Λ f F ↔ BaseChangeOfInvertibleOrder Λ f G) ∧
    (BaseChangeOfIsProper Λ f F ↔ BaseChangeOfIsProper Λ f G)  := by
  classical
  dsimp
  let G := (U.ι)_!open[ModuleCat.{u + 1} Λ].obj
    ((U.ι)^*[ModuleCat.{u + 1} Λ].obj F)
  have hG : r • 𝟙 G = 0 := by
    have h := congrArg (fun t ↦ ((U.ι)_!open[ModuleCat.{u + 1} Λ]).map
      (((U.ι)^*[ModuleCat.{u + 1} Λ]).map t)) hF
    simp only [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_zero] at h
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id] at h
    exact h
  have hcompare (k' : Type u) [Field k'] [IsAlgClosed k'] {X' : Scheme.{u}}
      {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : X' ⟶ Spec (.of k')}
      {ι' : X' ⟶ X} (h : IsPullback ι' f' f ι) :=
    dense_open_all_base_change Λ f h F U hU
  constructor
  · by_cases hr : IsUnit (r : Γ(Spec (.of k), ⊤))
    · have : Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F :=
        invertible_order_of_annihilator Λ r F hF hr
      have : Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) G :=
        invertible_order_of_annihilator Λ r G hG hr
      constructor
      · intro h _ k' _ _ X' ι f' ι' hp
        exact (hcompare k' hp).mp (h k' hp)
      · intro h _ k' _ _ X' ι f' ι' hp
        exact (hcompare k' hp).mpr (h k' hp)
    · have hz (H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
          (hH : r • 𝟙 H = 0) : BaseChangeOfInvertibleOrder Λ f H := by
        intro _ k' _ _ X' ι f' ι' _ q
        obtain ⟨hs, ht⟩ := prime_torsion_nonunit_cohomology Λ ι' r H hH hr q
        exact ⟨fun x y _ ↦ hs.elim x y, fun y ↦ ⟨0, ht.elim _ y⟩⟩
      exact ⟨fun _ ↦ hz G hG, fun _ ↦ hz F hF⟩
  · constructor
    · intro h _ k' _ _ X' ι f' ι' hp
      exact (hcompare k' hp).mp (h k' hp)
    · intro h _ k' _ _ X' ι f' ι' hp
      exact (hcompare k' hp).mpr (h k' hp)

end AlgebraicGeometry.IsCurve
