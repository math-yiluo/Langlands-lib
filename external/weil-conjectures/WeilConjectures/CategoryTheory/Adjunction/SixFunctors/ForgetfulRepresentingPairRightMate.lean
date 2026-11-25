/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Representing lifts and the right mate under forgetting

Source: blueprint, sec-six-functors/sk-thm-sf-package,
cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction sentence;
the DAG's native-derived expansion, Old proof Steps 7–8.
(blueprint: lem-sf-forgetful-representing-pair-right-mate)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe uWX uWY uCX uCY vWX vWY vCX vCY

namespace CategoryTheory.Adjunction

variable {WX : Type uWX} {WY : Type uWY} {CX : Type uCX} {CY : Type uCY}
  [Category.{vWX} WX] [Category.{vWY} WY] [Category.{vCX} CX] [Category.{vCY} CY]
  {UX : WX ⥤ CX} {UY : WY ⥤ CY} {FW : WX ⥤ WY} {GW : WY ⥤ WX}
  {F : CX ⥤ CY} {G : CY ⥤ CX}

/-- The fixed right mate of the inverse left-adjoint comparison, using Mathlib's
`mateEquiv` from def-weil-pbc-adjunction-mate. Its data depend only on the two
specified adjunctions and `c`, not on representing triples.
Source: cor-coef-verdier-weil-equivariance.proof.md, final sentence, expanded
as Step 2 of the node (Old proof Steps 7–8).
(blueprint: lem-sf-forgetful-representing-pair-right-mate) -/
def forgetfulRightMate (adjW : FW ⊣ GW) (adj : F ⊣ G)
    (c : FW ⋙ UY ≅ UX ⋙ F) : GW ⋙ UX ⟶ UY ⋙ G :=
  (mateEquiv adjW adj (TwoSquare.mk UX FW F UY c.inv))

/-- Objectwise representing lifts identify the fixed right mate with the forgotten
representing isomorphisms; it is invertible, independent of the lifts, and identifies
both adjunctions' units and counits. No functor structure on `H` is assumed.

Source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-adjunction
sentence; the DAG's native-derived expansion of Old proof Steps 7–8.
(blueprint: lem-sf-forgetful-representing-pair-right-mate)

Proof plan from the node:
1. For fixed `L`, put `A = GW.obj L`. The adjunction bijections `P` and the
representing bijections `Q` send a morphism to its composite with the corresponding
counit. Take `h = Q_A⁻¹(counitW)` and `k = P_H⁻¹(d)`. Functoriality gives
`Q_H(k ≫ h) = Q_H(1)` and `P_A(h ≫ k) = P_A(1)`; injectivity gives both inverse
identities. The same `Q_A`-injectivity gives uniqueness of `h`.
2. Apply def-weil-pbc-adjunction-mate (`mateEquiv`) to `c.inv`. Its component
is the ordinary adjunct of `c.inv.app A ≫ UY.map (adjW.counit.app L)`.
3. Naturality of `c` at `h`, the assumed formula for `UY.map d`, and the defining
counit equation for `h` show that `UX.map h ≫ e.hom` has that same transpose.
Injectivity of the ordinary adjunction bijection gives the factorization.
4. Each component has inverse `e.inv ≫ UX.map h.inv`. Cancelling components in
the naturality of the mate proves naturality of these inverses, so the mate is
an isomorphism without any functor structure on the chosen representing objects.
5. The transpose identity, composed with `c.hom`, gives the counit equation.
The inverse mate formula from def-weil-pbc-adjunction-mate, transposed under the
ordinary adjunction and composed with `G.map c.hom`, gives the unit equation.
6. Repeat the factorization for any second representing triple. Both expressions
are the same fixed mate component, since its definition never used a triple.
Equivalently, `h.inv ≫ h'` is the unique counit-preserving comparison of the
representing objects and its forgotten map identifies `e` and `e'`. No step uses
fullness or faithfulness of either forgetful functor. -/
theorem forgetful_representingPair_rightMate (adjW : FW ⊣ GW) (adj : F ⊣ G)
    (c : FW ⋙ UY ≅ UX ⋙ F) (H : WY → WX)
    (e : ∀ L : WY, UX.obj (H L) ≅ G.obj (UY.obj L))
    (d : ∀ L : WY, FW.obj (H L) ⟶ L)
    (hd : ∀ L : WY, UY.map (d L) =
      c.hom.app (H L) ≫ F.map (e L).hom ≫ adj.counit.app (UY.obj L))
    (hbij : ∀ (L : WY) (K : WX),
      Function.Bijective (fun u : K ⟶ H L => FW.map u ≫ d L)) :
    IsIso (forgetfulRightMate adjW adj c) ∧
    (∀ L : WY, ∃ h : GW.obj L ≅ H L,
      FW.map h.hom ≫ d L = adjW.counit.app L ∧
      (∀ h' : GW.obj L ≅ H L,
        FW.map h'.hom ≫ d L = adjW.counit.app L → h' = h) ∧
      (forgetfulRightMate adjW adj c).app L = UX.map h.hom ≫ (e L).hom) ∧
    (∀ L : WY, (forgetfulRightMate adjW adj c).app L =
      adj.homEquiv (UX.obj (GW.obj L)) (UY.obj L)
        (c.inv.app (GW.obj L) ≫ UY.map (adjW.counit.app L))) ∧
    (∀ L : WY,
      c.hom.app (GW.obj L) ≫ F.map ((forgetfulRightMate adjW adj c).app L) ≫
        adj.counit.app (UY.obj L) = UY.map (adjW.counit.app L)) ∧
    (∀ K : WX, UX.map (adjW.unit.app K) ≫
      (forgetfulRightMate adjW adj c).app (FW.obj K) ≫ G.map (c.hom.app K) =
        adj.unit.app (UX.obj K)) ∧
    (∀ (L : WY) (H' : WX) (e' : UX.obj H' ≅ G.obj (UY.obj L))
        (d' : FW.obj H' ⟶ L),
      UY.map d' = c.hom.app H' ≫ F.map e'.hom ≫ adj.counit.app (UY.obj L) →
      (∀ K : WX, Function.Bijective (fun u : K ⟶ H' => FW.map u ≫ d')) →
      ∀ (h : GW.obj L ≅ H L) (h' : GW.obj L ≅ H'),
        FW.map h.hom ≫ d L = adjW.counit.app L →
        FW.map h'.hom ≫ d' = adjW.counit.app L →
        UX.map h.hom ≫ (e L).hom = UX.map h'.hom ≫ e'.hom) := by
  have transpose (L : WY) :
      F.map ((forgetfulRightMate adjW adj c).app L) ≫
        adj.counit.app (UY.obj L) =
          c.inv.app (GW.obj L) ≫ UY.map (adjW.counit.app L) :=
    mateEquiv_counit adjW adj (TwoSquare.mk UX FW F UY c.inv) L
  have factor (L : WY) (B : WX) (j : UX.obj B ≅ G.obj (UY.obj L))
      (t : FW.obj B ⟶ L)
      (ht : UY.map t = c.hom.app B ≫ F.map j.hom ≫ adj.counit.app (UY.obj L))
      (h : GW.obj L ⟶ B) (hh : FW.map h ≫ t = adjW.counit.app L) :
      (forgetfulRightMate adjW adj c).app L = UX.map h ≫ j.hom := by
    apply (adj.homEquiv _ _).symm.injective
    rw [homEquiv_counit, homEquiv_counit, transpose]
    calc
      c.inv.app (GW.obj L) ≫ UY.map (adjW.counit.app L) =
          c.inv.app (GW.obj L) ≫ UY.map (FW.map h) ≫ UY.map t := by
        rw [← UY.map_comp, hh]
      _ = c.inv.app (GW.obj L) ≫ UY.map (FW.map h) ≫ c.hom.app B ≫
          F.map j.hom ≫ adj.counit.app (UY.obj L) := by rw [ht]
      _ = F.map (UX.map h) ≫ F.map j.hom ≫ adj.counit.app (UY.obj L) := by
        rw [← Functor.comp_map, c.hom.naturality_assoc]
        simp
      _ = F.map (UX.map h ≫ j.hom) ≫ adj.counit.app (UY.obj L) := by
        rw [F.map_comp, Category.assoc]
  have lifts (L : WY) : ∃ h : GW.obj L ≅ H L,
      FW.map h.hom ≫ d L = adjW.counit.app L ∧
      (∀ h' : GW.obj L ≅ H L,
        FW.map h'.hom ≫ d L = adjW.counit.app L → h' = h) ∧
      (forgetfulRightMate adjW adj c).app L = UX.map h.hom ≫ (e L).hom := by
    obtain ⟨h, hh⟩ := (hbij L (GW.obj L)).surjective (adjW.counit.app L)
    let k : H L ⟶ GW.obj L := adjW.homEquiv (H L) L (d L)
    have hk : FW.map k ≫ adjW.counit.app L = d L :=
      (adjW.homEquiv (H L) L).symm_apply_apply (d L)
    have hkh : h ≫ k = 𝟙 (GW.obj L) := by
      apply (adjW.homEquiv (GW.obj L) L).symm.injective
      simp only [homEquiv_counit, FW.map_comp, Category.assoc, hk, hh,
        FW.map_id, Category.id_comp]
    have khh : k ≫ h = 𝟙 (H L) := by
      apply (hbij L (H L)).injective
      simp only [FW.map_comp, Category.assoc, hh, hk, FW.map_id, Category.id_comp]
    let i : GW.obj L ≅ H L := ⟨h, k, hkh, khh⟩
    refine ⟨i, hh, ?_, factor L (H L) (e L) (d L) (hd L) h hh⟩
    intro h' hh'
    apply Iso.ext
    exact (hbij L (GW.obj L)).injective (hh'.trans hh.symm)
  have iso : IsIso (forgetfulRightMate adjW adj c) := by
    have (L : WY) : IsIso ((forgetfulRightMate adjW adj c).app L) := by
      obtain ⟨h, _, _, hf⟩ := lifts L
      rw [hf]
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  refine ⟨iso, lifts, ?_, ?_, ?_, ?_⟩
  · intro L
    exact (adj.eq_homEquiv_apply _ _).mpr (transpose L)
  · intro L
    rw [← Category.assoc, Category.assoc, transpose]
    simp
  · intro K
    rw [← Category.assoc]
    change (UX.map (adjW.unit.app K) ≫
      (mateEquiv adjW adj (TwoSquare.mk UX FW F UY c.inv)).app (FW.obj K)) ≫
        G.map (c.hom.app K) = adj.unit.app (UX.obj K)
    rw [unit_mateEquiv]
    simp [← G.map_comp]
  · intro L H' e' d' hd' _ h h' hh hh'
    exact (factor L (H L) (e L) (d L) (hd L) h.hom hh).symm.trans
      (factor L H' e' d' hd' h'.hom hh')

end CategoryTheory.Adjunction
