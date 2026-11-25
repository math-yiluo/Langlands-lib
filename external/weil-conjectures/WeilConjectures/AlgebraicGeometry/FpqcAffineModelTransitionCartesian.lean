/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Cover.Directed
import Mathlib.CategoryTheory.Sites.Hypercover.Subcanonical

/-!
# Cartesian transitions between fpqc local models

Source: Stacks Project, Descent, Tags 02W3 and 023Q
(blueprint: lem-galois-fpqc-affine-model-transition-cartesian).

The canonical restriction square is pasted with the model over the larger open.
Mathlib's pullback criterion for covers in a subcanonical topology then applies to the
fpqc singleton over the smaller open, using its given Cartesian model square.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A reconstructed transition between Cartesian local models is Cartesian.
Source: Stacks Project, Descent, Tag 02W3 (nested affine models), using Tag 02W0.
(blueprint: lem-galois-fpqc-affine-model-transition-cartesian)

Proof: Put P = W_B times_B U and let k : W_U -> P be induced by t and the
structural map to U. The Cartesian squares hp B and the two canonical
restriction squares X_U -> X_B and V_U -> V_B identify the pullback of P along
X_U -> U with V_U. The square hp U makes the same identification for W_U.
The reconstruction equation identifies the base change of k with the identity
under these identifications. Hence that base change is an isomorphism.
The map X_U -> U is fpqc by base change of hf. Full faithfulness of fpqc descent
of morphisms (Tag 02W0) descends the inverse of the base-changed k: its descent
compatibility follows by taking inverses in the compatibility equation for k.
Faithfulness makes both inverse composites identities. Thus k is an isomorphism,
and composing the defining pullback square for P with k gives the asserted
Cartesian square. This argument includes empty opens and objects. -/
theorem fpqc_affine_model_transition_cartesian
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : Presieve.singleton f ∈ Scheme.fpqcPrecoverage S)
    {V : Over X}
    (W : ∀ U : S.affineOpens, Over U.1.toScheme)
    (r : ∀ U : S.affineOpens,
      pullback V.hom (pullback.fst f U.1.ι) ⟶ (W U).left)
    (hp : ∀ U, IsPullback (r U) (pullback.snd V.hom (pullback.fst f U.1.ι))
      (W U).hom (pullback.snd f U.1.ι))
    {U B : S.affineOpens} (i : U ⟶ B)
    (t : (W U).left ⟶ (W B).left)
    (ht : t ≫ (W B).hom = (W U).hom ≫ S.directedAffineCover.trans i)
    (hr : Scheme.Cover.trans ((S.directedAffineCover.pullback₁ f).pullback₁ V.hom) i ≫
      r B = r U ≫ t) :
    IsPullback t (W U).hom (W B).hom (S.directedAffineCover.trans i) := by
  -- Paste the canonical restriction square, then check Cartesianity on the fpqc cover.
  let x := Scheme.Cover.trans (S.directedAffineCover.pullback₁ f) i
  let c := Scheme.Cover.trans ((S.directedAffineCover.pullback₁ f).pullback₁ V.hom) i
  have hx₁ : x ≫ pullback.fst f B.1.ι = pullback.fst f U.1.ι := by
    dsimp [x, Scheme.Cover.trans, Scheme.Cover.LocallyDirected.trans]
    simp [pullback.map, Scheme.directedAffineCover,
      Precoverage.ZeroHypercover.pullback₁, PreZeroHypercover.pullback₁]
  have hx₂ : x ≫ pullback.snd f B.1.ι =
      pullback.snd f U.1.ι ≫ S.directedAffineCover.trans i := by
    dsimp [x, Scheme.Cover.trans, Scheme.Cover.LocallyDirected.trans]
    simp [pullback.map, Scheme.directedAffineCover,
      Precoverage.ZeroHypercover.pullback₁, PreZeroHypercover.pullback₁]
  have hc₁ : c ≫ pullback.fst V.hom (pullback.fst f B.1.ι) =
      pullback.fst V.hom (pullback.fst f U.1.ι) := by
    dsimp [c, Scheme.Cover.trans, Scheme.Cover.LocallyDirected.trans]
    simp [pullback.map, Scheme.directedAffineCover,
      Precoverage.ZeroHypercover.pullback₁, PreZeroHypercover.pullback₁]
  have hc₂ : c ≫ pullback.snd V.hom (pullback.fst f B.1.ι) =
      pullback.snd V.hom (pullback.fst f U.1.ι) ≫ x := by
    dsimp [c, x, Scheme.Cover.trans, Scheme.Cover.LocallyDirected.trans]
    simp [pullback.map, Scheme.directedAffineCover,
      Precoverage.ZeroHypercover.pullback₁, PreZeroHypercover.pullback₁]
  have hc : IsPullback c (pullback.snd V.hom (pullback.fst f U.1.ι))
      (pullback.snd V.hom (pullback.fst f B.1.ι)) x := by
    apply IsPullback.of_right
      (t := (IsPullback.of_hasPullback V.hom (pullback.fst f B.1.ι)))
    · simpa only [hc₁, hx₁] using
        (IsPullback.of_hasPullback V.hom (pullback.fst f U.1.ι))
    · exact hc₂
  have houter := hc.paste_horiz (hp B)
  rw [show c ≫ r B = r U ≫ t from hr, hx₂] at houter
  have hq : Presieve.singleton (pullback.snd f U.1.ι) ∈
      Scheme.fpqcPrecoverage U.1.toScheme := by
    rw [← Presieve.ofArrows_pUnit.{0}] at hf ⊢
    exact Precoverage.mem_coverings_of_isPullback (fun _ : PUnit.{1} ↦ f) hf U.1.ι
      (fun _ ↦ pullback.snd f U.1.ι) (fun _ ↦ pullback.fst f U.1.ι)
      (fun _ ↦ (IsPullback.of_hasPullback f U.1.ι).flip)
  have hlocal : IsPullback (W U).hom t (S.directedAffineCover.trans i) (W B).hom := by
    apply Precoverage.ZeroHypercover.isPullback_of_forall_isPullback
      (W U).hom t (S.directedAffineCover.trans i) (W B).hom
      (Precoverage.ZeroHypercover.singleton _ hq)
    intro j
    dsimp only [Precoverage.ZeroHypercover.singleton, PreZeroHypercover.singleton]
    exact houter.flip.of_iso (hp U).isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [IsPullback.isoPullback_hom_snd])
      (by simp [← Category.assoc, IsPullback.isoPullback_hom_fst]) (by simp) (by simp)
  exact { hlocal.flip with w := ht }

end AlgebraicGeometry
