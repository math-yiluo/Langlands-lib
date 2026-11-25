/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import WeilConjectures.AlgebraicGeometry.FiberDegreeOfSplitCofan

/-!
# Splitting neighbourhoods with prescribed degree

Source: Stacks Project, Tag 04HN (lemma-finite-etale-etale-local) and Tag 03SH
(section-trace-method), paragraph after Definition 03SE.
(blueprint: lem-weil-pbc-finite-etale-degree-split-at).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Each point of a small étale object has a neighbourhood on which a finite étale
morphism of degree `d` splits into exactly `d` clopen copies of that neighbourhood.
Source: Stacks Project, Tag 04HN (lemma-finite-etale-etale-local), with the fibre-degree
count in Tag 03SH (section-trace-method), after Definition 03SE.
(blueprint: lem-weil-pbc-finite-etale-degree-split-at).

Proof:
1. Apply `finite_etale_etale_local_split` to the finite étale projection
   `Y ×_X W → W` and the given point `w`. It supplies an étale neighbourhood
   `g : U → W`, a point above `w`, and a finite clopen coproduct of copies of `U`.
2. Choose an algebraic closure of the residue field of the distinguished point of `U`.
   The degree of the geometric fibre of `f` at the composite geometric point is `d`:
   use `fiberDegree_of_isPullback`, `fiberDegree_eq_finrankΓ`, and the prescribed
   `IsFiniteLocallyFreeOfDegree.fiberDegree_eq`. The theorem
   `exists_overIso_sigma_of_isSepClosed` identifies that fibre with a coproduct of
   exactly `d` copies of the algebraically closed field's spectrum.
3. Pull the local splitting back to this geometric point. Base change preserves the
   clopen coproduct and the isomorphisms of its pieces with `U`; pullback pasting
   identifies the resulting scheme with the same geometric fibre. Each copy of the
   spectrum has one point, so the finite splitting index set has cardinality `d`.
4. Reindex by `Fin d`. Compose `g` with `W.hom` to make an object `V` of `X.Etale`,
   and use pullback pasting to transport the cofan to `pullback f V.hom`.
   Its projections remain isomorphisms, and its distinguished point maps to `w`.
   If `d = 0`, the cofan is empty; if `W` is empty there is no point to consider. -/
theorem exists_finiteEtale_degree_split_at
    {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]
    (d : ℕ) [f.IsFiniteLocallyFreeOfDegree d]
    (W : X.Etale) (w : W.left) :
    ∃ (V : X.Etale) (a : V ⟶ W) (v : V.left),
      a.left v = w ∧
      ∃ (D : ULift.{u} (Fin d) → Scheme.{u}) (i : ∀ j, D j ⟶ pullback f V.hom),
        Nonempty (IsColimit (Cofan.mk (pullback f V.hom) i)) ∧
        (∀ j, IsOpenImmersion (i j) ∧ IsClosedImmersion (i j)) ∧
        (∀ j, IsIso (i j ≫ pullback.snd f V.hom)) := by
  classical
  let p := pullback.snd f W.hom
  obtain ⟨U, g, v, hg, hv, J, D, i, hJ, hc, hi, hp⟩ :=
    finite_etale_etale_local_split p w
  let : Etale g := hg
  let : Finite J := hJ
  let : Fintype J := Fintype.ofFinite J
  have hpi (j : J) : IsIso (i j ≫ pullback.snd p g) := by
    obtain ⟨e, he⟩ := hp j
    rw [← he]
    infer_instance
  have hd : Nat.card J = d := by
    rw [← Scheme.Hom.fiberDegree_eq_nat_card_of_split_cofan
      (pullback.snd p g) D i hc hpi v]
    rw [Scheme.Hom.fiberDegree_of_isPullback p (.of_hasPullback p g) v]
    rw [Scheme.Hom.fiberDegree_of_isPullback f (.of_hasPullback f W.hom) (g v)]
    exact Scheme.Hom.IsFiniteLocallyFreeOfDegree.fiberDegree_eq _
  let V : X.Etale := Scheme.Etale.mk (g ≫ W.hom)
  let a : V ⟶ W := MorphismProperty.Over.homMk g rfl
  let e := pullbackLeftPullbackSndIso f W.hom g
  let b : ∀ j, D j ⟶ pullback f V.hom := fun j ↦ i j ≫ e.hom
  have hb : Nonempty (IsColimit (Cofan.mk (pullback f V.hom) b)) := by
    refine ⟨IsColimit.ofIsoColimit hc.some ?_⟩
    exact Cofan.ext e (fun j ↦ rfl)
  let t : ULift.{u} (Fin d) ≃ J :=
    Equiv.ulift.trans (Fintype.equivFinOfCardEq
      (show Fintype.card J = d by simpa only [Nat.card_eq_fintype_card] using hd)).symm
  refine ⟨V, a, v, hv, D ∘ t, fun j ↦ b (t j), ?_, ?_, ?_⟩
  · exact ⟨(Cofan.isColimitEquivOfEquiv t (Cofan.mk _ b)) hb.some⟩
  · intro j
    let : IsOpenImmersion (i (t j)) := (hi (t j)).1
    let : IsClosedImmersion (i (t j)) := (hi (t j)).2
    exact ⟨inferInstance, inferInstance⟩
  · intro j
    have he : b (t j) ≫ pullback.snd f V.hom =
        i (t j) ≫ pullback.snd p g := by
      change i (t j) ≫ e.hom ≫ pullback.snd f (g ≫ W.hom) = _
      rw [pullbackLeftPullbackSndIso_hom_snd]
    rw [he]
    exact hpi (t j)

end AlgebraicGeometry.Etale
