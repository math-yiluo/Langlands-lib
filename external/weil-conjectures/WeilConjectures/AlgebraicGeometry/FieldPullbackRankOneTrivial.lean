/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine
import Mathlib.AlgebraicGeometry.Properties

/-! A finite locally free module over a field with invertible nonempty pullback. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private noncomputable def tensorIsoPullback {A B : Scheme.{u}} (g : A ⟶ B) :
    tensorPullback g ≅ pullback g :=
  (nonempty_tensorPullbackAdjunction g).some.leftAdjointUniq
    (pullbackPushforwardAdjunction g)

/-- A finite locally free module on the spectrum of a field is trivial if its pullback
along a morphism from a nonempty scheme is invertible.

Source: Stacks Project, Tag 0BF0, the generic-field step of its use of Tag 0BDP.
(blueprint: lem-sc-field-pullback-rank-one-trivial).

Proof: On the one-point affine scheme Spec K, finite local freeness gives a global
finite free presentation N ≅ O_K^I for a finite type I. Pullback preserves this free
presentation. Choose a point y of Y and a neighbourhood V of y on which the invertible
pullback is trivial. On V it is both O_V^I and O_V. Taking global sections yields
linear isomorphisms with R^I and R, where R = Γ(V, O_V) is a nonzero commutative ring
because V contains y. The strong rank condition gives card I = 1. A coproduct indexed
by the resulting unique type I is the structure module, so N ≅ O_K. Nonemptiness is
essential: on the empty scheme all ranks have isomorphic pullbacks. No flatness,
properness or section of p is needed. -/
theorem nonempty_iso_unit_of_invertible_field_pullback
    (K : Type u) [Field K] {Y : Scheme.{u}} [Nonempty Y]
    (p : Y ⟶ Spec (CommRingCat.of K))
    (N : (Spec (CommRingCat.of K)).Modules) [N.IsFiniteLocallyFree]
    [((tensorPullback p).obj N).IsInvertible] :
    Nonempty (N ≅ SheafOfModules.unit _) := by
  classical
  let x := IsLocalRing.closedPoint K
  obtain ⟨U, I, hI, hx, ⟨eover⟩⟩ := exists_mem_over_iso_free N x
  let eU := overIsoFreeEquiv N U I eover
  have hU : U = ⊤ := by
    apply eq_top_iff.mpr
    intro z _
    rwa [Subsingleton.elim z x]
  subst U
  have : IsIso (⊤ : (Spec (CommRingCat.of K)).Opens).ι :=
    inferInstanceAs (IsIso (Spec (CommRingCat.of K)).topIso.hom)
  let e : N ≅ SheafOfModules.free I := isoFreeOfRestrictIso N _ eU
  let P := (pullback p).obj N
  have : P.IsInvertible := IsInvertible.of_iso ((tensorIsoPullback p).app N)
  let y : Y := Classical.choice inferInstance
  obtain ⟨V, hy, ⟨eu⟩⟩ := IsInvertible.exists_isoUnit (M := P) y
  have : Nonempty V := ⟨⟨y, hy⟩⟩
  let g := V.ι ≫ p
  let M := (pullback g).obj N
  let eunit : M ≅ SheafOfModules.unit _ := (pullbackComp V.ι p).symm.app N ≪≫ eu
  let ef : M ≅ SheafOfModules.free I := (pullback g).mapIso e ≪≫ pullbackFreeIso g I
  have hcard : Fintype.card I = 1 := by
    let R := Γ(V.toScheme, ⊤)
    have : Nonempty (⊤ : V.toScheme.Opens) := ⟨⟨⟨y, hy⟩, trivial⟩⟩
    have : Nontrivial R := Scheme.component_nontrivial V.toScheme ⊤
    have : StrongRankCondition R := inferInstance
    have hi : Module.finrank R Γ(M, ⊤) = Fintype.card I := by
      rw [(appLinearEquivOfIso ef ⊤).finrank_eq, (freeSectionsEquiv I).finrank_eq]
      exact Module.finrank_fintype_fun_eq_card R
    have h₁ : Module.finrank R Γ(M, ⊤) = 1 := by
      rw [(appLinearEquivOfIso eunit ⊤).finrank_eq]
      exact Module.finrank_self R
    exact hi.symm.trans h₁
  obtain ⟨i, hi⟩ := Fintype.card_eq_one_iff.mp hcard
  let : Unique I := ⟨⟨i⟩, hi⟩
  exact ⟨e ≪≫ coproductUniqueIso
    (fun _ : I ↦ SheafOfModules.unit (Spec (CommRingCat.of K)).ringCatSheaf)⟩

end AlgebraicGeometry.Scheme.Modules
