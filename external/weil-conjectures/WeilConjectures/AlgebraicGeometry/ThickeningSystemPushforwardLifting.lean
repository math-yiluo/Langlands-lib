/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ThickeningSystemPushforward
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.ThickeningSystemPushforwardAssembly
import WeilConjectures.AlgebraicGeometry.ThickeningSystemPushforwardTermwiseLift
import WeilConjectures.AlgebraicGeometry.ClosedImmersionCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.ClosedImmersionIdealPowerAnnihilation
import WeilConjectures.AlgebraicGeometry.TensorPullback

/-! # Lifting an adic system to the closed thickenings

Source: Stacks Project, Cohomology of Schemes, Remark 088F and Lemma 087T.
(blueprint: lem-weil-pbc-thickening-system-pushforward-lifting).
-/

@[expose] public section
universe v
open CategoryTheory
namespace AlgebraicGeometry
noncomputable section
set_option autoImplicit false

/-- Every adic system has a preimage under the explicit pushforward system functor.
This only asserts object lifting, without constructing an equivalence or evaluation
comparisons and without asserting full faithfulness.

Source: Stacks, Remark 088F, Lemma 087T, equation 0880
(blueprint: lem-weil-pbc-thickening-system-pushforward-lifting).
Proof: The sources of the closed immersions `j n` are Noetherian. For each term of `H`,
the annihilation condition and `(j n).ker = J^(n+1)` place it in the essential image
of the closed-immersion coherent equivalence. Choose coherent terms `M_n` and
isomorphisms `j_(n,*) M_n ≅ H_n`. Transport each adjacent transition of `H` across these
isomorphisms. Use pushforward composition and `hi` to regard its target as
`j_(n+1,*) i_(n,*) M_n`. Full faithfulness of `j_(n+1,*)` uniquely lifts this morphism
and the supplied adjunction takes it to a map `i_n^* M_(n+1) → M_n`.
The kernel of `i n` is `(J^(n+1)).comap (j (n+1))`. The unit-quotient theorem and the
closed pushforward ideal-power comparison identify the pushforward of the adjoint map
with the induced quotient transition of `H`, conjugated by the chosen term isomorphisms.
The adic quotient condition makes this pushforward invertible. Full faithfulness of
closed pushforward reflects isomorphisms, so these maps are the comparison isomorphisms
of a coherent thickening system `M`. The term isomorphisms commute with the adjacent
transitions by construction. `NatTrans.ofOpSequence` extends their homs and inverses
to natural transformations; their two inverse identities hold componentwise. They
therefore assemble to the displayed isomorphism of inverse systems. -/
theorem thickeningSystemPushforward_lifting
    {X : Scheme.{v}} [IsNoetherian X] {T : ℕ → Scheme.{v}}
    {i : ∀ n, T n ⟶ T (n + 1)}
    (j : ∀ n, T n ⟶ X) (hi : ∀ n, i n ≫ j (n + 1) = j n)
    (ai : ∀ n, Scheme.Modules.tensorPullback (i n) ⊣ Scheme.Modules.pushforward (i n))
    (J : X.IdealSheafData)
    (hgeom : ∀ n, IsClosedImmersion (j n) ∧ (j n).ker = J ^ (n + 1))
    (H : CoherentFormalModule X J) :
    ∃ M : CoherentThickeningSystem T i,
      Nonempty ((thickeningSystemPushforward j hi ai).obj M ≅ H.obj) := by
  classical
  have : ∀ n, IsClosedImmersion (j n) := fun n ↦ (hgeom n).1
  have terms (n : ℕ) : ∃ M : CoherentModules (T n),
      Nonempty ((Scheme.Modules.pushforward (j n)).obj M.obj ≅ H.obj.obj (Opposite.op n)) := by
    have : IsNoetherian (T n) := isNoetherian_of_locallyOfFiniteType (j n)
    let F : CoherentModules X := ⟨H.obj.obj (Opposite.op n), H.property.1 n⟩
    have hqc := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType
      X F.obj).mp F.property
    have : F.obj.IsQuasicoherent := hqc.1
    have hz : CoherentModuleSupportedOn F (j n) := by
      dsimp only [CoherentModuleSupportedOn]
      rw [(hgeom n).2]
      have hz := Scheme.closedImmersion_idealPower_annihilation (𝟙 X) J (n + 1) F.obj F.obj
        ((Scheme.Modules.pushforwardId X).app F.obj).symm (H.property.2.1 n)
      rw [Scheme.IdealSheafData.map_id] at hz
      exact hz
    obtain ⟨E, ⟨α⟩⟩ := closedImmersion_coherent_equivalence (j n)
    let K := E.inverse.obj ⟨F, hz⟩
    let β := E.counitIso.app ⟨F, hz⟩
    refine ⟨K, ⟨?_⟩⟩
    exact (α.app K).symm ≪≫
      (ObjectProperty.ι (RingedSpace.IsCoherent X.toRingedSpace)).mapIso
        ((ObjectProperty.ι (fun F : CoherentModules X ↦
          CoherentModuleSupportedOn F (j n))).mapIso β)
  choose M he using terms
  let e := fun n ↦ Classical.choice (he n)
  have lifts (n : ℕ) : ∃ u : (M (n + 1)).obj ⟶
        (Scheme.Modules.pushforward (i n)).obj (M n).obj,
      (Scheme.Modules.pushforward (j (n + 1))).map u =
        (e (n + 1)).hom ≫ H.obj.map (homOfLE (Nat.le_succ n)).op ≫
          (e n).inv ≫ (thickeningPushforwardComparison j hi n).inv.app (M n).obj :=
    (closedImmersion_pushforward_fullyFaithful (j (n + 1))).2 _ _ |>.2 _
  choose u hu using lifts
  have hc (n : ℕ) : IsIso ((ai n).homEquiv _ _ |>.symm (u n)) := by
    apply thickeningSystemPushforward_adjacent_isIso j hi ai J hgeom H n
      (M n).obj (M (n + 1)).obj (M n).property (M (n + 1)).property (e n) (e (n + 1))
    rw [hu n]
    simp
  let R : CoherentThickeningSystem T i :=
    ⟨fun n ↦ (M n).obj, fun n ↦ (M n).property,
      fun n ↦ @asIso _ _ _ _ ((ai n).homEquiv _ _ |>.symm (u n)) (hc n)⟩
  refine ⟨R, thickeningSystemPushforward_assemble j hi ai J R H e ?_⟩
  intro n
  rw [thickeningSystemPushforward_transition]
  change (Scheme.Modules.pushforward (j (n + 1))).map
      ((ai n).homEquiv _ _ (((ai n).homEquiv _ _).symm (u n))) ≫
      (Scheme.Modules.pushforwardComp (i n) (j (n + 1))).hom.app (M n).obj ≫
      (Scheme.Modules.pushforwardCongr (hi n)).hom.app (M n).obj ≫ (e n).hom = _
  rw [Equiv.apply_symm_apply, hu n]
  change _ ≫ (thickeningPushforwardComparison j hi n).hom.app (M n).obj ≫ (e n).hom = _
  simp

end
end AlgebraicGeometry
