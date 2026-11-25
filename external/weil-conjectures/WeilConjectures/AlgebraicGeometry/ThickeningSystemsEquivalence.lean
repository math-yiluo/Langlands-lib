/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentThickeningSystem
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.ThickeningSystemPushforward
import WeilConjectures.AlgebraicGeometry.ThickeningSystemPushforwardAdic
import WeilConjectures.AlgebraicGeometry.ThickeningSystemPushforwardLifting
import WeilConjectures.AlgebraicGeometry.TensorPullback

/-! # Pushforward of coherent thickening systems is an equivalence with adic systems.

Source: Stacks Project, Cohomology of Schemes, Remark 088F and Lemma 087T.
(blueprint: lem-weil-pbc-thickening-systems-pushforward-equivalence).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

noncomputable section

set_option autoImplicit false

/-- Pushforward of coherent thickening systems is an equivalence with adic systems.
Source: Stacks Project, Remark 088F, Lemma 087T and equation 0880.
(blueprint: lem-weil-pbc-thickening-systems-pushforward-equivalence).

Proof:
1. The projection j_n is a closed immersion with kernel J^(n+1) by hgeom, where
   J = I O_X. Since X is Noetherian, X_n is Noetherian. The two identities hi and hi₂
   identify i_n with the canonical nested-quotient immersion by uniqueness of maps to
   a pullback (quotientBaseChange_nestedIdeals). Its ideal is J^(n+1).comap j_(n+1).
2. For a system M, put G_n = j_(n,*) M.term n. Closed-immersion coherent equivalence
   says G_n is coherent and annihilated by J^(n+1). The adjoint of comparison n is
   t'_n : M.term (n+1) → i_(n,*) M.term n. Push it along j_(n+1),* and compose with
   pushforwardComp and pushforwardCongr hi to define t_n : G_(n+1) → G_n.
   The closed-immersion unit-quotient theorem identifies t'_n with the quotient by
   (J.comap j_(n+1))^(n+1), followed by an isomorphism. The pushforward ideal-power
   theorem identifies the induced quotient G_(n+1)/J^(n+1)G_(n+1) with G_n.
   Hence these terms and transitions define a coherent formal module. Adjoints of
   composites satisfy the required compatibility by naturality of the adjunction;
   applying j_(n,*) to each component defines the functor on compatible families.
   The inverse-system functor laws follow from functoriality of pushforward.
   Its evaluation comparisons β are the defining termwise identifications.
3. For a map of pushed inverse systems, fully faithful j_(n,*) gives a unique map
   u_n between terms. The inverse-system transition equation, faithfulness of
   j_(n+1),*, and the adjunction homEquiv identify this equation with precisely
   the comparison compatibility for u_n. Thus the constructed functor is full and
   faithful. Conversely compatible u_n give compatible pushed maps by the same
   equation, so this argument proves both directions, naturally in the objects.
4. Given a coherent formal module H, each H_n is annihilated by J^(n+1).
   Closed-immersion coherent equivalence for j_n supplies a coherent term M_n and
   an isomorphism j_(n,*) M_n ≅ H_n. Conjugate the transitions by these isomorphisms
   and uniquely lift them through fully faithful j_(n+1),*, using pushforwardComp
   and hi. Take their adjoints along i_n to obtain maps i_n^* M_(n+1) → M_n.
   The unit-quotient theorem and pushforward ideal-power comparison identify their
   pushforwards with the quotient transition isomorphisms of H. Full faithfulness
   reflects isomorphisms, so these adjoints are isomorphisms. Thus M is a coherent
   thickening system and the chosen termwise isomorphisms assemble into Φ M ≅ H.
   Full faithfulness and essential surjectivity prove Φ.IsEquivalence.
5. The calculation of the transitions in step 2 is the displayed β equation.
   The unit-quotient theorem is stated for a chosen adjunction. For the supplied ai,
   transport it along the unique comparison between left adjoints to the same
   pushforward; its unit identity identifies the transported quotient with ai.unit.
   This only changes the quotient identification by an isomorphism, preserving all
   the quotient and reflection arguments. No completeness or separatedness is used.
-/
theorem thickeningSystems_pushforward_equivalence {A : Type v} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{v}} (f : X ⟶ Spec (CommRingCat.of A))
    [LocallyOfFiniteType f] [QuasiCompact f] (I : Ideal A)
    (i : ∀ n : ℕ, pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) ⟶
        pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))
    (hi : ∀ n : ℕ,
      i n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))) =
          pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
    (hi₂ : ∀ n : ℕ,
      i n ≫ pullback.snd f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))) =
      pullback.snd f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) ≫
          Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := I) (Nat.le_succ (n + 1))))))
    (ai : ∀ n : ℕ, Scheme.Modules.tensorPullback (i n) ⊣ Scheme.Modules.pushforward (i n))
    (aj : ∀ n : ℕ, Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1)))))) ⊣
      Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (I ^ (n + 1)))))))
    [hX : IsNoetherian X]
    (hgeom : (∀ n : ℕ, IsClosedImmersion (pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (I ^ (n + 1)))))) ∧
        (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))).ker =
            (Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso (CommRingCat.of
            A)).inv.hom)).comap f ^ (n + 1))) :
    ∃ (Φ : CoherentThickeningSystem (fun n ↦ pullback f (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (I ^ (n + 1)))))) i ⥤
          @CoherentFormalModule X hX ((Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso
              (CommRingCat.of A)).inv.hom)).comap f))
        (β : ∀ n : ℕ,
          Φ ⋙ ObjectProperty.ι (IsCoherentFormalModule ((Scheme.IdealSheafData.ofIdealTop (I.map
              (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)) ⋙
            (CategoryTheory.evaluation ℕᵒᵖ X.Modules).obj (op n) ≅
          CoherentThickeningSystem.evaluation (fun n ↦ pullback f (Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk (I ^ (n + 1)))))) i n ⋙
            Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1))))))),
        Φ.IsEquivalence ∧
        (∀ (M : CoherentThickeningSystem (fun n ↦ pullback f (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (I ^ (n + 1)))))) i) (n : ℕ),
          (((Φ.obj M).obj).map (homOfLE (Nat.le_succ n)).op) ≫ (β n).hom.app M =
          (β (n + 1)).hom.app M ≫
            (Scheme.Modules.pushforward (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).map
              ((ai n).homEquiv _ _ (M.comparison n).hom) ≫
            (Scheme.Modules.pushforwardComp (i n) (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))).hom.app
              (M.term n) ≫
            (Scheme.Modules.pushforwardCongr (hi n)).hom.app (M.term n)) := by
  have _hsecondProjection := hi₂
  have _hpushforwardAdjunction := aj
  let T : ℕ → Scheme.{v} := fun n ↦ pullback f (Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (I ^ (n + 1)))))
  let j : ∀ n, T n ⟶ X := fun n ↦ pullback.fst f (Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (I ^ (n + 1)))))
  let J := (Scheme.IdealSheafData.ofIdealTop (I.map
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f
  have : ∀ n, IsClosedImmersion (j n) := fun n ↦ (hgeom n).1
  let P := thickeningSystemPushforward j hi ai
  have hP := thickeningSystemPushforward_fullyFaithful j hi ai
  have : P.Full := hP.1
  have : P.Faithful := hP.2
  let Φ : CoherentThickeningSystem T i ⥤ CoherentFormalModule X J :=
    ObjectProperty.lift (IsCoherentFormalModule J) P
      (thickeningSystemPushforward_isAdic j hi ai J hgeom)
  have : Φ.EssSurj := ⟨fun H ↦ by
    obtain ⟨M, ⟨e⟩⟩ := thickeningSystemPushforward_lifting j hi ai J hgeom H
    exact ⟨M, ⟨ObjectProperty.isoMk _ e⟩⟩⟩
  have : Φ.IsEquivalence := {}
  let β := fun n ↦ thickeningSystemPushforwardEvaluation j hi ai n
  refine ⟨Φ, β, inferInstance, ?_⟩
  intro M n
  change ((thickeningSystemPushforward j hi ai).obj M).map
    (homOfLE (Nat.le_succ n)).op ≫ 𝟙 _ = 𝟙 _ ≫ _
  rw [Category.comp_id, Category.id_comp]
  exact thickeningSystemPushforward_transition j hi ai M n

end
end AlgebraicGeometry
