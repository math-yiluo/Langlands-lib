/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.RingTheory.AdicCompletion.Algebra
import WeilConjectures.AlgebraicGeometry.FiniteEtaleLiftingComplete
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Lifting to the adic completion

Source: Stacks Project, Tag 0GS2, proof.
(blueprint: lem-weil-pbc-finite-etale-completion-lift).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Lift a closed-fibre finite étale cover to the base change over the adic completion.
Source: Stacks Project, Tag 0GS2, proof, lines 1815–1820
(blueprint: lem-weil-pbc-finite-etale-completion-lift).

Proof: Let B be the I-adic completion and J the extension of I to B. Since A is
Noetherian, I is finitely generated. B is Noetherian and J-adically complete, and
B/J is canonically A/I, compatibly with the maps from A. Properness is stable under
base change. Pasting the base-change square with Spec(B/J) identifies the closed
fibre of Y_B with Y_0. Transport V along that isomorphism and apply the complete
Noetherian lifting theorem to Y_B over B. Pull back the resulting finite étale cover
along the identification of closed fibres. The resulting morphism j is induced by
B → A/I; the two projection identities follow from the pullback construction. The
isomorphism over Y_0 follows from the lifted closed-fibre isomorphism and pasting.
The argument also applies when I is the unit ideal: both closed fibres are empty. -/
theorem exists_finiteEtale_completion_lift
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f]
    (V : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤
      (pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) :
    ∃ (U : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤
        (pullback f (Spec.map (CommRingCat.ofHom
          (algebraMap A (AdicCompletion I A))))))
      (j : pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ⟶
        pullback f (Spec.map (CommRingCat.ofHom
          (algebraMap A (AdicCompletion I A))))),
      j ≫ pullback.fst _ _ = pullback.fst _ _ ∧
      j ≫ pullback.snd _ _ = pullback.snd _ _ ≫
        Spec.map (CommRingCat.ofHom (AdicCompletion.evalOneₐ I).toRingHom) ∧
      Nonempty (Over.mk (pullback.snd U.hom j) ≅ Over.mk V.hom) := by
  let B := AdicCompletion I A
  let p : B →+* A ⧸ I := (AdicCompletion.evalOneₐ I).toRingHom
  let J : Ideal B := RingHom.ker p
  have hJ : J = I.map (algebraMap A B) :=
    AdicCompletion.ker_evalOneₐ_eq_map I (IsNoetherian.noetherian I)
  have : IsNoetherianRing B := AdicCompletion.isNoetherianRing I
  have : IsAdicComplete J B := by
    rw [hJ]
    exact AdicCompletion.isAdicComplete_self I (IsNoetherian.noetherian I)
  let e : B ⧸ J ≃+* A ⧸ I := p.quotientKerEquivOfSurjective
    (AdicCompletion.evalOneₐ_surjective I)
  let a := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  let s := Spec.map (CommRingCat.ofHom e.toRingHom)
  have : IsIso s := by
    change IsIso (Scheme.Spec.map e.toCommRingCatIso.hom.op)
    infer_instance
  have hq : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = s ≫ q ≫ a := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  let t₀ := pullback.map f
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) f (q ≫ a)
    (𝟙 Y) s (𝟙 _) (by simp) (by simpa [Category.assoc] using hq)
  let t := asIso t₀ ≪≫ (pullbackLeftPullbackSndIso f a q).symm
  let j := t.hom ≫ pullback.fst (pullback.snd f a) q
  have hjfst : j ≫ pullback.fst f a = pullback.fst f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) := by
    simp [j, t, t₀]
  have hjsnd : j ≫ pullback.snd f a = pullback.snd f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≫
        Spec.map (CommRingCat.ofHom p) := by
    simp only [j, t, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      pullbackLeftPullbackSndIso_inv_fst_snd]
    simp only [t₀, asIso_hom, pullback.map, pullback.lift_snd_assoc]
    rw [Category.assoc]
    dsimp only [s, q]
    rw [← Spec.map_comp]
    rfl
  have : IsFinite V.hom := V.prop.1
  have : Etale V.hom := V.prop.2
  let V' : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤
      (pullback (pullback.snd f a) q) := MorphismProperty.Over.mk _ (V.hom ≫ t.hom)
    (show IsFinite (V.hom ≫ t.hom) ∧ Etale (V.hom ≫ t.hom) from
      ⟨inferInstance, inferInstance⟩)
  obtain ⟨U, ⟨eU⟩⟩ := exists_finiteEtale_lift_of_isAdicComplete J (pullback.snd f a) V'
  refine ⟨U, j, hjfst, hjsnd, ?_⟩
  have eV : (Over.pullback t.hom).obj (Over.mk (V.hom ≫ t.hom)) ≅
      Over.mk V.hom := Over.isoMk (asIso (pullback.fst (V.hom ≫ t.hom) t.hom))
        (by simp [← cancel_mono t.hom, pullback.condition])
  exact ⟨(Over.pullbackComp t.hom (pullback.fst (pullback.snd f a) q)).app
    (Over.mk U.hom) ≪≫ (Over.pullback t.hom).mapIso eU ≪≫ eV⟩

end AlgebraicGeometry.Scheme
