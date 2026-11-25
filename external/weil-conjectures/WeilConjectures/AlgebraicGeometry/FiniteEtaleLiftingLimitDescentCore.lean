/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.FiniteEtaleHenselianGRingStage
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The limit-descent construction produces a lift together with the canonical identity
isomorphism of the proper base.  The latter records the compatibility datum used in the
limit argument.
Source: Stacks Project, Lemma 0GS2, proof, General case.
(blueprint: lem-weil-pbc-finite-etale-lifting-limit-descent-core). -/
theorem exists_finiteEtale_lift_of_henselianPair_of_gRing_lifting_core
    (H : ∀ (B : Type u) [CommRing B], IsGRing B →
      ∀ (J : Ideal B) [HenselianRing B J] (Z : Scheme.{u})
        (g : Z ⟶ Spec (.of B)) [IsProper g]
        (W : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤
          (pullback g (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))),
        ∃ U' : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Z,
          Nonempty
            (Over.mk (pullback.snd U'.hom
              (pullback.fst g (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))) ≅
              Over.mk W.hom))
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f]
    (V : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤
      (pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) :
    ∃ U : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y,
      Nonempty
        (Over.mk (pullback.snd U.hom
          (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) ≅
          Over.mk V.hom) ∧ Nonempty (Y ≅ Y) := by
  obtain ⟨B, hB, hGR, J, hJ, Z, g, hg, s, k, W, hsk, ⟨e⟩⟩ :=
    exists_finiteEtale_henselian_gRing_stage I f V
  let : CommRing B := hB
  let : HenselianRing B J := hJ
  let : IsProper g := hg
  obtain ⟨T, ⟨eT⟩⟩ := H B hGR J Z g W
  have : IsFinite T.hom := T.prop.1
  have : Etale T.hom := T.prop.2
  let qA := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let qB := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  let jA := pullback.fst f qA
  let jB := pullback.fst g qB
  let U : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y :=
    MorphismProperty.Over.mk ⊤ (pullback.snd T.hom s) ⟨inferInstance, inferInstance⟩
  refine ⟨U, ⟨?_⟩, ⟨Iso.refl Y⟩⟩
  let a := pullbackLeftPullbackSndIso T.hom s jA
  let d : pullback T.hom (jA ≫ s) ≅ pullback T.hom (k ≫ jB) :=
    pullback.congrHom rfl hsk
  let b := pullbackLeftPullbackSndIso T.hom jB k
  have ea : Over.mk (pullback.snd U.hom jA) ≅
      Over.mk (pullback.snd (pullback.snd T.hom jB) k) :=
    Over.isoMk (a ≪≫ d ≪≫ b.symm) (by
      dsimp [a, d, b]
      simp [U, jA, jB, qA, qB]
      rfl)
  exact ea ≪≫ (Over.pullback k).mapIso eT ≪≫ e

end AlgebraicGeometry.Scheme
