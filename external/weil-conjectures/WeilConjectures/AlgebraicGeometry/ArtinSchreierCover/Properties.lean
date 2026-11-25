/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ArtinSchreierCover.Centralizer

/-! # Properties of the Artin–Schreier cover

All properties of the Artin–Schreier cover `adjoinRootCover S (T ^ p - T - f)`: it is a finite
étale cover of degree `p`, a torsor under `𝔽_p` acting by translations, and its automorphisms
commuting with the translations are the locally constant functions `S → 𝔽_p`.
Source: blueprint, lemma-artin-schreier-character-sheaf.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Polynomial

noncomputable section

namespace AlgebraicGeometry

variable {p : ℕ} [Fact p.Prime] {S : Scheme.{u}} {f : Γ(S, ⊤)} {P : Polynomial Γ(S, ⊤)}

/-- The translations of the Artin–Schreier cover are pairwise distinct when `S` is
nonempty. -/
lemma injective_artinSchreierAction (hP : P = X ^ p - X - C f) (hchar : (p : Γ(S, ⊤)) = 0)
    [Nonempty S] : Function.Injective (artinSchreierAction hP hchar) := by
  obtain ⟨x⟩ : Nonempty S := inferInstance
  obtain ⟨y₀, -⟩ := (surjective_adjoinRootCover_artinSchreier hP hchar).surj x
  intro a b h
  have h' : 𝟙 _ ≫ (artinSchreierEtaleTorsor hP hchar).vadd (ULift.up a.toAdd) =
      𝟙 _ ≫ (artinSchreierEtaleTorsor hP hchar).vadd (ULift.up b.toAdd) := by
    rw [Category.id_comp, Category.id_comp]
    exact congr_arg (fun g : Aut (adjoinRootCover S P) ↦ g.asIso.hom.left) h
  exact congr_arg ULift.down ((artinSchreierEtaleTorsor hP hchar).eq_of_comp_vadd_eq _ h' y₀)

/-- **Properties of the Artin–Schreier cover** (blueprint: lemma-artin-schreier-character-sheaf),
for the cover `adjoinRootCover S P` of a polynomial `P = T ^ p - T - f` over a scheme `S` on which
`p = 0`. -/
theorem adjoinRootCover_artinSchreier_properties (hP : P = X ^ p - X - C f)
    (hchar : (p : Γ(S, ⊤)) = 0) :
    IsFinite (adjoinRootCover S P).hom ∧
    Etale (adjoinRootCover S P).hom ∧
    (adjoinRootCover S P).hom.IsFiniteLocallyFreeOfDegree p ∧
    ∃ σ : Multiplicative (ZMod p) →* Aut (adjoinRootCover S P),
      (∀ a : ZMod p, (σ (Multiplicative.ofAdd a)).asIso.hom.left.appTop
          (adjoinRootCoverRoot S P) =
        adjoinRootCoverRoot S P + (a.val : Γ((adjoinRootCover S P).left, ⊤))) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ S),
        Nonempty {s : Spec (.of Ω) ⟶ (adjoinRootCover S P).left //
          s ≫ (adjoinRootCover S P).hom = x} ∧
        ∀ s t : {s : Spec (.of Ω) ⟶ (adjoinRootCover S P).left //
          s ≫ (adjoinRootCover S P).hom = x},
          ∃! a : ZMod p, t.val = s.val ≫ (σ (Multiplicative.ofAdd a)).asIso.hom.left) ∧
      (∃ (R : Sheaf.Torsor
          ((constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod p)))))
          (e : R.sheaf.obj ≅ (Scheme.Etale.forget S).op ⋙
            yoneda.obj (adjoinRootCover S P) ⋙ uliftFunctor.{u + 1}),
        ∀ (U : S.Etale) (a : ZMod p) (s : R.sheaf.obj.obj (Opposite.op U)),
          (e.hom.app (Opposite.op U)
            (R.vadd (Opposite.op U)
              (((toSheafify S.smallEtaleTopology
                ((Functor.const S.Etaleᵒᵖ).obj
                  (AddCommGrpCat.of (ULift.{u + 1} (ZMod p))))).app
                    (Opposite.op U)) (ULift.up a)) s)).down =
            (e.hom.app (Opposite.op U) s).down ≫ (σ (Multiplicative.ofAdd a)).asIso.hom) ∧
      (Nonempty S → Function.Injective σ) ∧
      (∃ E : Multiplicative (LocallyConstant S (ZMod p)) ≃*
          Subgroup.centralizer (Set.range σ),
        ∀ (b : LocallyConstant S (ZMod p)) (a : ZMod p) (U : S.Opens),
          (∀ x : U, b x = a) →
          ((adjoinRootCover S P).hom ⁻¹ᵁ U).ι ≫
              (E (Multiplicative.ofAdd b)).val.asIso.hom.left =
            ((adjoinRootCover S P).hom ⁻¹ᵁ U).ι ≫
              (σ (Multiplicative.ofAdd a)).asIso.hom.left) ∧
      (ConnectedSpace (adjoinRootCover S P).left → Function.Bijective σ) ∧
      (IsEmpty S → IsEmpty (adjoinRootCover S P).left ∧
        Subsingleton (Aut (adjoinRootCover S P))) := by
  refine ⟨isFinite_artinSchreier hP, etale_artinSchreier hP hchar,
    isFiniteLocallyFreeOfDegree_artinSchreier hP, artinSchreierAction hP hchar,
    fun a ↦ artinSchreierTranslation_appTop_root hP hchar a,
    fun Ω _ _ x ↦ artinSchreier_geometricPoints hP hchar Ω x, artinSchreier_sheafTorsor hP hchar,
    fun _ ↦ injective_artinSchreierAction hP hchar,
    ArtinSchreierCover.artinSchreier_centralizer hP hchar,
    fun _ ↦ ArtinSchreierCover.bijective_artinSchreierAction hP hchar, fun hS ↦ ?_⟩
  have hY : IsEmpty (adjoinRootCover S P).left :=
    ⟨fun y ↦ hS.false ((adjoinRootCover S P).hom y)⟩
  refine ⟨hY, ⟨fun g h ↦ ?_⟩⟩
  apply Aut.ext
  ext : 1
  exact Over.OverMorphism.ext (isInitialOfIsEmpty.hom_ext _ _)

end AlgebraicGeometry
