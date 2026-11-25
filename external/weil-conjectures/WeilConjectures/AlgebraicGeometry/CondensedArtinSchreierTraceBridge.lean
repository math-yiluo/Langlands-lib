/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.CondensedArtinSchreierCharacters
import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.ArtinSchreierTraceComparison
import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.CondensedArtinSchreierTraceTensorInverse
import WeilConjectures.CategoryTheory.RingObjects.Condensed.PadicAlgClGlobalSections
import WeilConjectures.Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-! Comparison data reducing an arbitrary finite-field character to a trace character.

Source: current blueprint, sec-fourier-transform/sk-lem-as-properties/lem-fd-as-lisse.md
(blueprint: lemma-artin-schreier-character-sheaf--2).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

attribute [local instance] ZMod.algebra

namespace AlgebraicGeometry.ProEtale

open AlgebraicGeometry.ArtinSchreierTrace

attribute [local irreducible] CondensedRing.upperStar CondensedRing.upperStarComp
  CondensedRing.lowerStarComp CondensedRing.upperStarLowerStarAdjunction

/-- The morphism to the affine line defined by `c f` is that defined by `f` followed by the
scaling `[c]`. -/
private theorem homOfVector_comp_artinSchreierScaling (k : Type u) [Field k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] (c : k) (f : Γ(X, ⊤)) :
    AffineSpace.homOfVector (X ↘ Spec (.of k)) (fun _ : PUnit.{u + 1} ↦ f) ≫
        Etale.artinSchreierScaling k c =
      AffineSpace.homOfVector (X ↘ Spec (.of k)) (fun _ : PUnit.{u + 1} ↦ scalar k X c * f) := by
  refine AffineSpace.hom_ext (by simp) fun _ ↦ ?_
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    Etale.artinSchreierScaling_appTop_coord, map_mul, AffineSpace.homOfVector_appTop_coord]
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, AffineSpace.homOfVector_over,
    scalar]

/-- The condensed Artin–Schreier sheaf of a shifted character `ψ(c ·)`, `c ∈ kˣ`, at a
function `f` is that of `ψ` at `c f`: `L_{ψ(c ·), f} ≅ L_{ψ, c f}`.
Source: blueprint lemma-artin-schreier-character-sheaf (2) (blueprint:
lemma-artin-schreier-character-sheaf--2).

Proof: pullback along the scaling `[c]` carries `L_ψ` to `L_{ψ(c ·)}`, and the composite of
the morphism defined by `f` with `[c]` is the morphism defined by `c f`. -/
theorem condensedArtinSchreierSheafOf_mulShift
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (k : Type u) [Field k] [Fintype k] (ψ : AddChar k (MonObj.Γ Λ)) (c : kˣ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))] (f : Γ(X, ⊤)) :
    Nonempty (condensedArtinSchreierSheafOf Λ k X (ψ.mulShift c) f ≅
      condensedArtinSchreierSheafOf Λ k X ψ (scalar k X c * f)) := by
  obtain ⟨e⟩ := nonempty_iso_upperStar_scaling_condensedArtinSchreierSheaf Λ k c ψ
  rw [condensedArtinSchreierSheafOf, condensedArtinSchreierSheafOf,
    ← homOfVector_comp_artinSchreierScaling]
  exact ⟨(CondensedRing.upperStar Λ _).mapIso e.symm ≪≫
    (CondensedRing.upperStarComp Λ _ _).symm.app _⟩

/-! The comparison is deliberately only comparison data.  The lisse and tensor
clauses are obtained from the qlbar trace statements after this bridge. -/
/-- Every nontrivial condensed character is compared with one qlbar trace character.

Proof source: lemma-artin-schreier-character-sheaf (1)--(2).  Choose a nontrivial character
`Ψ` of `ZMod (ringChar k₀)` with values in `PadicAlgCl ℓ`, apply the character
classification to its constant global-section character, and use the unique
nonzero shift `a`.  The second part of lemma-artin-schreier-character-sheaf transports the
degree-cardinality projector to the prime-degree trace projector.  The same
comparison is natural in the function and for the inverse character.  This
statement records precisely that transport data; it does not include any
lissity, tensor, or inverse conclusion.
(blueprint: lemma-artin-schreier-character-sheaf--2). -/
theorem condensedArtinSchreier_trace_bridge
    (k₀ : Type u) [Field k₀] [Fintype k₀] (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k₀).Prime] [Fact (ringChar k₀ ≠ ℓ)]
    [Algebra (ZMod (ringChar k₀)) k₀] (X₀ : Scheme.{u})
    [X₀.Over (Spec (.of k₀))]
    (ψ : AddChar k₀ (MonObj.Γ (Profinite.padicAlgClRingObj.{u} ℓ)))
    (hψ : ψ ≠ 1) :
    ∃ (Ψ : AddChar (ZMod (ringChar k₀)) (PadicAlgCl ℓ)),
      ∃ (a : k₀ˣ),
        (Ψ ≠ 1) ∧
        (ψ = ((qlbarCharacter ℓ Ψ).compTrace k₀).mulShift (a : k₀)) ∧
      (∀ h : Γ(X₀, ⊤),
        Nonempty (condensedArtinSchreierSheafOf
            (Profinite.padicAlgClRingObj ℓ) k₀ X₀ ψ h ≅
          qlbarTraceSheafOf (ringChar k₀) ℓ k₀ Ψ X₀
            (scalar k₀ X₀ (a : k₀) * h))) ∧
      (∀ h : Γ(X₀, ⊤),
        Nonempty (condensedArtinSchreierSheafOf
            (Profinite.padicAlgClRingObj ℓ) k₀ X₀ ψ⁻¹ h ≅
          qlbarTraceSheafOf (ringChar k₀) ℓ k₀ Ψ⁻¹ X₀
            (scalar k₀ X₀ (a : k₀) * h))) := by
  classical
  let cH := Profinite.PadicAlgCl.constRingHom.{u} ℓ
  let : Nontrivial (MonObj.Γ (Profinite.padicAlgClRingObj.{u} ℓ)) :=
    ⟨⟨1, 0, fun h ↦ Profinite.PadicAlgCl.one_ne_zero_end_regular ℓ
      (by rw [← map_one Mod.regularEndRingHom, h, map_zero])⟩⟩
  let eΓ : PadicAlgCl ℓ ≃+* MonObj.Γ (Profinite.padicAlgClRingObj.{u} ℓ) :=
    RingEquiv.ofBijective cH ⟨cH.injective, Profinite.PadicAlgCl.constRingHom_surjective ℓ⟩
  have hchar : ringChar (PadicAlgCl ℓ) ≠ ringChar (ZMod (ringChar k₀)) := by
    rw [ringChar.eq_zero, ZMod.ringChar_zmod_n]
    exact (Fact.out : (ringChar k₀).Prime).ne_zero.symm
  obtain ⟨Ψ, hΨ⟩ := AddChar.exists_ne_one_of_isAlgClosed (ZMod (ringChar k₀)) (PadicAlgCl ℓ) hchar
  obtain ⟨a, ha⟩ := AddChar.exists_mulShift_eq_of_isPrimitive
    (AddChar.isPrimitive_compTrace (L := k₀) hΨ)
    ((eΓ.symm : MonObj.Γ (Profinite.padicAlgClRingObj.{u} ℓ) →* PadicAlgCl ℓ).compAddChar ψ)
  have hψa : ψ = ((qlbarCharacter ℓ Ψ).compTrace k₀).mulShift a := by
    ext x : 1
    have hx := DFunLike.congr_fun ha x
    simp only [AddChar.mulShift_apply, AddChar.compTrace_apply,
      MonoidHom.compAddChar_apply, Function.comp_apply] at hx ⊢
    rw [hx]
    exact (eΓ.apply_symm_apply (ψ x)).symm
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hψ (by rw [hψa, AddChar.mulShift_zero])
  have hinv : ψ⁻¹ = ((qlbarCharacter ℓ Ψ⁻¹).compTrace k₀).mulShift a := by
    rw [hψa]
    ext x : 1
    simp [qlbarCharacter, AddChar.compTrace_apply, AddChar.inv_apply, AddChar.mulShift_apply]
  refine ⟨Ψ, Units.mk0 a ha0, hΨ, hψa, fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [hψa]
    exact condensedArtinSchreierSheafOf_mulShift _ k₀ _ (Units.mk0 a ha0) X₀ h
  · rw [hinv]
    exact condensedArtinSchreierSheafOf_mulShift _ k₀ _ (Units.mk0 a ha0) X₀ h

end AlgebraicGeometry.ProEtale
