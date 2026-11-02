import Langlands.AlgebraicGeometry.FiniteFlatConstantRankCompositionStatement
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.Dimension.Free

/-! # Constant native rank under finite flat composition -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open TensorProduct

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry

/-- Constant stalk rank over a finite-dimensional algebra computes scalar restriction. -/
private theorem finrank_restrictScalars_of_constant_rank
    (k B M : Type u) [Field k] [CommRing B] [Algebra k B]
    [Module.Finite k B] [AddCommGroup M] [Module B M] [Module k M]
    [IsScalarTower k B M] [Module.Finite B M] [Module.Flat B M]
    (r : ℕ) (h : ∀ p : PrimeSpectrum B, Module.rankAtStalk M p = r) :
    Module.finrank k M = r * Module.finrank k B := by
  classical
  cases subsingleton_or_nontrivial B with
  | inl hB =>
    let := hB
    let := Module.subsingleton B M
    simp only [Module.finrank_zero_of_subsingleton, Nat.mul_zero]
  | inr hB =>
    let := hB
    let : IsArtinianRing B := IsArtinianRing.of_finite k B
    -- A finite-dimensional algebra is semilocal; its constant-rank flat module is free.
    obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq B M r (fun P ↦ by
      let : Field (B ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
      have e := Module.rankAtStalk_baseChange (R := B) (M := M)
        (IsLocalRing.closedPoint (B ⧸ P.asIdeal))
      simpa using e.trans (h _))
    let : Module.Free B M := Module.Free.of_basis b
    have hb : Module.finrank B M = r := by
      simpa using Module.finrank_eq_card_basis b
    rw [← Module.finrank_mul_finrank k B M, hb, Nat.mul_comm]

/-- The scalar-restriction formula in the native ranks of spectrum maps. -/
private theorem finrank_comp_spec_over_field
    (k : Type u) [Field k] {B C : CommRingCat.{u}}
    (f : B ⟶ C) (q : CommRingCat.of k ⟶ B)
    (hf₁ : f.hom.Finite) (hf₂ : f.hom.Flat)
    (hq₁ : q.hom.Finite) (hq₂ : q.hom.Flat)
    (r : ℕ) (h : ∀ p : PrimeSpectrum B, f.hom.finrank p = r)
    (z : PrimeSpectrum k) :
    (Spec.map f ≫ Spec.map q).finrank z = r * (Spec.map q).finrank z := by
  rw [← Spec.map_comp, Scheme.Hom.finrank_SpecMap_eq_finrank (f := q ≫ f)
    (hf₁.comp hq₁) (hq₂.comp hf₂),
    Scheme.Hom.finrank_SpecMap_eq_finrank hq₁ hq₂]
  algebraize [q.hom, f.hom, (q ≫ f).hom]
  have : IsScalarTower k B C := .of_algebraMap_eq' rfl
  have : Module.Finite k C := Module.Finite.trans B C
  change ∀ p, Module.rankAtStalk (R := B) C p = r at h
  change Module.rankAtStalk (R := k) C z = r * Module.rankAtStalk (R := k) B z
  simpa only [Module.rankAtStalk_eq_finrank_of_free, Pi.natCast_apply, Nat.cast_id] using
    finrank_restrictScalars_of_constant_rank k B C r h

/-- Finite schemes over a field reduce to their affine coordinate algebras. -/
private theorem finrank_comp_over_field
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (q : Y ⟶ Spec (.of k))
    [IsFinite f] [Flat f] [IsFinite q] [Flat q]
    (r : ℕ) (h : ∀ y : Y, f.finrank y = r)
    (z : Spec (.of k)) :
    (f ≫ q).finrank z = r * q.finrank z := by
  have : IsAffine Y := isAffine_of_isAffineHom q
  have : IsAffine X := isAffine_of_isAffineHom f
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.isoSpec.inv ≫ f ≫ Y.isoSpec.hom)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (Y.isoSpec.inv ≫ q)
  have hφ₁ : φ.hom.Finite := (IsFinite.SpecMap_iff φ).mp (by rw [hφ]; infer_instance)
  have hφ₂ : φ.hom.Flat := Flat.SpecMap_iff.mp (by rw [hφ]; infer_instance)
  have hψ₁ : ψ.hom.Finite := (IsFinite.SpecMap_iff ψ).mp (by rw [hψ]; infer_instance)
  have hψ₂ : ψ.hom.Flat := Flat.SpecMap_iff.mp (by rw [hψ]; infer_instance)
  have hr : ∀ p, φ.hom.finrank p = r := by
    intro p
    rw [← Scheme.Hom.finrank_SpecMap_eq_finrank hφ₁ hφ₂, hφ,
      Scheme.Hom.finrank_comp_left_of_isIso]
    rw [Scheme.Hom.finrank_of_isPullback (𝟙 X) (f ≫ Y.isoSpec.hom) f Y.isoSpec.inv
      (IsPullback.of_horiz_isIso ⟨by simp⟩)]
    exact h _
  have e := finrank_comp_spec_over_field k φ ψ hφ₁ hφ₂ hψ₁ hψ₂ r hr z
  simpa [hφ, hψ, Category.assoc] using e

/-- Constant native ranks multiply under finite flat composition. -/
theorem finiteFlatConstantRankComposition :
    FiniteFlatConstantRankCompositionStatement.{u} := by
  intro X Y Z _ f q _ _ _ _ r s hf hq z
  -- Pull both maps back along the actual residue-field point of the target.
  let b := Z.fromSpecResidueField z
  let Y' := pullback q b
  let q' : Y' ⟶ Spec (Z.residueField z) := pullback.snd q b
  let a : Y' ⟶ Y := pullback.fst q b
  let f' := pullback.snd f a
  have hf' : ∀ y, f'.finrank y = r := by
    intro y
    rw [Scheme.Hom.finrank_pullback_snd]
    exact hf _
  have sq : IsPullback (pullback.fst f a) (f' ≫ q') (f ≫ q) b :=
    (IsPullback.of_hasPullback f a).paste_vert (IsPullback.of_hasPullback q b)
  have e := finrank_comp_over_field (Z.residueField z) f' q' r hf'
    (IsLocalRing.closedPoint (Z.residueField z))
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ sq,
    Scheme.Hom.finrank_pullback_snd] at e
  simpa [b, hq] using e

end Langlands.AlgebraicGeometry
