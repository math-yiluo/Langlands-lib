/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.ReductionKummerTranspose
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ReductionTateTwist

/-!
# The Kummer boundaries under the reduction of coefficients

Let `ρ : Λ →+* Λ'` be a surjective morphism of commutative rings of positive characteristics
`n = n' d` and `n'`, with principal kernel, and `Ψ = - ⊗ᴸ_Λ Λ'` the derived extension of scalars
(`AlgebraicGeometry.Etale.derivedExtendScalars`). For a unit `v` of a scheme `X` on which `n` is
invertible, the Kummer class `κ(v)` over `Λ` is the connecting morphism of the Kummer sequence
`0 ⟶ μₙ ⟶ 𝔾ₘ ⟶ 𝔾ₘ ⟶ 0` of level `n`, pulled back along `v : ℤ ⟶ 𝔾ₘ` and tensored with `Λ`
(`AlgebraicGeometry.Etale.kummerδ`), and similarly over `Λ'` with the level `n'`. The `d`-th
power maps form a morphism of Kummer sequences
```
0 ──▶ μₙ ──▶ 𝔾ₘ ──n──▶ 𝔾ₘ ──▶ 0
      │ d     │ d       ‖
      ▼       ▼         ‖
0 ──▶ μ_{n'} ─▶ 𝔾ₘ ──n'─▶ 𝔾ₘ ──▶ 0
```
(`AlgebraicGeometry.Scheme.kummerSequencePowMap`), hence of the pulled back sequences, and,
composed with `Λ ⊗ F ⟶ Λ' ⊗ F`, a morphism from the sequence over `Λ` to the restriction of
scalars of the sequence over `Λ'`
(`AlgebraicGeometry.Etale.kummerSequenceReductionMap`). Since `Ψ` is left adjoint to the exact
restriction of scalars, it carries the connecting morphism over `Λ` to the connecting morphism
over `Λ'`, through the transposes of the components of this morphism
(`AlgebraicGeometry.Etale.derivedExtendScalars_map_kummerδ`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace CategoryTheory.ShortComplex

variable {C : Type*} [Category* C] [Abelian C]

/-- The morphism `S.pullback φ ⟶ S'.pullback φ'` of pulled back short complexes induced by a
morphism `f : S ⟶ S'` with `φ ≫ f.τ₃ = φ'`; it is `f.τ₁` on the first terms and the identity on
the third terms. -/
@[simps]
noncomputable def pullbackMapOfHom {S S' : ShortComplex C} (f : S ⟶ S') {Y : C} (φ : Y ⟶ S.X₃)
    (φ' : Y ⟶ S'.X₃) (h : φ ≫ f.τ₃ = φ') : S.pullback φ ⟶ S'.pullback φ' where
  τ₁ := f.τ₁
  τ₂ := Limits.pullback.lift (Limits.pullback.fst _ _ ≫ f.τ₂) (Limits.pullback.snd _ _)
    (by rw [Category.assoc, f.comm₂₃, Limits.pullback.condition_assoc, h])
  τ₃ := 𝟙 Y
  comm₁₂ := by
    apply Limits.pullback.hom_ext <;> simp [ShortComplex.pullback, f.comm₁₂]
  comm₂₃ := by simp [ShortComplex.pullback]

end CategoryTheory.ShortComplex

namespace AlgebraicGeometry

namespace Scheme

variable {X : Scheme.{u}}

/-- The morphism of Kummer sequences `(μ_c ⟶ 𝔾ₘ ⟶ 𝔾ₘ) ⟶ (μ_a ⟶ 𝔾ₘ ⟶ 𝔾ₘ)`, for `c = a b`, given
by the `b`-th power maps `μ_c ⟶ μ_a` and `𝔾ₘ ⟶ 𝔾ₘ` and the identity of the last term. -/
@[simps]
noncomputable def kummerSequencePowMap (a b c : ℕ) (h : c = a * b) :
    X.kummerSequence c ⟶ X.kummerSequence a where
  τ₁ := rootsOfUnityPow a b c h
  τ₂ := b • 𝟙 X.gmSheaf
  τ₃ := 𝟙 _
  comm₁₂ := rootsOfUnityPow_ι a b c h
  comm₂₃ := by
    simp only [kummerSequence, Category.comp_id]
    rw [nsmul_id_comp_nsmul_id, h]

end Scheme

namespace Etale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')

/-- The natural map `Λ ⊗ F ⟶ Λ' ⊗ F` of étale sheaves of `Λ`-modules, from the extension of
scalars to `Λ` to the restriction of scalars of the extension of scalars to `Λ'`: the unit of
`Λ' ⊗_Λ - ⊣ Res`, followed by `Λ' ⊗_Λ (Λ ⊗ F) ≅ Λ' ⊗ F`
(`AlgebraicGeometry.Etale.extendScalarsCompSheafExtendScalarsIso`). -/
noncomputable def extendScalarsToRestrictScalars (X : Scheme.{u}) :
    extendScalars Λ X ⟶
      extendScalars Λ' X ⋙ Sheaf.restrictScalars X.smallEtaleTopology ρ :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft (extendScalars Λ X)
      (Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ).unit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (extendScalarsCompSheafExtendScalarsIso ρ X).hom
      (Sheaf.restrictScalars X.smallEtaleTopology ρ)

variable {X : Scheme.{u}} {C : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
  (φ : C ⟶ X.gmSheaf) {d : ℕ} (hd : ringChar Λ = ringChar Λ' * d)

/-- The morphism from the Kummer sequence of level `n` pulled back along `φ : C ⟶ 𝔾ₘ`, tensored
with `Λ`, to the restriction of scalars of the Kummer sequence of level `n'` pulled back along
`φ`, tensored with `Λ'`, for `n = n' d`: the `d`-th power maps followed by `Λ ⊗ - ⟶ Λ' ⊗ -`. -/
noncomputable def kummerSequenceReductionMap :
    ((X.kummerSequence (ringChar Λ)).pullback φ).map (extendScalars Λ X) ⟶
      (Sheaf.restrictScalars X.smallEtaleTopology ρ).mapShortComplex.obj
        (((X.kummerSequence (ringChar Λ')).pullback φ).map (extendScalars Λ' X)) :=
  (extendScalars Λ X).mapShortComplex.map
      (ShortComplex.pullbackMapOfHom (kummerSequencePowMap _ d _ hd) φ φ
        (Category.comp_id φ)) ≫
    ShortComplex.mapNatTrans _ (extendScalarsToRestrictScalars ρ X)

variable [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' X] {ρ}
  (hρ : Function.Surjective ρ) {a : Λ} (ha : RingHom.ker ρ = Ideal.span {a})

omit [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' X] in
/-- The adjunction `Ψ ⊣ Res` of the derived extension of scalars is the derived adjunction of the
extension and restriction of scalars of sheaves, with the exact right adjoint computed
levelwise. -/
lemma derivedExtendScalarsAdjunction_eq :
    derivedExtendScalarsAdjunction hρ ha X =
      have := preservesKFlatQuasiIso_extendScalars hρ ha X
      (Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ).derivedAdjunctionMapDerivedCategory :=
  rfl

/-- **The derived extension of scalars of a Kummer boundary is the Kummer boundary.** For
`φ : C ⟶ 𝔾ₘ` (for instance a unit `v : ℤ ⟶ 𝔾ₘ`), the derived extension of scalars
`Ψ = - ⊗ᴸ_Λ Λ'` carries the connecting morphism `Λ ⊗ C ⟶ (μₙ ⊗ Λ)[1]` of the Kummer sequence of
level `n` (`AlgebraicGeometry.Etale.kummerδ`) to the connecting morphism
`Λ' ⊗ C ⟶ (μ_{n'} ⊗ Λ')[1]` of the Kummer sequence of level `n'`, through the transposes under
`Ψ ⊣ Res` of the components `Λ ⊗ C ⟶ Res(Λ' ⊗ C)` and `μₙ ⊗ Λ ⟶ Res(μ_{n'} ⊗ Λ')` of the
morphism of Kummer sequences `AlgebraicGeometry.Etale.kummerSequenceReductionMap`. -/
theorem derivedExtendScalars_map_kummerδ
    (hC : ∀ x : X, Projective ((X.uliftPointSmallEtale x).sheafFiber.obj C)) :
    letI := derivedExtendScalarsCommShift hρ ha X
    (derivedExtendScalars hρ ha X).map (kummerδ Λ φ hC) ≫
        ((derivedExtendScalars hρ ha X).commShiftIso (1 : ℤ)).hom.app _ ≫
        (ShortComplex.ShortExact.singleTranspose (Sheaf.restrictScalars X.smallEtaleTopology ρ)
          (derivedExtendScalarsAdjunction hρ ha X)
            (kummerSequenceReductionMap ρ φ hd).τ₁)⟦(1 : ℤ)⟧' =
      ShortComplex.ShortExact.singleTranspose (Sheaf.restrictScalars X.smallEtaleTopology ρ)
          (derivedExtendScalarsAdjunction hρ ha X) (kummerSequenceReductionMap ρ φ hd).τ₃ ≫
        kummerδ Λ' φ hC := by
  let := derivedExtendScalarsCommShift hρ ha X
  have := (derivedExtendScalarsAdjunction hρ ha X).commShift_of_rightAdjoint ℤ
  exact ShortComplex.ShortExact.map_singleδ_comp_adjunction _ _ _ _ _

end Etale

end AlgebraicGeometry
