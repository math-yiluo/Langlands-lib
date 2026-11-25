/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor
public import WeilConjectures.EtaleCohomology.TateTwist.KummerClass

/-!
# The affine-line datum

For a scheme `Y`, the affine line `𝔸¹_Y = 𝔸¹_ℤ ×_ℤ Y` has the projection `p : 𝔸¹_Y ⟶ Y`, the zero
section `s : Y ⟶ 𝔸¹_Y` cut out by the coordinate `t`, and the open complement
`j : 𝔾_{m,Y} = 𝔸¹_Y ∖ s(Y) ⟶ 𝔸¹_Y` of the zero section, the basic open of `t`
(`AlgebraicGeometry.Etale.multiplicativeGroup`), on which `t` is a unit
(`AlgebraicGeometry.Etale.multiplicativeGroupCoord`).

For a finite coefficient ring `Λ` of characteristic `n = ℓ^N` invertible on `Y`, the *Kummer class*
of `t` is `κ(t) ∈ H¹(𝔾_{m,Y}, Λ(1))` (`AlgebraicGeometry.Etale.affineLineKummerClass`): the boundary
of `t` in the Kummer sequence `0 ⟶ μₙ ⟶ 𝔾ₘ ⟶ 𝔾ₘ ⟶ 0`, with coefficients extended to `Λ`
(`AlgebraicGeometry.Etale.kummerClassOf`). In torsor form, the `n`-th root of `t` defines the
Kummer cover `𝒯_t = Spec 𝒪[T₀]/(T₀ⁿ - t) ⟶ 𝔾_{m,Y}` (`AlgebraicGeometry.Scheme.kummerCover`),
which is finite étale (`AlgebraicGeometry.Etale.affineLineKummerCover`) of degree `n`
(`AlgebraicGeometry.Etale.finrank_affineLineKummerAlgebra`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Y : Scheme.{u})

/-- The multiplicative group `𝔾_{m,Y} = 𝔸¹_Y ∖ s(Y)`, the open subscheme of the affine line on
which the coordinate `t` is invertible. -/
noncomputable abbrev multiplicativeGroup : (𝔸(ULift.{u} (Fin 1); Y)).Opens :=
  (𝔸(ULift.{u} (Fin 1); Y)).basicOpen (AffineSpace.coord Y 0)

/-- `𝔾_{m,Y}` is the complement of the zero section `s : Y ⟶ 𝔸¹_Y`. -/
lemma coe_multiplicativeGroup :
    (multiplicativeGroup Y : Set 𝔸(ULift.{u} (Fin 1); Y)) =
      (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y).base)ᶜ := by
  ext y
  have := congr(y ∈ $(AffineSpace.range_zeroSection (ULift.{u} (Fin 1)) Y))
  simp only [Set.mem_ofPred_eq] at this
  rw [Set.mem_compl_iff, this]
  simp only [SetLike.mem_coe, not_forall, not_not]
  exact ⟨fun h ↦ ⟨0, h⟩, fun ⟨i, h⟩ ↦ by rwa [Subsingleton.elim i 0] at h⟩

/-- The global coordinate `t` of `𝔸¹_Y`, as a global unit of `𝔾_{m,Y}`. -/
noncomputable def multiplicativeGroupCoord : Γ((multiplicativeGroup Y).toScheme, ⊤)ˣ :=
  (𝔸(ULift.{u} (Fin 1); Y)).basicOpenUnit (AffineSpace.coord Y 0)

variable (Λ : Type (u + 1)) [CommRing Λ] [HasInvertibleExponent Λ Y] [NeZero (ringChar Λ)]

instance : HasInvertibleExponent Λ (multiplicativeGroup Y).toScheme :=
  .of_hom ((multiplicativeGroup Y).ι ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)

/-- Blueprint `def-pur-affine-line-datum`: The affine-line datum

The *Kummer class of the coordinate* `κ(t) ∈ H¹(𝔾_{m,Y}, Λ(1)) = Hom(Λ, Λ(1)[1])`: the boundary of
the global unit `t ∈ Γ(𝔾_{m,Y}, 𝔾ₘ)` (`AlgebraicGeometry.Etale.multiplicativeGroupCoord`) in the
Kummer sequence `0 ⟶ μ_{ℓ^N} ⟶ 𝔾ₘ ⟶ 𝔾ₘ ⟶ 0` on `𝔾_{m,Y}`, `ℓ^N` being the characteristic of `Λ`,
followed by the extension of coefficients `μ_{ℓ^N} ⟶ μ_{ℓ^N} ⊗ Λ = Λ(1)`
(`AlgebraicGeometry.Etale.kummerClassOf`). -/
noncomputable def affineLineKummerClass :
    constantComplex Λ (multiplicativeGroup Y).toScheme ⟶
      (tateTwistObject Λ (multiplicativeGroup Y).toScheme 1)⟦(1 : ℤ)⟧ :=
  kummerClassOf (multiplicativeGroup Y).toScheme Λ (multiplicativeGroupCoord Y)

omit [NeZero (ringChar Λ)] in
/-- `ringChar Λ` is a unit on `𝔾_{m,Y}`. -/
lemma isUnit_ringChar_multiplicativeGroup :
    IsUnit ((ringChar Λ : ℕ) : Γ((multiplicativeGroup Y).toScheme, ⊤)) := by
  obtain ⟨n, hn, hΛ, hu⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ)
    (X := (multiplicativeGroup Y).toScheme)
  obtain ⟨m, rfl⟩ := (ringChar.spec Λ n).1 hΛ
  rw [Nat.cast_mul] at hu
  exact isUnit_of_mul_isUnit_left hu

/-- Blueprint `def-pur-affine-line-datum`: The affine-line datum

The torsor form of `κ(t)`: the `ℓ^N`-th root of the coordinate defines the Kummer cover
`𝒯_t = Spec 𝒪_{𝔾_{m,Y}}[T₀]/(T₀^{ℓ^N} - t) ⟶ 𝔾_{m,Y}`, a finite étale `𝔾_{m,Y}`-scheme: the
quotient is finite free, `T₀` is a unit and `ℓ^N T₀^{ℓ^N - 1}` is invertible. Multiplication of
`T₀` by `ℓ^N`-th roots of unity makes it a `μ_{ℓ^N}`-torsor
(`AlgebraicGeometry.Scheme.EtaleTorsor.kummer`). -/
noncomputable def affineLineKummerCover : (multiplicativeGroup Y).toScheme.FiniteEtale :=
  kummerFiniteEtale (n := ringChar Λ) (f := (multiplicativeGroupCoord Y : _))
    (isUnit_ringChar_multiplicativeGroup Y Λ) (Units.isUnit _)

omit [HasInvertibleExponent Λ Y] in
/-- Blueprint `def-pur-affine-line-datum`: The affine-line datum

The Kummer cover `𝒯_t ⟶ 𝔾_{m,Y}` has degree `ℓ^N`: its algebra `Γ(𝔾_{m,Y})[T₀]/(T₀^{ℓ^N} - t)` is
free of rank `ℓ^N` over `Γ(𝔾_{m,Y})`, with basis `1, T₀, …, T₀^{ℓ^N - 1}`. -/
theorem finrank_affineLineKummerAlgebra [Nontrivial Γ((multiplicativeGroup Y).toScheme, ⊤)] :
    Module.Free Γ((multiplicativeGroup Y).toScheme, ⊤)
        (KummerAlgebra (multiplicativeGroup Y).toScheme (ringChar Λ)
          (multiplicativeGroupCoord Y : _)) ∧
      Module.finrank Γ((multiplicativeGroup Y).toScheme, ⊤)
        (KummerAlgebra (multiplicativeGroup Y).toScheme (ringChar Λ)
          (multiplicativeGroupCoord Y : _)) = ringChar Λ := by
  have hm := Polynomial.monic_X_pow_sub_C (multiplicativeGroupCoord Y :
    Γ((multiplicativeGroup Y).toScheme, ⊤)) (NeZero.ne (ringChar Λ))
  refine ⟨hm.free_adjoinRoot, ?_⟩
  rw [Module.finrank_eq_card_basis (AdjoinRoot.powerBasis' hm).basis, Fintype.card_fin,
    AdjoinRoot.powerBasis'_dim, Polynomial.natDegree_X_pow_sub_C]

end Etale

end AlgebraicGeometry
