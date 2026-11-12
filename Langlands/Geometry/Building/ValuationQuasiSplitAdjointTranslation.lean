import Langlands.Geometry.Building.AffineExtendedWeylTransport
import Langlands.Geometry.Building.ValuationBuildingAxioms
import Langlands.Geometry.Building.AffineWeylGroups

/-!
# The quasi-split adjoint sentence of AS 5, reduced to translations

The last sentence of AS 5 (KP Axiom 4.1.6, KP Proposition 6.6.2) says that for a quasi-split
adjoint group the image of `N(F)` in the affine automorphisms of the apartment is all of
`W(Ψ)ᵉˣᵗ`. Since `W(Ψ)` already lies in the image (the first sentence of AS 5), it is enough to
realize the translations of `W(Ψ)ᵉˣᵗ`, as in the proof of KP Proposition 6.6.2.

This module states the translation part, `ValuationBuildingQuasiSplitAdjointTranslationStatement`:
every translation of the apartment that preserves `Ψ` is the translation by `ν(z)` for some
`z ∈ Z(F)`. It proves that this statement and the first sentence of AS 5 give the last one.
-/

noncomputable section

universe u uV uA

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

namespace AffineRootSystem

variable {V : Type uV} {A : Type uA} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]

/-- An affine automorphism with trivial derivative is a translation. -/
theorem exists_eq_constVAdd_of_linear_eq {e : A ≃ᵃ[ℝ] A} (he : e.linear = LinearEquiv.refl ℝ V) :
    ∃ v : V, e = AffineEquiv.constVAdd ℝ A v := by
  obtain ⟨p⟩ : Nonempty A := inferInstance
  refine ⟨e p -ᵥ p, AffineEquiv.ext fun x => ?_⟩
  rw [AffineEquiv.constVAdd_apply]
  calc e x = e ((x -ᵥ p) +ᵥ p) := by rw [vsub_vadd]
    _ = e.linear (x -ᵥ p) +ᵥ e p := e.map_vadd p (x -ᵥ p)
    _ = (e p -ᵥ p) +ᵥ x := by
      rw [he, LinearEquiv.refl_apply]
      have h : e p = (e p -ᵥ p) +ᵥ p := (vsub_vadd (e p) p).symm
      conv_lhs => rw [h]
      conv_rhs => rw [← vsub_vadd x p]
      rw [vadd_vadd, vadd_vadd, add_comm]

/-- If a subgroup `H` contains `W(Ψ)` and every translation preserving `Ψ`, it contains
`W(Ψ)ᵉˣᵗ`. (Every `e ∈ W(Ψ)ᵉˣᵗ` has the derivative of some `w ∈ W(Ψ)`, and `w⁻¹ e` is a
translation preserving `Ψ`.) -/
theorem extendedAffineWeylGroup_le_of_constVAdd_mem {Ψ : Set (A →ᵃ[ℝ] ℝ)}
    {H : Subgroup (A ≃ᵃ[ℝ] A)} (hW : affineWeylGroup Ψ ≤ H)
    (hT : ∀ v : V, AffineEquiv.constVAdd ℝ A v ∈ rootStabilizer Ψ →
      AffineEquiv.constVAdd ℝ A v ∈ H) :
    extendedAffineWeylGroup Ψ ≤ H := by
  intro e he
  have hlin : AffineEquiv.linearHom e ∈ (affineWeylGroup Ψ).map AffineEquiv.linearHom := by
    rw [map_affineWeylGroup_linearHom]
    exact he.2
  obtain ⟨w, hw, hwe⟩ := hlin
  have h1 : (w⁻¹ * e).linear = LinearEquiv.refl ℝ V := by
    change AffineEquiv.linearHom (w⁻¹ * e) = 1
    rw [map_mul, map_inv, hwe, inv_mul_cancel]
  obtain ⟨v, hv⟩ := exists_eq_constVAdd_of_linear_eq h1
  have hmem : w⁻¹ * e ∈ rootStabilizer Ψ :=
    (rootStabilizer Ψ).mul_mem
      ((rootStabilizer Ψ).inv_mem (affineWeylGroup_le_extendedAffineWeylGroup Ψ hw).1) he.1
  have hH : w⁻¹ * e ∈ H := by
    rw [hv] at hmem ⊢
    exact hT v hmem
  have : e = w * (w⁻¹ * e) := by rw [mul_inv_cancel_left]
  rw [this]
  exact H.mul_mem (hW hw) hH

/-- `W(Ψ)ᵉˣᵗ` is the only subgroup between `W(Ψ)` and `W(Ψ)ᵉˣᵗ` that contains every
translation preserving `Ψ`. -/
theorem eq_extendedAffineWeylGroup_of_constVAdd_mem {Ψ : Set (A →ᵃ[ℝ] ℝ)}
    {H : Subgroup (A ≃ᵃ[ℝ] A)} (hW : affineWeylGroup Ψ ≤ H)
    (hle : H ≤ extendedAffineWeylGroup Ψ)
    (hT : ∀ v : V, AffineEquiv.constVAdd ℝ A v ∈ rootStabilizer Ψ →
      AffineEquiv.constVAdd ℝ A v ∈ H) :
    H = extendedAffineWeylGroup Ψ :=
  le_antisymm hle (extendedAffineWeylGroup_le_of_constVAdd_mem hW hT)

end AffineRootSystem

/-- **Translations of the extended affine Weyl group of a quasi-split adjoint group** (the
translation part of KP Proposition 6.6.2, via KP Lemma 6.4.10). For a nonarchimedean local
field `F`, every quasi-split adjoint `G` over `F` and every `B : ValuationBuildingData G`: if
the translation of the apartment `A(S)` by `v ∈ V(S)/V(S)^Φ` preserves the affine roots `Ψ`,
then `v` is the class of `ν(z)` for some `z ∈ Z(F)`, `Z = Z_G(S)`. -/
def ValuationBuildingQuasiSplitAdjointTranslationStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G), IsQuasiSplit G → IsAdjoint G →
    ∀ v : TranslationSpace B.i,
      AffineEquiv.constVAdd ℝ B.Apartment v ∈ AffineRootSystem.rootStabilizer B.affineRoots →
      ∃ z : rationalPoints B.centralizer.Z,
        (Submodule.Quotient.mk (B.translation z).toAdd : TranslationSpace B.i) = v

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-- The translation by `ν(z)` is the action of `z ∈ Z(F)`, so it lies in the image of `N(F)`. -/
theorem constVAdd_translation_mem_range (z : rationalPoints B.centralizer.Z) :
    AffineEquiv.constVAdd ℝ B.Apartment
        (Submodule.Quotient.mk (B.translation z).toAdd : TranslationSpace B.i) ∈
      B.apartment.normalizerAffineEquiv.range :=
  ⟨B.centralizer.toNormalizer z, B.isOmegaCompatible.normalizerAffineEquiv_eq z⟩

/-- **The last sentence of AS 5 from its translation part.** If `W(Ψ)` lies in the image of
`N(F)`, the image lies in `W(Ψ)ᵉˣᵗ` (the first sentence of AS 5), and every translation
preserving `Ψ` is a translation by some `ν(z)`, then the image of `N(F)` is `W(Ψ)ᵉˣᵗ`. -/
theorem range_eq_extendedAffineWeylGroup_of_translation
    (hW : AffineRootSystem.affineWeylGroup B.affineRoots ≤ B.apartment.normalizerAffineEquiv.range)
    (hle : B.apartment.normalizerAffineEquiv.range ≤
      AffineRootSystem.extendedAffineWeylGroup B.affineRoots)
    (hT : ∀ v : TranslationSpace B.i,
      AffineEquiv.constVAdd ℝ B.Apartment v ∈ AffineRootSystem.rootStabilizer B.affineRoots →
      ∃ z : rationalPoints B.centralizer.Z,
        (Submodule.Quotient.mk (B.translation z).toAdd : TranslationSpace B.i) = v) :
    B.apartment.normalizerAffineEquiv.range =
      AffineRootSystem.extendedAffineWeylGroup B.affineRoots := by
  refine AffineRootSystem.eq_extendedAffineWeylGroup_of_constVAdd_mem hW hle fun v hv => ?_
  obtain ⟨z, rfl⟩ := hT v hv
  exact B.constVAdd_translation_mem_range z

/-- The quasi-split adjoint sentence of AS 5 for `B`, from
`ValuationBuildingQuasiSplitAdjointTranslationStatement` and the first sentence of AS 5. -/
theorem range_eq_extendedAffineWeylGroup_of_quasiSplitAdjointTranslation
    (hQA : ValuationBuildingQuasiSplitAdjointTranslationStatement.{u})
    (hW : AffineRootSystem.affineWeylGroup B.affineRoots ≤ B.apartment.normalizerAffineEquiv.range)
    (hle : B.apartment.normalizerAffineEquiv.range ≤
      AffineRootSystem.extendedAffineWeylGroup B.affineRoots)
    (hqs : IsQuasiSplit G) (had : IsAdjoint G) :
    B.apartment.normalizerAffineEquiv.range =
      AffineRootSystem.extendedAffineWeylGroup B.affineRoots :=
  B.range_eq_extendedAffineWeylGroup_of_translation hW hle (hQA F G B hqs had)

end ValuationBuildingData

end Langlands.Geometry.Building
