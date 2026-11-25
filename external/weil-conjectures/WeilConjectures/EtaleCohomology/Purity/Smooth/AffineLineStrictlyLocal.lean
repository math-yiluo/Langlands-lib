/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineStrictlyLocalSections
public import WeilConjectures.SixFunctors.BaseChange.DerivedForget
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent

/-!
# Acyclicity of the affine line over strictly henselian local rings: assembly

Let `φ : A ⟶ B` be a local homomorphism of strictly henselian local rings and `M` a locally
constant sheaf of `Λ`-modules on `Spec A`. The pullback map
`Hᵠ(𝔸¹_A, p_A^* M) ⟶ Hᵠ(𝔸¹_B, p_A^* M|)` along `𝔸¹_B ⟶ 𝔸¹_A` is bijective in degree `0`
(`AlgebraicGeometry.Etale.bijective_cohomologyMap_zero_affineLine_of_strictlyHenselian`). In
positive degrees it is bijective as soon as `Hᵠ(𝔸¹_R, p_R^* L) = 0` for every strictly
henselian local ring `R` on which the exponent of `Λ` is invertible and every locally constant
sheaf `L` of `Λ`-modules on `Spec R`: both sides then vanish, the target being identified with
`Hᵠ(𝔸¹_B, p_B^* (g^* M))`, `g : Spec B ⟶ Spec A`.

The vanishing in positive degrees is taken as a hypothesis here, split into degree `1` and
degrees `≥ 2`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The pullback along `𝔸¹_B ⟶ 𝔸¹_A` of the underlying abelian sheaf of `p_A^* M` is the
underlying abelian sheaf of `p_B^* (g^* M)`, `g : Spec B ⟶ Spec A`. -/
noncomputable def affineLineMapUpperStarForget₂Iso {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (M : Sheaf (Spec (.of A)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (AffineSpace.map (ULift.{u} (Fin 1)) (Spec.map (CommRingCat.ofHom φ)))^*[
        AddCommGrpCat.{u + 1}].obj
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((𝔸(ULift.{u} (Fin 1); Spec (.of A)) ↘ Spec (.of A))^*[ModuleCat.{u + 1} Λ].obj M)) ≅
      (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((𝔸(ULift.{u} (Fin 1); Spec (.of B)) ↘ Spec (.of B))^*[ModuleCat.{u + 1} Λ].obj
          ((Spec.map (CommRingCat.ofHom φ))^*[ModuleCat.{u + 1} Λ].obj M)) :=
  asIso ((upperStarForget₂ Λ
      (AffineSpace.map (ULift.{u} (Fin 1)) (Spec.map (CommRingCat.ofHom φ)))).app _) ≪≫
    (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).mapIso
      (((upperStarComp _ (AffineSpace.map (ULift.{u} (Fin 1)) (Spec.map (CommRingCat.ofHom φ)))
        (𝔸(ULift.{u} (Fin 1); Spec (.of A)) ↘ Spec (.of A))).app M).symm ≪≫
      (upperStarComp _ (𝔸(ULift.{u} (Fin 1); Spec (.of B)) ↘ Spec (.of B))
        (Spec.map (CommRingCat.ofHom φ)) _ (AffineSpace.map_over _)).app M)

/-- **Acyclicity of the affine line over strictly henselian local rings, from the vanishing in
positive degrees.** Suppose that `Hᵠ(𝔸¹_R, p_R^* L) = 0` for `q > 0`, every strictly henselian
local ring `R` on which the exponent of `Λ` is invertible and every locally constant sheaf `L`
of `Λ`-modules on `Spec R`. Then for a local homomorphism `φ : A ⟶ B` of strictly henselian
local rings and `M` locally constant on `Spec A`, the pullback map
`Hᵠ(𝔸¹_A, p_A^* M) ⟶ Hᵠ(𝔸¹_B, p_A^* M|)` is bijective for every `q`. -/
theorem bijective_cohomologyMap_affineLine_of_strictlyHenselian_of_subsingleton
    (hvan : ∀ (R : Type u) [CommRing R] [HenselianLocalRing R]
      [IsSepClosed (IsLocalRing.ResidueField R)] [HasInvertibleExponent Λ (Spec (.of R))]
      (L : Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
      [IsLocallyConstantSheaf L] (q : ℕ), 0 < q →
      Subsingleton (Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
        AddCommGrpCat.{u + 1})).obj
          ((𝔸(ULift.{u} (Fin 1); Spec (.of R)) ↘ Spec (.of R))^*[ModuleCat.{u + 1} Λ].obj L)) q))
    {A B : Type u} [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)] [CommRing B] [HenselianLocalRing B]
    [IsSepClosed (IsLocalRing.ResidueField B)] (φ : A →+* B)
    [HasInvertibleExponent Λ (Spec (.of A))]
    (M : Sheaf (Spec (.of A)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsLocallyConstantSheaf M] (q : ℕ) :
    Function.Bijective (cohomologyMap
      (AffineSpace.map (ULift.{u} (Fin 1)) (Spec.map (CommRingCat.ofHom φ)))
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((𝔸(ULift.{u} (Fin 1); Spec (.of A)) ↘ Spec (.of A))^*[ModuleCat.{u + 1} Λ].obj M)) q) := by
  obtain rfl | hq := Nat.eq_zero_or_pos q
  · exact bijective_cohomologyMap_zero_affineLine_of_strictlyHenselian Λ φ M
  have : HasInvertibleExponent Λ (Spec (.of B)) := .of_hom (Spec.map (CommRingCat.ofHom φ))
  have := IsLocallyConstantSheaf.upperStar (Spec.map (CommRingCat.ofHom φ)) M
  have hA := hvan A M q hq
  have hB := hvan B ((Spec.map (CommRingCat.ofHom φ))^*[ModuleCat.{u + 1} Λ].obj M) q hq
  have hB' := ((bijective_sheafHMap_hom (affineLineMapUpperStarForget₂Iso Λ φ M).symm q).2)
  have := hB'.subsingleton
  exact ⟨fun a b _ ↦ Subsingleton.elim a b, fun c ↦ ⟨0, Subsingleton.elim _ _⟩⟩

/-- **Positive-degree vanishing for locally constant coefficients from constant ones.** Let `R`
be a strictly henselian local ring on which the exponent of `Λ` is invertible and `q : ℕ`.
Suppose that `Hᵠ(𝔸¹_R, N) = 0` for every abelian group `N` killed by an integer `n` invertible
in `R`. Then `Hᵠ(𝔸¹_R, p_R^* M) = 0` for every locally constant sheaf `M` of `Λ`-modules on
`Spec R`: `M` is constant (`AlgebraicGeometry.Scheme.isConstant_of_isStrictlyHenselianLocalRing`)
with value a `Λ`-module, which is killed by the exponent of `Λ`. -/
theorem subsingleton_sheafH_affineLine_upperStar_of_constantSheaf {R : Type u} [CommRing R]
    [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    [HasInvertibleExponent Λ (Spec (.of R))] (q : ℕ)
    (h : ∀ n : ℕ, IsUnit (n : R) → ∀ N : AddCommGrpCat.{u + 1}, (∀ a : N, n • a = 0) →
      Subsingleton (Sheaf.H ((constantSheaf 𝔸(ULift.{u} (Fin 1); Spec (.of R)).smallEtaleTopology
        AddCommGrpCat.{u + 1}).obj N) q))
    (M : Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsLocallyConstantSheaf M] :
    Subsingleton (Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
      AddCommGrpCat.{u + 1})).obj
        ((𝔸(ULift.{u} (Fin 1); Spec (.of R)) ↘ Spec (.of R))^*[ModuleCat.{u + 1} Λ].obj M)) q) := by
  have : IsStrictlyHenselianLocalRing R := { isSepClosed_residueField := inferInstance }
  obtain ⟨N, ⟨e⟩⟩ := (isConstant_of_isStrictlyHenselianLocalRing M).mem_essImage
  obtain ⟨n, -, hΛ, hu⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ)
    (X := Spec (.of R))
  have hn : IsUnit (n : R) := by
    simpa using hu.map (Scheme.ΓSpecIso (.of R)).hom.hom
  let p := 𝔸(ULift.{u} (Fin 1); Spec (.of R)) ↘ Spec (.of R)
  have := h n hn ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj N) fun a ↦
    (Nat.cast_smul_eq_nsmul Λ n (show N from a)).symm.trans (by rw [hΛ, zero_smul])
  let iso := (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).mapIso
      ((p)^*[ModuleCat.{u + 1} Λ].mapIso e.symm ≪≫
        (upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) p).app N) ≪≫
      (constantSheafSheafComposeForget₂Iso Λ).app N
  exact @Function.Surjective.subsingleton _ _ _ this (bijective_sheafHMap_hom iso.symm q).2

/-- **Acyclicity of the affine line over strictly henselian local rings**, from
* the vanishing of `H¹(𝔸¹_R, N)` for strictly henselian local rings `R` and abelian groups `N`
  killed by an integer invertible in `R` (`h₁`), and
* the vanishing of `Hᵠ(𝔸¹_R, p_R^* L)`, `q ≥ 2`, for strictly henselian local rings `R` with
  the exponent of `Λ` invertible and locally constant sheaves `L` of `Λ`-modules on `Spec R`
  (`h₂`). -/
theorem bijective_cohomologyMap_affineLine_of_strictlyHenselian_of_vanishing
    (h₁ : ∀ (R : Type u) [CommRing R] [HenselianLocalRing R]
      [IsSepClosed (IsLocalRing.ResidueField R)] (n : ℕ), IsUnit (n : R) →
      ∀ N : AddCommGrpCat.{u + 1}, (∀ a : N, n • a = 0) →
      Subsingleton (Sheaf.H ((constantSheaf 𝔸(ULift.{u} (Fin 1); Spec (.of R)).smallEtaleTopology
        AddCommGrpCat.{u + 1}).obj N) 1))
    (h₂ : ∀ (R : Type u) [CommRing R] [HenselianLocalRing R]
      [IsSepClosed (IsLocalRing.ResidueField R)] [HasInvertibleExponent Λ (Spec (.of R))]
      (L : Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
      [IsLocallyConstantSheaf L] (q : ℕ), 2 ≤ q →
      Subsingleton (Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
        AddCommGrpCat.{u + 1})).obj
          ((𝔸(ULift.{u} (Fin 1); Spec (.of R)) ↘ Spec (.of R))^*[ModuleCat.{u + 1} Λ].obj L)) q))
    {A B : Type u} [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)] [CommRing B] [HenselianLocalRing B]
    [IsSepClosed (IsLocalRing.ResidueField B)] (φ : A →+* B)
    [HasInvertibleExponent Λ (Spec (.of A))]
    (M : Sheaf (Spec (.of A)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsLocallyConstantSheaf M] (q : ℕ) :
    Function.Bijective (cohomologyMap
      (AffineSpace.map (ULift.{u} (Fin 1)) (Spec.map (CommRingCat.ofHom φ)))
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((𝔸(ULift.{u} (Fin 1); Spec (.of A)) ↘ Spec (.of A))^*[ModuleCat.{u + 1} Λ].obj M)) q) := by
  refine bijective_cohomologyMap_affineLine_of_strictlyHenselian_of_subsingleton Λ
    (fun R _ _ _ _ L _ q hq ↦ ?_) φ M q
  obtain rfl | hq := (Nat.one_le_iff_ne_zero.2 hq.ne').eq_or_lt
  · exact subsingleton_sheafH_affineLine_upperStar_of_constantSheaf Λ 1 (h₁ R) L
  · exact h₂ R L q hq

end Etale

end AlgebraicGeometry
