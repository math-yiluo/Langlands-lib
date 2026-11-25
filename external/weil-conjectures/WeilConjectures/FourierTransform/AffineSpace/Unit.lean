/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpaceTrace
public import WeilConjectures.FourierTransform.AffineSpace.UnitVanishing
public import WeilConjectures.SixFunctors.OpenClosed.Derived

/-!
# The Fourier transform of the constant sheaf

On relative affine space `𝔸(n; S)` of dimension `r = #n`, the Fourier–Deligne transform of the
constant sheaf is the skyscraper at the origin, twisted and shifted: `FT_ψ(Λ) ≅ δ₀(-r)[-r]`.

The transform vanishes off the origin
(`AlgebraicGeometry.Etale.isZero_leftDerivedUpperStar_affineFourierTransform_unit`), so by the
open–closed triangle it is the direct image of its restriction to the zero section; by the
stalk formula along the zero section that restriction is the compactly supported cohomology
`Rπ_! Λ[r]` of `π : 𝔸(n; S) ⟶ S`, which is `Λ(-r)[-r]` by the affine-space trace
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_twistShift_affineSpace`).

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_unit`: `FT_ψ(Λ) ≅ δ₀(-r)[-r]`.

## Blueprint

The `sk-*` labels quoted below are block names of the *sketch* blueprint, a separate
repository; they are not labels of `blueprint/src` and so are not checked by the build.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open AlgebraicGeometry.AffineSpace

section General

variable (Λ : Type (u + 1)) [CommRing Λ]

open Pretriangulated in
/-- A complex whose restriction to the open complement of a closed immersion `i` vanishes is
the direct image of its restriction to `i`: `K ≅ Ri_* i^* K`, by the open–closed triangle. -/
lemma nonempty_iso_rightDerivedLowerStar_of_isZero_leftDerivedUpperStar {X U Z : Scheme.{u}}
    (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : IsZero ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K)) :
    Nonempty (K ≅ (R((i)_*[ModuleCat.{u + 1} Λ])).obj
      ((D((i)^*[ModuleCat.{u + 1} Λ])).obj K)) := by
  let A := ModuleCat.{u + 1} Λ
  obtain ⟨w, hw⟩ := exists_distTriang_openClosed A j i hij K
  have : IsIso ((mapDerivedUpperStarLowerStarAdjunction A i).unit.app K) :=
    (Triangle.isZero₁_iff_isIso₂ _ hw).1 (D((j)_!open[A]).map_isZero
      (hK.of_iso ((leftDerivedUpperStarIsoMapDerivedCategory A j).app K).symm))
  exact ⟨asIso ((mapDerivedUpperStarLowerStarAdjunction A i).unit.app K)⟩

/-- The global sections of a retract of a scheme `Y` have the characteristic of those of
`Y`. -/
lemma charP_appTop_of_comp_eq_id {p : ℕ} {X Y : Scheme.{u}} (s : X ⟶ Y) (h : Y ⟶ X)
    (hsh : s ≫ h = 𝟙 X) [CharP Γ(Y, ⊤) p] : CharP Γ(X, ⊤) p := by
  have hinj : Function.Injective h.appTop.hom := by
    refine Function.LeftInverse.injective (g := s.appTop.hom) fun x ↦ ?_
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hsh, Scheme.Hom.id_appTop,
      CommRingCat.id_apply]
  exact ⟨fun m ↦ by
    rw [← CharP.cast_eq_zero_iff Γ(Y, ⊤) p, ← map_natCast h.appTop.hom, map_eq_zero_iff _ hinj]⟩

/-- The derived pullback along an endomorphism equal to the identity is the identity. -/
lemma nonempty_leftDerivedUpperStar_iso_id {S : Scheme.{u}} (h : S ⟶ S) (hh : h = 𝟙 S) :
    Nonempty (L((h)^*[ModuleCat.{u + 1} Λ]) ≅ 𝟭 _) := by
  subst hh
  exact ⟨Functor.leftDerivedFunctorNatIso _ (Etale.upperStarId _ _) ≪≫
    (𝟭 _).leftDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryIdIso _⟩

/-- Compactly supported cohomology of `Λ` is unchanged by base change along an endomorphism
`h = 𝟙` of the base: `R(pr₂)_! Λ ≅ Rf_! Λ` for `pr₂ : X ×_S S ⟶ S`. -/
lemma nonempty_iso_rightDerivedLowerShriek_pullbackSnd_unit [Finite Λ] {X S : Scheme.{u}}
    (f : X ⟶ S) [HasCompactification f] [QuasiCompact f] (h : S ⟶ S) (hh : h = 𝟙 S) :
    Nonempty ((R(pullback.snd f h)_![ModuleCat.{u + 1} Λ]).obj (𝟙_ _) ≅
      (R(f)_![ModuleCat.{u + 1} Λ]).obj (𝟙_ _)) := by
  let A := ModuleCat.{u + 1} Λ
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ (IsPullback.of_hasPullback f h)
  obtain ⟨e⟩ := nonempty_leftDerivedUpperStar_iso_id Λ h hh
  exact ⟨(R(pullback.snd f h)_![A]).mapIso
      (leftDerivedUpperStarUnitIso A (pullback.fst f h)).symm ≪≫
    ((asIso (rightDerivedLowerShriekBaseChangeMap Λ (IsPullback.of_hasPullback f h))).app _).symm ≪≫
    e.app _⟩

variable [HasTateTwist Λ]

/-- `F(T(M)[a]) ≅ T'(F M)[a]` for `F` commuting with shifts and `F ⋙ T' ≅ T ⋙ F`, stated for
abstract functors so that the kernel never unfolds the concrete derived functors. -/
private lemma nonempty_iso_obj_comp_shiftFunctor {C D : Type*} [Category C] [Category D]
    [HasShift C ℤ] [HasShift D ℤ] (F : C ⥤ D) [F.CommShift ℤ] (TX TX' : C ⥤ C) (TY : D ⥤ D)
    (pf : F ⋙ TY ≅ TX' ⋙ F) (e : TX' ≅ TX) (a : ℤ) (M : C) :
    Nonempty (F.obj ((TX ⋙ shiftFunctor C a).obj M) ≅ (TY ⋙ shiftFunctor D a).obj (F.obj M)) :=
  ⟨(F.commShiftIso a).app _ ≪≫
    (shiftFunctor D a).mapIso (F.mapIso (e.symm.app M) ≪≫ (pf.app M).symm)⟩

/-- The projection formula for a Tate twist: `Rf_!(-) (m) ≅ Rf_!(- ⊗ᴸ Lf^* Λ_Y(m))`. -/
private lemma nonempty_iso_rightDerivedLowerShriek_comp_tateTwist [Finite Λ] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] (m : ℤ) :
    Nonempty (R(f)_![ModuleCat.{u + 1} Λ] ⋙ tateTwist Λ Y m ≅
      derivedTensorRight _ X ((L((f)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ Y m)) ⋙
        R(f)_![ModuleCat.{u + 1} Λ]) :=
  nonempty_iso_rightDerivedLowerShriek_comp_derivedTensorRight _ f
    (tateObject Λ Y m) (fun K ↦ hasProjectionFormula_of_finite Λ _ K _)

/-- Tensoring with `Lf^* Λ_Y(m)` is the Tate twist `(m)` on `X`. -/
private lemma nonempty_iso_derivedTensorRight_leftDerivedUpperStar_tateObject
    {X Y : Scheme.{u}} [HasInvertibleExponent Λ X]
    [HasInvertibleExponent Λ Y] (f : X ⟶ Y) (m : ℤ) :
    Nonempty (derivedTensorRight _ X ((L((f)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ Y m)) ≅
      tateTwist Λ X m) :=
  ⟨(derivedTensor _ X).flip.mapIso (leftDerivedUpperStarTateObjectIso f m)⟩

/-- `Rf_!(M(m)[2m]) ≅ (Rf_! M)(m)[2m]`, with the twist-and-shift written as a composite. -/
private lemma nonempty_iso_rightDerivedLowerShriek_tateTwist_comp_shiftFunctor [Finite Λ]
    {X Y : Scheme.{u}} [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y]
    (f : X ⟶ Y) [HasCompactification f] (m : ℤ)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((R(f)_![ModuleCat.{u + 1} Λ]).obj
        ((tateTwist Λ X m ⋙ shiftFunctor _ (2 * m)).obj M) ≅
      (tateTwist Λ Y m ⋙ shiftFunctor _ (2 * m)).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj M)) := by
  obtain ⟨pf⟩ := nonempty_iso_rightDerivedLowerShriek_comp_tateTwist Λ f m
  obtain ⟨e⟩ := nonempty_iso_derivedTensorRight_leftDerivedUpperStar_tateObject Λ f m
  exact nonempty_iso_obj_comp_shiftFunctor (R(f)_![ModuleCat.{u + 1} Λ]) (tateTwist Λ X m) _
    (tateTwist Λ Y m) pf e (2 * m) M

/-- Compactly supported direct image commutes with twist-and-shift,
`Rf_!(M(m)[2m]) ≅ (Rf_! M)(m)[2m]`, by the projection formula. -/
lemma nonempty_iso_rightDerivedLowerShriek_twistShift [Finite Λ] {X Y : Scheme.{u}}
    [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y] (f : X ⟶ Y) [HasCompactification f]
    (m : ℤ)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((R(f)_![ModuleCat.{u + 1} Λ]).obj ((twistShift Λ X m).obj M) ≅
      (twistShift Λ Y m).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj M)) :=
  nonempty_iso_rightDerivedLowerShriek_tateTwist_comp_shiftFunctor Λ f m M

end General

section Twist

variable (Λ : Type (u + 1)) [CommRing Λ] [HasTateTwist Λ]

/-- Proper direct image commutes with twist-and-shift, `Rf_*(M(m)[2m]) ≅ (Rf_* M)(m)[2m]`. -/
lemma nonempty_iso_rightDerivedLowerStar_twistShift [Finite Λ] {X Y : Scheme.{u}}
    [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y] (f : X ⟶ Y) [IsProper f] (m : ℤ)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((twistShift Λ X m).obj M) ≅
      (twistShift Λ Y m).obj ((R((f)_*[ModuleCat.{u + 1} Λ])).obj M)) := by
  let e := rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) f
  obtain ⟨t⟩ := nonempty_iso_rightDerivedLowerShriek_twistShift Λ f m M
  exact ⟨(e.app _).symm ≪≫ t ≪≫ (twistShift Λ Y m).mapIso (e.app M)⟩

/-- Compactly supported cohomology of affine space, `Rπ_! Λ ≅ Λ_S(-r)[-2r]`. -/
lemma nonempty_iso_rightDerivedLowerShriek_unit_affineSpace [Finite Λ]
    [HasTateTwist.IsNormalized Λ] (n : Type u) [Fintype n] (S : Scheme.{u})
    [HasInvertibleExponent Λ S] :
    Nonempty ((R(𝔸(n; S) ↘ S)_![ModuleCat.{u + 1} Λ]).obj (𝟙_ _) ≅
      (twistShift Λ S (-(Fintype.card n : ℤ))).obj (𝟙_ _)) := by
  let A := ModuleCat.{u + 1} Λ
  obtain ⟨tr⟩ := nonempty_iso_rightDerivedLowerShriek_twistShift_affineSpace Λ n S
  obtain ⟨t⟩ := nonempty_iso_rightDerivedLowerShriek_twistShift Λ (𝔸(n; S) ↘ S)
    (-(Fintype.card n : ℤ)) ((twistShift Λ 𝔸(n; S) (Fintype.card n)).obj (𝟙_ _))
  exact ⟨(R(𝔸(n; S) ↘ S)_![A]).mapIso
      ((twistShiftZeroIso Λ 𝔸(n; S) (add_neg_cancel _) (𝟙_ _)).symm ≪≫
        (twistShiftTwistShiftIso Λ 𝔸(n; S) _ _ (𝟙_ _)).symm) ≪≫ t ≪≫
    (twistShift Λ S (-(Fintype.card n : ℤ))).mapIso tr⟩

end Twist

section Fourier

variable (Λ : Type (u + 1)) [CommRing Λ] {p : ℕ} [Fact p.Prime] [Invertible (p : Λ)]
variable (n : Type u) [Fintype n] (S : Scheme.{u})

/-- The standard pairing vanishes on the fibre of `𝔸(n; S) ×_S 𝔸(n; S)` over the origin of
the dual. -/
lemma pairingAt_stdPairing_zeroSection :
    pairingAt (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) (stdPairing n S) (zeroSection n S) = 0 := by
  rw [pairingAt, stdPairing, map_sum]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have h : (fibreToProduct _ _ (zeroSection n S)).appTop
      ((pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)).appTop (coord S i)) = 0 := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, fibreToProduct_snd,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply, zeroSection_appTop_coord, map_zero]
  rw [map_mul, h, mul_zero]

omit [Fact p.Prime] [Fintype n] in
/-- The fibre over the origin of the dual is a retract of `𝔸(n; S) ×_S 𝔸(n; S)`, so its
global sections have characteristic `p` when those of the product do. -/
lemma charP_appTop_pullback_zeroSection
    [CharP Γ(pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S), ⊤) p] :
    CharP Γ(pullback (𝔸(n; S) ↘ S) (zeroSection n S ≫ 𝔸(n; S) ↘ S), ⊤) p :=
  charP_appTop_of_comp_eq_id (fibreToProduct _ _ (zeroSection n S))
    (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ 𝔸(n; S) ↘ S)
      (by rw [zeroSection_comp_over, Category.comp_id, pullback.condition]))
    (by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, pullback.lift_fst, fibreToProduct_fst, Category.id_comp]
      · rw [Category.assoc, pullback.lift_snd, fibreToProduct_snd_assoc, zeroSection_comp_over,
          Category.comp_id, Category.id_comp])

/-- Twisting `Λ` by the Artin–Schreier sheaf of the zero function gives back `Λ`. -/
lemma nonempty_iso_artinSchreierTwist_obj_unit (X : Scheme.{u}) [CharP Γ(X, ⊤) p]
    (Ψ : AddChar (ZMod p) Λ) {f : Γ(X, ⊤)} (hf : f = 0) :
    Nonempty ((artinSchreierTwist Λ X Ψ f).obj (𝟙_ _) ≅ 𝟙_ _) := by
  subst hf
  let := X.overSpecZModOfCharP p
  obtain ⟨e₀⟩ := nonempty_iso_artinSchreierSheafOf_zero X
    (Ψ.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom) (Λ := Λ)
  exact ⟨derivedTensorLeftUnitor _ X _ ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso e₀ ≪≫
    singleFunctorObjUnitIso _ X⟩

/-- `(F ⋙ G ⋙ H ⋙ K).obj X ≅ K.obj (H.obj Y)` from `G.obj (F.obj X) ≅ Y`, stated for abstract
functors so that the kernel never unfolds the concrete derived functors. -/
private lemma nonempty_iso_comp_obj_of_iso {C₁ C₂ C₃ C₄ C₅ : Type*} [Category C₁]
    [Category C₂] [Category C₃] [Category C₄] [Category C₅] (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃)
    (H : C₃ ⥤ C₄) (K : C₄ ⥤ C₅) (X : C₁) {Y : C₃} (a : G.obj (F.obj X) ≅ Y) :
    Nonempty ((F ⋙ G ⋙ H ⋙ K).obj X ≅ K.obj (H.obj Y)) :=
  ⟨K.mapIso (H.mapIso a)⟩

/-- The restriction of `FT_ψ(Λ)` to the zero section of the dual is the compactly supported
cohomology of the fibre over the origin, shifted: `z^* FT_ψ(Λ) ≅ R(pr₂)_! Λ [r]`. -/
lemma nonempty_iso_leftDerivedUpperStar_zeroSection_fourierTransform_unit [Finite Λ]
    [CharP Γ(pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S), ⊤) p]
    [HasCompactification (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))]
    [CharP Γ(pullback (𝔸(n; S) ↘ S) (zeroSection n S ≫ 𝔸(n; S) ↘ S), ⊤) p]
    (Ψ : AddChar (ZMod p) Λ) (r : ℤ) :
    Nonempty ((D((zeroSection n S)^*[ModuleCat.{u + 1} Λ])).obj
        ((fourierTransform Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ (stdPairing n S) r).obj (𝟙_ _)) ≅
      (shiftFunctor _ r).obj ((R(pullback.snd (𝔸(n; S) ↘ S)
        (zeroSection n S ≫ 𝔸(n; S) ↘ S))_![ModuleCat.{u + 1} Λ]).obj (𝟙_ _))) := by
  let A := ModuleCat.{u + 1} Λ
  obtain ⟨t⟩ := nonempty_iso_artinSchreierTwist_obj_unit Λ _ Ψ
    (pairingAt_stdPairing_zeroSection n S)
  obtain ⟨a⟩ := nonempty_iso_comp_obj_of_iso
    (D((pullback.fst (𝔸(n; S) ↘ S) (zeroSection n S ≫ 𝔸(n; S) ↘ S))^*[A]))
    (artinSchreierTwist Λ _ Ψ (pairingAt _ _ (stdPairing n S) (zeroSection n S)))
    (R(pullback.snd (𝔸(n; S) ↘ S) (zeroSection n S ≫ 𝔸(n; S) ↘ S))_![A]) (shiftFunctor _ r)
    (𝟙_ _) ((artinSchreierTwist Λ _ Ψ _).mapIso
      (((leftDerivedUpperStarIsoMapDerivedCategory A _).app _).symm ≪≫
        leftDerivedUpperStarUnitIso A _) ≪≫ t)
  exact ⟨(fourierTransformStalkIso Λ _ _ Ψ (stdPairing n S) r (zeroSection n S)).app (𝟙_ _) ≪≫
    a⟩

end Fourier

variable (Λ : Type (u + 1)) [CommRing Λ] {p : ℕ} [Fact p.Prime] [Invertible (p : Λ)]
variable (n : Type u) [Fintype n] (S : Scheme.{u})
variable [CharP Γ(pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S), ⊤) p]
variable [HasCompactification (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))]

/-- The Fourier–Deligne transform of the constant sheaf on `𝔸(n; S)` is the skyscraper at
the origin of the dual, Tate twisted and shifted by the relative dimension `r = #n`:

`FT_ψ(Λ) ≅ δ₀(-r)[-r]`.

On the affine line, the blueprint's case, this reads `FT_ψ(Λ) ≅ δ₀(-1)[-1]`.

The character must be **nontrivial** in the strong sense that `Ψ 1 - 1` is a unit of `Λ`:
the proof uses `H_c^*(𝔸¹, ℒ_ψ) = 0`, and the `ψ`-isotypic part of `H_c^*(𝔸¹, Λ)` is killed
by `Ψ 1 - 1`. For `Ψ = 1` the kernel is the constant sheaf and the transform of `Λ` is
`Λ(-r)[-r]`, supported everywhere. Asking `Ψ ≠ 1` is not enough when `Λ` is not a domain:
for `Λ = 𝔽_ℓ × 𝔽_ℓ` and `Ψ = (ψ₀, 1)` the transform has the trivial-character transform as a
factor.

Class: torsion; decided by the cohomology of `𝔸^r`, `H_c^*(𝔸^r, Λ) ≅ Λ(-r)[-2r]`, which needs
`[Finite Λ] [HasInvertibleExponent Λ S]`.
(sketch blueprint: `lemma-fourier-transform-constant-sheaf`) -/
theorem nonempty_iso_affineFourierTransform_unit [Finite Λ] [HasInvertibleExponent Λ S]
    [HasTateTwist Λ] [HasTateTwist.IsNormalized Λ] (Ψ : AddChar (ZMod p) Λ)
    (hΨ : IsUnit (Ψ 1 - 1)) :
    Nonempty ((affineFourierTransform Λ n S Ψ).obj (𝟙_ _) ≅
        (shiftFunctor _ (-(Fintype.card n : ℤ))).obj
          ((tateTwist Λ (𝔸(n; S)) (-(Fintype.card n : ℤ))).obj
            (skyscraperZero Λ n S))) := by
  have := charP_appTop_pullback_zeroSection n S (p := p)
  obtain ⟨a⟩ := nonempty_iso_rightDerivedLowerStar_of_isZero_leftDerivedUpperStar Λ _
    (zeroSection n S) (zeroSection n S).range_eq_compl_range_openComplement_ι _
    (isZero_leftDerivedUpperStar_affineFourierTransform_unit Λ n S Ψ hΨ _
      (by rw [(zeroSection n S).range_eq_compl_range_openComplement_ι, compl_compl]))
  obtain ⟨b⟩ := nonempty_iso_leftDerivedUpperStar_zeroSection_fourierTransform_unit Λ n S Ψ
    (Fintype.card n)
  obtain ⟨c⟩ := nonempty_iso_rightDerivedLowerShriek_pullbackSnd_unit Λ (𝔸(n; S) ↘ S) _
    (zeroSection_comp_over n S)
  obtain ⟨d⟩ := nonempty_iso_rightDerivedLowerShriek_unit_affineSpace Λ n S
  obtain ⟨t⟩ := nonempty_iso_rightDerivedLowerStar_twistShift Λ (zeroSection n S)
    (-(Fintype.card n : ℤ)) (𝟙_ _)
  exact ⟨a ≪≫ (R((zeroSection n S)_*[ModuleCat.{u + 1} Λ])).mapIso
      (b ≪≫ (shiftFunctor _ (Fintype.card n : ℤ)).mapIso (c ≪≫ d)) ≪≫
    ((R((zeroSection n S)_*[ModuleCat.{u + 1} Λ])).commShiftIso (Fintype.card n : ℤ)).app _ ≪≫
    (shiftFunctor _ (Fintype.card n : ℤ)).mapIso t ≪≫
    ((shiftFunctorAdd' _ (2 * -(Fintype.card n : ℤ)) (Fintype.card n) (-(Fintype.card n : ℤ))
      (by ring)).app _).symm⟩

end AlgebraicGeometry.Etale
