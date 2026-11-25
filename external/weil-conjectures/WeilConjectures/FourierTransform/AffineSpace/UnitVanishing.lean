/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.LinearForm
public import WeilConjectures.FourierTransform.AffineSpace.ArtinSchreierVanishing
public import WeilConjectures.FourierTransform.AffineSpace.Transform
public import WeilConjectures.FourierTransform.Properties.Stalk

/-!
# The transform of the constant sheaf vanishes off the origin

On relative affine space `𝔸(n; S)`, for a character `Ψ` with `Ψ(1) - 1` a unit, the
Fourier–Deligne transform of the constant sheaf vanishes on the complement of the zero section
of the dual. On the basic open set `ξᵢ ≠ 0` the linear form `x ↦ ⟨x, ξ⟩` is a coordinate
after a linear change of variables, so the restriction of the transform is the compactly
supported cohomology of `𝔸^{n-1}` times that of `ℒ_{ψ(t)}` on the affine line, which vanishes
(`AlgebraicGeometry.Etale.isZero_rightDerivedLowerShriek_artinSchreierSheafZMod_coord`).

## Main statements

- `AlgebraicGeometry.Etale.isZero_rightDerivedLowerShriek_artinSchreierSheafZMod_linearForm`:
  `Rq_! ℒ_{ψ(ℓ)} = 0` on `𝔸(n; S) ×_S T` for a linear form `ℓ = ∑ⱼ cⱼ xⱼ` with `cᵢ` a unit.
- `AlgebraicGeometry.Etale.isZero_mapDerivedCategory_upperStar_affineFourierTransform_unit`:
  the restriction of `FT_ψ(Λ)` along a point `ξ` of the dual with a unit coordinate is zero.
- `AlgebraicGeometry.Etale.isZero_leftDerivedUpperStar_affineFourierTransform_unit`: the
  restriction of `FT_ψ(Λ)` to the complement of the zero section is zero.

## Implementation notes

The vanishing is checked along the points `Spec κ(y) ⟶ U` of `U`, which jointly detect zero
objects (`AlgebraicGeometry.Etale.isZero_of_isZero_mapDerivedCategory_upperStar`). Along such a
point `ξ` some coordinate `ξᵢ` is a unit, and the stalk formula
`AlgebraicGeometry.Etale.fourierTransformStalkIso` writes `ξ^* FT_ψ(Λ)` as
`Rq_! ℒ_{ψ(∑ⱼ ξⱼ xⱼ)}[r]` on the fibre `𝔸(n; S) ×_S T`. The change of variables
`AlgebraicGeometry.AffineSpace.linearCoordHom` identifies the fibre with the affine line over
`𝔸(n ∖ {i}; T)`, the linear form with its coordinate, and `q` with the composite of the two
projections, so the composition law for `R(-)_!` reduces the vanishing to the affine line.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory ZeroObject
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open AlgebraicGeometry.AffineSpace

/-- An object of `D(X_ét)` is zero if its pullbacks along a jointly surjective family of
morphisms are zero: the pullbacks of its homology sheaves vanish, and these pullbacks jointly
reflect isomorphisms (`AlgebraicGeometry.Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective`).
-/
lemma isZero_of_isZero_mapDerivedCategory_upperStar (Λ : Type (u + 1)) [CommRing Λ]
    {X : Scheme.{u}} {ι : Type u} {U : ι → Scheme.{u}} (a : ∀ i, U i ⟶ X)
    (ha : ∀ x : X, ∃ (i : ι) (y : U i), (a i).base y = x)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (h : ∀ i, IsZero ((D((a i)^*[ModuleCat.{u + 1} Λ])).obj K)) : IsZero K := by
  refine _root_.DerivedCategory.isZero_of_forall_isZero_homology K fun q ↦ ?_
  have := Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ) a ha
    (0 : (_root_.DerivedCategory.homologyFunctor _ q).obj K ⟶ 0) fun i ↦
      isIso_of_source_target_iso_zero _
        (((_root_.DerivedCategory.homologyFunctor _ q).map_isZero (h i)).of_iso
          ((((a i)^*[ModuleCat.{u + 1} Λ].mapDerivedCategoryHomologyFunctorIso q).app K))).isoZero
        (Functor.map_isZero _ (isZero_zero _)).isoZero
  exact (isZero_zero _).of_iso
    (asIso (0 : (_root_.DerivedCategory.homologyFunctor _ q).obj K ⟶ 0))

variable (Λ : Type (u + 1)) [CommRing Λ] {p : ℕ} [Fact p.Prime] [Invertible (p : Λ)]

/-- **Compactly supported cohomology of `ℒ_ψ` of a linear form with a unit coefficient.** For
`g : T ⟶ S` and coefficients `c : n → Γ(T, 𝒪)` with `cᵢ` a unit, the compactly supported
direct image along `q : 𝔸(n; S) ×_S T ⟶ T` of the Artin–Schreier sheaf of the linear form
`ℓ = ∑ⱼ cⱼ xⱼ` vanishes: `Rq_! ℒ_{ψ(ℓ)} = 0`. The change of variables
`AlgebraicGeometry.AffineSpace.linearCoordHom` makes `ℓ` the coordinate of the affine line over
`𝔸(n ∖ {i}; T)`; compact-support base change along it and the composition law reduce the
statement to `AlgebraicGeometry.Etale.isZero_rightDerivedLowerShriek_artinSchreierSheafZMod_coord`.
(sketch blueprint: `lemma-fourier-transform-constant-sheaf`, proof) -/
theorem isZero_rightDerivedLowerShriek_artinSchreierSheafZMod_linearForm [Finite Λ]
    [HasTateTwist Λ] [HasTateTwist.IsNormalized Λ] {n : Type u} [Fintype n]
    {S T : Scheme.{u}} (g : T ⟶ S) [HasInvertibleExponent Λ T]
    [CharP Γ(pullback (𝔸(n; S) ↘ S) g, ⊤) p] {c : n → Γ(T, ⊤)} {i : n} (hc : IsUnit (c i))
    (Ψ : AddChar (ZMod p) Λ) (hΨ : IsUnit (Ψ 1 - 1)) :
    IsZero ((R(pullback.snd (𝔸(n; S) ↘ S) g)_![ModuleCat.{u + 1} Λ]).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        (artinSchreierSheafZMod (pullback (𝔸(n; S) ↘ S) g) Ψ (linearForm g c)))) := by
  classical
  let A := ModuleCat.{u + 1} Λ
  have := isIso_linearCoordHom g hc
  have := isIso_linearCoordInv g hc
  have : CharP Γ(𝔸(PUnit.{u + 1}; 𝔸({j // j ≠ i}; T)), ⊤) p :=
    charP_of_injective_ringHom (ConcreteCategory.bijective_of_isIso
      (linearCoordInv g hc).appTop).1 p
  have : HasInvertibleExponent Λ 𝔸({j // j ≠ i}; T) :=
    HasInvertibleExponent.of_hom (𝔸({j // j ≠ i}; T) ↘ T)
  -- `q` is the base change of `𝔸¹(𝔸(n ∖ {i}; T)) ⟶ 𝔸(n ∖ {i}; T) ⟶ T` along the change of
  -- variables
  have sq : IsPullback (linearCoordHom g c i) (pullback.snd (𝔸(n; S) ↘ S) g)
      (𝔸(PUnit.{u + 1}; 𝔸({j // j ≠ i}; T)) ↘ 𝔸({j // j ≠ i}; T) ≫ 𝔸({j // j ≠ i}; T) ↘ T)
      (𝟙 T) :=
    IsPullback.of_horiz_isIso ⟨by rw [linearCoordHom_over, Category.comp_id]⟩
  have : HasCompactification
      (𝔸(PUnit.{u + 1}; 𝔸({j // j ≠ i}; T)) ↘ 𝔸({j // j ≠ i}; T) ≫ 𝔸({j // j ≠ i}; T) ↘ T) :=
    .of_isPullback (IsPullback.of_horiz_isIso (fst := linearCoordInv g hc)
      (f := pullback.snd (𝔸(n; S) ↘ S) g) (g := 𝟙 T)
      ⟨by rw [linearCoordInv_snd, Category.comp_id]⟩)
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  obtain ⟨c₁⟩ := nonempty_iso_rightDerivedLowerShriek_comp Λ
    (𝔸(PUnit.{u + 1}; 𝔸({j // j ≠ i}; T)) ↘ 𝔸({j // j ≠ i}; T)) (𝔸({j // j ≠ i}; T) ↘ T)
  -- the change of variables pulls `ℒ_{ψ(y)}` back to `ℒ_{ψ(ℓ)}`
  obtain ⟨e⟩ := nonempty_iso_leftDerivedUpperStar_singleFunctor Λ (linearCoordHom g c i) _ _
    (artinSchreierSheafZModPullbackIso (linearCoordHom g c i) Ψ (coord _ PUnit.unit) ≪≫
      eqToIso (congrArg _ (linearCoordHom_appTop_coord g c i)))
  have h₀ := isZero_rightDerivedLowerShriek_artinSchreierSheafZMod_coord Λ
    𝔸({j // j ≠ i}; T) Ψ hΨ
  refine ((L((𝟙 T)^*[A])).map_isZero ((c₁.app _).symm.isZero_iff.1
    ((R(𝔸({j // j ≠ i}; T) ↘ T)_![A]).map_isZero h₀))).of_iso ?_
  exact (R(pullback.snd (𝔸(n; S) ↘ S) g)_![A]).mapIso e.symm ≪≫
    ((asIso (rightDerivedLowerShriekBaseChangeMap Λ sq)).app _).symm

/-- On the fibre `𝔸(n; S) ×_S T` over a point `ξ : T ⟶ 𝔸(n; S)` of the dual, the standard
pairing is the linear form `x ↦ ∑ⱼ ξⱼ xⱼ`. -/
lemma pairingAt_stdPairing (n : Type u) [Fintype n] (S : Scheme.{u}) {T : Scheme.{u}}
    (ξ : T ⟶ 𝔸(n; S)) :
    pairingAt (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) (stdPairing n S) ξ =
      linearForm (ξ ≫ 𝔸(n; S) ↘ S) fun j ↦ ξ.appTop (coord S j) := by
  rw [pairingAt, stdPairing, map_sum, linearForm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_mul, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, fibreToProduct_fst,
    ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, fibreToProduct_snd,
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

/-- `(F ⋙ G ⋙ H ⋙ K).obj X ≅ K.obj (H.obj Y)` from `G.obj (F.obj X) ≅ Y`, stated for abstract
functors so that the kernel never unfolds the concrete derived functors. -/
private lemma nonempty_iso_comp_comp_comp_obj_of_iso {C₁ C₂ C₃ C₄ C₅ : Type*} [Category C₁]
    [Category C₂] [Category C₃] [Category C₄] [Category C₅] (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃)
    (H : C₃ ⥤ C₄) (K : C₄ ⥤ C₅) (X : C₁) {Y : C₃} (a : G.obj (F.obj X) ≅ Y) :
    Nonempty ((F ⋙ G ⋙ H ⋙ K).obj X ≅ K.obj (H.obj Y)) :=
  ⟨K.mapIso (H.mapIso a)⟩

variable (n : Type u) [Fintype n] (S : Scheme.{u})
variable [CharP Γ(pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S), ⊤) p]
variable [HasCompactification (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))]

/-- The restriction of `FT_ψ(Λ)` along a point `ξ : T ⟶ 𝔸(n; S)` of the dual, `T` nonempty,
with a unit coordinate `ξᵢ` vanishes. By the stalk formula
(`AlgebraicGeometry.Etale.fourierTransformStalkIso`) it is `Rq_! ℒ_{ψ(∑ⱼ ξⱼ xⱼ)}[r]` on the
fibre `q : 𝔸(n; S) ×_S T ⟶ T`, which vanishes by
`AlgebraicGeometry.Etale.isZero_rightDerivedLowerShriek_artinSchreierSheafZMod_linearForm`.
(sketch blueprint: `lemma-fourier-transform-constant-sheaf`, proof) -/
theorem isZero_mapDerivedCategory_upperStar_affineFourierTransform_unit [Finite Λ]
    [HasInvertibleExponent Λ S] [HasTateTwist Λ] [HasTateTwist.IsNormalized Λ]
    (Ψ : AddChar (ZMod p) Λ) (hΨ : IsUnit (Ψ 1 - 1)) {T : Scheme.{u}} [Nonempty T]
    (ξ : T ⟶ 𝔸(n; S)) {i : n} (hξ : IsUnit (ξ.appTop (coord S i))) :
    IsZero ((D((ξ)^*[ModuleCat.{u + 1} Λ])).obj
      ((affineFourierTransform Λ n S Ψ).obj (𝟙_ _))) := by
  let A := ModuleCat.{u + 1} Λ
  have : HasInvertibleExponent Λ T := HasInvertibleExponent.of_hom (ξ ≫ 𝔸(n; S) ↘ S)
  -- the fibre has characteristic `p`: it is nonempty, having a section over `T`, and maps to
  -- the product
  have x : (pullback (𝔸(n; S) ↘ S) (ξ ≫ 𝔸(n; S) ↘ S) : Scheme.{u}) :=
    (pullback.lift (ξ ≫ 𝔸(n; S) ↘ S ≫ zeroSection n S) (𝟙 T)
      (by rw [Category.assoc, Category.assoc, zeroSection_over, Category.comp_id,
        Category.id_comp])).base (Classical.arbitrary T)
  have := ((pullback (𝔸(n; S) ↘ S) (ξ ≫ 𝔸(n; S) ↘ S)).presheaf.germ ⊤ x
    trivial).hom.domain_nontrivial
  have : CharP Γ(pullback (𝔸(n; S) ↘ S) (ξ ≫ 𝔸(n; S) ↘ S), ⊤) p :=
    (CharP.charP_iff_prime_eq_zero Fact.out).2 (by
      rw [← map_natCast (fibreToProduct (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) ξ).appTop.hom,
        CharP.cast_eq_zero, map_zero])
  -- the integrand on the fibre is `Λ ⊗ ℒ_{ψ(b(x, ξ))} ≅ ℒ_{ψ(∑ⱼ ξⱼ xⱼ)}`
  obtain ⟨a⟩ := nonempty_iso_comp_comp_comp_obj_of_iso
    (D((pullback.fst (𝔸(n; S) ↘ S) (ξ ≫ 𝔸(n; S) ↘ S))^*[A]))
    (artinSchreierTwist Λ _ Ψ (pairingAt _ _ (stdPairing n S) ξ))
    (R(pullback.snd (𝔸(n; S) ↘ S) (ξ ≫ 𝔸(n; S) ↘ S))_![A])
    (shiftFunctor _ (Fintype.card n : ℤ)) (𝟙_ _)
    ((artinSchreierTwist Λ _ Ψ _).mapIso
      (((leftDerivedUpperStarIsoMapDerivedCategory A _).app _).symm ≪≫
        leftDerivedUpperStarUnitIso A _) ≪≫ derivedTensorLeftUnitor _ _ _ ≪≫
      eqToIso (by rw [pairingAt_stdPairing]))
  exact ((shiftFunctor _ (Fintype.card n : ℤ)).map_isZero
    (isZero_rightDerivedLowerShriek_artinSchreierSheafZMod_linearForm Λ (ξ ≫ 𝔸(n; S) ↘ S)
      (c := fun j ↦ ξ.appTop (coord S j)) hξ Ψ hΨ)).of_iso
    ((fourierTransformStalkIso Λ _ _ Ψ (stdPairing n S) (Fintype.card n) ξ).app (𝟙_ _) ≪≫ a)

/-- The Fourier–Deligne transform of the constant sheaf on `𝔸(n; S)` vanishes off the origin:
its restriction to the open complement `U` of the zero section of the dual is zero. The
character must satisfy `IsUnit (Ψ 1 - 1)`, which is what makes `H^*_c(𝔸¹, ℒ_ψ)` vanish.
(sketch blueprint: `lemma-fourier-transform-constant-sheaf`, proof) -/
theorem isZero_leftDerivedUpperStar_affineFourierTransform_unit [Finite Λ]
    [HasInvertibleExponent Λ S] [HasTateTwist Λ] [HasTateTwist.IsNormalized Λ]
    (Ψ : AddChar (ZMod p) Λ) (hΨ : IsUnit (Ψ 1 - 1)) {U : Scheme.{u}} (j : U ⟶ 𝔸(n; S))
    [IsOpenImmersion j] (hj : Set.range j.base = (Set.range (zeroSection n S).base)ᶜ) :
    IsZero ((L((j)^*[ModuleCat.{u + 1} Λ])).obj
      ((affineFourierTransform Λ n S Ψ).obj (𝟙_ _))) := by
  let A := ModuleCat.{u + 1} Λ
  -- the points `Spec κ(y) ⟶ U` jointly detect zero objects
  refine isZero_of_isZero_mapDerivedCategory_upperStar Λ (fun y : U ↦ U.fromSpecResidueField y)
    (fun y ↦ ⟨y, IsLocalRing.closedPoint _, U.fromSpecResidueField_apply _ _⟩) _ fun y ↦ ?_
  -- some coordinate of `j y` does not vanish
  obtain ⟨i, hi⟩ : ∃ i, j.base y ∈ 𝔸(n; S).basicOpen (coord S i) := by
    have : j.base y ∉ Set.range (zeroSection n S).base := by
      rw [← Set.mem_compl_iff, ← hj]
      exact ⟨y, rfl⟩
    rw [range_zeroSection] at this
    simpa using this
  have hξ : IsUnit ((U.fromSpecResidueField y ≫ j).appTop (coord S i)) := by
    refine RingedSpace.isUnit_of_isUnit_germ _ ⊤ _ fun t _ ↦ ?_
    rw [← Scheme.mem_basicOpen_top, ← Scheme.preimage_basicOpen_top,
      Subsingleton.elim t (IsLocalRing.closedPoint _)]
    rwa [Scheme.Hom.mem_preimage, Scheme.Hom.comp_apply, U.fromSpecResidueField_apply]
  exact (isZero_mapDerivedCategory_upperStar_affineFourierTransform_unit Λ n S Ψ hΨ
    (U.fromSpecResidueField y ≫ j) hξ).of_iso
    (((leftDerivedUpperStarIsoMapDerivedCategory A _).app _).symm ≪≫
      ((leftDerivedUpperStarComp A (U.fromSpecResidueField y) j).app _).symm ≪≫
      (leftDerivedUpperStarIsoMapDerivedCategory A _).app _)

end AlgebraicGeometry.Etale
