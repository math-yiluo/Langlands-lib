/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.Affine
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpaceTrace
public import WeilConjectures.FourierTransform.AffineSpace.KernelTransform
public import WeilConjectures.FourierTransform.ArtinSchreier
public import WeilConjectures.Mathlib.Algebra.Group.AddChar
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import WeilConjectures.SixFunctors.Etale.Derived.Composition
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricPoint
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal
public import WeilConjectures.SixFunctors.Finite.Exact

/-!
# Compactly supported cohomology of the affine line with Artin–Schreier coefficients

Let `T` be a scheme of characteristic `p` and `Ψ` an additive character of `𝔽_p` with values
in a finite coefficient ring `Λ` in which `p` and the exponent of `Λ` are invertible on `T`, and
such that `Ψ(1) - 1` is a unit. Then the compactly supported cohomology of the relative affine
line `π : 𝔸¹_T ⟶ T` with coefficients in the Artin–Schreier sheaf `ℒ_{Ψ, x}` of the
coordinate vanishes: `Rπ_! ℒ_{Ψ, x} = 0`.

## Main statements

- `AlgebraicGeometry.Etale.isZero_rightDerivedLowerShriek_artinSchreierSheaf`: over a finite
  field `k`, `Rπ_! ℒ_Ψ = 0` for `π : 𝔸¹_k ⟶ Spec k` and `∑_a Ψ(a) = 0`.
- `AlgebraicGeometry.Etale.isZero_rightDerivedLowerShriek_artinSchreierSheafZMod_coord`:
  `Rπ_! ℒ_{Ψ, x} = 0`.

## Implementation notes

Over a finite field `k`, the idempotents `e_1` and `e_Ψ` of `(AS_q)_* Λ` are orthogonal when
`∑_a Ψ(a) = 0`, so `(AS_q)_* Λ ≅ (Λ ⊞ ℒ_Ψ) ⊞ M`
(`AlgebraicGeometry.Etale.exists_iso_artinSchreierPushforward_biprod`). Since `AS_q` is finite
and `AS_q ≫ π = π`, `Rπ_! (AS_q)_* Λ ≅ Rπ_! Λ`. After tensoring with `Λ(1)[2]`, the affine-line
trace identifies `Rπ_! Λ` with `Λ`, so that `Λ ≅ Λ ⊞ N` with `N` containing `Rπ_! ℒ_Ψ(1)[2]`
as a summand; on the stalks of the cohomology sheaves this forces `N = 0`, the stalks of `Λ`
being finite (`AlgebraicGeometry.Etale.isZero_of_iso_singleFunctor_unit_biprod`). The relative
statement over `T` follows by compact-support base change along `T ⟶ Spec 𝔽_p`.

## Blueprint

This is the vanishing `H^*_c(𝔸¹, ℒ_ψ) = 0` used in the proofs of
`lemma-fourier-transform-constant-sheaf` and `proposition-fourier-inversion` (blueprint
`lemma-fourier-transform-constant-sheaf`, `proposition-fourier-inversion`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Any two morphisms into `Spec 𝔽_p` agree: a ring map out of `ℤ/p` is unique. -/
lemma _root_.AlgebraicGeometry.Scheme.hom_ext_spec_ulift_zmod {p : ℕ} {X : Scheme.{u}}
    (f g : X ⟶ Spec (.of (ULift.{u} (ZMod p)))) : f = g := by
  refine ext_of_isAffine ?_
  rw [← cancel_epi (Scheme.ΓSpecIso (.of (ULift.{u} (ZMod p)))).inv]
  ext ⟨x⟩
  exact congrArg (· x) (RingHom.ext_zmod
    (((Scheme.ΓSpecIso _).inv ≫ f.appTop).hom.comp ULift.ringEquiv.symm.toRingHom)
    (((Scheme.ΓSpecIso _).inv ≫ g.appTop).hom.comp ULift.ringEquiv.symm.toRingHom))

section Cancellation

variable {Λ : Type (u + 1)} [CommRing Λ]

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

/-- Over a finite coefficient ring, the constant sheaf `Λ` cannot be split off from itself
non-trivially: `Λ_X ≅ Λ_X ⊞ G` forces `G = 0`, as is seen on the stalks, which are finite. -/
theorem isZero_of_iso_unit_biprod [Finite Λ] {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (e : 𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ≅ 𝟙_ _ ⊞ G) : IsZero G := by
  have : IsIso (0 : G ⟶ G) := Scheme.isIso_of_isIso_sheafFiber_map _ fun s ↦ by
    let Φ := (X.uliftPointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)
    have : Φ.Additive := (X.uliftPointSmallEtale s).sheafFiber_additive
    let e' : ModuleCat.of Λ Λ ≅ ModuleCat.of Λ Λ ⊞ Φ.obj G :=
      (sheafFiberUnitIso _ _).symm ≪≫ Φ.mapIso e ≪≫ Φ.mapBiprod _ _ ≪≫
        biprod.mapIso (sheafFiberUnitIso _ _) (Iso.refl _)
    have hc := Nat.card_congr (e' ≪≫ ModuleCat.biprodIsoProd _ _).toLinearEquiv.toEquiv
    rw [Nat.card_prod, eq_comm, Nat.mul_eq_left Nat.card_pos.ne'] at hc
    have : Finite (Φ.obj G) := Nat.finite_of_card_ne_zero (by rw [hc]; exact one_ne_zero)
    have : Subsingleton (Φ.obj G) := Finite.card_le_one_iff_subsingleton.mp hc.le
    have hz : IsZero (Φ.obj G) := ModuleCat.isZero_of_subsingleton _
    rw [Functor.map_zero]
    exact ⟨0, hz.eq_of_src _ _, hz.eq_of_src _ _⟩
  rw [IsZero.iff_id_eq_zero, ← IsIso.hom_inv_id (0 : G ⟶ G), zero_comp]

/-- Over a finite coefficient ring, `Λ_X ≅ Λ_X ⊞ N` in `D(X_ét, Λ)` forces `N = 0`: on the
cohomology sheaves this is `AlgebraicGeometry.Etale.isZero_of_iso_unit_biprod` in degree `0`,
and the cohomology of `Λ_X` vanishes in the other degrees. -/
theorem isZero_of_iso_singleFunctor_unit_biprod [Finite Λ] {X : Scheme.{u}}
    (N : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (e : (DerivedCategory.singleFunctor _ 0).obj (𝟙_ _) ≅
      (DerivedCategory.singleFunctor _ 0).obj (𝟙_ _) ⊞ N) : IsZero N := by
  refine DerivedCategory.isZero_of_forall_isZero_homology _ fun n ↦ ?_
  let H := DerivedCategory.homologyFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) n
  let e' := H.mapIso e ≪≫ H.mapBiprod _ _
  obtain rfl | hn := eq_or_ne n 0
  · let ε := (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).app (𝟙_ _)
    exact isZero_of_iso_unit_biprod _ (ε.symm ≪≫ e' ≪≫ biprod.mapIso ε (Iso.refl _))
  · have hz : IsZero (H.obj ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ _))) := by
      obtain h | h := hn.lt_or_gt
      · exact DerivedCategory.isZero_of_isGE _ 0 n h
      · exact DerivedCategory.isZero_of_isLE _ 0 n h
    exact IsZero.of_mono biprod.inr (hz.of_iso e'.symm)

variable (Λ) in
/-- Tensoring with a Tate twisting object and shifting reflects vanishing: the twisting objects
are tensor invertible, `Λ_X(d) ⊗ Λ_X(-d) ≅ Λ_X`. -/
theorem isZero_of_isZero_shift_derivedTensorRight_tateObject [HasTateTwist Λ] {X : Scheme.{u}}
    [HasInvertibleExponent Λ X]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (d a : ℤ)
    (h : IsZero ((shiftFunctor _ a).obj
      ((derivedTensorRight _ X (tateObject Λ X d)).obj K))) :
    IsZero K := by
  have h' : IsZero ((derivedTensorRight _ X (tateObject Λ X d)).obj K) :=
    ((shiftFunctor _ (-a)).map_isZero h).of_iso
      ((shiftFunctorCompIsoId _ a (-a) (add_neg_cancel a)).app _).symm
  let v : 𝟙_ (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (tateObject Λ X d)).obj
        (tateObject Λ X (-d)) :=
    (HasTateTwist.twistObjectZeroIso X).symm ≪≫ eqToIso (by rw [add_neg_cancel]) ≪≫
      (HasTateTwist.twistObjectAddIso X d (-d)).symm
  refine (((derivedTensor _ X).flip.obj (tateObject Λ X (-d))).map_isZero h').of_iso ?_
  exact (derivedTensorRightUnitor _ X K).symm ≪≫ ((derivedTensor _ X).obj K).mapIso v ≪≫
    (derivedTensorAssociator _ X K _ _).symm

end Cancellation

section AffineSpace

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The compactly supported cohomology of affine `d`-space, tensored with `Λ_S(d)` and shifted
by `2d`, is `Λ_S`: this is the affine-space trace
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_twistShift_affineSpace`, with the
twist moved out of `Rp_!` by the projection formula. -/
theorem nonempty_iso_shift_derivedTensorRight_rightDerivedLowerShriek_affineSpace [Finite Λ]
    [HasTateTwist Λ] [HasTateTwist.IsNormalized Λ] (n : Type u) [Fintype n] (S : Scheme.{u})
    [HasInvertibleExponent Λ S] :
    Nonempty ((shiftFunctor _ (2 * (Fintype.card n : ℤ))).obj
      ((derivedTensorRight _ S (tateObject Λ S (Fintype.card n))).obj
        ((R(𝔸(n; S) ↘ S)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ 𝔸(n; S)))) ≅
      constantComplex Λ S) := by
  obtain ⟨tr⟩ := nonempty_iso_rightDerivedLowerShriek_twistShift_affineSpace Λ n S
  obtain ⟨pf⟩ := nonempty_iso_rightDerivedLowerShriek_comp_derivedTensorRight
    (ModuleCat.{u + 1} Λ) (𝔸(n; S) ↘ S) (tateObject Λ S (Fintype.card n))
    (fun K ↦ hasProjectionFormula_of_finite Λ _ K _)
  exact ⟨(shiftFunctor _ _).mapIso (pf.app _ ≪≫ (R(𝔸(n; S) ↘ S)_![ModuleCat.{u + 1} Λ]).mapIso
    (((derivedTensor _ _).obj _).mapIso (leftDerivedUpperStarTateObjectIso _ _))) ≪≫
    (((R(𝔸(n; S) ↘ S)_![ModuleCat.{u + 1} Λ]).commShiftIso
      (2 * (Fintype.card n : ℤ))).app _).symm ≪≫ tr⟩

/-- For a finite morphism `f`, `Rg_!(f_* F) ≅ R(f ≫ g)_! F` on sheaves placed in degree `0`:
`f_*` is exact, so it is its own derived functor, which is `Rf_!` as `f` is proper, and the
composition law for `R(-)_!` applies. -/
theorem nonempty_iso_rightDerivedLowerShriek_singleFunctor_lowerStar [Finite Λ]
    {X Y S : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (g : Y ⟶ S) [HasCompactification g]
    [HasCompactification (f ≫ g)] [QuasiCompact (f ≫ g)]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Nonempty ((R(g)_![ModuleCat.{u + 1} Λ]).obj
        ((DerivedCategory.singleFunctor _ 0).obj ((f)_*[ModuleCat.{u + 1} Λ].obj F)) ≅
      (R(f ≫ g)_![ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.singleFunctor _ 0).obj F)) := by
  obtain ⟨c⟩ := nonempty_iso_rightDerivedLowerShriek_comp Λ f g
  obtain ⟨pf⟩ := nonempty_iso_rightDerivedLowerShriek_rightDerivedLowerStar
    (ModuleCat.{u + 1} Λ) f
  exact ⟨(R(g)_![ModuleCat.{u + 1} Λ]).mapIso
    ((((f)_*[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).symm.app F ≪≫
      (rightDerivedFunctorLowerStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) f).symm.app _ ≪≫
      pf.symm.app _) ≪≫ (c.app _).symm⟩

variable {Λ} in
/-- The isomorphism `Rf_! ≅ Rf'_!` induced by an equality `f = f'`. -/
lemma nonempty_rightDerivedLowerShriek_iso_of_eq {X Y : Scheme.{u}} {f f' : X ⟶ Y}
    [HasCompactification f] [HasCompactification f'] (h : f = f') :
    Nonempty (R(f)_![ModuleCat.{u + 1} Λ] ≅ R(f')_![ModuleCat.{u + 1} Λ]) := by
  subst h
  exact ⟨Iso.refl _⟩

end AffineSpace

section FiniteField

/-- The affine line `𝔸¹_k` over a field `k`. -/
local notation "𝔸¹[" k "]" => 𝔸(PUnit; Spec (CommRingCat.of k))

/-- The Artin–Schreier map `AS_q : 𝔸¹_k ⟶ 𝔸¹_k`, `x ↦ x ^ q - x`, where `q = #k`. -/
local notation "AS[" k "]" =>
  AffineSpace.artinSchreierMap PUnit (Spec (CommRingCat.of k)) (Fintype.card k)

set_option quotPrecheck false in
/-- The pushforward `(AS_q)_* Λ` of the constant sheaf along the Artin–Schreier map. -/
local notation "𝒫[" Λ ", " k "]" => (AS[k])_*[ModuleCat Λ].obj (𝟙_ _)

variable {Λ : Type (u + 1)} [CommRing Λ] {k : Type u} [Field k] [Fintype k]
  [Invertible (Fintype.card k : Λ)]

/-- On the image of `e_χ`, the idempotent `e_{χ'}` acts by the scalar
`q⁻¹ ∑_a χ'(-a) χ(a)`. -/
lemma image_ι_artinSchreierIdempotent_comp_artinSchreierIdempotent (χ χ' : AddChar k Λ) :
    image.ι (artinSchreierIdempotent χ) ≫ artinSchreierIdempotent χ' =
      (⅟(Fintype.card k : Λ) * ∑ a : k, χ' (-a) * χ a) •
        image.ι (artinSchreierIdempotent χ) := by
  rw [artinSchreierIdempotent.eq_1 χ', Preadditive.comp_sum, Finset.mul_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Linear.comp_smul, image_ι_artinSchreierIdempotent_comp_artinSchreierTranslationAction,
    smul_smul, mul_assoc]

attribute [local instance] Abelian.hasFiniteBiproducts in
/-- For a character `Ψ` with `∑_a Ψ(a) = 0`, the components `ℒ_1 ≅ Λ` and `ℒ_Ψ` split off from
`(AS_q)_* Λ` together: `(AS_q)_* Λ ≅ (Λ ⊞ ℒ_Ψ) ⊞ M` for some `M`, the idempotents `e_1` and
`e_Ψ` being orthogonal. -/
theorem exists_iso_artinSchreierPushforward_biprod (Ψ : AddChar k Λ)
    (hΨ : ∑ a : k, Ψ a = 0) :
    ∃ M, Nonempty (𝒫[Λ, k] ≅ (𝟙_ _ ⊞ artinSchreierSheaf Ψ) ⊞ M) := by
  obtain ⟨e₁⟩ := nonempty_iso_artinSchreierSheaf_one (Λ := Λ) (k := k)
  have hΨ' : ∑ a : k, Ψ (-a) = 0 := by
    rw [← hΨ]
    exact Fintype.sum_equiv (Equiv.neg k) _ _ fun _ ↦ rfl
  have h₁₂ : image.ι (artinSchreierIdempotent (1 : AddChar k Λ)) ≫
      factorThruImage (artinSchreierIdempotent Ψ) = 0 := by
    rw [← cancel_mono (image.ι (artinSchreierIdempotent Ψ)), Category.assoc, image.fac,
      image_ι_artinSchreierIdempotent_comp_artinSchreierIdempotent, zero_comp]
    simp [hΨ']
  have h₂₁ : image.ι (artinSchreierIdempotent Ψ) ≫
      factorThruImage (artinSchreierIdempotent (1 : AddChar k Λ)) = 0 := by
    rw [← cancel_mono (image.ι (artinSchreierIdempotent (1 : AddChar k Λ))), Category.assoc,
      image.fac, image_ι_artinSchreierIdempotent_comp_artinSchreierIdempotent, zero_comp]
    simp [hΨ]
  let s : 𝟙_ _ ⊞ artinSchreierSheaf Ψ ⟶ 𝒫[Λ, k] :=
    biprod.desc (e₁.inv ≫ image.ι (artinSchreierIdempotent (1 : AddChar k Λ)))
      (image.ι (artinSchreierIdempotent Ψ))
  let r : 𝒫[Λ, k] ⟶ 𝟙_ _ ⊞ artinSchreierSheaf Ψ :=
    biprod.lift (factorThruImage (artinSchreierIdempotent (1 : AddChar k Λ)) ≫ e₁.hom)
      (factorThruImage (artinSchreierIdempotent Ψ))
  have : IsSplitMono s := IsSplitMono.mk' ⟨r, by
    refine biprod.hom_ext' _ _ (biprod.hom_ext _ _ ?_ ?_) (biprod.hom_ext _ _ ?_ ?_) <;>
      simp [s, r, h₁₂, reassoc_of% h₂₁, artinSchreierSheaf]⟩
  exact ⟨cokernel s, ⟨biprod.uniqueUpToIso _ _
    (isBilimitBinaryBiconeOfIsSplitMonoOfCokernel (cokernelIsCokernel s))⟩⟩

attribute [local instance] Abelian.hasFiniteBiproducts
  preservesBinaryBiproducts_of_preservesBiproducts in
/-- **Vanishing of `H^*_c(𝔸¹_k, ℒ_Ψ)`.** For a character `Ψ` of the finite field `k` with
`∑_a Ψ(a) = 0`, the compactly supported direct image of `ℒ_Ψ` along `π : 𝔸¹_k ⟶ Spec k`
vanishes. Write `G(K) = (Rπ_! K ⊗ Λ(1))[2]`. By the splitting `(AS_q)_* Λ ≅ (Λ ⊞ ℒ_Ψ) ⊞ M`
and `Rπ_! (AS_q)_* Λ ≅ R(AS_q ≫ π)_! Λ = Rπ_! Λ`, one gets `G(Λ) ≅ G(Λ) ⊞ G(ℒ_Ψ) ⊞ G(M)`, and
`G(Λ) ≅ Λ` by the affine-line trace; so `G(ℒ_Ψ) = 0`, whence `Rπ_! ℒ_Ψ = 0`, the twists being
invertible. -/
theorem isZero_rightDerivedLowerShriek_artinSchreierSheaf [Finite Λ] [HasTateTwist Λ]
    [HasTateTwist.IsNormalized Λ] [HasInvertibleExponent Λ (Spec (.of k))]
    (Ψ : AddChar k Λ) (hΨ : ∑ a : k, Ψ a = 0) :
    IsZero ((R(𝔸¹[k] ↘ Spec (.of k))_![ModuleCat.{u + 1} Λ]).obj
      ((DerivedCategory.singleFunctor _ 0).obj (artinSchreierSheaf Ψ))) := by
  obtain ⟨M, ⟨e⟩⟩ := exists_iso_artinSchreierPushforward_biprod Ψ hΨ
  let d : ℤ := Fintype.card PUnit.{u + 1}
  have : (derivedTensorRight _ (Spec (.of k)) (tateObject Λ (Spec (.of k)) d)).Additive :=
    inferInstanceAs ((derivedTensor _ _).flip.obj _).Additive
  -- `H(K) = (K ⊗ Λ(1))[2]` and `G(F) = H(Rπ_! F)`
  let H := derivedTensorRight _ (Spec (.of k)) (tateObject Λ (Spec (.of k)) d) ⋙
    shiftFunctor (DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ))) (2 * d)
  let G := DerivedCategory.singleFunctor
    (Sheaf 𝔸¹[k].smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0 ⋙
      R(𝔸¹[k] ↘ Spec (.of k))_![ModuleCat.{u + 1} Λ] ⋙ H
  obtain ⟨tr⟩ := nonempty_iso_shift_derivedTensorRight_rightDerivedLowerShriek_affineSpace Λ
    PUnit.{u + 1} (Spec (.of k))
  let hA : G.obj (𝟙_ _) ≅ (DerivedCategory.singleFunctor _ 0).obj (𝟙_ _) :=
    H.mapIso ((R(𝔸¹[k] ↘ Spec (.of k))_![ModuleCat.{u + 1} Λ]).mapIso
      (constantComplexIsoSingleFunctor Λ _).symm) ≪≫ tr ≪≫ constantComplexIsoSingleFunctor Λ _
  have : HasCompactification (AS[k] ≫ 𝔸¹[k] ↘ Spec (.of k)) :=
    .of_eq (AffineSpace.artinSchreierMap_over _ _ _).symm
  obtain ⟨as⟩ := nonempty_iso_rightDerivedLowerShriek_singleFunctor_lowerStar Λ AS[k]
    (𝔸¹[k] ↘ Spec (.of k)) (𝟙_ _)
  obtain ⟨cc⟩ := nonempty_rightDerivedLowerShriek_iso_of_eq (Λ := Λ)
    (AffineSpace.artinSchreierMap_over PUnit (Spec (.of k)) (Fintype.card k))
  obtain ⟨eU⟩ := G.nonempty_iso_biprod_of_iso_biprod e (H.mapIso (as ≪≫ cc.app _) ≪≫ hA) hA
  exact isZero_of_isZero_shift_derivedTensorRight_tateObject Λ _ d (2 * d)
    (IsZero.of_mono biprod.inl (isZero_of_iso_singleFunctor_unit_biprod _ eU))

end FiniteField

section ZMod

variable (Λ : Type (u + 1)) [CommRing Λ] {p : ℕ} [Fact p.Prime]

/-- The exponent of `Λ` is invertible on `𝔽_p` as soon as it is invertible on some scheme of
characteristic `p`. -/
lemma hasInvertibleExponent_spec_ulift_zmod {X : Scheme.{u}} [CharP Γ(X, ⊤) p]
    [HasInvertibleExponent Λ X] :
    HasInvertibleExponent Λ (Spec (.of (ULift.{u} (ZMod p)))) := by
  obtain ⟨n, hn, hΛ, hu⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ) (X := X)
  refine ⟨n, hn, hΛ, ?_⟩
  have hn' : (n : ZMod p) ≠ 0 := by
    intro h0
    rw [ZMod.natCast_eq_zero_iff] at h0
    rw [(CharP.cast_eq_zero_iff Γ(X, ⊤) p n).2 h0] at hu
    have : Nontrivial Γ(X, ⊤) :=
      CharP.nontrivial_of_char_ne_one (Fact.out : p.Prime).one_lt.ne'
    exact not_isUnit_zero hu
  have : IsUnit (n : ULift.{u} (ZMod p)) := by
    rw [isUnit_iff_ne_zero]
    intro h0
    exact hn' (by simpa using congrArg ULift.down h0)
  simpa using this.map (Scheme.ΓSpecIso (.of (ULift.{u} (ZMod p)))).inv.hom

end ZMod

variable (Λ : Type (u + 1)) [CommRing Λ] {p : ℕ} [Fact p.Prime] [Invertible (p : Λ)]

/-- **Vanishing of the compactly supported cohomology of `ℒ_ψ` on the affine line.** For a
scheme `T` of characteristic `p`, a finite coefficient ring `Λ` whose exponent is invertible on
`T`, and an additive character `Ψ` of `𝔽_p` with `Ψ(1) - 1` a unit of `Λ`, the compactly
supported direct image of the Artin–Schreier sheaf `ℒ_{Ψ, x}` of the coordinate along
`π : 𝔸¹_T ⟶ T` vanishes.
(sketch blueprint: `lemma-fourier-transform-constant-sheaf`, proof) -/
theorem isZero_rightDerivedLowerShriek_artinSchreierSheafZMod_coord [Finite Λ] [HasTateTwist Λ]
    [HasTateTwist.IsNormalized Λ] (T : Scheme.{u}) [HasInvertibleExponent Λ T]
    [CharP Γ(𝔸(PUnit.{u + 1}; T), ⊤) p] (Ψ : AddChar (ZMod p) Λ) (hΨ : IsUnit (Ψ 1 - 1)) :
    IsZero ((R(𝔸(PUnit.{u + 1}; T) ↘ T)_![ModuleCat.{u + 1} Λ]).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        (artinSchreierSheafZMod 𝔸(PUnit.{u + 1}; T) Ψ (AffineSpace.coord T PUnit.unit)))) := by
  -- `ℒ_{Ψ, x}` is the pullback of `ℒ_Ψ` on `𝔸¹_{𝔽_p}` along `𝔸¹_T ⟶ 𝔸¹_{𝔽_p}`, so this is
  -- the case `T = Spec 𝔽_p` by compact-support base change
  let := 𝔸(PUnit.{u + 1}; T).overSpecZModOfCharP p
  let k := ULift.{u} (ZMod p)
  have : HasInvertibleExponent Λ 𝔸(PUnit.{u + 1}; T) := .of_hom (𝔸(PUnit.{u + 1}; T) ↘ T)
  have := hasInvertibleExponent_spec_ulift_zmod Λ (p := p) (X := 𝔸(PUnit.{u + 1}; T))
  let Ψ' : AddChar k Λ := Ψ.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom
  have hΨ' : ∑ a : k, Ψ' a = 0 := by
    rw [← AddChar.sum_eq_zero_of_isUnit_sub_one hΨ]
    exact Fintype.sum_equiv Equiv.ulift _ _ fun _ ↦ rfl
  let h : T ⟶ Spec (.of k) :=
    AffineSpace.zeroSection PUnit T ≫ (𝔸(PUnit.{u + 1}; T) ↘ Spec (.of k))
  have hmap : AffineSpace.homOfVector (𝔸(PUnit.{u + 1}; T) ↘ Spec (.of k))
      (fun _ ↦ AffineSpace.coord T PUnit.unit) = AffineSpace.map PUnit h :=
    AffineSpace.hom_ext (Scheme.hom_ext_spec_ulift_zmod _ _) fun ⟨⟩ ↦ by simp
  let eL : artinSchreierSheafZMod 𝔸(PUnit.{u + 1}; T) Ψ (AffineSpace.coord T PUnit.unit) ≅
      (AffineSpace.map PUnit h)^*[ModuleCat.{u + 1} Λ].obj (artinSchreierSheaf Ψ') :=
    eqToIso (by rw [artinSchreierSheafZMod, artinSchreierSheafOf, hmap])
  have sq := AffineSpace.isPullback_map (n := PUnit.{u + 1}) h
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  obtain ⟨es⟩ := nonempty_iso_leftDerivedUpperStar_singleFunctor Λ (AffineSpace.map PUnit h)
    (artinSchreierSheaf Ψ') _ (Iso.refl _)
  refine (((L((h)^*[ModuleCat.{u + 1} Λ])).map_isZero
    (isZero_rightDerivedLowerShriek_artinSchreierSheaf Ψ' hΨ')).of_iso ?_)
  exact (R(𝔸(PUnit.{u + 1}; T) ↘ T)_![ModuleCat.{u + 1} Λ]).mapIso
    ((DerivedCategory.singleFunctor _ 0).mapIso eL ≪≫ es.symm) ≪≫
      (asIso (rightDerivedLowerShriekBaseChangeMap Λ sq)).symm.app _

end AlgebraicGeometry.Etale
