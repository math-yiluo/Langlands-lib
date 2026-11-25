/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineAcyclicDVR
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineAcyclicStrictlyLocal
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineAcyclicityStalk
public import WeilConjectures.EtaleCohomology.Purity.Smooth.GmRelativeKummer
public import WeilConjectures.EtaleCohomology.TateTwist.AffineLineDescentKummer
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula
public import WeilConjectures.ConstructibleSheaf.Pullback

/-!
# Acyclicity of the affine line over an arbitrary base

For every scheme `S` on which the exponent of the finite coefficient ring `Λ` is invertible, the
unit `Λ_S(1) ⟶ Rp_* Lp^* Λ_S(1)` of the projection `p : 𝔸¹_S ⟶ S` is an isomorphism
(`AlgebraicGeometry.Etale.isIso_unit_tateObject_affineLine_of_strictlyHenselian`; SGA 4 XV 2.2,
Milne, *Étale cohomology*, VI.4, Fu, *Étale cohomology theory*, 7.7).

## The argument

The question is local for the geometric points `s̄ : Spec Ω ⟶ S`
(`AlgebraicGeometry.Etale.isIso_of_isIso_leftDerivedUpperStar_algClosurePoint_map`). Over the
algebraically closed field `Ω` the unit is an isomorphism
(`AlgebraicGeometry.Etale.isIso_unit_tateObject_affineLine`), so it suffices that the derived
base change map of `p` along `s̄` is an isomorphism at `Lp^* Λ_S(1) = p^* L[0]`, `L` the locally
constant sheaf underlying `Λ_S(1)`. On the cohomology sheaves this base change map is checked on
the geometric stalks, where it is the pullback map `Hᵠ(𝔸¹_A, F) ⟶ Hᵠ(𝔸¹_B, F)` along a local
homomorphism `A ⟶ B` of strictly henselian local rings
(`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_affineLine_of_strictLocal`), with
`F = p_A^* M` for the locally constant sheaf `M = L|_{Spec A}`.

The bijectivity of these pullback maps is the strictly henselian case of the acyclicity of the
affine line (`AlgebraicGeometry.Etale.bijective_cohomologyMap_affineLine_of_strictlyHenselian`),
the one input which is not proved here.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

attribute [local instance] neZero_ringChar_of_finite

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- **Acyclicity of the affine line over strictly henselian local rings, in the form of
invariance under local homomorphisms.** Let `φ : A ⟶ B` be a local homomorphism of strictly
henselian local rings, `Λ` a finite coefficient ring whose exponent is invertible on `A`, and
`M` a locally constant sheaf of `Λ`-modules on `Spec A`. Then the pullback map
`Hᵠ(𝔸¹_A, p_A^* M) ⟶ Hᵠ(𝔸¹_B, p_A^* M|)` along `𝔸¹_B ⟶ 𝔸¹_A` is bijective for every `q`.

This is SGA 4 XV 2.1–2.2 (Milne, *Étale cohomology*, VI.4.20; Fu, *Étale cohomology theory*,
7.7.4): over a strictly henselian local ring `R` with residue characteristic prime to the
exponent of `Λ`, `Hᵠ(𝔸¹_R, p_R^* M) = 0` for `q > 0` and `H⁰(𝔸¹_R, p_R^* M) = M(R)`; for `R = A`
and `R = B` both sides of the map are the stalk of `M` at the closed point, and the map is the
identity of it. It is the strictly henselian case of
`AlgebraicGeometry.Etale.isIso_unit_tateObject_affineLine_of_strictlyHenselian`, and the one
input of it which is not proved in the repository (where the acyclicity is proved over fields,
`AlgebraicGeometry.Etale.isIso_unit_tateObject_affineLine_of_field`). The classical proof
compactifies `𝔸¹_R ⊆ ℙ¹_R`, uses proper base change for `ℙ¹_R`
(`AlgebraicGeometry.Etale.bijective_cohomologyMap_projectiveLine_residueField`) and computes the
local cohomology along the section at infinity by Kummer theory over the henselisation of `ℙ¹_R`
along it. -/
theorem bijective_cohomologyMap_affineLine_of_strictlyHenselian
    {A B : Type u} [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)] [CommRing B] [HenselianLocalRing B]
    [IsSepClosed (IsLocalRing.ResidueField B)] (φ : A →+* B) [IsLocalHom φ]
    [HasInvertibleExponent Λ (Spec (.of A))]
    (M : Sheaf (Spec (.of A)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsLocallyConstantSheaf M] (q : ℕ) :
    Function.Bijective (cohomologyMap
      (AffineSpace.map (ULift.{u} (Fin 1)) (Spec.map (CommRingCat.ofHom φ)))
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((𝔸(ULift.{u} (Fin 1); Spec (.of A)) ↘ Spec (.of A))^*[ModuleCat.{u + 1} Λ].obj M)) q) := by
  exact bijective_cohomologyMap_affineLine_of_strictlyHenselian_of_affineLineAcyclicAt Λ
    (fun A _ _ _ _ ↦ affineLineAcyclicAt_of_isDiscreteValuationRing Λ A) φ M q

/-- The exchange morphism of the affine line `p : 𝔸¹_S ⟶ S` along any `g : T ⟶ S` is an
isomorphism in every degree at the pullback `p^* L` of a locally constant sheaf `L` of
`Λ`-modules on `S`: by
`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_affineLine_of_strictLocal`
this reduces to `AlgebraicGeometry.Etale.bijective_cohomologyMap_affineLine_of_strictlyHenselian`.
-/
theorem isIso_baseChangeHomologyMap_affineLine_upperStar {S T X' : Scheme.{u}}
    [HasInvertibleExponent Λ S] {g : T ⟶ S} {f' : X' ⟶ T} {g' : X' ⟶ 𝔸(ULift.{u} (Fin 1); S)}
    (sq : IsPullback g' f' (𝔸(ULift.{u} (Fin 1); S) ↘ S) g)
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsLocallyConstantSheaf L] (q : ℤ) :
    IsIso (baseChangeHomologyMap Λ sq q
      ((𝔸(ULift.{u} (Fin 1); S) ↘ S)^*[ModuleCat.{u + 1} Λ].obj L)) := by
  obtain hq | hq := lt_or_ge q 0
  · exact isIso_baseChangeHomologyMap_of_neg Λ sq hq _
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hq
  refine isIso_baseChangeHomologyMap_affineLine_of_strictLocal Λ sq _ q
    fun A B _ _ _ _ _ _ φ _ j ↦ ?_
  have : HasInvertibleExponent Λ (Spec (.of A)) := .of_hom j
  have := IsLocallyConstantSheaf.upperStar j L
  refine bijective_cohomologyMap_of_iso
    (AffineSpace.map (ULift.{u} (Fin 1)) (Spec.map (CommRingCat.ofHom φ))) ((sheafCompose _
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).mapIso
      (((upperStarComp _ (𝔸(ULift.{u} (Fin 1); Spec (.of A)) ↘ Spec (.of A)) j _
        (AffineSpace.map_over j)).app L).symm ≪≫
      (upperStarComp _ (AffineSpace.map (ULift.{u} (Fin 1)) j)
        (𝔸(ULift.{u} (Fin 1); S) ↘ S)).app L)) q ?_
  exact bijective_cohomologyMap_affineLine_of_strictlyHenselian Λ φ _ q

variable [HasTateTwist Λ]

/-- **Homotopy invariance of the affine line over an arbitrary base**, for the coefficients
`Λ(1)`: for every scheme `S` on which the exponent of `Λ` is invertible, the unit
`Λ_S(1) ⟶ Rp_* Lp^* Λ_S(1)` of the projection `p : 𝔸¹_S ⟶ S` is an isomorphism.

It is checked after pullback to the geometric points `s̄ : Spec Ω ⟶ S`: over `Ω` the unit is an
isomorphism (`AlgebraicGeometry.Etale.isIso_unit_tateObject_affineLine`), and the derived base
change map of `p` along `s̄` is an isomorphism at `Lp^* Λ_S(1)`
(`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_affineLine_upperStar`). -/
theorem isIso_unit_tateObject_affineLine_of_strictlyHenselian (S : Scheme.{u})
    [HasInvertibleExponent Λ S] :
    IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      (𝔸(ULift.{u} (Fin 1); S) ↘ S)).unit.app (tateObject Λ S 1)) := by
  obtain ⟨L, hL, -, ⟨eL⟩⟩ := HasTateTwist.exists_isLocallyConstantSheaf_twistObject (Λ := Λ) S 1
  refine isIso_of_isIso_leftDerivedUpperStar_algClosurePoint_map Λ _ fun s ↦ ?_
  rw [_root_.DerivedCategory.isIso_iff]
  intro n
  have : HasInvertibleExponent Λ (Spec (.of (AlgebraicClosure (S.residueField s)))) :=
    .of_hom (S.algClosurePoint s)
  have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); S) := .of_hom (𝔸(ULift.{u} (Fin 1); S) ↘ S)
  let sq := AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) (S.algClosurePoint s)
  have hBC : IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
      ((L((𝔸(ULift.{u} (Fin 1); S) ↘ S)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ S 1))) := by
    refine (NatTrans.isIso_app_iff_of_iso _
      ((L((𝔸(ULift.{u} (Fin 1); S) ↘ S)^*[ModuleCat.{u + 1} Λ])).mapIso eL ≪≫
        (singleFunctorCompLeftDerivedUpperStarIso _ (𝔸(ULift.{u} (Fin 1); S) ↘ S)).app L)).2 ?_
    refine (isIso_derivedBaseChangeMap_app_ι_obj_iff (ModuleCat.{u + 1} Λ) sq.toCommSq
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((𝔸(ULift.{u} (Fin 1); S) ↘ S)^*[ModuleCat.{u + 1} Λ].obj L))).2 ?_
    rw [← baseChange_eq_derivedBaseChangeMapPlus]
    exact (isIso_baseChange_app_singleFunctor_obj_iff Λ sq _).2 fun q ↦
      isIso_baseChangeHomologyMap_affineLine_upperStar Λ sq L q
  have : IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      (𝔸(ULift.{u} (Fin 1); Spec (.of (AlgebraicClosure (S.residueField s)))) ↘
        Spec (.of (AlgebraicClosure (S.residueField s))))).unit.app
      (tateObject Λ (Spec (.of (AlgebraicClosure (S.residueField s)))) 1)) := by
    obtain ⟨LT, -, hLT, ⟨eT⟩⟩ := HasTateTwist.exists_isLocallyConstantSheaf_twistObject (Λ := Λ)
      (Spec (.of (AlgebraicClosure (S.residueField s)))) 1
    exact isIso_unit_affineLine_of_cohomology Λ (𝟙 _)
      (isZero_cohomology_affineLine Λ (k := AlgebraicClosure (S.residueField s)))
      (nonempty_iso_cohomology_zero_affineLine Λ (k := AlgebraicClosure (S.residueField s))).some
      (boundedConstructibleFiniteTor_tateObject Λ _ 1) eT hLT
  exact isIso_homology_map_leftDerivedUpperStar_unit_app Λ sq.toCommSq _
    (leftDerivedUpperStarTateObjectIso (S.algClosurePoint s) 1) n hBC inferInstance

end Etale

end AlgebraicGeometry
