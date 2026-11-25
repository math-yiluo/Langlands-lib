/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.AlgebraicGeometry.TorIndependentPerfectTensorBaseChange
public import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeNaturality
public import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeCoordinateNaturality
public import WeilConjectures.AlgebraicGeometry.FlatPullbackTorIndependent
public import WeilConjectures.AlgebraicGeometry.PseudoCoherentSupportAnnihilation

/-!
# The derived base change map is invertible for flat base change

Consider a cartesian square of schemes
```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```
with `S`, `S'` affine, `f` quasi-compact and quasi-separated and `g` flat. Then the canonical
base change map `Lg^* Rf_* E ⟶ Rf'_* Lg'^* E` is an isomorphism for every `E ∈ D_QCoh(𝒪_X)`
(Stacks 08IB, 02KH).

The square is Tor-independent since `g` is flat
(`AlgebraicGeometry.flat_right_pullback_torIndependent`), so this is the case `P = 𝒪_X` of
`AlgebraicGeometry.torIndependent_perfect_tensor_baseChange`, transported to an arbitrary
cartesian square by `AlgebraicGeometry.exists_derivedBaseChange_coordinate_naturality`.
-/

@[expose] public section

universe w u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

/-- A quasi-coherent module placed in degree `0` has quasi-coherent cohomology sheaves. -/
theorem schemeDerivedQCohProperty_singleFunctor {X : Scheme.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (ℱ : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] :
    schemeDerivedQCohProperty X ((DerivedCategory.singleFunctor _ 0).obj ℱ) := by
  have hM : SheafOfModules.IsQuasicoherent (R := moduleRings X.toRingedSpace) ℱ := ‹_›
  have hzero : IsZero
      (SheafOfModules.free (R := moduleRings X.toRingedSpace) PEmpty.{u + 1}) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply (SheafOfModules.freeHomEquiv _).injective
    funext i
    exact PEmpty.elim i
  have : (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).ContainsZero :=
    ⟨⟨_, hzero, SheafOfModules.isQuasicoherent_free PEmpty.{u + 1}⟩⟩
  intro i
  by_cases hi : i = 0
  · subst i
    exact (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).app ℱ).symm hM
  · apply (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_isZero
    rcases lt_or_gt_of_ne hi with hi | hi
    · exact DerivedCategory.isZero_of_isGE _ 0 i hi
    · exact DerivedCategory.isZero_of_isLE _ 0 i hi

/-- Flat base change for the chosen pullback square of `f` and `g`: the case `P = 𝒪_X` of
`torIndependent_perfect_tensor_baseChange`. Source: Stacks Project, Tags 08IB and 02KH. -/
theorem isIso_schemeDerivedBaseChangeMap_of_flat_pullback
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S S' : Scheme.{u}} [IsAffine S] [IsAffine S']
    (f : X ⟶ S) (g : S' ⟶ S) [QuasiCompact f] [QuasiSeparated f] [Flat g]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (E : schemeDerivedCategory X) (hE : schemeDerivedQCohProperty X E) :
    IsIso (schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
      pullback.condition E) := by
  have h := torIndependent_perfect_tensor_baseChange f g
    (flat_right_pullback_torIndependent f g) (𝟙_ _) E (isPerfect_tensorUnit X) hE
  have hn := schemeDerivedBaseChangeMap_naturality f (pullback.snd f g) g
    (pullback.fst f g) pullback.condition (λ_ E).hom
  have hc : IsIso ((schemeDerivedDirectImage f ⋙ derivedPullback g).map (λ_ E).hom ≫
      schemeDerivedBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
        pullback.condition E) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((schemeDerivedDirectImage f ⋙ derivedPullback g).map (λ_ E).hom) _

/-- **Flat base change, sheaf form** (Stacks 02KH). For a cartesian square with `S`, `S'` affine,
`f` quasi-compact and quasi-separated and `g` flat, the canonical base change map
`Lg^* Rf_* E ⟶ Rf'_* Lg'^* E` is an isomorphism for every `E ∈ D_QCoh(𝒪_X)`. -/
theorem isIso_schemeDerivedBaseChangeMap_of_flat
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}} [IsAffine S] [IsAffine S']
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X) (sq : IsPullback g' f' f g)
    [QuasiCompact f] [QuasiSeparated f] [Flat g]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (E : schemeDerivedCategory X) (hE : schemeDerivedQCohProperty X E) :
    IsIso (schemeDerivedBaseChangeMap f f' g g' sq.w E) := by
  obtain ⟨e, -, -, j, k, a, h⟩ :=
    exists_derivedBaseChange_coordinate_naturality f g g' f' sq (Iso.refl S) (Iso.refl S')
  have hA := isIso_schemeDerivedBaseChangeMap_of_flat_pullback
    (f ≫ (Iso.refl S).hom) ((Iso.refl S').inv ≫ g ≫ (Iso.refl S).hom) E hE
  have hc : IsIso (schemeDerivedBaseChangeMap f f' g g' sq.w E ≫
      k.hom.app ((derivedPullback g').obj E) ≫
        (schemeDerivedDirectImage (Iso.refl S').inv).map
          ((schemeDerivedDirectImage _).map (j.hom.app E))) := by
    rw [h E]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (k.hom.app ((derivedPullback g').obj E) ≫
    (schemeDerivedDirectImage (Iso.refl S').inv).map
      ((schemeDerivedDirectImage _).map (j.hom.app E)))

end AlgebraicGeometry
