/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.GmRelativeKummer
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FieldExtensionBaseChange
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
public import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnboundedPlus
public import WeilConjectures.SixFunctors.BaseChange.EtaleDerived
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.Local
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.SixFunctors.Etale.Derived.AdjunctionShift
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.FiniteEtaleAdjoint
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom
public import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSectionComplement

/-!
# Descent of the computations on `𝔸¹` and `𝔾ₘ` with `Λ(1)`-coefficients

The vanishing clauses (a) and (c) of blueprint `sk-prop-a1-kummer` for the twist
`Λ(1) = μₙ ⊗ Λ`, over a base `B` separated and locally of finite type over an arbitrary field
`k`: with `p : 𝔸¹_B ⟶ B` and `j : 𝔾_{m,B} ⟶ 𝔸¹_B` the basic open of the coordinate,

* `R^n p_* Λ(1) = 0` for `n > 0`
  (`AlgebraicGeometry.Etale.isZero_homology_rightDerivedLowerStar_tateObject_affineLine_of_field`);
* `R^n p_* Rj_* j^* Λ(1) = 0` for `n ≥ 2`
  (`AlgebraicGeometry.Etale.isZero_homology_rightDerivedLowerStar_tateObject_basicOpen_of_field`).

Over an algebraically closed field and for `B` quasi-compact, these are proved in
`WeilConjectures.EtaleCohomology.Purity.Smooth.GmRelativeKummer`. The quasi-compactness is
removed by étale base change to the affine opens of `B`, and the field is made algebraically
closed by base change along the field extension `k ⊆ k̄`
(`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_fieldExtension`), along which the
vanishing of cohomology sheaves descends since `B ×_k k̄ ⟶ B` is surjective.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [NeZero (ringChar Λ)]

section BaseChange

variable {X Y X' Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The unbounded derived base change map of a commutative square is an isomorphism at the Tate
twist `Λ_X(m)` as soon as the bounded below one is an isomorphism at every sheaf placed in
degree zero: `Λ_X(m)` is a sheaf placed in degree zero. -/
lemma isIso_derivedBaseChangeMap_app_tateObject_of_singleFunctor [HasInvertibleExponent Λ X]
    (sq : CommSq g' f' f g)
    (h : ∀ F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      IsIso ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) (m : ℤ) :
    IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq).app (tateObject Λ X m)) :=
  (NatTrans.isIso_app_iff_of_iso _ (tateTwistObjectIsoSingleFunctor Λ X m)).2
    ((isIso_derivedBaseChangeMap_app_ι_obj_iff (ModuleCat.{u + 1} Λ) sq _).2 (h _))

/-- Étale base change: the derived base change map of a cartesian square along an étale
morphism is an isomorphism at the Tate twist `Λ_X(m)`. -/
lemma isIso_derivedBaseChangeMap_app_tateObject_of_etale [HasInvertibleExponent Λ X]
    (sq : IsPullback g' f' f g) [AlgebraicGeometry.Etale g] (m : ℤ) :
    IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app (tateObject Λ X m)) :=
  have := Etale.isIso_derivedBaseChangeMapPlus_of_etale Λ sq
  isIso_derivedBaseChangeMap_app_tateObject_of_singleFunctor Λ sq.toCommSq
    (fun _ ↦ inferInstance) m

/-- Base change along a field extension: for a scheme `Y` over a field `K` on which the
exponent of `Λ` is invertible, its base change `Y' = Y ×_K L` to a field extension `L` and a
quasi-compact quasi-separated `f : X ⟶ Y` with base change `f' : X' ⟶ Y'`, the derived base
change map is an isomorphism at the Tate twist `Λ_X(m)`. -/
lemma isIso_derivedBaseChangeMap_app_tateObject_of_fieldExtension {K L : Type u} [Field K]
    [Field L] [Algebra K L] [HasInvertibleExponent Λ (Spec (.of K))] [HasInvertibleExponent Λ X]
    (σ : Y ⟶ Spec (.of K)) (σ' : Y' ⟶ Spec (.of L))
    (hY : IsPullback g σ' σ (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    [QuasiCompact f] [QuasiSeparated f] (sq : IsPullback g' f' f g) (m : ℤ) :
    IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app (tateObject Λ X m)) := by
  obtain ⟨n, hn, hΛ, hu⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ)
    (X := Spec (.of K))
  refine isIso_derivedBaseChangeMap_app_tateObject_of_singleFunctor Λ sq.toCommSq (fun F ↦ ?_) m
  have : Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of K)) F :=
    Scheme.IsTorsionSheafOfInvertibleOrder.of_natCast_eq_zero Λ n hn.ne' hΛ hu F
  have h := (Etale.isIso_baseChange_app_singleFunctor_obj_iff Λ sq F).2 fun q ↦
    Etale.isIso_baseChangeHomologyMap_of_fieldExtension Λ σ f g σ' hY sq q F
  rwa [Etale.baseChange_eq_derivedBaseChangeMapPlus] at h

end BaseChange

/-- Every point of a scheme lies in the image of the inclusion of some affine open. -/
theorem _root_.AlgebraicGeometry.Scheme.exists_affineOpens_ι_eq (Y : Scheme.{u}) (x : Y) :
    ∃ (V : Y.affineOpens) (y : V.1), V.1.ι y = x := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact ⟨⟨V, hV⟩, ⟨x, hx⟩, rfl⟩

/-- The Tate twist `Λ_X(m)` is concentrated in degree zero, so it lies in `D^{≤ 0}`. -/
instance isLE_tateObject (X : Scheme.{u}) [HasInvertibleExponent Λ X]
    (m : ℤ) : (tateObject Λ X m).IsLE 0 :=
  DerivedCategory.TStructure.t.isLE_of_iso (tateTwistObjectIsoSingleFunctor Λ X m).symm 0

section AlgClosed

variable [Finite Λ] {k : Type u} [Field k] [IsAlgClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))] {Y : Scheme.{u}} (aY : Y ⟶ Spec (.of k))
  [IsSeparated aY] [LocallyOfFiniteType aY] [HasInvertibleExponent Λ Y]

include aY in
/-- Over an algebraically closed field and without quasi-compactness assumption on `Y`, the
higher direct images `R^n p_* Λ(1)` of the projection `p : 𝔸¹_Y ⟶ Y` vanish for `n > 0`: by
étale base change this may be checked on the affine opens `V` of `Y`, where it is
`AlgebraicGeometry.Etale.isIso_unit_tateObject_affineLine`. -/
theorem isZero_homology_rightDerivedLowerStar_tateObject_affineLine_of_isAlgClosed (n : ℤ)
    (hn : 0 < n) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
      ((R((𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_*[ModuleCat.{u + 1} Λ])).obj
        (tateObject Λ 𝔸(ULift.{u} (Fin 1); Y) 1))) := by
  refine isZero_homology_of_jointlySurjective Λ (fun V : Y.affineOpens ↦ V.1.ι)
    (fun x ↦ ?_) _ n fun V ↦ ?_
  · exact Y.exists_affineOpens_ι_eq x
  have : IsAffine V.1 := V.2
  have : QuasiCompact (V.1.ι ≫ aY) := inferInstance
  have : HasInvertibleExponent Λ V.1 := .of_hom V.1.ι
  have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); V.1) :=
    .of_hom (𝔸(ULift.{u} (Fin 1); V.1) ↘ V.1)
  let sq := AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) V.1.ι
  have := isIso_derivedBaseChangeMap_app_tateObject_of_etale Λ sq 1
  have hu := isIso_unit_tateObject_affineLine Λ (V.1.ι ≫ aY)
  refine (DerivedCategory.isZero_of_isLE (tateObject Λ V.1 1) 0 n hn).of_iso
    ((_root_.DerivedCategory.homologyFunctor _ n).mapIso ?_)
  exact asIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app _) ≪≫
    (R((𝔸(ULift.{u} (Fin 1); V.1) ↘ V.1)_*[ModuleCat.{u + 1} Λ])).mapIso
      (leftDerivedUpperStarTateObjectIso _ 1 ≪≫ (leftDerivedUpperStarTateObjectIso _ 1).symm) ≪≫
    (asIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      (𝔸(ULift.{u} (Fin 1); V.1) ↘ V.1)).unit.app (tateObject Λ V.1 1))).symm

include aY in
/-- Over an algebraically closed field and without quasi-compactness assumption on `Y`: for an
open immersion `j : G ⟶ 𝔸¹_Y` onto the complement of the zero section and `π = j ≫ p`,
`R^n π_* Λ(1) = 0` for `n ∉ {0, 1}`. By étale base change this may be checked on the affine
opens of `Y`, where it is
`AlgebraicGeometry.Etale.isZero_homology_rightDerivedLowerStar_tateObject_multiplicativeGroup`. -/
theorem isZero_homology_rightDerivedLowerStar_tateObject_multiplicativeGroup_of_isAlgClosed
    {G : Scheme.{u}} (j : G ⟶ 𝔸(ULift.{u} (Fin 1); Y)) [IsOpenImmersion j]
    (hj : Set.range j.base =
      (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y).base)ᶜ)
    [HasInvertibleExponent Λ G] (n : ℤ) (h₀ : n ≠ 0) (h₁ : n ≠ 1) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
      ((R((j ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)_*[ModuleCat.{u + 1} Λ])).obj
        (tateObject Λ G 1))) := by
  refine isZero_homology_of_jointlySurjective Λ (fun V : Y.affineOpens ↦ V.1.ι)
    (fun x ↦ ?_) _ n fun V ↦ ?_
  · exact Y.exists_affineOpens_ι_eq x
  have : IsAffine V.1 := V.2
  have : QuasiCompact (V.1.ι ≫ aY) := inferInstance
  have : HasInvertibleExponent Λ V.1 := .of_hom V.1.ι
  let jV := (𝔸(ULift.{u} (Fin 1); V.1).basicOpen (AffineSpace.coord V.1 (ULift.up 0))).ι
  have hjV := AffineSpace.range_basicOpen_ι_coord V.1
  have : HasInvertibleExponent Λ
      (𝔸(ULift.{u} (Fin 1); V.1).basicOpen (AffineSpace.coord V.1 (ULift.up 0))) :=
    .of_hom (jV ≫ 𝔸(ULift.{u} (Fin 1); V.1) ↘ V.1)
  let sq := AffineSpace.isPullback_complementMap_over V.1.ι j jV hj hjV
  have := isIso_derivedBaseChangeMap_app_tateObject_of_etale Λ sq 1
  exact (isZero_homology_rightDerivedLowerStar_tateObject_multiplicativeGroup Λ (V.1.ι ≫ aY)
    jV hjV n h₀ h₁).of_iso ((_root_.DerivedCategory.homologyFunctor _ n).mapIso
      (asIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app _) ≪≫
        (R((jV ≫ 𝔸(ULift.{u} (Fin 1); V.1) ↘ V.1)_*[ModuleCat.{u + 1} Λ])).mapIso
          (leftDerivedUpperStarTateObjectIso _ 1)))

end AlgClosed

section Field

variable {k : Type u} [Field k] {B : Scheme.{u}} (aB : B ⟶ Spec (.of k))

/-- Descent of the vanishing of a cohomology sheaf of a higher direct image of the Tate twist
along the base change `B' = B ×_k k̄ ⟶ B` to an algebraic closure `k̄` of `k`. Given the base
change `f' : X' ⟶ B'` of a quasi-compact quasi-separated `f : X ⟶ B`, if `H^n(Rf'_* Λ(m))`
vanishes, so does `H^n(Rf_* Λ(m))`: the base change map along the field extension is an
isomorphism (`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_fieldExtension`) and
`B' ⟶ B` is surjective. The hypothesis may use that the exponent of `Λ` is invertible in `k̄`,
which holds as soon as `B` is nonempty. -/
lemma isZero_homology_rightDerivedLowerStar_tateObject_of_algebraicClosure
    [HasInvertibleExponent Λ B] {X X' : Scheme.{u}} (f : X ⟶ B) [QuasiCompact f]
    [QuasiSeparated f] [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ X']
    (g' : X' ⟶ X) (f' : X' ⟶ pullback aB (Spec.map (CommRingCat.ofHom
      (algebraMap k (AlgebraicClosure k)))))
    (sq : IsPullback g' f' f (pullback.fst _ _)) (m n : ℤ)
    (h : HasInvertibleExponent Λ (Spec (.of (AlgebraicClosure k))) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
        ((R((f')_*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ X' m)))) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ X m))) := by
  by_cases hB : Nonempty B
  · have := HasInvertibleExponent.of_hom_of_nonempty (Λ := Λ) aB
    let ι := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
    have : HasInvertibleExponent Λ (Spec (.of (AlgebraicClosure k))) := .of_hom ι
    have hY := IsPullback.of_hasPullback aB ι
    have : Surjective ι := ⟨fun _ ↦ ⟨default, Subsingleton.elim _ _⟩⟩
    have hg : Surjective (pullback.fst aB ι) := MorphismProperty.of_isPullback hY.flip this
    have := isIso_derivedBaseChangeMap_app_tateObject_of_fieldExtension Λ aB _ hY sq m
    refine isZero_homology_of_jointlySurjective Λ (ι := PUnit.{u + 1})
      (fun _ ↦ pullback.fst aB ι) (fun x ↦ ?_) _ n fun _ ↦ ?_
    · obtain ⟨y, hy⟩ := hg.surj x
      exact ⟨⟨⟩, y, hy⟩
    · exact (h inferInstance).of_iso ((_root_.DerivedCategory.homologyFunctor _ n).mapIso
        (asIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app _) ≪≫
          (R((f')_*[ModuleCat.{u + 1} Λ])).mapIso (leftDerivedUpperStarTateObjectIso g' m)))
  · rw [not_nonempty_iff] at hB
    exact isZero_homology_of_jointlySurjective Λ (ι := PEmpty.{u + 1}) (fun _ ↦ 𝟙 B)
      (fun x ↦ isEmptyElim x) _ n fun i ↦ i.elim

variable [Finite Λ] (B) [IsSeparated aB] [LocallyOfFiniteType aB] [HasInvertibleExponent Λ B]

include aB in
/-- Blueprint `sk-prop-a1-kummer`, clause (a), for the twist `Λ(1) = μₙ ⊗ Λ`, over an arbitrary
field: for `B` separated and locally of finite type over a field `k` and the projection
`p : 𝔸¹_B ⟶ B`, `R^n p_* Λ(1) = 0` for `n > 0`. After base change to an algebraic closure of
`k` this is
`isZero_homology_rightDerivedLowerStar_tateObject_affineLine_of_isAlgClosed`.
-/
theorem isZero_homology_rightDerivedLowerStar_tateObject_affineLine_of_field (n : ℤ)
    (hn : 0 < n) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
      ((R((𝔸(ULift.{u} (Fin 1); B) ↘ B)_*[ModuleCat.{u + 1} Λ])).obj
        (tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1))) := by
  let ι := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  have hY := IsPullback.of_hasPullback aB ι
  have : IsSeparated (pullback.snd aB ι) := MorphismProperty.of_isPullback hY inferInstance
  have : LocallyOfFiniteType (pullback.snd aB ι) :=
    MorphismProperty.of_isPullback hY inferInstance
  have : HasInvertibleExponent Λ (pullback aB ι) := .of_hom (pullback.fst aB ι)
  have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); B) := .of_hom (𝔸(ULift.{u} (Fin 1); B) ↘ B)
  have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); pullback aB ι) :=
    .of_hom (𝔸(ULift.{u} (Fin 1); pullback aB ι) ↘ pullback aB ι)
  exact isZero_homology_rightDerivedLowerStar_tateObject_of_algebraicClosure Λ aB _ _ _
    (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) (pullback.fst aB ι)) 1 n fun _ ↦
      isZero_homology_rightDerivedLowerStar_tateObject_affineLine_of_isAlgClosed Λ
        (pullback.snd aB ι) n hn

include aB in
/-- Over an arbitrary field: for `B` separated and locally of finite type over a field `k`, a
quasi-compact open immersion `j : G ⟶ 𝔸¹_B` onto the complement of the zero section and
`π = j ≫ p`, `R^n π_* Λ(1) = 0` for `n ∉ {0, 1}`. After base change to an algebraic closure of
`k` this is
`isZero_homology_rightDerivedLowerStar_tateObject_multiplicativeGroup_of_isAlgClosed`. -/
theorem isZero_homology_rightDerivedLowerStar_tateObject_multiplicativeGroup_of_field
    {G : Scheme.{u}} (j : G ⟶ 𝔸(ULift.{u} (Fin 1); B)) [IsOpenImmersion j] [QuasiCompact j]
    (hj : Set.range j.base =
      (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B).base)ᶜ)
    [HasInvertibleExponent Λ G] (n : ℤ) (h₀ : n ≠ 0) (h₁ : n ≠ 1) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
      ((R((j ≫ 𝔸(ULift.{u} (Fin 1); B) ↘ B)_*[ModuleCat.{u + 1} Λ])).obj
        (tateObject Λ G 1))) := by
  let ι := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  have hY := IsPullback.of_hasPullback aB ι
  have : IsSeparated (pullback.snd aB ι) := MorphismProperty.of_isPullback hY inferInstance
  have : LocallyOfFiniteType (pullback.snd aB ι) :=
    MorphismProperty.of_isPullback hY inferInstance
  have : HasInvertibleExponent Λ (pullback aB ι) := .of_hom (pullback.fst aB ι)
  let j' := (𝔸(ULift.{u} (Fin 1); pullback aB ι).basicOpen
    (AffineSpace.coord (pullback aB ι) (ULift.up 0))).ι
  have hj' := AffineSpace.range_basicOpen_ι_coord (pullback aB ι)
  have : HasInvertibleExponent Λ (𝔸(ULift.{u} (Fin 1); pullback aB ι).basicOpen
      (AffineSpace.coord (pullback aB ι) (ULift.up 0))) :=
    .of_hom (j' ≫ 𝔸(ULift.{u} (Fin 1); pullback aB ι) ↘ pullback aB ι)
  exact isZero_homology_rightDerivedLowerStar_tateObject_of_algebraicClosure Λ aB _ _ _
    (AffineSpace.isPullback_complementMap_over (pullback.fst aB ι) j j' hj hj') 1 n fun _ ↦
      isZero_homology_rightDerivedLowerStar_tateObject_multiplicativeGroup_of_isAlgClosed Λ
        (pullback.snd aB ι) j' hj' n h₀ h₁

include aB in
/-- Blueprint `sk-prop-a1-kummer`, clause (c), for the twist `Λ(1) = μₙ ⊗ Λ`, over an arbitrary
field: for `B` separated and locally of finite type over a field `k`, the projection
`p : 𝔸¹_B ⟶ B` and the basic open `j : 𝔾_{m,B} ⟶ 𝔸¹_B` of the coordinate,
`R^n p_* Rj_* j^* Λ(1) = 0` for `n ≥ 2`. -/
theorem isZero_homology_rightDerivedLowerStar_tateObject_basicOpen_of_field (n : ℤ)
    (hn : 2 ≤ n) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
      ((R((𝔸(ULift.{u} (Fin 1); B) ↘ B)_*[ModuleCat.{u + 1} Λ])).obj
        ((R(((𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))).ι)_*[
            ModuleCat.{u + 1} Λ])).obj
          ((L(((𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))).ι)^*[
            ModuleCat.{u + 1} Λ])).obj (tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1))))) := by
  let j := (𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))).ι
  have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); B) := .of_hom (𝔸(ULift.{u} (Fin 1); B) ↘ B)
  have : HasInvertibleExponent Λ
      (𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))) := .of_hom j
  exact (isZero_homology_rightDerivedLowerStar_tateObject_multiplicativeGroup_of_field Λ B aB j
    (AffineSpace.range_basicOpen_ι_coord B) n (by lia) (by lia)).of_iso
      ((_root_.DerivedCategory.homologyFunctor _ n).mapIso
        ((R((𝔸(ULift.{u} (Fin 1); B) ↘ B)_*[ModuleCat.{u + 1} Λ])).mapIso
          ((R((j)_*[ModuleCat.{u + 1} Λ])).mapIso (leftDerivedUpperStarTateObjectIso j 1)) ≪≫
        (rightDerivedLowerStarComp (ModuleCat.{u + 1} Λ) j
          (𝔸(ULift.{u} (Fin 1); B) ↘ B)).app _))

end Field

end Etale

end AlgebraicGeometry
