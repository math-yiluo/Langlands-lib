/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.DisjointUnion
public import WeilConjectures.SixFunctors.Finite.BaseChange
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocallyTrivial
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Products

/-!
# Pushforwards of constant sheaves along finite étale morphisms

For a finite étale morphism `π : V ⟶ X`, the pushforward `π_* M_V` of a constant sheaf is
locally constant (`AlgebraicGeometry.Scheme.isLocallyConstantSheaf_lowerStar_constantSheaf`):
étale locally `π` is a trivial cover `∐ₛ U ⟶ U`
(`AlgebraicGeometry.Scheme.FiniteEtale.exists_etale_isPullback_sigma`), the pushforward commutes
with this base change (`AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isFinite`), and along a
trivial cover the pushforward of a constant sheaf is constant
(`AlgebraicGeometry.Scheme.isConstant_lowerStar_trivialCoverFold`). This is an input to the
constructibility of extensions by zero along étale maps [Stacks 03SA].
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {V X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]

/-- **The pushforward of a constant sheaf along a finite étale morphism is locally constant**:
étale locally the morphism is a trivial cover `∐ₛ U ⟶ U`, the pushforward commutes with this
base change (finite base change), and along a trivial cover the pushforward of a constant sheaf
is constant. -/
theorem isLocallyConstantSheaf_lowerStar_constantSheaf (π : V ⟶ X) [IsFinite π] [Etale π]
    (M : ModuleCat.{u + 1} Λ) :
    IsLocallyConstantSheaf ((Etale.lowerStar (ModuleCat.{u + 1} Λ) π).obj
      ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) := by
  let P : X.FiniteEtale := ⟨MorphismProperty.Over.mk ⊤ π inferInstance,
    (inferInstance : IsFinite π)⟩
  choose U g hg S hS fst hx hpb using fun x ↦ FiniteEtale.exists_etale_isPullback_sigma P x
  let 𝒰 : Cover.{u} etalePrecoverage X :=
    { I₀ := X
      X := U
      f := g
      mem₀ := (presieve₀_mem_precoverage_iff _).mpr ⟨fun x ↦ by
        obtain ⟨y, hy⟩ := hx x
        exact ⟨x, y, hy⟩, fun x ↦ hg x⟩ }
  refine ⟨⟨𝒰, fun x ↦ ?_⟩⟩
  rw [isConstant_over_iff_upperStar]
  change ((Etale.upperStar _ (g x)).obj _).IsConstant _
  have : IsFinite P.obj.hom := (inferInstance : IsFinite π)
  have := Etale.isIso_baseChangeMap_of_isFinite (ModuleCat.{u + 1} Λ) (hpb x)
  have : (((Etale.lowerStar (ModuleCat.{u + 1} Λ) (trivialCoverFold (U x) (S x))).obj
      ((constantSheaf _ (ModuleCat.{u + 1} Λ)).obj M))).IsConstant (U x).smallEtaleTopology :=
    isConstant_lowerStar_trivialCoverFold M
  exact Sheaf.isConstant_congr _
    ((Etale.lowerStar _ (trivialCoverFold (U x) (S x))).mapIso
      ((upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) (fst x)).app M).symm ≪≫
      (asIso ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ) (hpb x).toCommSq).app _)).symm)

/-- **Geometric points lift along étale morphisms**: a point `Spec Ω ⟶ X` with `Ω` separably
closed whose image lies in the image of an étale `g : U ⟶ X` factors through `g`, the residue
field extensions of `g` being separable. -/
lemma exists_comp_eq_of_etale {U X : Scheme.{u}} (g : U ⟶ X) [Etale g] {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) (hs : s (IsLocalRing.closedPoint _) ∈ Set.range g) :
    ∃ s' : Spec (.of Ω) ⟶ U, s' ≫ g = s := by
  obtain ⟨⟨x, φ⟩, rfl⟩ := (SpecToEquivOfField Ω X).symm.surjective s
  obtain ⟨w, hw⟩ := hs
  simp only [SpecToEquivOfField_symm_apply, Hom.comp_apply, fromSpecResidueField_apply] at hw
  subst hw
  let : Algebra (X.residueField (g w)) (U.residueField w) := (g.residueFieldMap w).hom.toAlgebra
  let : Algebra (X.residueField (g w)) Ω := φ.hom.toAlgebra
  let ψ : U.residueField w →ₐ[X.residueField (g w)] Ω := IsSepClosed.lift
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ U.fromSpecResidueField w, ?_⟩
  simp only [SpecToEquivOfField_symm_apply]
  rw [Category.assoc, ← Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc,
    ← Spec.map_comp]
  congr 2
  ext a
  exact ψ.commutes a

/-- Limits of size `u` exist in `ModuleCat.{u + 1} Λ`. -/
local instance hasLimitsOfSizeModuleCat_finiteEtale {Λ : Type (u + 1)} [CommRing Λ] :
    HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
  hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _

/-- The forgetful functor of `ModuleCat.{u + 1} Λ` preserves filtered colimits of size `u`. -/
local instance preservesFilteredColimits_finiteEtale {Λ : Type (u + 1)} [CommRing Λ] :
    PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
  preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _

/-- **The pushforward of a finite constant sheaf along a finite étale morphism is finite locally
constant.** Its stalk at a geometric point is, after lifting the point to a member of a
trivialising étale cover, the value `Mˢ` of a constant sheaf. -/
theorem isFiniteLocallyConstantSheaf_lowerStar_constantSheaf {V X : Scheme.{u}}
    {Λ : Type (u + 1)} [CommRing Λ] (π : V ⟶ X) [IsFinite π] [Etale π]
    (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M] :
    IsFiniteLocallyConstantSheaf ((Etale.lowerStar (ModuleCat.{u + 1} Λ) π).obj
      ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) where
  toIsLocallyConstantSheaf := isLocallyConstantSheaf_lowerStar_constantSheaf π M
  toIsFiniteSheaf := ⟨fun Ω _ _ s ↦ by
    let P : X.FiniteEtale := ⟨MorphismProperty.Over.mk ⊤ π inferInstance,
      (inferInstance : IsFinite π)⟩
    have : IsFinite P.obj.hom := (inferInstance : IsFinite π)
    obtain ⟨U, g, hg, S, hS, fst, hx, hpb⟩ :=
      FiniteEtale.exists_etale_isPullback_sigma P (s (IsLocalRing.closedPoint _))
    obtain ⟨s', rfl⟩ := exists_comp_eq_of_etale g s hx
    have := Etale.isIso_baseChangeMap_of_isFinite (ModuleCat.{u + 1} Λ) hpb
    let e := ((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) g s').app _).symm ≪≫
      (pointSmallEtale s').sheafFiber.mapIso
        (asIso ((Etale.baseChangeMap (ModuleCat.{u + 1} Λ) hpb.toCommSq).app _) ≪≫
          (Etale.lowerStar _ (trivialCoverFold U S)).mapIso
            ((upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) fst).app M) ≪≫
          lowerStarTrivialCoverFoldConstantIso M) ≪≫
      (pointSmallEtale s').sheafFiberConstantSheafIso _ ≪≫
      ModuleCat.piIsoPi.{u + 1, u, u + 1} (fun _ : S ↦ M)
    have : Module.Finite Λ (S → M) := Module.Finite.pi
    exact ((ModuleCat.isFinitelyGenerated_iff (ModuleCat.of Λ (S → M))).2 this).of_iso e.symm⟩


/-- **Extensions by zero of finite constant sheaves along finite étale morphisms are
constructible**, indeed finite locally constant: for finite étale `v`, the extension by zero
`v_!` and the pushforward `v_*` are both left adjoint to `v^*`. This is the finite case of
[Stacks 03SA]. -/
theorem isFiniteLocallyConstantSheaf_etaleLowerShriek_constantSheaf {V X : Scheme.{u}}
    {Λ : Type (u + 1)} [CommRing Λ] (v : V ⟶ X) [IsFinite v] [Etale v]
    (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M] :
    IsFiniteLocallyConstantSheaf
      ((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v inferInstance).obj
      ((constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) := by
  have := isFiniteLocallyConstantSheaf_lowerStar_constantSheaf v M
  exact IsFiniteLocallyConstantSheaf.of_iso
    (((Etale.etaleLowerShriekUpperStarAdjunction _ v inferInstance).leftAdjointUniq
      (Etale.lowerStarUpperStarAdjunctionOfIsFinite _ v)).app _).symm


end AlgebraicGeometry.Scheme
