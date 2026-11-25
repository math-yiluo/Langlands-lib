/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.RingTheory.PicardGroup
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import WeilConjectures.ConstructibleSheaf.StalkZeroLocus
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal
import WeilConjectures.ConstructibleSheaf.MonoidalParts
import WeilConjectures.ConstructibleSheaf.DualLocallyConstant
import WeilConjectures.ConstructibleSheaf.DualStalk

/-!
# Tensor products and duals of constructible sheaves

Let `Λ` be a commutative ring. For sheaves of `Λ`-modules on the small étale site of a scheme
`X`:

- a finite locally constant sheaf is constructible, for the trivial stratification, and a
  constructible sheaf has finitely generated stalks; so a sheaf is finite locally constant if and
  only if it is constructible and locally constant;
- the tensor product of two constructible sheaves is constructible: on the strata of a common
  refinement of stratifications the pullback of `F ⊗ G` is the tensor product of two finite
  locally constant sheaves, the pullback being monoidal;
- a sheaf of modules with a tensor inverse is finite: its stalks are invertible modules, hence
  finitely generated; in particular the constant sheaf `Λ_X` is finite locally constant, hence
  constructible, and so is a finite direct sum of constructible sheaves;
- for `Λ` noetherian, the internal hom `[F, Λ]` of a finite locally constant sheaf `F` into the
  unit is finite locally constant: on a trivialising cover it is the constant sheaf at
  `Hom_Λ(M, Λ)` for the finitely generated module `M`, a finitely generated module.

Unlike the tensor product, the internal hom of a constructible sheaf into the unit need not be
constructible without finiteness hypotheses on `X`: for an open immersion `j` it sends `j_!Λ` to
`j_*Λ`.

## Main results

- `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.isConstructibleSheaf`
- `AlgebraicGeometry.Scheme.IsConstructibleSheaf.isFiniteSheaf`
- `AlgebraicGeometry.Scheme.IsConstructibleSheaf.tensorObj`
- `AlgebraicGeometry.Scheme.IsFiniteSheaf.of_tensorIso`
- `AlgebraicGeometry.Scheme.isConstructibleSheaf_unit`
- `AlgebraicGeometry.Scheme.IsConstructibleSheaf.biproduct`
- `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.ihom_unit`

## TODO

Prove `IsFiniteLocallyConstantSheaf.ihom_unit`.
-/

@[expose] public section

universe u u'

open CategoryTheory MonoidalCategory Limits ZeroObject

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

section General

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  {F : Sheaf X.smallEtaleTopology A}

/-- A finite locally constant sheaf is constructible, for the trivial stratification. -/
theorem IsFiniteLocallyConstantSheaf.isConstructibleSheaf (hF : IsFiniteLocallyConstantSheaf F) :
    IsConstructibleSheaf F :=
  ⟨Stratification.trivial X, fun _ ↦ IsFiniteLocallyConstantSheaf.upperStar (𝟙 X) F⟩

omit [HasSmallSiteSheafify A] in
/-- A constructible sheaf is finite: a geometric point of `X` lies in a stratum, through whose
immersion it factors, and the stalk of `F` there is the stalk of the finite locally constant
pullback of `F` to the stratum. -/
theorem IsConstructibleSheaf.isFiniteSheaf (hF : IsConstructibleSheaf F) : IsFiniteSheaf F where
  isFinitelyGenerated_sheafFiber Ω _ _ s := by
    obtain ⟨S, hS⟩ := hF.exists_stratification
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
      (S.iUnion_stratum_eq_univ ▸ Set.mem_univ (s.base (IsLocalRing.closedPoint Ω)))
    rw [← S.range_immersion] at hi
    obtain ⟨t, rfl⟩ := IsImmersion.exists_comp_eq_of_field (S.immersion i) s hi
    have := (hS i).toIsFiniteSheaf
    exact (IsFiniteSheaf.isFinitelyGenerated_sheafFiber (FA := FA) (CA := CA)
      (F := (Etale.upperStar A (S.immersion i)).obj F) Ω t).of_iso
        ((Etale.upperStarCompSheafFiberIso A (S.immersion i) t).app F)

omit [HasSmallSiteSheafify A] in
/-- A constructible locally constant sheaf is finite locally constant. -/
theorem IsConstructibleSheaf.isFiniteLocallyConstantSheaf (hF : IsConstructibleSheaf F)
    (hF' : IsLocallyConstantSheaf F) :
    IsFiniteLocallyConstantSheaf F where
  toIsLocallyConstantSheaf := hF'
  toIsFiniteSheaf := hF.isFiniteSheaf

end General

section Modules

variable {Λ : Type (u + 1)} [CommRing Λ] {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}

/-- The tensor product of two finite locally constant sheaves of modules is finite locally
constant: on a common trivialising cover it is the constant sheaf at the tensor product of two
finitely generated modules. -/
theorem IsFiniteLocallyConstantSheaf.tensorObj (hF : IsFiniteLocallyConstantSheaf F)
    (hG : IsFiniteLocallyConstantSheaf G) :
    IsFiniteLocallyConstantSheaf (F ⊗ G) where
  toIsLocallyConstantSheaf :=
    IsLocallyConstantSheaf.tensorObj_part hF.toIsLocallyConstantSheaf hG.toIsLocallyConstantSheaf
  toIsFiniteSheaf := IsFiniteSheaf.tensorObj_part hF.toIsFiniteSheaf hG.toIsFiniteSheaf

/-- **The tensor product of two constructible sheaves of modules is constructible**: on the
common refinement of witnessing stratifications, the pullback of `F ⊗ G` to a stratum is the
tensor product of two finite locally constant sheaves, the pullback being monoidal. -/
theorem IsConstructibleSheaf.tensorObj (hF : IsConstructibleSheaf F) (hG : IsConstructibleSheaf G) :
    IsConstructibleSheaf (F ⊗ G) := by
  obtain ⟨S, hS⟩ := hF.exists_stratification
  obtain ⟨T, hT⟩ := hG.exists_stratification
  refine ⟨S.inter T, fun k ↦ ?_⟩
  have hF' := (S.inter_refines_left T).isFiniteLocallyConstantSheaf_upperStar F hS k
  have hG' := (S.inter_refines_right T).isFiniteLocallyConstantSheaf_upperStar G hT k
  have hFG := hF'.tensorObj hG'
  exact IsFiniteLocallyConstantSheaf.of_iso
    (Functor.Monoidal.μIso (Etale.upperStar (ModuleCat.{u + 1} Λ) ((S.inter T).immersion k)) F G)

/-- **The dual of a finite locally constant sheaf is finite locally constant**: for `Λ`
noetherian, the internal hom `[F, Λ]` of a finite locally constant sheaf `F` into the unit is
finite locally constant. On a trivialising cover it is the constant sheaf at `Hom_Λ(M, Λ)`, `M`
being finitely generated and hence finitely presented, `Λ` being noetherian; and
`Hom_Λ(M, Λ)` is finitely generated, being a submodule of `Λⁿ` for a surjection `Λⁿ ⟶ M`. -/
theorem IsFiniteLocallyConstantSheaf.ihom_unit [IsNoetherianRing Λ]
    (hF : IsFiniteLocallyConstantSheaf F) :
    IsFiniteLocallyConstantSheaf ((ihom F).obj (𝟙_ _)) where
  toIsLocallyConstantSheaf := hF.ihom_unit_locallyConstant
  toIsFiniteSheaf := ⟨fun Ω _ _ s ↦ by
    have : Module.Finite Λ
        (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F) :=
      (ModuleCat.isFinitelyGenerated_iff _).1
        (hF.toIsFiniteSheaf.isFinitelyGenerated_sheafFiber Ω s)
    obtain ⟨e⟩ := hF.nonempty_ihom_unit_stalk_iso Ω s
    exact ((ModuleCat.isFinitelyGenerated_iff _).2
      (inferInstance : Module.Finite Λ
        (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F →ₗ[Λ] Λ))).of_iso e.symm⟩

/-- A sheaf of `Λ`-modules with a tensor inverse, `F ⊗ G ≅ Λ`, is finite: the stalks are strong
monoidal, so `F_s ⊗ G_s ≅ Λ` and `F_s` is an invertible, hence finitely generated, `Λ`-module. -/
theorem IsFiniteSheaf.of_tensorIso (e : F ⊗ G ≅ 𝟙_ _) : IsFiniteSheaf F where
  isFinitelyGenerated_sheafFiber Ω _ _ s := by
    let Φ := (pointSmallEtale s).ulift.{u + 1}
    let e' : Φ.sheafFiber.obj F ⊗ Φ.sheafFiber.obj G ≅ 𝟙_ (ModuleCat.{u + 1} Λ) :=
      (Etale.sheafFiberTensorIso s F G).symm ≪≫ Φ.sheafFiber.mapIso e ≪≫
        Etale.sheafFiberUnitIso _ s
    have : Module.Invertible Λ ((Φ.sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F) :=
      .left e'.toLinearEquiv
    exact (((ModuleCat.isFinitelyGenerated_iff _).2 inferInstance).of_iso
      (((pointSmallEtale s).uliftSheafFiberIso.{u + 1} (ModuleCat.{u + 1} Λ)).app F))

variable (X Λ)

/-- The constant sheaf `Λ_X`, the monoidal unit, is locally constant, trivialised by the
identity cover. -/
instance isLocallyConstantSheaf_unit :
    IsLocallyConstantSheaf (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) := by
  have : etalePrecoverage.{u}.HasIsos := inferInstanceAs (precoverage @Etale).HasIsos
  refine ⟨⟨⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun _ ↦ ?_⟩⟩⟩
  rw [isConstant_over_iff_upperStar]
  exact Sheaf.isConstant_of_iso _ (X := 𝟙_ (ModuleCat.{u + 1} Λ))
    ((Etale.upperStarId _ X).app _ ≪≫
      Functor.Monoidal.εIso (presheafToSheaf _ (ModuleCat.{u + 1} Λ)))

/-- The constant sheaf `Λ_X` is finite, being its own tensor inverse. -/
instance isFiniteSheaf_unit :
    IsFiniteSheaf (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  .of_tensorIso (λ_ _)

/-- The constant sheaf `Λ_X` is constructible, being finite locally constant. -/
instance isConstructibleSheaf_unit :
    IsConstructibleSheaf (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  IsFiniteLocallyConstantSheaf.isConstructibleSheaf {}

variable {X Λ}

attribute [local instance] Abelian.hasFiniteBiproducts in
/-- **A finite direct sum of constructible sheaves of modules is constructible**, by induction
from the binary case `AlgebraicGeometry.Scheme.IsConstructibleSheaf.biprod`; for instance the
finite free sheaf `Λ_Xʳ`. -/
theorem IsConstructibleSheaf.biproduct {J : Type} [Finite J]
    (F : J → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [∀ j, IsConstructibleSheaf (F j)] :
    IsConstructibleSheaf (⨁ F) := by
  let P : ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    fun G ↦ IsConstructibleSheaf G
  have : P.IsClosedUnderIsomorphisms := ⟨fun e h ↦ by
    have : IsConstructibleSheaf _ := h
    exact IsConstructibleSheaf.of_iso e⟩
  have : P.ContainsZero := ⟨⟨0, isZero_zero _, IsConstructibleSheaf.of_isZero (isZero_zero _)⟩⟩
  have : P.IsClosedUnderBinaryProducts := .mk' (by
    rintro _ ⟨G, hG⟩
    have : IsConstructibleSheaf (G.obj ⟨.left⟩) := hG _
    have : IsConstructibleSheaf (G.obj ⟨.right⟩) := hG _
    have := IsConstructibleSheaf.biprod (G.obj ⟨.left⟩) (G.obj ⟨.right⟩)
    exact IsConstructibleSheaf.of_iso ((biprod.isoProd _ _) ≪≫
      (HasLimit.isoOfNatIso (diagramIsoPair G)).symm))
  have : P.IsClosedUnderFiniteProducts := .mk'
  have : IsConstructibleSheaf (∏ᶜ F) :=
    P.prop_product fun j ↦ (inferInstance : IsConstructibleSheaf (F j))
  exact IsConstructibleSheaf.of_iso (biproduct.isoProduct F).symm

variable (X Λ) in
/-- The constant sheaf `Λ_X`, the monoidal unit, is finite locally constant. -/
instance isFiniteLocallyConstantSheaf_unit :
    IsFiniteLocallyConstantSheaf (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) where

attribute [local instance] Abelian.hasFiniteBiproducts in
/-- **A finite direct sum of finite locally constant sheaves of modules is finite locally
constant**, by induction from the binary case
`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.biprod`; for instance the finite free
sheaf `Λ_Xʳ`. -/
theorem IsFiniteLocallyConstantSheaf.biproduct {J : Type} [Finite J]
    (F : J → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [∀ j, IsFiniteLocallyConstantSheaf (F j)] :
    IsFiniteLocallyConstantSheaf (⨁ F) := by
  let P : ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    fun G ↦ IsFiniteLocallyConstantSheaf G
  have : P.IsClosedUnderIsomorphisms := ⟨fun e h ↦ by
    have : IsFiniteLocallyConstantSheaf _ := h
    exact IsFiniteLocallyConstantSheaf.of_iso e⟩
  have : P.ContainsZero :=
    ⟨⟨0, isZero_zero _, IsFiniteLocallyConstantSheaf.of_isZero (isZero_zero _)⟩⟩
  have : P.IsClosedUnderBinaryProducts := .mk' (by
    rintro _ ⟨G, hG⟩
    have : IsFiniteLocallyConstantSheaf (G.obj ⟨.left⟩) := hG _
    have : IsFiniteLocallyConstantSheaf (G.obj ⟨.right⟩) := hG _
    have := IsFiniteLocallyConstantSheaf.biprod (G.obj ⟨.left⟩) (G.obj ⟨.right⟩)
    exact IsFiniteLocallyConstantSheaf.of_iso ((biprod.isoProd _ _) ≪≫
      (HasLimit.isoOfNatIso (diagramIsoPair G)).symm))
  have : P.IsClosedUnderFiniteProducts := .mk'
  have : IsFiniteLocallyConstantSheaf (∏ᶜ F) :=
    P.prop_product fun j ↦ (inferInstance : IsFiniteLocallyConstantSheaf (F j))
  exact IsFiniteLocallyConstantSheaf.of_iso (biproduct.isoProduct F).symm

end Modules

end AlgebraicGeometry.Scheme
