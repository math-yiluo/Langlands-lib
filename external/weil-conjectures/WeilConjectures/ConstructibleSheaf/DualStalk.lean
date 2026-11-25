/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits

import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import WeilConjectures.ConstructibleSheaf.EtaleDualRestriction
import WeilConjectures.ConstructibleSheaf.ConstantModuleDual

/-! # Stalk comparison for coefficient duals -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [IsNoetherianRing Λ]
variable {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}

/-- The geometric stalk of the coefficient dual is the linear dual of the geometric stalk.

Source: `WeilConjectures/ConstructibleSheaf/Monoidal.lean`, the docstring of
`IsFiniteLocallyConstantSheaf.ihom_unit`, finite presentation and module dual argument.

Proof: Fix s and an étale trivializing neighborhood through which s lifts. On this
neighborhood F is constant with value M, identified with F_s, and M is finitely generated.
Noetherianity gives a finite presentation Λᵐ → Λⁿ → M → 0. After exact constant
sheafification, internal Hom into the unit is the kernel of the transposed finite matrix.
The geometric stalk functor is exact, and its monoidal unit comparison identifies the
stalks of the finite free constant sheaves with Λⁿ and Λᵐ. It therefore identifies the stalk
of the sheaf dual with the kernel of the same transposed matrix on modules, namely
Hom_Λ(M, Λ). Transport along M ≅ F_s yields the asserted module isomorphism. This uses
finite presentation, not projectivity, and does not assert that stalks commute with
internal Hom for arbitrary sheaves.

(blueprint: lem-weil-pbc-flc-dual-stalk) -/
theorem IsFiniteLocallyConstantSheaf.nonempty_ihom_unit_stalk_iso
    (hF : IsFiniteLocallyConstantSheaf F) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X) :
    Nonempty (((pointSmallEtale s).sheafFiber.obj ((ihom F).obj (𝟙_ _))) ≅
      ModuleCat.of Λ
        (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F →ₗ[Λ] Λ)) := by
  classical
  have : JointlySurjective etalePrecoverage.{u} :=
    inferInstanceAs (JointlySurjective (precoverage @Etale))
  have : CategoryTheory.Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    CategoryTheory.Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨d⟩ := hF.toIsLocallyConstantSheaf.nonempty_locallyConstantDatum
  obtain ⟨i, x, hx⟩ := d.cover.exists_eq (s default)
  have : Etale (d.cover.f i) := d.cover.map_prop i
  obtain ⟨t, ht, -⟩ := exists_fac_of_etale_of_isSepClosed (d.cover.f i) s x hx
  let U := d.cover.etalePrecoverageToEtale i
  have htU : t ≫ U.hom = s := ht
  let P := Etale.upperStar (ModuleCat.{u + 1} Λ) U.hom
  have hconstant : (P.obj F).IsConstant U.left.smallEtaleTopology :=
    (isConstant_over_iff_upperStar (ModuleCat.{u + 1} Λ) U F).mp (d.isConstant i)
  let : (P.obj F).IsConstant U.left.smallEtaleTopology := hconstant
  obtain ⟨M, ⟨e⟩⟩ := (P.obj F).mem_essImage_of_isConstant (J := U.left.smallEtaleTopology)
  let eF : ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F ≅ M := by
    have e' := ((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) U.hom t).app F).symm
      ≪≫ (pointSmallEtale t).sheafFiber.mapIso e.symm
      ≪≫ (pointSmallEtale t).sheafFiberConstantSheafIso M
    rw [htU] at e'
    exact e'
  have : Module.Finite Λ M :=
    (ModuleCat.isFinitelyGenerated_iff M).1
      ((hF.toIsFiniteSheaf.isFinitelyGenerated_sheafFiber Ω s).of_iso eF)
  obtain ⟨eR⟩ := nonempty_etaleDualRestrictionIso U F
  obtain ⟨eC⟩ := nonempty_constantModuleDualIso U.left M
  let eD : P.obj ((ihom F).obj (𝟙_ _)) ≅
      (constantSheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ (M →ₗ[Λ] Λ)) :=
    eR ≪≫ ((MonoidalClosed.internalHom.mapIso e.op).app (𝟙_ _)) ≪≫ eC
  let eS : ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
      ((ihom F).obj (𝟙_ _)) ≅ ModuleCat.of Λ (M →ₗ[Λ] Λ) := by
    have e' := ((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) U.hom t).app
        ((ihom F).obj (𝟙_ _))).symm
      ≪≫ (pointSmallEtale t).sheafFiber.mapIso eD
      ≪≫ (pointSmallEtale t).sheafFiberConstantSheafIso (ModuleCat.of Λ (M →ₗ[Λ] Λ))
    rw [htU] at e'
    exact e'
  exact ⟨eS ≪≫ (LinearEquiv.arrowCongr eF.toLinearEquiv.symm
    (LinearEquiv.refl Λ Λ)).toModuleIso⟩

end AlgebraicGeometry.Scheme
