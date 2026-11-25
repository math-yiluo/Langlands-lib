/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
public import WeilConjectures.SixFunctors.ProEtale.InternalCompletionSectionTransport
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom

/-! # Isomorphism invariance of the Stacks adic constructibility predicate

The Stacks adic constructibility predicate `stacksConstructible` of
`lemma-integral-models--2` is invariant under isomorphism.

Source: Stacks Tags 0999, 09C1 and 09C2 (auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace CategoryTheory.ConstantCompletion

/-- Local derived completeness along `q` is invariant under isomorphism. Proof: derived
restriction and derived internal Hom carry the isomorphism to an isomorphism on every slice.
Source: Stacks Tag 0999 (auxiliary; not a blueprint node). -/
theorem IsComplete.of_iso
    {C : Type (u + 1)} [SmallCategory C] {J : GrothendieckTopology C}
    {O S : Sheaf J CommRingCat.{u + 1}} {q : O ⟶ S}
    {K L : D O} (e : K ≅ L) (hK : IsComplete q K) : IsComplete q L := by
  let := HasDerivedCategory.standard (Mod O)
  let (U : C) := HasDerivedCategory.standard (Mod (O.over U))
  intro U f hf
  let H := (Functor.curry.obj (derivedInternalHom (J.over U) (O.over U))).obj
    (op ((DerivedCategory.singleFunctor _ 0).obj
      (ringedSectionLocalization (O.over U) (ringedSliceSection O U f))))
  exact (((ringedDerivedRestriction O U ⋙ H).mapIso e).isZero_iff).mp (hK U f hf)

end CategoryTheory.ConstantCompletion

namespace AlgebraicGeometry.ProEtale.IntegralModelsStacks

/-- An isomorphism of derived objects induces an isomorphism of their transports to the
small site. Proof: compare both transports with the derived functor of the section-module
equivalence `smallModules` on localization representatives. Source: Stacks Tag 05RU
(auxiliary; not a blueprint node). -/
def smallDerivedIso (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)}
    (e : K ≅ L) : smallDerivedObject X R K ≅ smallDerivedObject X R L := by
  let := HasDerivedCategory.standard (ConstantCompletion.Mod (smallRing X R))
  let F := smallModules X R
  have : F.IsEquivalence := InternalCompletionTransport.smallModules_equivalence X R
  have : F.Additive := ⟨by intros; ext U x; rfl⟩
  change DerivedCategory.Q.obj
      ((F.mapHomologicalComplex (.up ℤ)).obj (DerivedCategory.Q.objPreimage K)) ≅
    DerivedCategory.Q.obj
      ((F.mapHomologicalComplex (.up ℤ)).obj (DerivedCategory.Q.objPreimage L))
  exact (F.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage K)).symm ≪≫
    F.mapDerivedCategory.mapIso ((DerivedCategory.Q.objObjPreimageIso K) ≪≫ e ≪≫
      (DerivedCategory.Q.objObjPreimageIso L).symm) ≪≫
    F.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage L)

/-- Stacks adic constructibility is invariant under isomorphism. Proof: completeness by
`ConstantCompletion.IsComplete.of_iso` after `smallDerivedIso`, the residue clause by
`residueCondition_iso`.
Source: Stacks Tags 09C1 and 09C2 (auxiliary; not a blueprint node). -/
theorem stacksConstructible_iso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X]
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (discreteObj (Padic.coefficientExtensionIntegers l E)) X))}
    (e : K ≅ L) (hK : stacksConstructible l E X K) : stacksConstructible l E X L := by
  refine ⟨ConstantCompletion.IsComplete.of_iso (smallDerivedIso X _ e) hK.1, ?_⟩
  exact residueCondition_iso l E X e hK.2

end AlgebraicGeometry.ProEtale.IntegralModelsStacks
