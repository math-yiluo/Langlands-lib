/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Local.LocalAcyclicityAbelianSheaf
public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.GroupTheory.OrderOfElement
import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalConstantComparison
import WeilConjectures.AlgebraicGeometry.Constant.ConstantTorsionAcyclicDevissage
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Local acyclicity for locally constant torsion coefficients

## References

* Stacks Project, Tag 0GJR
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Local acyclicity extends to locally constant abelian sheaves whose stalk elements
have finite order prime to the residue characteristic; in characteristic zero every
finite order is allowed. No finiteness of stalks or common annihilator is assumed. -/
theorem isLocallyAcyclicRelative_of_locallyConstant_torsion
    {X S : Scheme.{u}} (f : X ⟶ S) (hf : IsLocallyAcyclic f)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    [Scheme.IsLocallyConstantSheaf G]
    (hG : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
      (m : ((Scheme.pointSmallEtale x).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj G),
      IsOfFinAddOrder m ∧
        (ringChar (X.residueField (x default)) = 0 ∨
          (addOrderOf m).Coprime (ringChar (X.residueField (x default))))) :
    IsLocallyAcyclicRelative f G := by
  intro Ω _ _ x Ω' _ _ t
  let M := (Scheme.pointSmallEtale x).sheafFiber.obj G
  let V := localAcyclicityFiber f x t
  let C := constantSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}
  let Γ := Sheaf.Γ V.smallEtaleTopology AddCommGrpCat.{u + 1}
  let η := (constantSheafΓAdj V.smallEtaleTopology AddCommGrpCat.{u + 1}).unit
  have : Limits.PreservesFilteredColimitsOfSize.{u, u}
      (forget AddCommGrpCat.{u + 1}) :=
    Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have : IsAffine (Scheme.strictHenselizationScheme x) := by
    unfold Scheme.strictHenselizationScheme
    infer_instance
  have : IsAffine (Scheme.strictHenselizationScheme (x ≫ f)) := by
    unfold Scheme.strictHenselizationScheme
    infer_instance
  have : IsAffine V := by
    dsimp [V, localAcyclicityFiber]
    infer_instance
  have hcyclic (n : ℕ) (hn : 0 < n)
      (hp : ringChar (X.residueField (x default)) = 0 ∨
        n.Coprime (ringChar (X.residueField (x default)))) := hf Ω x n hn hp Ω' t
  have hunit (n : ℕ) (hn : 0 < n)
      (hp : ringChar (X.residueField (x default)) = 0 ∨
        n.Coprime (ringChar (X.residueField (x default)))) :
      IsIso (η.app (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))) ∧
      ∀ q : ℕ, 0 < q → Limits.IsZero
        ((cohomology AddCommGrpCat.{u + 1} V (q : ℤ)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (C.obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))))) := by
    let N := AddCommGrpCat.of (ULift.{u + 1} (ZMod n))
    let F := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj N
    have hc : F.IsConstant X.smallEtaleTopology := ⟨N, ⟨Iso.refl _⟩⟩
    have : Scheme.IsLocallyConstantSheaf F := hc.isLocallyConstantSheaf
    obtain ⟨e, he⟩ := exists_strictLocalConstantComparison f x t F
    let a := (Scheme.pointSmallEtale x).sheafFiberConstantSheafIso N
    have hα := (hcyclic n hn hp).1
    rw [he] at hα
    have hη : IsIso (η.app ((Scheme.pointSmallEtale x).sheafFiber.obj F)) :=
      (isIso_comp_right_iff _ _).mp hα
    have hnatur : η.app N =
        a.inv ≫ η.app ((Scheme.pointSmallEtale x).sheafFiber.obj F) ≫
          (C ⋙ Γ).map a.hom := by
      rw [← η.naturality a.hom]
      simp
    constructor
    · rw [hnatur]
      infer_instance
    · intro q hq
      let H := DerivedCategory.singleFunctor _ 0 ⋙ cohomology AddCommGrpCat.{u + 1} V (q : ℤ)
      exact Limits.IsZero.of_iso ((hcyclic n hn hp).2 q hq)
        (H.mapIso ((C.mapIso a).symm ≪≫ e))
  obtain ⟨hη, hH⟩ := constantTorsion_acyclic_of_cyclic V
    (ringChar (X.residueField (x default))) hunit M (hG Ω x)
  obtain ⟨e, he⟩ := exists_strictLocalConstantComparison f x t G
  constructor
  · rw [he]
    infer_instance
  · intro q hq
    exact Limits.IsZero.of_iso (hH q hq)
      (((DerivedCategory.singleFunctor _ 0 ⋙
        cohomology AddCommGrpCat.{u + 1} V (q : ℤ)).mapIso e).symm)

end AlgebraicGeometry.Etale
