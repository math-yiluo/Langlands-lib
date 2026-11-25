/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Algebra.Category.Grp.Biproducts
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.AlgebraicGeometry.EtaleDirectedCohomologyColimitExtension

/-!
# Extending acyclic constant coefficients from cyclic groups to torsion groups

Source: Stacks Project, Tag 0GJR, proof of lemma-locally-acyclic-locally-constant.
(blueprint: lem-weil-pbc-constant-torsion-acyclic-devissage).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- On a qcqs scheme, acyclicity and the constant-section isomorphism for positive
cyclic coefficients prime to p extend to all elementwise prime-to-p torsion groups.
The case p = 0 allows every finite order.
Source: Stacks Project, Tag 0GJR, proof of lemma-locally-acyclic-locally-constant.
(blueprint: lem-weil-pbc-constant-torsion-acyclic-devissage).

Proof: express M as the directed union of its finitely generated subgroups. Each is
finite by the finite-order assumption. Decompose each finite abelian subgroup into a
finite sum of nontrivial cyclic groups by the structure theorem. A cyclic generator
has the indicated order also in M, so its order is admissible. Constant sheaves and
cohomology preserve finite sums, and the constant-section unit is additive and natural;
therefore the claimed two conditions hold for every finite subgroup, including zero.
The constant-sheaf left adjoint preserves their filtered colimit. On a qcqs scheme
etale cohomology preserves filtered colimits in every nonnegative degree, as do sections.
In positive degrees the image cocone consists of zero groups, so its colimit is zero.
In degree zero naturality of the constant-section unit gives an isomorphism of diagrams,
whose colimit is the asserted unit for M. -/
theorem constantTorsion_acyclic_of_cyclic
    (V : Scheme.{u}) [CompactSpace V] [QuasiSeparatedSpace V] (p : ℕ)
    (hcyclic : ∀ n : ℕ, 0 < n → (p = 0 ∨ n.Coprime p) →
      IsIso ((constantSheafΓAdj V.smallEtaleTopology AddCommGrpCat.{u + 1}).unit.app
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))) ∧
      ∀ q : ℕ, 0 < q → IsZero
        ((cohomology AddCommGrpCat.{u + 1} V (q : ℤ)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((constantSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
              (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))))))
    (M : AddCommGrpCat.{u + 1})
    (hM : ∀ m : M, IsOfFinAddOrder m ∧ (p = 0 ∨ (addOrderOf m).Coprime p)) :
    IsIso ((constantSheafΓAdj V.smallEtaleTopology AddCommGrpCat.{u + 1}).unit.app M) ∧
      ∀ q : ℕ, 0 < q → IsZero
        ((cohomology AddCommGrpCat.{u + 1} V (q : ℤ)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((constantSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M))) := by
  classical
  let C := constantSheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}
  let Γ := Sheaf.Γ V.smallEtaleTopology AddCommGrpCat.{u + 1}
  let η := (constantSheafΓAdj V.smallEtaleTopology AddCommGrpCat.{u + 1}).unit
  let H (q : ℕ) := DerivedCategory.singleFunctor _ 0 ⋙
    cohomology AddCommGrpCat.{u + 1} V (q : ℤ)
  have : (rightDerivedGlobalSections AddCommGrpCat.{u + 1} V).Additive :=
    inferInstanceAs
      ((Sheaf.Γ V.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctor.Additive)
  have hHadd (q : ℕ) : (H q).Additive := by
    dsimp [H, cohomology]
    infer_instance
  have hfinite (A : AddCommGrpCat.{u + 1}) [Finite A]
      (hA : ∀ a : A, p = 0 ∨ (addOrderOf a).Coprime p) :
      IsIso (η.app A) ∧ ∀ q : ℕ, 0 < q → IsZero ((H q).obj (C.obj A)) := by
    obtain ⟨ι, _, n, hn, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' A
    let N (i : ι) := AddCommGrpCat.of (ULift.{u + 1} (ZMod (n i)))
    have hprime (i : ι) : p = 0 ∨ (n i).Coprime p := by
      let k := e.symm.toAddMonoidHom.comp (DirectSum.of (fun i ↦ ZMod (n i)) i)
      have hk : Function.Injective k := e.symm.injective.comp (DirectSum.of_injective i)
      have ho : addOrderOf (k 1) = n i :=
        (addOrderOf_injective k hk 1).trans (ZMod.addOrderOf_one _)
      simpa only [ho] using hA (k 1)
    have hN (i : ι) := hcyclic (n i) (lt_trans Nat.zero_lt_one (hn i)) (hprime i)
    let a : A ≅ ⨁ N :=
      ((e.trans (DirectSum.addEquivProd _)).trans
        (AddEquiv.piCongrRight (fun i ↦
          (AddEquiv.ulift (α := ZMod (n i))).symm))).toAddCommGrpIso ≪≫
      (AddCommGrpCat.biproductIsoPi N).symm
    have hηsum : IsIso (η.app (⨁ N)) := by
      have : IsIso (Functor.whiskerLeft (Discrete.functor N) η) :=
        (NatTrans.isIso_iff_isIso_app _).2 (fun i ↦ (hN i.as).1)
      exact isIso_app_coconePt_of_preservesColimit (Discrete.functor N) η
        (biproduct.bicone N).toCocone (biproduct.isColimit N)
    constructor
    · have heq : η.app A = a.hom ≫ η.app (⨁ N) ≫ (C ⋙ Γ).map a.inv := by
        rw [← η.naturality a.inv]
        simp
      rw [heq]
      infer_instance
    · intro q hq
      have hzero : IsZero (((Discrete.functor N) ⋙ C ⋙ H q)) :=
        Functor.isZero _ (fun i ↦ (hN i.as).2 q hq)
      have hz := (isColimitOfPreserves (C ⋙ H q) (biproduct.isColimit N)).isZero_pt hzero
      exact IsZero.of_iso hz ((C ⋙ H q).mapIso a)
  let I := {A : AddSubgroup M // A.FG}
  have : Nonempty I := ⟨⟨⊥, AddSubgroup.FG.bot⟩⟩
  have : IsDirectedOrder I := ⟨fun i j ↦
    ⟨⟨i.val ⊔ j.val, i.property.sup j.property⟩,
      (show i.val ≤ i.val ⊔ j.val from le_sup_left),
      (show j.val ≤ i.val ⊔ j.val from le_sup_right)⟩⟩
  let D : I ⥤ AddCommGrpCat.{u + 1} :=
    { obj := fun i ↦ AddCommGrpCat.of i.val
      map := fun {i j} h ↦ AddCommGrpCat.ofHom (AddSubgroup.inclusion (leOfHom h))
      map_id := by intros; rfl
      map_comp := by intros; rfl }
  let c : Cocone D :=
    { pt := M
      ι := { app := fun i ↦ AddCommGrpCat.ofHom i.val.subtype
             naturality := by intros; rfl } }
  have : ReflectsColimit D (forget AddCommGrpCat.{u + 1}) :=
    reflectsColimit_of_reflectsIsomorphisms D _
  have hc : IsColimit c := by
    apply isColimitOfReflects (forget AddCommGrpCat.{u + 1})
    refine Types.FilteredColimit.isColimitOf' _ _ ?_ ?_
    · intro m
      let A := AddSubgroup.closure ({m} : Set M)
      have hA : A.FG := AddSubgroup.isAddFG_iff.mpr ⟨{m}, by simp [A]⟩
      exact ⟨⟨A, hA⟩, ⟨m, AddSubgroup.subset_closure (by simp)⟩, rfl⟩
    · intro i a b hab
      exact ⟨i, 𝟙 i, Subtype.ext hab⟩
  have hD (i : I) : IsIso (η.app (D.obj i)) ∧
      ∀ q : ℕ, 0 < q → IsZero ((H q).obj (C.obj (D.obj i))) := by
    have : AddGroup.FG i.val := (AddGroup.fg_iff_addSubgroup_fg _).2 i.property
    have ht : IsAddTorsion i.val := fun a ↦
      (Function.Injective.isOfFinAddOrder_iff (f := i.val.subtype)
        Subtype.coe_injective).1 (hM a.val).1
    have : Finite i.val := AddCommGroup.finite_of_fg_isAddTorsion i.val ht
    apply hfinite
    intro a
    rw [← addOrderOf_injective i.val.subtype Subtype.coe_injective a]
    exact (hM a.val).2
  have hpres (q : ℕ) : PreservesColimitsOfShape I (H q) :=
    ⟨fun {F} ↦ ⟨fun {d} hd ↦
      Scheme.etaleCohomology_isColimit_of_isFiltered_coefficientSize V hd q⟩⟩
  have e₀ : H 0 ≅ Γ :=
    (Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0)
        Γ.rightDerivedFunctorPlusCompatibility.symm)
      (DerivedCategory.homologyFunctor AddCommGrpCat (0 : ℤ)) ≪≫
        Γ.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso 0) ≪≫
      Γ.rightDerivedZeroIsoSelf
  have := hpres 0
  have : PreservesColimitsOfShape I Γ := preservesColimitsOfShape_of_natIso e₀
  constructor
  · have : IsIso (Functor.whiskerLeft D η) :=
      (NatTrans.isIso_iff_isIso_app _).2 (fun i ↦ (hD i).1)
    exact isIso_app_coconePt_of_preservesColimit D η c hc
  · intro q hq
    have := hpres q
    have hz : IsZero (D ⋙ C ⋙ H q) := Functor.isZero _ (fun i ↦ (hD i).2 q hq)
    exact (isColimitOfPreserves (C ⋙ H q) hc).isZero_pt hz

end AlgebraicGeometry.Etale
