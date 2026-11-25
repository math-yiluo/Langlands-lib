/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Data.ZMod.Basic
import WeilConjectures.AlgebraicGeometry.FiniteLocalCyclicModuleForget
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.AlgebraicGeometry.ModuleAbelianInverseImageComparison
import WeilConjectures.ConstructibleSheaf.Pullback

/-! # Prime-field coefficients on a prime-annihilated constructible sheaf

Source: Stacks Project, Theorem 03SC, second proof paragraph.
(blueprint: lem-pbc-prime-coefficient-constructibility-transfer)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

private theorem finiteAbelianLocal_of_module {Λ : Type (u + 1)}
    [CommRing Λ] [Finite Λ] {Y : Scheme.{u}}
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsFiniteLocallyConstantSheaf F] :
    let G := (sheafCompose Y.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F
    IsLocallyConstantSheaf G ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y),
        Finite (((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj G) := by
  dsimp only
  constructor
  · obtain ⟨d⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := F)
    refine ⟨⟨⟨d.cover, fun i ↦ ?_⟩⟩⟩
    let := d.isConstant i
    have : GrothendieckTopology.PreservesSheafification
        (Y.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i))
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
      GrothendieckTopology.instPreservesSheafification _ _
    change ((sheafCompose (Y.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i))
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
      (F.over (d.cover.etalePrecoverageToEtale i))).IsConstant _
    infer_instance
  · intro Ω _ _ s
    let P := pointSmallEtale s
    let M := (P.sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F
    let : Module.Finite Λ M := (ModuleCat.isFinitelyGenerated_iff M).mp
      (IsFiniteSheaf.isFinitelyGenerated_sheafFiber Ω s)
    let : Finite M := Module.finite_of_finite Λ
    let : Limits.PreservesFilteredColimitsOfSize.{u, u}
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
      Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    let e := (P.sheafFiberCompIso
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).app F
    exact Finite.of_equiv M e.addCommGroupIsoToAddEquiv.toEquiv.symm

private noncomputable def moduleAbelianPullbackIso {X Y : Scheme.{u}}
    (g : Y ⟶ X) (Λ : Type (u + 1)) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Etale.upperStar AddCommGrpCat.{u + 1} g).obj
      ((sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) ≅
    (sheafCompose Y.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj F) := by
  let c := ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv
    ((sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F)
    ((sheafCompose Y.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj F))).symm
      ((sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
          ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app F))
  have : IsIso c := Etale.isIso_moduleAbelianInverseImageComparison g Λ F
  exact asIso c

/-- A prime-field module sheaf with the same underlying abelian sheaf as a
constructible sheaf over finite coefficients is constructible.
Source: Stacks Project, Theorem 03SC, second proof paragraph; Definition 03RW.
(blueprint: lem-pbc-prime-coefficient-constructibility-transfer)

Proof: Choose a finite constructible stratification for F and finite locally constant
module trivializations on each stratum. Forgetting coefficients commutes with inverse
image and restriction and sends each constant finite module value to its constant
abelian group. The given abelian sheaf isomorphism therefore gives local constant
finite abelian values for G on the same strata. Discard empty members of the covers.
On every remaining member, such a constant value is a geometric stalk. It is killed
by r, since G is a sheaf of prime-field modules. Equip this finite group with its
canonical ZMod r action, lifted to ULift (ZMod r). Every additive map between groups
killed by r commutes with that action: choose an integer representative of the scalar
and use preservation of repeated addition. Thus each abelian trivialization uniquely
lifts to a module trivialization of G. The finite values are finitely generated over
the prime field, so G is finite locally constant on every stratum. This witnesses
constructibility in the recorded module-sheaf sense. Empty strata need no nonempty
cover members; the zero sheaf and the zero coefficient ring cause no exception. -/
theorem isConstructibleSheaf_prime_of_underlyingAbelianIso
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u})
    (r : ℕ) [Fact r.Prime]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))))
    (e : (sheafCompose _ (forget₂
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) AddCommGrpCat.{u + 1})).obj G ≅
        (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) :
    IsConstructibleSheaf G := by
  classical
  let R := ULift.{u + 1} (ZMod r)
  let : NeZero r := ⟨(Fact.out : r.Prime).ne_zero⟩
  obtain ⟨S, hS⟩ := IsConstructibleSheaf.exists_stratification
    (A := ModuleCat.{u + 1} Λ)
    (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
    (CA := fun M : ModuleCat.{u + 1} Λ ↦ ↥M) (F := F)
  refine ⟨S, fun i ↦ ?_⟩
  let F' := (Etale.upperStar (ModuleCat.{u + 1} Λ) (S.immersion i)).obj F
  let G' := (Etale.upperStar (ModuleCat.{u + 1} R) (S.immersion i)).obj G
  let UF := (sheafCompose (S.domain i).smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F'
  let UG := (sheafCompose (S.domain i).smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).obj G'
  let e' : UG ≅ UF :=
    (moduleAbelianPullbackIso (S.immersion i) R G).symm ≪≫
      (Etale.upperStar AddCommGrpCat.{u + 1} (S.immersion i)).mapIso e ≪≫
      moduleAbelianPullbackIso (S.immersion i) Λ F
  let : IsFiniteLocallyConstantSheaf F' := hS i
  have hF' := finiteAbelianLocal_of_module F'
  let : IsLocallyConstantSheaf UF := hF'.1
  have hG' : IsLocallyConstantSheaf UG ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S.domain i),
        Finite (((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj UG) := by
    refine ⟨IsLocallyConstantSheaf.of_iso e'.symm, ?_⟩
    intro Ω _ _ s
    let := hF'.2 Ω s
    exact Finite.of_equiv _
      (((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).mapIso
        e'.symm).addCommGroupIsoToAddEquiv.toEquiv
  exact (finite_locally_constant_module_values_iff G').1.mp
    ((finite_local_cyclic_module_forget_iff r G').mp hG')

end AlgebraicGeometry.Scheme
