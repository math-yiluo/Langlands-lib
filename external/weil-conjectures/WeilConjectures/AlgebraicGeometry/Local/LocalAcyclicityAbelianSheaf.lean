/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import WeilConjectures.AlgebraicGeometry.Strict.Henselization.StrictHenselizationCanonicalMap
public import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalSectionCone
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Data.ZMod.Basic
import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import WeilConjectures.Mathlib.RingTheory.Henselian
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointedMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationComparison
import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.AlgebraicGeometry.EtalePointedMapRigidity
import WeilConjectures.AlgebraicGeometry.StrictHenselizationMapExists

/-!
# Local acyclicity relative to an abelian étale sheaf

## References

* Stacks Project, Tag 0GJP, preceding diagram
* Tags 04GU and 04HX
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The pointed map of strict localizations is unique. -/
theorem existsUnique_localAcyclicityStrictMap
    {X S : Scheme.{u}} (f : X ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) :
    ∃! h : Scheme.strictHenselizationScheme x ⟶ Scheme.strictHenselizationScheme (x ≫ f),
      h ≫ Scheme.strictHenselizationStructuralMap (x ≫ f) =
        Scheme.strictHenselizationStructuralMap x ≫ f ∧
      Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationRingPointEvaluation x)) ≫ h =
        Spec.map (CommRingCat.ofHom
          (Scheme.strictHenselizationRingPointEvaluation (x ≫ f))) :=
  Scheme.strictHenselizationMap_existsUnique f x

/-- The canonical pointed strict-local map induced by pulling back neighbourhoods. -/
noncomputable def localAcyclicityStrictMap
    {X S : Scheme.{u}} (f : X ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) :
    Scheme.strictHenselizationScheme x ⟶ Scheme.strictHenselizationScheme (x ≫ f) :=
  Classical.choose (existsUnique_localAcyclicityStrictMap f x)

/-- The variety of vanishing cycles, with no algebraicity requirement on the test point. -/
noncomputable def localAcyclicityFiber
    {X S : Scheme.{u}} (f : X ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']
    (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme (x ≫ f)) : Scheme.{u} :=
  pullback (localAcyclicityStrictMap f x) t

/-- The canonical map from the stalk to sections on the variety of vanishing cycles.
The uniquely characterized strict-local restriction is the inverse of the germ
isomorphism (Tags 03QO and 03Q1). It is followed by pullback of global sections and
the composition comparison for inverse images. -/
noncomputable def localAcyclicityAlpha
    {X S : Scheme.{u}} (f : X ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']
    (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme (x ≫ f))
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (Scheme.pointSmallEtale x).sheafFiber.obj G ⟶
      (Sheaf.Γ (localAcyclicityFiber f x t).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        ((upperStar AddCommGrpCat.{u + 1}
          (pullback.fst (localAcyclicityStrictMap f x) t ≫
            Scheme.strictHenselizationStructuralMap x)).obj G) :=
  Classical.choose ((strictLocalSectionCone x).existsUnique_restriction G) ≫
    globalSectionsUpperStarMap AddCommGrpCat.{u + 1}
      (pullback.fst (localAcyclicityStrictMap f x) t)
      ((upperStar AddCommGrpCat.{u + 1}
        (Scheme.strictHenselizationStructuralMap x)).obj G) ≫
    (Sheaf.Γ (localAcyclicityFiber f x t).smallEtaleTopology AddCommGrpCat.{u + 1}).map
      ((upperStarComp AddCommGrpCat.{u + 1}
        (pullback.fst (localAcyclicityStrictMap f x) t)
        (Scheme.strictHenselizationStructuralMap x)).inv.app G)

/-- Local acyclicity at a geometric point relative to an abelian sheaf: the canonical
map is an isomorphism in degree zero and all positive cohomology groups vanish. -/
def IsLocallyAcyclicAtRelative
    {X S : Scheme.{u}} (f : X ⟶ S) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) : Prop :=
  ∀ (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω']
    (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme (x ≫ f)),
    IsIso (localAcyclicityAlpha f x t G) ∧
      ∀ q : ℕ, 0 < q → IsZero
        ((cohomology AddCommGrpCat.{u + 1} (localAcyclicityFiber f x t) (q : ℤ)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((upperStar AddCommGrpCat.{u + 1}
              (pullback.fst (localAcyclicityStrictMap f x) t ≫
                Scheme.strictHenselizationStructuralMap x)).obj G)))

/-- Local acyclicity relative to an abelian sheaf at every geometric point. -/
def IsLocallyAcyclicRelative
    {X S : Scheme.{u}} (f : X ⟶ S)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
    IsLocallyAcyclicAtRelative f x G

/-- Local acyclicity for all constant cyclic coefficients of positive order prime
to the residue characteristic, including every positive order in characteristic zero. -/
def IsLocallyAcyclic
    {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
    (n : ℕ), 0 < n →
    (ringChar (X.residueField (x default)) = 0 ∨
      n.Coprime (ringChar (X.residueField (x default)))) →
    IsLocallyAcyclicAtRelative f x
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))))

/-- Universal local acyclicity: local acyclicity after every scheme base change. -/
def IsUniversallyLocallyAcyclic
    {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ (S' : Scheme.{u}) (g : S' ⟶ S), IsLocallyAcyclic (pullback.snd f g)

end AlgebraicGeometry.Etale
