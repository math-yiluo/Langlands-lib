/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectProjection.PerfectProjectionFormula
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnityInverseImageSupplement
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.RootsOfUnityInverseImageIso
public import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheavesSupplement
public import WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageTensorHomDefinitions
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf

/-! # Canonical root-tower pullback and tensor coherence

Source: Stacks Project, Tags 03CO, 03DB, 03CB, 03EL and 03D7; vector-bundle purity,
proof paragraph 1 (blueprint: lem-amb-root-tower-pullback-coherence).

Index `s : ℕ` means the positive exponent `s + 1`. Maps are specified by their
adjuncts, so identity and composition use the actual fibre-product comparisons.
The root limit and its completed action are the existing `purTwistZlOne` and
`purTwistZlModule`. Only restriction to constant scalars is used here.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Scheme

-- Avoid the broad abelian-coefficient search when constructing ring sheafification.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology

variable (l : ℕ) [Fact l.Prime]

set_option maxHeartbeats 100000 in
-- Bound the one-time search for the cached sheafification proof.
/-- The canonical ring sheafification instance, cached for the constructions below. -/
theorem ambRootRingSheafify (S : Scheme.{u}) :
    HasWeakSheafify (ProEt.topology S) RingCat.{u + 1} := inferInstance

set_option maxHeartbeats 100000 in
-- Bound the one-time search for the cached sheafification proof.
/-- The canonical abelian sheafification instance, cached for the constructions below. -/
theorem ambRootAbSheafify (S : Scheme.{u}) :
    HasWeakSheafify (ProEt.topology S) AddCommGrpCat.{u + 1} :=
  (CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
    AddCommGrpCat.{u + 1} S).isRightAdjoint

attribute [local instance] PerfectProjection.completedCommRingWeakSheafify
  ambRootRingSheafify ambRootAbSheafify

/-- The canonical limit instance of the existing root tower, cached for its projections. -/
theorem ambRootHasLimit (S : Scheme.{u}) :
    HasLimit (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)) := inferInstance

attribute [local instance] ambRootHasLimit

-- Keep the chosen scalar structures abstract while elaborating their module carriers.
attribute [local irreducible] purTwistZlAction purTwistFiniteRingIso

/-- The constant scalar action, by the existing completion map and coordinate action.
Source: Stacks Tags 03CO/03DB (blueprint: lem-amb-root-tower-pullback-coherence). -/
def ambRootAction (T : Scheme.{u}) (U : T.ProEtᵒᵖ)
    (a : (purTwistZlConstant T l).obj.obj U) (x : (purTwistZlOne T l).obj.obj U) :
    (purTwistZlOne T l).obj.obj U :=
  @SMul.smul _ _ (purTwistZlAction T l U).toSMul
    ((purTwistZlCompletionMap T l).hom.app U a) x

/-- The constant scalar homomorphism induced by the specified Z_l-algebra structure.
Source: Stacks Tag 03EK (blueprint: lem-amb-root-tower-pullback-coherence). -/
def ambRootScalar (B : Type u) [CommRing B] [Algebra ℤ_[l] B] (T : Scheme.{u}) :
    purTwistZlConstant T l ⟶ proEtaleConstantRing T B :=
  (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((algebraMap ℤ_[l] B).comp ULift.ringEquiv.toRingHom)))

attribute [irreducible] ambRootScalar

/-- H_T, the ordinary tensor of the existing root limit with B over constant Z_l.
Source: Stacks Tag 03EK (blueprint: lem-amb-root-tower-pullback-coherence). -/
def ambRootTensor (B : Type u) [CommRing B] [Algebra ℤ_[l] B] (T : Scheme.{u}) :
    SheafOfModules.{u + 1} (purTwistRing T (proEtaleConstantRing T B)) :=
  SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
    (ambRootScalar l B T)
    ((SheafOfModules.restrictScalars
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (purTwistZlCompletionMap T l))).obj (purTwistZlModule T l))

/-- The actual sheafification image of x tensor b, written with the scalar first.
Source: Stacks Tag 03EK (blueprint: lem-amb-root-tower-pullback-coherence). -/
def ambRootTensorPure (B : Type u) [CommRing B] [Algebra ℤ_[l] B]
    (T : Scheme.{u}) (U : T.ProEt)
    (b : (proEtaleConstantRing T B).obj.obj (op U))
    (x : (purTwistZlOne T l).obj.obj (op U)) :
    (ambRootTensor l B T).val.obj (op U) :=
  purScalarSection (purTwistZlConstant T l) (proEtaleConstantRing T B)
    (ambRootScalar l B T)
    ((SheafOfModules.restrictScalars
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (purTwistZlCompletionMap T l))).obj (purTwistZlModule T l)) U b x

/-- The unique finite-ring scalar map on a killed algebra, using ZMod's cast map.
Source: Stacks Tag 03EK (blueprint: lem-amb-root-tower-pullback-coherence). -/
def ambRootFiniteScalar (B : Type u) [CommRing B] (r : ℕ)
    (hB : ((l ^ (r + 1) : ℕ) : B) = 0) (T : Scheme.{u}) :
    purTwistFiniteRing T l r ⟶ proEtaleConstantRing T B :=
  (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((ZMod.castHom
        ((CharP.cast_eq_zero_iff B (ringChar B) (l ^ (r + 1))).mp
          hB) B).comp
        ULift.ringEquiv.toRingHom)))

attribute [irreducible] ambRootFiniteScalar

/-- D_r,T is the finite root module tensored over its finite constant ring with B.
Source: Stacks Tag 03EK (blueprint: lem-amb-root-tower-pullback-coherence). -/
def ambRootFiniteTensor (B : Type u) [CommRing B] (r : ℕ)
    (hB : ((l ^ (r + 1) : ℕ) : B) = 0) (T : Scheme.{u}) :
    SheafOfModules.{u + 1} (purTwistRing T (proEtaleConstantRing T B)) :=
  SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
    (ambRootFiniteScalar l B r hB T) (purTwistRootsModule T l r)

/-- The actual sheafification image of a finite root tensor b.
Source: Stacks Tag 03EK (blueprint: lem-amb-root-tower-pullback-coherence). -/
def ambRootFinitePure (B : Type u) [CommRing B] (r : ℕ)
    (hB : ((l ^ (r + 1) : ℕ) : B) = 0) (T : Scheme.{u}) (U : T.ProEt)
    (b : (proEtaleConstantRing T B).obj.obj (op U))
    (x : (proEtaleRootsOfUnitySheaf T (l ^ (r + 1))).obj.obj (op U)) :
    (ambRootFiniteTensor l B r hB T).val.obj (op U) :=
  purScalarSection (purTwistFiniteRing T l r) (proEtaleConstantRing T B)
    (ambRootFiniteScalar l B r hB T) (purTwistRootsModule T l r) U b x

/-- A named component of canonical root pullback coherence.
Source: Stacks Tags 03CB and 03CO (blueprint: lem-amb-root-tower-pullback-coherence). -/
def AmbRootConstantIso : Prop :=
∀ {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T),
    IsIso (proEtaleConstantInverseImageMap v CommRingCat.{u + 1}
      (CommRingCat.of (ULift.{u + 1} ℤ_[l]))) ∧
    (∀ s : ℕ, IsIso (proEtaleConstantInverseImageMap v CommRingCat.{u + 1}
      (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (s + 1))))))) ∧
    ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B],
      IsIso (proEtaleCoefficientInverseImageMap v B)

attribute [local irreducible] AmbRootConstantIso

/-- A named component of canonical root pullback coherence.
Source: Stacks Tags 03CB and 03CO (blueprint: lem-amb-root-tower-pullback-coherence). -/
def AmbRootTransition : Prop :=
∀ {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T) (s : ℕ),
    (proEtaleSheafInverseImage v AddCommGrpCat.{u + 1}).map
        ((proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)).map
          (homOfLE (Nat.le_succ s)).op) ≫
        proEtaleRootsOfUnityInverseImageMap v (l ^ (s + 1)) =
      proEtaleRootsOfUnityInverseImageMap v (l ^ (s + 2)) ≫
        (proEtaleRootsOfUnityTower T' l (Fact.out : l.Prime)).map
          (homOfLE (Nat.le_succ s)).op

attribute [local irreducible] AmbRootTransition

/-- The specified finite-root semilinearity proposition, kept abstract during record generation.
Source: Stacks Tag 03CY (blueprint: lem-amb-root-tower-pullback-coherence). -/
def AmbRootFiniteSemilinear : Prop :=
∀ {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T) (s : ℕ) (U : T'.ProEtᵒᵖ)
    (a : (proEtaleRootsOfUnityInverseImageRing v (l ^ (s + 1))).obj.obj U)
    (x : ((proEtaleSheafInverseImage v AddCommGrpCat.{u + 1}).obj
      (proEtaleRootsOfUnitySheaf T (l ^ (s + 1)))).obj.obj U),
    (proEtaleRootsOfUnityInverseImageMap v (l ^ (s + 1))).hom.app U
      (@SMul.smul _ _ (proEtaleRootsOfUnityInverseImageAction v (l ^ (s + 1))
        (pow_pos (Fact.out : l.Prime).pos _) U).toSMul a x) =
      @SMul.smul _ _ (torsionSheafModuleStructure.{u + 1} (ProEt.topology T')
        (l ^ (s + 1)) (pow_pos (Fact.out : l.Prime).pos _)
        (proEtaleRootsOfUnitySheaf T' (l ^ (s + 1)))
        (proEtaleRootsOfUnity_nsmul T' (l ^ (s + 1))) U).toSMul
        ((proEtaleConstantInverseImageMap v RingCat.{u + 1}
          (RingCat.of (ULift.{u + 1} (ZMod (l ^ (s + 1)))))).hom.app U a)
        ((proEtaleRootsOfUnityInverseImageMap v (l ^ (s + 1))).hom.app U x)

attribute [local irreducible] AmbRootFiniteSemilinear

/-- Identity of finite root maps, transposed under the specified adjunction.
Source: Stacks Tags 03CO and 03EK
(blueprint: lem-amb-root-tower-pullback-coherence). -/
def AmbRootLawRootId : Prop :=
∀ (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.presheaf.stalk x)] (s : ℕ) (U : T.ProEt)
    (x : (proEtaleRootsOfUnitySheaf T (l ^ (s + 1))).obj.obj (op U)),
    (proEtaleRootsOfUnityDirectImageMap (𝟙 T) (l ^ (s + 1))).hom.app (op U) x =
      (proEtaleRootsOfUnitySheaf T (l ^ (s + 1))).obj.map
        ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).hom.app U).op x

attribute [local irreducible] AmbRootLawRootId

/-- Composition of the specified finite root maps.
Source: Stacks Tags 03CO and 03EK
(blueprint: lem-amb-root-tower-pullback-coherence). -/
def AmbRootLawRootComp : Prop :=
∀ {T T' T'' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)]
    [∀ x : T'', Invertible (l : T''.presheaf.stalk x)] (v : T' ⟶ T) (w : T'' ⟶ T')
    (s : ℕ) (U : T.ProEt)
    (x : (proEtaleRootsOfUnitySheaf T (l ^ (s + 1))).obj.obj (op U)),
    (proEtaleRootsOfUnityDirectImageMap (w ≫ v) (l ^ (s + 1))).hom.app (op U) x =
      (proEtaleRootsOfUnitySheaf T'' (l ^ (s + 1))).obj.map
        ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) w v).hom.app U).op
        ((proEtaleRootsOfUnityDirectImageMap w (l ^ (s + 1))).hom.app
          (op ((proEtaleBaseChange v).obj U))
          ((proEtaleRootsOfUnityDirectImageMap v (l ^ (s + 1))).hom.app (op U) x))

attribute [local irreducible] AmbRootLawRootComp

/-- The specified projection equation, transposed under adjunction.
Source: Stacks Tags 03CO and 03EK
(blueprint: lem-amb-root-tower-pullback-coherence). -/
def AmbRootLawCProjection
    (c : ∀ {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T),
    purTwistZlOne T l ⟶
      (proEtaleSheafDirectImage v AddCommGrpCat.{u + 1}).obj (purTwistZlOne T' l)) : Prop :=
∀ {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T) (s : ℕ),
    c v ≫ (proEtaleSheafDirectImage v AddCommGrpCat.{u + 1}).map
        (limit.π (proEtaleRootsOfUnityTower T' l (Fact.out : l.Prime)) (op s)) =
      limit.π (proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)) (op s) ≫
        proEtaleRootsOfUnityDirectImageMap v (l ^ (s + 1))

attribute [local irreducible] AmbRootLawCProjection

/-- Uniqueness among all additive maps with the specified projections.
Source: Stacks Tags 03CO and 03EK
(blueprint: lem-amb-root-tower-pullback-coherence). -/
def AmbRootLawCUnique
    (c : ∀ {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T),
    purTwistZlOne T l ⟶
      (proEtaleSheafDirectImage v AddCommGrpCat.{u + 1}).obj (purTwistZlOne T' l)) : Prop :=
∀ {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T)
    (f : purTwistZlOne T l ⟶
      (proEtaleSheafDirectImage v AddCommGrpCat.{u + 1}).obj (purTwistZlOne T' l)),
    (∀ s : ℕ, f ≫ (proEtaleSheafDirectImage v AddCommGrpCat.{u + 1}).map
        (limit.π (proEtaleRootsOfUnityTower T' l (Fact.out : l.Prime)) (op s)) =
      limit.π (proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)) (op s) ≫
        proEtaleRootsOfUnityDirectImageMap v (l ^ (s + 1))) → f = c v

attribute [local irreducible] AmbRootLawCUnique

/-- Constant Z_l-linearity of c_L, in its equivalent adjunct form.
Source: Stacks Tags 03CO and 03EK
(blueprint: lem-amb-root-tower-pullback-coherence). -/
def AmbRootLawCLinear
    (c : ∀ {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T),
    purTwistZlOne T l ⟶
      (proEtaleSheafDirectImage v AddCommGrpCat.{u + 1}).obj (purTwistZlOne T' l)) : Prop :=
∀ {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T) (U : T.ProEt)
    (a : (purTwistZlConstant T l).obj.obj (op U))
    (x : (purTwistZlOne T l).obj.obj (op U)),
    (c v).hom.app (op U) (ambRootAction l T (op U) a x) =
      ambRootAction l T' (op ((proEtaleBaseChange v).obj U))
        ((proEtaleConstantDirectImageMap v CommRingCat.{u + 1}
          (CommRingCat.of (ULift.{u + 1} ℤ_[l]))).hom.app (op U) a)
        ((c v).hom.app (op U) x)

attribute [local irreducible] AmbRootLawCLinear

/-- Identity of c_L under the canonical fibre-product identity.
Source: Stacks Tags 03CO and 03EK
(blueprint: lem-amb-root-tower-pullback-coherence). -/
def AmbRootLawCId
    (c : ∀ {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T),
    purTwistZlOne T l ⟶
      (proEtaleSheafDirectImage v AddCommGrpCat.{u + 1}).obj (purTwistZlOne T' l)) : Prop :=
∀ (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.presheaf.stalk x)] (U : T.ProEt)
    (x : (purTwistZlOne T l).obj.obj (op U)),
    (c (𝟙 T)).hom.app (op U) x = (purTwistZlOne T l).obj.map
      ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).hom.app U).op x

attribute [local irreducible] AmbRootLawCId

/-- Composition of c_L under the canonical fibre-product associator.
Source: Stacks Tags 03CO and 03EK
(blueprint: lem-amb-root-tower-pullback-coherence). -/
def AmbRootLawCComp
    (c : ∀ {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T),
    purTwistZlOne T l ⟶
      (proEtaleSheafDirectImage v AddCommGrpCat.{u + 1}).obj (purTwistZlOne T' l)) : Prop :=
∀ {T T' T'' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)]
    [∀ x : T'', Invertible (l : T''.presheaf.stalk x)] (v : T' ⟶ T) (w : T'' ⟶ T')
    (U : T.ProEt)
    (x : (purTwistZlOne T l).obj.obj (op U)),
    (c (w ≫ v)).hom.app (op U) x = (purTwistZlOne T'' l).obj.map
      ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) w v).hom.app U).op
      ((c w).hom.app (op ((proEtaleBaseChange v).obj U)) ((c v).hom.app (op U) x))

attribute [local irreducible] AmbRootLawCComp

/-- Tensor normalization: h_v is c_L tensor 1, not an arbitrary map.
Source: Stacks Tags 03CO and 03EK
(blueprint: lem-amb-root-tower-pullback-coherence). -/
def AmbRootLawHPure
    (H : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B] (T : Scheme.{u}),
      SheafOfModules.{u + 1} (purTwistRing T (proEtaleConstantRing T B)))
    (HP : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B]
      (T : Scheme.{u}) (U : T.ProEt)
      (_b : (proEtaleConstantRing T B).obj.obj (op U))
      (_x : (purTwistZlOne T l).obj.obj (op U)), (H B T).val.obj (op U))
    (c : ∀ {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T),
    purTwistZlOne T l ⟶
      (proEtaleSheafDirectImage v AddCommGrpCat.{u + 1}).obj (purTwistZlOne T' l))
    (h : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B]
    {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T),
    H B T ⟶
      (proEtaleConstantModuleDirectImage v B).obj (H B T')) : Prop :=
∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B]
    {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T) (U : T.ProEt)
    (b : (proEtaleConstantRing T B).obj.obj (op U))
    (x : (purTwistZlOne T l).obj.obj (op U)),
    (h B v).val.app (op U) (HP B T U b x) =
      HP B T' ((proEtaleBaseChange v).obj U)
        ((proEtaleCoefficientDirectImageMap v B).hom.app (op U) b)
        ((c v).hom.app (op U) x)

attribute [local irreducible] AmbRootLawHPure

/-- Identity of h_v on all sections.
Source: Stacks Tags 03CO and 03EK
(blueprint: lem-amb-root-tower-pullback-coherence). -/
def AmbRootLawHId
    (H : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B] (T : Scheme.{u}),
      SheafOfModules.{u + 1} (purTwistRing T (proEtaleConstantRing T B)))
    (h : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B]
    {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T),
    H B T ⟶
      (proEtaleConstantModuleDirectImage v B).obj (H B T')) : Prop :=
∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B]
    (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.presheaf.stalk x)] (U : T.ProEt)
    (x : (H B T).val.obj (op U)),
    (h B (𝟙 T)).val.app (op U) x = (H B T).val.map
      ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).hom.app U).op x

attribute [local irreducible] AmbRootLawHId

/-- Composition of h_v on all sections, with the canonical associator.
Source: Stacks Tags 03CO and 03EK
(blueprint: lem-amb-root-tower-pullback-coherence). -/
def AmbRootLawHComp
    (H : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B] (T : Scheme.{u}),
      SheafOfModules.{u + 1} (purTwistRing T (proEtaleConstantRing T B)))
    (h : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B]
    {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T),
    H B T ⟶
      (proEtaleConstantModuleDirectImage v B).obj (H B T')) : Prop :=
∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B]
    {T T' T'' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)]
    [∀ x : T'', Invertible (l : T''.presheaf.stalk x)] (v : T' ⟶ T) (w : T'' ⟶ T')
    (U : T.ProEt) (x : (H B T).val.obj (op U)),
    (h B (w ≫ v)).val.app (op U) x = (H B T'').val.map
      ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) w v).hom.app U).op
      ((h B w).val.app (op ((proEtaleBaseChange v).obj U)) ((h B v).val.app (op U) x))

attribute [local irreducible] AmbRootLawHComp

/-- The projection formula determining alpha.
Source: Stacks Tags 03CO and 03EK
(blueprint: lem-amb-root-tower-pullback-coherence). -/
def AmbRootLawAlphaPure
    (H : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B] (T : Scheme.{u}),
      SheafOfModules.{u + 1} (purTwistRing T (proEtaleConstantRing T B)))
    (HP : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B]
      (T : Scheme.{u}) (U : T.ProEt)
      (_b : (proEtaleConstantRing T B).obj.obj (op U))
      (_x : (purTwistZlOne T l).obj.obj (op U)), (H B T).val.obj (op U))
    (D : ∀ (B : Type u) [CommRing B] (n : ℕ)
      (_hB : ((l ^ (n + 1) : ℕ) : B) = 0) (T : Scheme.{u}),
      SheafOfModules.{u + 1} (purTwistRing T (proEtaleConstantRing T B)))
    (DP : ∀ (B : Type u) [CommRing B] (n : ℕ)
      (_hB : ((l ^ (n + 1) : ℕ) : B) = 0) (T : Scheme.{u}) (U : T.ProEt)
      (_b : (proEtaleConstantRing T B).obj.obj (op U))
      (_x : (proEtaleRootsOfUnitySheaf T (l ^ (n + 1))).obj.obj (op U)),
      (D B n _hB T).val.obj (op U))
    (alpha : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B] (r : ℕ)
    (hB : ((l ^ (r + 1) : ℕ) : B) = 0) (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.presheaf.stalk x)],
    H B T ⟶ D B r hB T) : Prop :=
∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B] (r : ℕ)
    (hB : ((l ^ (r + 1) : ℕ) : B) = 0) (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.presheaf.stalk x)] (U : T.ProEt)
    (b : (proEtaleConstantRing T B).obj.obj (op U))
    (x : (purTwistZlOne T l).obj.obj (op U)),
    (alpha B r hB T).val.app (op U) (HP B T U b x) =
      DP B r hB T U b
        ((limit.π (proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)) (op r)).hom.app (op U) x)

attribute [local irreducible] AmbRootLawAlphaPure

/-- Normalization of the finite tensor map by the specified root adjunct.
Source: Stacks Tags 03CO and 03EK
(blueprint: lem-amb-root-tower-pullback-coherence). -/
def AmbRootLawDPure
    (D : ∀ (B : Type u) [CommRing B] (n : ℕ)
      (_hB : ((l ^ (n + 1) : ℕ) : B) = 0) (T : Scheme.{u}),
      SheafOfModules.{u + 1} (purTwistRing T (proEtaleConstantRing T B)))
    (DP : ∀ (B : Type u) [CommRing B] (n : ℕ)
      (_hB : ((l ^ (n + 1) : ℕ) : B) = 0) (T : Scheme.{u}) (U : T.ProEt)
      (_b : (proEtaleConstantRing T B).obj.obj (op U))
      (_x : (proEtaleRootsOfUnitySheaf T (l ^ (n + 1))).obj.obj (op U)),
      (D B n _hB T).val.obj (op U))
    (d : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B] (r : ℕ)
    (hB : ((l ^ (r + 1) : ℕ) : B) = 0) {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T),
    D B r hB T ⟶
      (proEtaleConstantModuleDirectImage v B).obj (D B r hB T')) : Prop :=
∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B] (r : ℕ)
    (hB : ((l ^ (r + 1) : ℕ) : B) = 0) {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T) (U : T.ProEt)
    (b : (proEtaleConstantRing T B).obj.obj (op U))
    (x : (proEtaleRootsOfUnitySheaf T (l ^ (r + 1))).obj.obj (op U)),
    (d B r hB v).val.app (op U) (DP B r hB T U b x) =
      DP B r hB T' ((proEtaleBaseChange v).obj U)
        ((proEtaleCoefficientDirectImageMap v B).hom.app (op U) b)
        ((proEtaleRootsOfUnityDirectImageMap v (l ^ (r + 1))).hom.app (op U) x)

attribute [local irreducible] AmbRootLawDPure

/-- Exactly the displayed reduction square, transposed under module adjunction.
Source: Stacks Tags 03CO and 03EK
(blueprint: lem-amb-root-tower-pullback-coherence). -/
def AmbRootLawSquare
    (H : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B] (T : Scheme.{u}),
      SheafOfModules.{u + 1} (purTwistRing T (proEtaleConstantRing T B)))
    (D : ∀ (B : Type u) [CommRing B] (n : ℕ)
      (_hB : ((l ^ (n + 1) : ℕ) : B) = 0) (T : Scheme.{u}),
      SheafOfModules.{u + 1} (purTwistRing T (proEtaleConstantRing T B)))
    (h : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B]
    {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T),
    H B T ⟶
      (proEtaleConstantModuleDirectImage v B).obj (H B T'))
    (alpha : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B] (r : ℕ)
    (hB : ((l ^ (r + 1) : ℕ) : B) = 0) (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.presheaf.stalk x)],
    H B T ⟶ D B r hB T)
    (d : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B] (r : ℕ)
    (hB : ((l ^ (r + 1) : ℕ) : B) = 0) {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T),
    D B r hB T ⟶
      (proEtaleConstantModuleDirectImage v B).obj (D B r hB T')) : Prop :=
∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B] (r : ℕ)
    (hB : ((l ^ (r + 1) : ℕ) : B) = 0) {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T),
    h B v ≫ (proEtaleConstantModuleDirectImage v B).map (alpha B r hB T') =
      alpha B r hB T ≫ d B r hB v

attribute [local irreducible] AmbRootLawSquare

-- Keep large dependent constructor equations out of the generated API.
set_option genCtorIdx false in
set_option genSizeOf false in
set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- All canonical maps and their normalizations. The maps c, h and d are direct-image
adjuncts of c_L, h_v and c_r tensor 1; their section equations are equations on the
original unit sections, not an assertion that pulled-back sections are pure tensors.
Source: Stacks Tags 03CO, 03DB, 03CB, 03EL and 03D7
(blueprint: lem-amb-root-tower-pullback-coherence). -/
structure AmbRootTowerPullbackCoherenceData
    (H : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B] (T : Scheme.{u}),
      SheafOfModules.{u + 1} (purTwistRing T (proEtaleConstantRing T B)))
    (HP : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B]
      (T : Scheme.{u}) (U : T.ProEt)
      (_b : (proEtaleConstantRing T B).obj.obj (op U))
      (_x : (purTwistZlOne T l).obj.obj (op U)), (H B T).val.obj (op U))
    (D : ∀ (B : Type u) [CommRing B] (n : ℕ)
      (_hB : ((l ^ (n + 1) : ℕ) : B) = 0) (T : Scheme.{u}),
      SheafOfModules.{u + 1} (purTwistRing T (proEtaleConstantRing T B)))
    (DP : ∀ (B : Type u) [CommRing B] (n : ℕ)
      (_hB : ((l ^ (n + 1) : ℕ) : B) = 0) (T : Scheme.{u}) (U : T.ProEt)
      (_b : (proEtaleConstantRing T B).obj.obj (op U))
      (_x : (proEtaleRootsOfUnitySheaf T (l ^ (n + 1))).obj.obj (op U)),
      (D B n _hB T).val.obj (op U)) where
  /-- Constant-ring comparisons are the specified structure maps and are invertible. -/
  constant_iso : AmbRootConstantIso.{u} l
  /-- Finite root maps commute with the power transitions. -/
  root_transition : AmbRootTransition.{u} l
  /-- Semilinearity over the actual inverse-image finite ring structure map. -/
  root_linear : AmbRootFiniteSemilinear.{u} l
  /-- Identity of finite root maps, transposed under the specified adjunction. -/
  root_id : AmbRootLawRootId.{u} l
  /-- Composition of the specified finite root maps. -/
  root_comp : AmbRootLawRootComp.{u} l
  /-- The adjunct of the map to the target inverse limit. -/
  c : ∀ {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T),
    purTwistZlOne T l ⟶
      (proEtaleSheafDirectImage v AddCommGrpCat.{u + 1}).obj (purTwistZlOne T' l)
  /-- The specified projection equation, transposed under adjunction. -/
  c_projection : AmbRootLawCProjection.{u} l c
  /-- Uniqueness among all additive maps with the specified projections. -/
  c_unique : AmbRootLawCUnique.{u} l c
  /-- Constant Z_l-linearity of c_L, in its equivalent adjunct form. -/
  c_linear : AmbRootLawCLinear.{u} l c
  /-- Identity of c_L under the canonical fibre-product identity. -/
  c_id : AmbRootLawCId.{u} l c
  /-- Composition of c_L under the canonical fibre-product associator. -/
  c_comp : AmbRootLawCComp.{u} l c
  /-- The B-linear adjunct of h_v. -/
  h : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B]
    {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T),
    H B T ⟶
      (proEtaleConstantModuleDirectImage v B).obj (H B T')
  /-- Tensor normalization: h_v is c_L tensor 1, not an arbitrary map. -/
  h_pure : AmbRootLawHPure.{u} l H HP c h
  /-- Identity of h_v on all sections. -/
  h_id : AmbRootLawHId.{u} l H h
  /-- Composition of h_v on all sections, with the canonical associator. -/
  h_comp : AmbRootLawHComp.{u} l H h
  /-- The B-linear projection-induced reduction, without an invertibility claim. -/
  alpha : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B] (r : ℕ)
    (hB : ((l ^ (r + 1) : ℕ) : B) = 0) (T : Scheme.{u})
    [∀ x : T, Invertible (l : T.presheaf.stalk x)],
    H B T ⟶ D B r hB T
  /-- The projection formula determining alpha. -/
  alpha_pure : AmbRootLawAlphaPure.{u} l H HP D DP alpha
  /-- The B-linear adjunct of the finite root map tensor 1. -/
  d : ∀ (B : Type u) [CommRing B] [Algebra ℤ_[l] B] (r : ℕ)
    (hB : ((l ^ (r + 1) : ℕ) : B) = 0) {T T' : Scheme.{u}}
    [∀ x : T, Invertible (l : T.presheaf.stalk x)]
    [∀ x : T', Invertible (l : T'.presheaf.stalk x)] (v : T' ⟶ T),
    D B r hB T ⟶
      (proEtaleConstantModuleDirectImage v B).obj (D B r hB T')
  /-- Normalization of the finite tensor map by the specified root adjunct. -/
  d_pure : AmbRootLawDPure.{u} l D DP d
  /-- Exactly the displayed reduction square, transposed under module adjunction. -/
  square : AmbRootLawSquare.{u} l H D h alpha d

/-- The coherence data for the specified ordinary root tensors.
Source: Stacks Tags 03CO, 03DB, 03CB, 03EL and 03D7
(blueprint: lem-amb-root-tower-pullback-coherence). -/
abbrev AmbRootTowerPullbackCoherence :=
  AmbRootTowerPullbackCoherenceData l (ambRootTensor l) (ambRootTensorPure l)
    (ambRootFiniteTensor l) (ambRootFinitePure l)

attribute [local semireducible] AmbRootFiniteSemilinear AmbRootTransition AmbRootConstantIso
attribute [local semireducible]
  AmbRootLawRootId
  AmbRootLawRootComp
  AmbRootLawCProjection
  AmbRootLawCUnique
  AmbRootLawCLinear
  AmbRootLawCId
  AmbRootLawCComp
  AmbRootLawHPure
  AmbRootLawHId
  AmbRootLawHComp
  AmbRootLawAlphaPure
  AmbRootLawDPure
  AmbRootLawSquare

set_option backward.isDefEq.respectTransparency false

private theorem constant_adjunct {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : CommRingCat.{u + 1}) :
    (sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
      ((Functor.const Y.ProEtᵒᵖ).obj A)
      ((proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
        ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj A))
      (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A) =
    Functor.whiskerLeft (proEtaleBaseChange f).op
      (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)) :=
  Equiv.apply_symm_apply _ _

private theorem constant_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : CommRingCat.{u + 1}) :
    toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A) ≫
      (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A).hom =
    Functor.whiskerLeft (proEtaleBaseChange f).op
      (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)) :=
  ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv _ _
    |>.apply_symm_apply _)

private theorem constant_iso_generic
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (G : C ⥤ D) [G.IsContinuous J K]
    (L : Sheaf J CommRingCat.{u + 1} ⥤ Sheaf K CommRingCat.{u + 1})
    (adj : L ⊣ G.sheafPushforwardContinuous CommRingCat.{u + 1} J K)
    [HasWeakSheafify J CommRingCat.{u + 1}] [HasWeakSheafify K CommRingCat.{u + 1}]
    {T : C} (hT : IsTerminal T) (hGT : IsTerminal (G.obj T))
    (A : CommRingCat.{u + 1})
    (ρ : (constantSheaf J CommRingCat.{u + 1}).obj A ⟶
      (G.sheafPushforwardContinuous CommRingCat.{u + 1} J K).obj
        ((constantSheaf K CommRingCat.{u + 1}).obj A))
    (hρ : (sheafificationAdjunction J CommRingCat.{u + 1}).homEquiv _ _ ρ =
      Functor.whiskerLeft G.op
        (toSheafify K ((Functor.const Dᵒᵖ).obj A))) :
    IsIso ((adj.homEquiv _ _).symm ρ) := by
  let adjC := constantSheafAdj J CommRingCat.{u + 1} hT
  let adjD := constantSheafAdj K CommRingCat.{u + 1} hGT
  let adj' := (adjC.comp adj).ofNatIsoRight
    (G.sheafPushforwardContinuousCompSheafSectionsObjIso
      CommRingCat.{u + 1} J K (op T))
  have he : (adj.homEquiv _ _).symm ρ = (adj'.leftAdjointUniq adjD).hom.app A := by
    apply (adj'.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app,
      Adjunction.homEquiv_ofNatIsoRight_apply]
    change (adjC.comp adj).homEquiv _ _ ((adj.homEquiv _ _).symm ρ) ≫ 𝟙 _ = _
    rw [Category.comp_id, Adjunction.comp_homEquiv]
    change adjC.homEquiv _ _ ((adj.homEquiv _ _)
      ((adj.homEquiv _ _).symm ρ)) = _
    rw [Equiv.apply_symm_apply]
    change ((constantPresheafAdj CommRingCat.{u + 1} hT).comp
      (sheafificationAdjunction J CommRingCat.{u + 1})).homEquiv _ _ ρ = _
    rw [Adjunction.comp_homEquiv]
    change (constantPresheafAdj CommRingCat.{u + 1} hT).homEquiv _ _
      ((sheafificationAdjunction J CommRingCat.{u + 1}).homEquiv _ _ ρ) = _
    rw [hρ]
    change 𝟙 A ≫ _ = _
    rw [Category.id_comp]
    rfl
  rw [he]
  infer_instance

private theorem constant_iso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : CommRingCat.{u + 1}) :
    IsIso (proEtaleConstantInverseImageMap f CommRingCat.{u + 1} A) :=
  constant_iso_generic (ProEt.topology Y) (ProEt.topology X) (proEtaleBaseChange f)
    (proEtaleSheafInverseImage f CommRingCat.{u + 1})
    (proEtaleSheafAdjunction f CommRingCat.{u + 1})
    (terminalIsTerminal (C := Y.ProEt))
    ((terminalIsTerminal (C := Y.ProEt)).isTerminalObj (proEtaleBaseChange f))
    A (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A) (constant_adjunct f A)

private def root_comparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj (purTwistZlOne Y l) ⟶
      purTwistZlOne X l :=
  limit.post (proEtaleRootsOfUnityTower Y l (Fact.out : l.Prime))
    (proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}) ≫
      limMap ((proEtaleRootsOfUnityInverseImageIso f).2.1 l (Fact.out : l.Prime)).choose

private theorem root_comparison_projection {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    root_comparison l f ≫
        limit.π (proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)) (op n) =
      (proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map
        (limit.π (proEtaleRootsOfUnityTower Y l (Fact.out : l.Prime)) (op n)) ≫
          proEtaleRootsOfUnityInverseImageMap f (l ^ (n + 1)) := by
  dsimp only [root_comparison]
  erw [Category.assoc, limMap_π, ← Category.assoc, limit.post_π]
  erw [(proEtaleRootsOfUnityInverseImageIso f).2.1 l (Fact.out : l.Prime) |>.choose_spec]

private def root_direct {X Y : Scheme.{u}} (f : X ⟶ Y) :
    purTwistZlOne Y l ⟶
      (proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).obj (purTwistZlOne X l) :=
  (proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv _ _ (root_comparison l f)

attribute [local irreducible] root_direct

private theorem root_direct_projection {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    root_direct l f ≫ (proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).map
        (limit.π (proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)) (op n)) =
      limit.π (proEtaleRootsOfUnityTower Y l (Fact.out : l.Prime)) (op n) ≫
        proEtaleRootsOfUnityDirectImageMap f (l ^ (n + 1)) := by
  erw [root_direct, ← Adjunction.homEquiv_naturality_right, root_comparison_projection,
    Adjunction.homEquiv_naturality_left]
  change _ ≫ ((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv _ _
    (((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv _ _).symm _)) = _
  erw [Equiv.apply_symm_apply]

private theorem root_direct_unique {X Y : Scheme.{u}} (f : X ⟶ Y)
    (g : purTwistZlOne Y l ⟶
      (proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).obj (purTwistZlOne X l))
    (hg : ∀ n : ℕ, g ≫ (proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).map
        (limit.π (proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)) (op n)) =
      limit.π (proEtaleRootsOfUnityTower Y l (Fact.out : l.Prime)) (op n) ≫
        proEtaleRootsOfUnityDirectImageMap f (l ^ (n + 1))) : g = root_direct l f := by
  apply ((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv _ _).symm.injective
  erw [root_direct, Equiv.symm_apply_apply]
  apply limit.hom_ext
  intro n
  apply ((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv _ _).injective
  erw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply,
    hg, root_comparison_projection, Adjunction.homEquiv_naturality_left]
  change _ = _ ≫ ((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv _ _
    (((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv _ _).symm _))
  erw [Equiv.apply_symm_apply]

private theorem roots_inclusion (S : Scheme.{u}) (N : ℕ)
    (U : S.ProEtᵒᵖ) (x : (proEtaleRootsOfUnitySheaf S N).obj.obj U) :
    (proEtaleRootsOfUnityInclusion S N).hom.app U x =
      ULift.up (Additive.ofMul
        (Additive.toMul (proEtaleRootsOfUnitySections S N U x)).val) :=
  ((existsUnique_proEtaleRootsOfUnitySections S N U).exists.choose_spec x).symm

private theorem roots_restrict_value (S : Scheme.{u}) (N : ℕ)
    {U V : S.ProEtᵒᵖ} (b : U ⟶ V)
    (x : (proEtaleRootsOfUnitySheaf S N).obj.obj U) :
    (Additive.toMul (proEtaleRootsOfUnitySections S N V
      ((proEtaleRootsOfUnitySheaf S N).obj.map b x))).val.val =
    b.unop.left.appTop.hom
      (Additive.toMul (proEtaleRootsOfUnitySections S N U x)).val.val := by
  have h := ConcreteCategory.congr_hom
    ((proEtaleRootsOfUnityInclusion S N).hom.naturality b) x
  change (proEtaleRootsOfUnityInclusion S N).hom.app V
    ((proEtaleRootsOfUnitySheaf S N).obj.map b x) =
    (proEtaleUnitsSheaf S).obj.map b
      ((proEtaleRootsOfUnityInclusion S N).hom.app U x) at h
  erw [roots_inclusion, roots_inclusion] at h
  exact congrArg (fun z ↦ (Additive.toMul z.down).val) h

private theorem roots_direct_value {X Y : Scheme.{u}} (f : X ⟶ Y) (N : ℕ)
    (U : Y.ProEtᵒᵖ) (x : (proEtaleRootsOfUnitySheaf Y N).obj.obj U) :
    (Additive.toMul (proEtaleRootsOfUnitySections X N ((proEtaleBaseChange f).op.obj U)
      ((proEtaleRootsOfUnityDirectImageMap f N).hom.app U x))).val.val =
      (pullback.fst U.unop.hom f).appTop.hom
        (Additive.toMul (proEtaleRootsOfUnitySections Y N U x)).val.val :=
  congrArg (fun z ↦ (Additive.toMul z).val.val)
    ((existsUnique_proEtaleRootsOfUnityDirectImageMap f N).exists.choose_spec U x)

private theorem roots_direct_id (S : Scheme.{u}) (N : ℕ) (U : S.ProEt)
    (x : (proEtaleRootsOfUnitySheaf S N).obj.obj (op U)) :
    (proEtaleRootsOfUnityDirectImageMap (𝟙 S) N).hom.app (op U) x =
      (proEtaleRootsOfUnitySheaf S N).obj.map
        ((MorphismProperty.Over.pullbackId @WeaklyEtale.{u} ⊤ S).hom.app U).op x := by
  apply (proEtaleRootsOfUnitySections S N _).injective
  apply Additive.toMul.injective
  apply Subtype.val_injective
  apply Units.ext
  exact (roots_direct_value (𝟙 S) N (op U) x).trans
    (roots_restrict_value S N
      ((MorphismProperty.Over.pullbackId @WeaklyEtale.{u} ⊤ S).hom.app U).op x).symm

set_option maxHeartbeats 40000 in
-- The fibre-product projection comparison has several definitionally equal section types.
private theorem roots_direct_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (N : ℕ) (U : Z.ProEt) (x : (proEtaleRootsOfUnitySheaf Z N).obj.obj (op U)) :
    (proEtaleRootsOfUnityDirectImageMap (f ≫ g) N).hom.app (op U) x =
      (proEtaleRootsOfUnitySheaf X N).obj.map
        ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale.{u}) (Q := ⊤) f g).hom.app U).op
        ((proEtaleRootsOfUnityDirectImageMap f N).hom.app
          (op ((proEtaleBaseChange g).obj U))
          ((proEtaleRootsOfUnityDirectImageMap g N).hom.app (op U) x)) := by
  apply (proEtaleRootsOfUnitySections X N _).injective
  apply Additive.toMul.injective
  apply Subtype.val_injective
  apply Units.ext
  refine (roots_direct_value (f ≫ g) N (op U) x).trans ?_
  refine Eq.trans ?_ (roots_restrict_value X N
    ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale.{u}) (Q := ⊤) f g).hom.app U).op
    ((proEtaleRootsOfUnityDirectImageMap f N).hom.app
      (op ((proEtaleBaseChange g).obj U))
      ((proEtaleRootsOfUnityDirectImageMap g N).hom.app (op U) x))).symm
  have hf := roots_direct_value f N (op ((proEtaleBaseChange g).obj U))
    ((proEtaleRootsOfUnityDirectImageMap g N).hom.app (op U) x)
  have hg := roots_direct_value g N (op U) x
  refine Eq.trans ?_ (congrArg
    (((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale.{u}) (Q := ⊤)
      f g).hom.app U).left.appTop.hom) hf).symm
  refine Eq.trans ?_ (congrArg (fun z ↦
    ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale.{u}) (Q := ⊤)
      f g).hom.app U).left.appTop.hom
      ((pullback.fst (pullback.snd U.hom g) f).appTop.hom z)) hg).symm
  have h := congrArg (fun k ↦ k.appTop)
    (MorphismProperty.Over.pullbackComp_left_fst_fst
      (P := @WeaklyEtale.{u}) (Q := ⊤) f g U)
  erw [Hom.comp_appTop, Hom.comp_appTop] at h
  exact (ConcreteCategory.congr_hom h
    (Additive.toMul (proEtaleRootsOfUnitySections Z N (op U) x)).val.val).symm

private theorem root_section_ext (S : Scheme.{u}) (U : S.ProEtᵒᵖ)
    (x y : (purTwistZlOne S l).obj.obj U)
    (h : ∀ n : ℕ,
      (limit.π (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)) (op n)).hom.app U x =
      (limit.π (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)) (op n)).hom.app U y) :
    x = y := by
  let ev := sheafToPresheaf (ProEt.topology S) AddCommGrpCat.{u + 1} ⋙
    (CategoryTheory.evaluation S.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj U
  exact Concrete.isLimit_ext _
    (isLimitOfPreserves ev
      (limit.isLimit (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime))))
    x y (fun n ↦ h n.unop)

private theorem root_direct_project_value {X Y : Scheme.{u}} (f : X ⟶ Y)
    (n : ℕ) (U : Y.ProEtᵒᵖ) (x : (purTwistZlOne Y l).obj.obj U) :
    (limit.π (proEtaleRootsOfUnityTower X l (Fact.out : l.Prime)) (op n)).hom.app
        ((proEtaleBaseChange f).op.obj U) ((root_direct l f).hom.app U x) =
      (proEtaleRootsOfUnityDirectImageMap f (l ^ (n + 1))).hom.app U
        ((limit.π (proEtaleRootsOfUnityTower Y l (Fact.out : l.Prime)) (op n)).hom.app
          U x) :=
  congrArg (fun k ↦ k.hom.app U x) (root_direct_projection l f n)

private theorem root_direct_id (S : Scheme.{u}) (U : S.ProEt)
    (x : (purTwistZlOne S l).obj.obj (op U)) :
    (root_direct l (𝟙 S)).hom.app (op U) x = (purTwistZlOne S l).obj.map
      ((MorphismProperty.Over.pullbackId @WeaklyEtale.{u} ⊤ S).hom.app U).op x := by
  apply root_section_ext l
  intro n
  refine (root_direct_project_value l (𝟙 S) n (op U) x).trans ?_
  refine (roots_direct_id S _ U _).trans ?_
  exact (NatTrans.naturality_apply
    (limit.π (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)) (op n)).hom _ x).symm

private theorem root_direct_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (U : Z.ProEt) (x : (purTwistZlOne Z l).obj.obj (op U)) :
    (root_direct l (f ≫ g)).hom.app (op U) x = (purTwistZlOne X l).obj.map
      ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale.{u}) (Q := ⊤) f g).hom.app U).op
      ((root_direct l f).hom.app (op ((proEtaleBaseChange g).obj U))
        ((root_direct l g).hom.app (op U) x)) := by
  apply root_section_ext l
  intro n
  erw [root_direct_project_value, NatTrans.naturality_apply,
    root_direct_project_value, root_direct_project_value, roots_direct_comp]
  rfl

set_option maxHeartbeats 100000 in
-- The normalized scalar action is transported along the ring-sheaf comparison.
private theorem finite_module_linear
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J RingCat.{u + 1}] (N : ℕ) (hN : 0 < N)
    (R : Sheaf J RingCat.{u + 1})
    (e : constantZModRingSheaf J N ≅ R)
    (F G : SheafOfModules.{u + 1} R)
    (φ : (SheafOfModules.toSheaf R).obj F ⟶ (SheafOfModules.toSheaf R).obj G)
    (U : Cᵒᵖ) (a : R.obj.obj U) (x : F.val.obj U) :
    φ.hom.app U (a • x) = a • (show G.val.obj U from φ.hom.app U x) := by
  let M (V : Cᵒᵖ) :
      Module ((constantZModRingSheaf J N).obj.obj V) (F.val.obj V) :=
    Module.compHom _ (e.hom.hom.app V).hom
  let M' (V : Cᵒᵖ) :
      Module ((constantZModRingSheaf J N).obj.obj V) (G.val.obj V) :=
    Module.compHom _ (e.hom.hom.app V).hom
  have spec (H : SheafOfModules.{u + 1} R) :
      IsConstantZModSheafModuleStructure J N
        ((SheafOfModules.toSheaf R).obj H)
        (fun V ↦ Module.compHom (H.val.obj V) (e.hom.hom.app V).hom) := by
    constructor
    · intro V z y
      change e.hom.hom.app V
        ((toSheafify J
          ((Functor.const Cᵒᵖ).obj (RingCat.of (ULift.{u + 1} (ZMod N))))).app V
            (z : ULift.{u + 1} (ZMod N))) • (show H.val.obj V from y) =
          z • (show H.val.obj V from y)
      erw [map_intCast, map_intCast, Int.cast_smul_eq_zsmul]
    · intro V W b r y
      change H.val.map b (e.hom.hom.app V r • (show H.val.obj V from y)) =
        e.hom.hom.app W
          ((constantZModRingSheaf J N).obj.map b r) • H.val.map b y
      erw [H.val.map_smul]
      exact congrArg (fun z ↦ z • H.val.map b y)
        (ConcreteCategory.congr_hom (e.hom.hom.naturality b) r).symm
  have killed (H : SheafOfModules.{u + 1} R) (V : Cᵒᵖ) (y : H.val.obj V) :
      N • y = 0 := by
    have hn : (N : R.obj.obj V) = 0 := by
      have hz : (N : ULift.{u + 1} (ZMod N)) = 0 := by
        apply ULift.ext
        exact ZMod.natCast_self N
      have hh := congrArg (fun z ↦ e.hom.hom.app V
        ((toSheafify J
          ((Functor.const Cᵒᵖ).obj (RingCat.of (ULift.{u + 1} (ZMod N))))).app V z)) hz
      simpa only [map_natCast, map_zero] using hh
    erw [← Nat.cast_smul_eq_nsmul (R.obj.obj V), hn, zero_smul]
  have h := torsionSheaf_hom_linear J N hN
    ((SheafOfModules.toSheaf R).obj F) ((SheafOfModules.toSheaf R).obj G)
    (killed F) (killed G) φ M M' (spec F) (spec G) U (e.inv.hom.app U a) x
  have he : e.hom.hom.app U (e.inv.hom.app U a) = a :=
    ConcreteCategory.congr_hom (congrArg (fun k ↦ k.hom.app U) e.inv_hom_id) a
  change φ.hom.app U (e.hom.hom.app U (e.inv.hom.app U a) • x) =
    e.hom.hom.app U (e.inv.hom.app U a) • (show G.val.obj U from φ.hom.app U x) at h
  rwa [he] at h

private def root_push {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    SheafOfModules.{u + 1} (purTwistRing Y (purTwistFiniteRing Y l n)) :=
  (SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
    (J := ProEt.topology Y) (K := ProEt.topology X)
    (S := purTwistRing Y (purTwistFiniteRing Y l n))
    (R := purTwistRing X (purTwistFiniteRing X l n))
    ⟨Functor.whiskerRight
      (proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
        (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩).obj (purTwistRootsModule X l n)

private theorem root_direct_linear {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (U : Y.ProEtᵒᵖ) (a : (purTwistFiniteRing Y l n).obj.obj U)
    (x : (proEtaleRootsOfUnitySheaf Y (l ^ (n + 1))).obj.obj U) :
    (proEtaleRootsOfUnityDirectImageMap f (l ^ (n + 1))).hom.app U
      (a • (show (purTwistRootsModule Y l n).val.obj U from x)) =
    (show (purTwistFiniteRing X l n).obj.obj ((proEtaleBaseChange f).op.obj U) from
      (proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
        (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))).hom.app U a) •
      (show (purTwistRootsModule X l n).val.obj ((proEtaleBaseChange f).op.obj U) from
        (proEtaleRootsOfUnityDirectImageMap f (l ^ (n + 1))).hom.app U x) := by
  exact finite_module_linear (ProEt.topology Y) (l ^ (n + 1)) (pow_pos (Fact.out : l.Prime).pos _)
    (purTwistRing Y (purTwistFiniteRing Y l n)) (purTwistFiniteRingIso Y l n).symm
    (purTwistRootsModule Y l n) (root_push l f n)
    (proEtaleRootsOfUnityDirectImageMap f (l ^ (n + 1))) U a x

private abbrev Mod (X : Scheme.{u}) (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
  SheafOfModules.{u + 1} (purTwistRing X R)

private def direct_id (S : Scheme.{u}) (D : Type v) [Category.{u + 1} D]
    (F : Sheaf (ProEt.topology S) D) :
    F ⟶ (proEtaleSheafDirectImage (𝟙 S) D).obj F :=
  (Functor.sheafPushforwardContinuousId'
    (MorphismProperty.Over.pullbackId @WeaklyEtale.{u} ⊤ S)
    D (ProEt.topology S)).inv.app F

private def direct_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (D : Type v) [Category.{u + 1} D] (F : Sheaf (ProEt.topology X) D) :
    (proEtaleSheafDirectImage g D).obj ((proEtaleSheafDirectImage f D).obj F) ⟶
      (proEtaleSheafDirectImage (f ≫ g) D).obj F :=
  (Functor.sheafPushforwardContinuousComp'
    (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale.{u}) (Q := ⊤) f g).symm
    D (ProEt.topology Z) (ProEt.topology Y) (ProEt.topology X)).hom.app F

set_option backward.isDefEq.respectTransparency false in
private theorem scalar_abelian_ext (S : Scheme.{u})
    {R Q : Sheaf (ProEt.topology S) CommRingCat.{u + 1}} (a : R ⟶ Q)
    (M : Mod S R)
    (H : Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1})
    (f g : (SheafOfModules.toSheaf (purTwistRing S Q)).obj
      (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} a M) ⟶ H)
    (h : ∀ U b x,
      f.hom.app U (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} a M U b x) =
      g.hom.app U
        (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} a M U b x)) :
    f = g := by
  unfold SheafOfModules.changeOfRingsOfUniverses at f g
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (ProEt.topology S) _ _ H.property
  ext U z
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul b x => exact h U b x

set_option maxHeartbeats 50000 in
-- Normalize the two constant-sheaf adjuncts before comparing their units.
private theorem constant_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : CommRingCat.{u + 1}} (k : A ⟶ B) :
    (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map k ≫
      proEtaleConstantDirectImageMap f CommRingCat.{u + 1} B =
    proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A ≫
      (proEtaleSheafDirectImage f CommRingCat.{u + 1}).map
        ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map k) := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (ProEt.topology Y) _ _
    ((proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj _).property
  apply NatTrans.ext
  funext U
  let V := (proEtaleBaseChange f).op.obj U
  let ηY (C : CommRingCat.{u + 1}) :=
    (toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj C)).app U
  let ηX (C : CommRingCat.{u + 1}) :=
    (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj C)).app V
  let mY := ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map k).hom.app U
  let mX := ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map k).hom.app V
  let β (C : CommRingCat.{u + 1}) :=
    (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} C).hom.app U
  have hY : k ≫ ηY B = ηY A ≫ mY := congrArg (fun z ↦ z.app U)
    (toSheafify_naturality (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).map k))
  have hX : k ≫ ηX B = ηX A ≫ mX := congrArg (fun z ↦ z.app V)
    (toSheafify_naturality (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).map k))
  have hβ (C : CommRingCat.{u + 1}) : ηY C ≫ β C = ηX C :=
    congrArg (fun z ↦ z.app U) (constant_unit f C)
  change ηY A ≫ (mY ≫ β B) = ηY A ≫ (β A ≫ mX)
  calc
    _ = (ηY A ≫ mY) ≫ β B := (Category.assoc _ _ _).symm
    _ = (k ≫ ηY B) ≫ β B := congrArg (fun z ↦ z ≫ β B) hY.symm
    _ = k ≫ (ηY B ≫ β B) := Category.assoc _ _ _
    _ = k ≫ ηX B := congrArg (fun z ↦ k ≫ z) (hβ B)
    _ = ηX A ≫ mX := hX
    _ = (ηY A ≫ β A) ≫ mX := congrArg (fun z ↦ z ≫ mX) (hβ A).symm
    _ = _ := Category.assoc _ _ _

private theorem constant_id (S : Scheme.{u}) (A : CommRingCat.{u + 1}) :
    proEtaleConstantDirectImageMap (𝟙 S) CommRingCat.{u + 1} A =
      direct_id S CommRingCat.{u + 1}
        ((constantSheaf (ProEt.topology S) CommRingCat.{u + 1}).obj A) := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (ProEt.topology S) _ _
    ((proEtaleSheafDirectImage (𝟙 S) CommRingCat.{u + 1}).obj _).property
  erw [constant_unit]
  apply NatTrans.ext
  funext U
  change (toSheafify (ProEt.topology S) ((Functor.const S.ProEtᵒᵖ).obj A)).app
    ((proEtaleBaseChange (𝟙 S)).op.obj U) =
    (toSheafify (ProEt.topology S) ((Functor.const S.ProEtᵒᵖ).obj A)).app U ≫
      ((constantSheaf (ProEt.topology S) CommRingCat.{u + 1}).obj A).obj.map
        ((MorphismProperty.Over.pullbackId @WeaklyEtale.{u} ⊤ S).hom.app U.unop).op
  have hh := (toSheafify (ProEt.topology S) ((Functor.const S.ProEtᵒᵖ).obj A)).naturality
      ((MorphismProperty.Over.pullbackId @WeaklyEtale.{u} ⊤ S).hom.app U.unop).op
  change (𝟙 A) ≫ _ = _ at hh
  erw [Category.id_comp] at hh
  exact hh

private theorem constant_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (A : CommRingCat.{u + 1}) :
    proEtaleConstantDirectImageMap (f ≫ g) CommRingCat.{u + 1} A =
      proEtaleConstantDirectImageMap g CommRingCat.{u + 1} A ≫
        (proEtaleSheafDirectImage g CommRingCat.{u + 1}).map
          (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A) ≫
        direct_comp f g CommRingCat.{u + 1}
          ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj A) := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (ProEt.topology Z) _ _
    ((proEtaleSheafDirectImage (f ≫ g) CommRingCat.{u + 1}).obj _).property
  erw [constant_unit]
  apply NatTrans.ext
  funext U
  change (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app
      ((proEtaleBaseChange (f ≫ g)).op.obj U) =
    (toSheafify (ProEt.topology Z) ((Functor.const Z.ProEtᵒᵖ).obj A)).app U ≫
      ((proEtaleConstantDirectImageMap g CommRingCat.{u + 1} A).hom.app U ≫
        (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A).hom.app
          ((proEtaleBaseChange g).op.obj U) ≫
        ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj A).obj.map
          ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale.{u}) (Q := ⊤)
            f g).hom.app U.unop).op)
  erw [← Category.assoc]
  have h1 := congrArg (fun k ↦ k.app U) (constant_unit g A)
  change _ ≫ (proEtaleConstantDirectImageMap g CommRingCat.{u + 1} A).hom.app U = _ at h1
  erw [h1, ← Category.assoc]
  have h2 := congrArg (fun k ↦ k.app ((proEtaleBaseChange g).op.obj U)) (constant_unit f A)
  change _ ≫ (proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A).hom.app _ = _ at h2
  dsimp only [Functor.whiskerLeft_app] at *
  erw [h2]
  have hh := (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).naturality
      ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale.{u}) (Q := ⊤)
        f g).hom.app U.unop).op
  change (𝟙 A) ≫ _ = _ at hh
  erw [Category.id_comp] at hh
  exact hh

private theorem root_action_projection (S : Scheme.{u}) (n : ℕ) (U : S.ProEtᵒᵖ)
    (a : (purTwistZlConstant S l).obj.obj U) (x : (purTwistZlOne S l).obj.obj U) :
    (limit.π (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)) (op n)).hom.app U
      (ambRootAction l S U a x) =
    (purTwistZlReduction S l n).hom.app U a •
      (show (purTwistRootsModule S l n).val.obj U from
        (limit.π (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)) (op n)).hom.app U x) := by
  unfold ambRootAction purTwistZlAction
  have h := (purTwistZlAction_existsUnique S l).exists.choose_spec.2 n U
    ((purTwistZlCompletionMap S l).hom.app U a) x
  have hc := congrArg (fun k ↦ k.hom.app U a)
    ((purTwistZlCompletionMap_existsUnique S l).exists.choose_spec n)
  exact h.trans (congrArg (fun z ↦ z • (show (purTwistRootsModule S l n).val.obj U from
    (limit.π (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)) (op n)).hom.app U x)) hc)

private theorem root_limit_linear {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.ProEt)
    (a : (purTwistZlConstant Y l).obj.obj (op U))
    (x : (purTwistZlOne Y l).obj.obj (op U)) :
    (root_direct l f).hom.app (op U) (ambRootAction l Y (op U) a x) =
      ambRootAction l X (op ((proEtaleBaseChange f).obj U))
        ((proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
          (CommRingCat.of (ULift.{u + 1} ℤ_[l]))).hom.app (op U) a)
        ((root_direct l f).hom.app (op U) x) := by
  apply root_section_ext l
  intro n
  erw [root_direct_project_value, root_action_projection, root_direct_linear,
    root_action_projection, root_direct_project_value]
  congr 1
  exact ConcreteCategory.congr_hom (congrArg (fun k ↦ k.hom.app (op U))
    (constant_naturality f
      (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
        ((PadicInt.toZModPow (n + 1)).comp ULift.ringEquiv.toRingHom))))) a

attribute [local irreducible] SheafOfModules.changeOfRingsOfUniverses

private def tensor_direct {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (F : C ⥤ D)
    [F.IsContinuous J K]
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [K.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [HasWeakSheafify K AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {R S : Sheaf J CommRingCat.{u + 1}}
    {R' S' : Sheaf K CommRingCat.{u + 1}}
    (α : R ⟶ S) (α' : R' ⟶ S')
    (ρ : R ⟶ (F.sheafPushforwardContinuous CommRingCat.{u + 1} J K).obj R')
    (σ : S ⟶ (F.sheafPushforwardContinuous CommRingCat.{u + 1} J K).obj S')
    (h : α ≫ σ = ρ ≫ (F.sheafPushforwardContinuous CommRingCat.{u + 1} J K).map α')
    (M : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (N : SheafOfModules.{u + 1}
      ((sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R'))
    (β : (SheafOfModules.toSheaf
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)).obj M ⟶
      (F.sheafPushforwardContinuous AddCommGrpCat.{u + 1} J K).obj
        ((SheafOfModules.toSheaf
          ((sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R')).obj N))
    (hb : ∀ (U : Cᵒᵖ) (a : R.obj.obj U) (x : M.val.obj U),
      β.hom.app U (a • x) =
      (show R'.obj.obj (F.op.obj U) from ρ.hom.app U a) •
        (show N.val.obj (F.op.obj U) from
        β.hom.app U x)) :
    SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α M ⟶
      (SheafOfModules.pushforward.{u + 1} (F := F)
        (J := J) (K := K)
        (S := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)
        (R := (sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S')
        ⟨Functor.whiskerRight σ.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩).obj
        (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α' N) := by
  let H := (SheafOfModules.pushforward.{u + 1} (F := F)
    (J := J) (K := K)
    (S := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)
    (R := (sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S')
    ⟨Functor.whiskerRight σ.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩).obj
      (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α' N)
  apply SheafOfModules.scalarExtensionLift.{u + 1, u, u + 1, u + 1} α M H
  refine ⟨{
    app := fun U ↦
      ModuleCat.ofHom
        (X := M.val.obj U)
        (Y := ((SheafOfModules.restrictScalars.{u + 1}
        ((sheafCompose J
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map α)).obj H).val.obj U)
        { toFun := fun x ↦ SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} α' N
            (F.op.obj U) 1 (β.hom.app U x)
          map_add' := by
            intro x y
            erw [map_add, SheafOfModules.scalarExtensionSection_add]
          map_smul' := by
            intro a x
            have he := congrArg (fun k ↦ k.hom.app U
              (show R.obj.obj U from a)) h
            change σ.hom.app U (α.hom.app U a) =
              α'.hom.app (F.op.obj U) (ρ.hom.app U a) at he
            change SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} α' N _ 1
              (β.hom.app U (a • x)) =
              (show S'.obj.obj (F.op.obj U) from
                σ.hom.app U (α.hom.app U a)) •
              SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} α' N
                (F.op.obj U) 1 (β.hom.app U x)
            erw [hb, SheafOfModules.scalarExtensionSection_base_smul, one_mul,
              ← he, SheafOfModules.scalarExtensionSection_smul, mul_one] }
    naturality := ?_ }⟩
  intro U V i
  ext x
  change SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} α' N _ 1
      (β.hom.app V (M.val.map i x)) =
    (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α' N).val.map
      (F.op.map i)
      (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} α' N _ 1 (β.hom.app U x))
  erw [SheafOfModules.scalarExtensionSection_naturality, map_one]
  exact congrArg (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} α' N _ 1)
    (ConcreteCategory.congr_hom (β.hom.naturality i) x)

attribute [local irreducible] tensor_direct

private theorem tensor_direct_pure {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (F : C ⥤ D)
    [F.IsContinuous J K]
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [K.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [HasWeakSheafify K AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {R S : Sheaf J CommRingCat.{u + 1}}
    {R' S' : Sheaf K CommRingCat.{u + 1}}
    (α : R ⟶ S) (α' : R' ⟶ S')
    (ρ : R ⟶ (F.sheafPushforwardContinuous CommRingCat.{u + 1} J K).obj R')
    (σ : S ⟶ (F.sheafPushforwardContinuous CommRingCat.{u + 1} J K).obj S')
    (h : α ≫ σ = ρ ≫ (F.sheafPushforwardContinuous CommRingCat.{u + 1} J K).map α')
    (M : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (N : SheafOfModules.{u + 1}
      ((sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R'))
    (β : (SheafOfModules.toSheaf
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)).obj M ⟶
      (F.sheafPushforwardContinuous AddCommGrpCat.{u + 1} J K).obj
        ((SheafOfModules.toSheaf
          ((sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R')).obj N))
    (hb : ∀ (U : Cᵒᵖ) (a : R.obj.obj U) (x : M.val.obj U),
      β.hom.app U (a • x) =
      (show R'.obj.obj (F.op.obj U) from ρ.hom.app U a) •
        (show N.val.obj (F.op.obj U) from
        β.hom.app U x))
    (U : Cᵒᵖ) (b : S.obj.obj U) (x : M.val.obj U) :
    (tensor_direct J K F α α' ρ σ h M N β hb).val.app U
      (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} α M U b x) =
    SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} α' N (F.op.obj U)
      (σ.hom.app U b) (β.hom.app U x) := by
  erw [tensor_direct, SheafOfModules.scalarExtensionLift_tmul]
  exact (SheafOfModules.scalarExtensionSection_smul α' N (F.op.obj U)
    (σ.hom.app U b) 1 (β.hom.app U x)).trans
      (congrArg (fun z ↦ SheafOfModules.scalarExtensionSection α' N
        (F.op.obj U) z (β.hom.app U x)) (mul_one _))

private abbrev root_module (S : Scheme.{u}) : Mod S (purTwistZlConstant S l) :=
  (SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose (ProEt.topology S)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (purTwistZlCompletionMap S l))).obj (purTwistZlModule S l)

private def tensor_root_direct (B : Type u) [CommRing B] [Algebra ℤ_[l] B]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ambRootTensor l B Y ⟶
      (proEtaleConstantModuleDirectImage f B).obj (ambRootTensor l B X) :=
  tensor_direct (ProEt.topology Y) (ProEt.topology X) (proEtaleBaseChange f)
    (ambRootScalar l B Y) (ambRootScalar l B X)
    (proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
      (CommRingCat.of (ULift.{u + 1} ℤ_[l])))
    (proEtaleCoefficientDirectImageMap f B)
    (by
      unfold ambRootScalar
      exact constant_naturality f _)
    (root_module l Y) (root_module l X) (root_direct l f)
    (fun U a x ↦ root_limit_linear l f U.unop a x)

attribute [local irreducible] tensor_root_direct

private theorem tensor_root_pure (B : Type u) [CommRing B] [Algebra ℤ_[l] B]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.ProEt)
    (b : (proEtaleConstantRing Y B).obj.obj (op U))
    (x : (purTwistZlOne Y l).obj.obj (op U)) :
    (tensor_root_direct l B f).val.app (op U) (ambRootTensorPure l B Y U b x) =
      ambRootTensorPure l B X ((proEtaleBaseChange f).obj U)
        ((proEtaleCoefficientDirectImageMap f B).hom.app (op U) b)
        ((root_direct l f).hom.app (op U) x) := by
  unfold tensor_root_direct
  exact tensor_direct_pure (ProEt.topology Y) (ProEt.topology X) (proEtaleBaseChange f) _ _ _ _ _
    (root_module l Y) (root_module l X) (root_direct l f)
    (fun V a y ↦ root_limit_linear l f V.unop a y) (op U) b x

private def tensor_finite_direct (B : Type u) [CommRing B] (n : ℕ)
    (hB : ((l ^ (n + 1) : ℕ) : B) = 0) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ambRootFiniteTensor l B n hB Y ⟶
      (proEtaleConstantModuleDirectImage f B).obj (ambRootFiniteTensor l B n hB X) :=
  tensor_direct (ProEt.topology Y) (ProEt.topology X) (proEtaleBaseChange f)
    (ambRootFiniteScalar l B n hB Y) (ambRootFiniteScalar l B n hB X)
    (proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
      (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1))))))
    (proEtaleCoefficientDirectImageMap f B)
    (by
      unfold ambRootFiniteScalar
      exact constant_naturality f _)
    (purTwistRootsModule Y l n) (purTwistRootsModule X l n)
    (proEtaleRootsOfUnityDirectImageMap f (l ^ (n + 1)))
    (root_direct_linear l f n)

attribute [local irreducible] tensor_finite_direct

private theorem tensor_finite_pure (B : Type u) [CommRing B] (n : ℕ)
    (hB : ((l ^ (n + 1) : ℕ) : B) = 0) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.ProEt) (b : (proEtaleConstantRing Y B).obj.obj (op U))
    (x : (proEtaleRootsOfUnitySheaf Y (l ^ (n + 1))).obj.obj (op U)) :
    (tensor_finite_direct l B n hB f).val.app (op U)
      (ambRootFinitePure l B n hB Y U b x) =
    ambRootFinitePure l B n hB X ((proEtaleBaseChange f).obj U)
      ((proEtaleCoefficientDirectImageMap f B).hom.app (op U) b)
      ((proEtaleRootsOfUnityDirectImageMap f (l ^ (n + 1))).hom.app (op U) x) := by
  unfold tensor_finite_direct
  exact tensor_direct_pure (ProEt.topology Y) (ProEt.topology X) (proEtaleBaseChange f) _ _ _ _ _
    (purTwistRootsModule Y l n) (purTwistRootsModule X l n)
    (proEtaleRootsOfUnityDirectImageMap f (l ^ (n + 1)))
    (root_direct_linear l f n) (op U) b x

private def tensor_root_abelian (B : Type u) [CommRing B] [Algebra ℤ_[l] B]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (SheafOfModules.toSheaf (purTwistRing Y (proEtaleConstantRing Y B))).obj
        (ambRootTensor l B Y) ⟶
      (proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).obj
        ((SheafOfModules.toSheaf (purTwistRing X (proEtaleConstantRing X B))).obj
          (ambRootTensor l B X)) :=
  (SheafOfModules.toSheaf (purTwistRing Y (proEtaleConstantRing Y B))).map
    (tensor_root_direct l B f)

private theorem tensor_root_id (B : Type u) [CommRing B] [Algebra ℤ_[l] B]
    (S : Scheme.{u}) (U : S.ProEt) (x : (ambRootTensor l B S).val.obj (op U)) :
    (tensor_root_direct l B (𝟙 S)).val.app (op U) x =
      (ambRootTensor l B S).val.map
        ((MorphismProperty.Over.pullbackId @WeaklyEtale.{u} ⊤ S).hom.app U).op x := by
  have he : tensor_root_abelian l B (𝟙 S) =
      direct_id S AddCommGrpCat.{u + 1}
        ((SheafOfModules.toSheaf (purTwistRing S (proEtaleConstantRing S B))).obj
          (ambRootTensor l B S)) := by
    apply scalar_abelian_ext S (ambRootScalar l B S) (root_module l S)
    intro V b y
    change (tensor_root_direct l B (𝟙 S)).val.app V
      (ambRootTensorPure l B S V.unop b y) =
        (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
          (ambRootScalar l B S) (root_module l S)).val.map
          ((MorphismProperty.Over.pullbackId @WeaklyEtale.{u} ⊤ S).hom.app V.unop).op
          (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1} (ambRootScalar l B S)
            (root_module l S) V b y)
    apply Eq.trans (tensor_root_pure l B (𝟙 S) V.unop b y)
    apply Eq.trans ?_ (SheafOfModules.scalarExtensionSection_naturality
      (ambRootScalar l B S) (root_module l S)
      ((MorphismProperty.Over.pullbackId @WeaklyEtale.{u} ⊤ S).hom.app V.unop).op b y).symm
    have hc := congrArg (fun k ↦ k.hom.app V b)
      (constant_id S (CommRingCat.of (ULift.{u + 1} B)))
    exact congrArg₂ (fun a z ↦ SheafOfModules.scalarExtensionSection
      (ambRootScalar l B S) (root_module l S) _ a z) hc
        (root_direct_id l S V.unop y)
  exact congrArg (fun k ↦ k.hom.app (op U) x) he

private theorem tensor_root_comp (B : Type u) [CommRing B] [Algebra ℤ_[l] B]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.ProEt)
    (x : (ambRootTensor l B Z).val.obj (op U)) :
    (tensor_root_direct l B (f ≫ g)).val.app (op U) x =
      (ambRootTensor l B X).val.map
        ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale.{u}) (Q := ⊤)
          f g).hom.app U).op
        ((tensor_root_direct l B f).val.app (op ((proEtaleBaseChange g).obj U))
          ((tensor_root_direct l B g).val.app (op U) x)) := by
  have he : tensor_root_abelian l B (f ≫ g) =
      tensor_root_abelian l B g ≫
        (proEtaleSheafDirectImage g AddCommGrpCat.{u + 1}).map
          (tensor_root_abelian l B f) ≫
        direct_comp f g AddCommGrpCat.{u + 1}
          ((SheafOfModules.toSheaf (purTwistRing X (proEtaleConstantRing X B))).obj
            (ambRootTensor l B X)) := by
    apply scalar_abelian_ext Z (ambRootScalar l B Z) (root_module l Z)
    intro V b y
    change (tensor_root_direct l B (f ≫ g)).val.app V
      (ambRootTensorPure l B Z V.unop b y) =
        (ambRootTensor l B X).val.map
          ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale.{u}) (Q := ⊤)
            f g).hom.app V.unop).op
          ((tensor_root_direct l B f).val.app ((proEtaleBaseChange g).op.obj V)
            ((tensor_root_direct l B g).val.app V
              (ambRootTensorPure l B Z V.unop b y)))
    have hg := tensor_root_pure l B g V.unop b y
    have hf := tensor_root_pure l B f ((proEtaleBaseChange g).obj V.unop)
      ((proEtaleCoefficientDirectImageMap g B).hom.app V b)
      ((root_direct l g).hom.app V y)
    have hfg := (congrArg (fun z ↦ (tensor_root_direct l B f).val.app
      ((proEtaleBaseChange g).op.obj V) z) hg).trans hf
    let i : op ((proEtaleBaseChange f).obj ((proEtaleBaseChange g).obj V.unop)) ⟶
        op ((proEtaleBaseChange (f ≫ g)).obj V.unop) :=
      ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale.{u}) (Q := ⊤)
        f g).hom.app V.unop).op
    have hm := congrArg (fun z : (ambRootTensor l B X).val.obj
      (op ((proEtaleBaseChange f).obj ((proEtaleBaseChange g).obj V.unop))) ↦
        (ambRootTensor l B X).val.map i z) hfg
    apply Eq.trans (tensor_root_pure l B (f ≫ g) V.unop b y)
    apply Eq.trans ?_ hm.symm
    apply Eq.trans ?_ (SheafOfModules.scalarExtensionSection_naturality
      (ambRootScalar l B X) (root_module l X)
      ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale.{u}) (Q := ⊤)
        f g).hom.app V.unop).op _ _).symm
    have hc := congrArg (fun k ↦ k.hom.app V b)
      (constant_comp f g (CommRingCat.of (ULift.{u + 1} B)))
    exact congrArg₂ (fun a z ↦ SheafOfModules.scalarExtensionSection
      (ambRootScalar l B X) (root_module l X) _ a z) hc
        (root_direct_comp l f g V.unop y)
  exact congrArg (fun k ↦ k.hom.app (op U) x) he

private theorem killed_scalar_factor (B : Type u) [CommRing B] [Algebra ℤ_[l] B]
    (n : ℕ) (hB : ((l ^ (n + 1) : ℕ) : B) = 0) (S : Scheme.{u}) :
    purTwistZlReduction S l n ≫ ambRootFiniteScalar l B n hB S = ambRootScalar l B S := by
  have hk : RingHom.ker (PadicInt.toZModPow (n + 1) : ℤ_[l] →+* ZMod (l ^ (n + 1))) ≤
      RingHom.ker (algebraMap ℤ_[l] B) := by
    erw [PadicInt.ker_toZModPow, Ideal.span_le, Set.singleton_subset_iff]
    change (algebraMap ℤ_[l] B) ((l : ℤ_[l]) ^ (n + 1)) = 0
    simpa only [map_pow, map_natCast, Nat.cast_pow] using hB
  let q := (PadicInt.toZModPow (n + 1)).liftOfSurjective (ZMod.ringHom_surjective _)
    ⟨algebraMap ℤ_[l] B, hk⟩
  have hq : q = ZMod.castHom
      ((CharP.cast_eq_zero_iff B (ringChar B) (l ^ (n + 1))).mp hB) B :=
    Subsingleton.elim _ _
  unfold ambRootScalar ambRootFiniteScalar purTwistZlReduction
  change (constantSheaf (ProEt.topology S) CommRingCat.{u + 1}).map _ ≫
    (constantSheaf (ProEt.topology S) CommRingCat.{u + 1}).map _ = _
  erw [← Functor.map_comp]
  congr 1
  ext a
  change (ZMod.castHom
    ((CharP.cast_eq_zero_iff B (ringChar B) (l ^ (n + 1))).mp hB) B)
    (PadicInt.toZModPow (n + 1) a.down) =
    (algebraMap ℤ_[l] B) a.down
  erw [← hq]
  exact RingHom.liftOfSurjective_comp_apply _ _ _ _

-- Scalar reduction on one site avoids unfolding identity pushforwards of module sheaves.
private def tensor_reduce {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {R R' Q : Sheaf J CommRingCat.{u + 1}} (α : R ⟶ Q) (α' : R' ⟶ Q)
    (ρ : R ⟶ R') (h : ρ ≫ α' = α)
    (M : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (N : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R'))
    (β : (SheafOfModules.toSheaf
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)).obj M ⟶
      (SheafOfModules.toSheaf
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R')).obj N)
    (hb : ∀ (U : Cᵒᵖ) (a : R.obj.obj U) (x : M.val.obj U),
      β.hom.app U (a • x) =
        (show R'.obj.obj U from ρ.hom.app U a) • (show N.val.obj U from β.hom.app U x)) :
    SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α M ⟶
      SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α' N := by
  apply SheafOfModules.scalarExtensionLift.{u + 1, u, u + 1, u + 1} α M _
  refine ⟨{
    app := fun U ↦ ModuleCat.ofHom
      (X := M.val.obj U)
      (Y := ((SheafOfModules.restrictScalars.{u + 1}
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map α)).obj
          (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α' N)).val.obj U)
      { toFun := fun x ↦ SheafOfModules.scalarExtensionSection α' N U 1 (β.hom.app U x)
        map_add' := by
          intro x y
          erw [map_add, SheafOfModules.scalarExtensionSection_add]
        map_smul' := by
          intro a x
          have he := congrArg (fun k ↦ k.hom.app U a) h
          change SheafOfModules.scalarExtensionSection α' N U 1 (β.hom.app U (a • x)) =
            (show Q.obj.obj U from α.hom.app U a) •
              SheafOfModules.scalarExtensionSection α' N U 1 (β.hom.app U x)
          erw [hb, SheafOfModules.scalarExtensionSection_base_smul, one_mul,
            he, SheafOfModules.scalarExtensionSection_smul, mul_one] }
    naturality := ?_ }⟩
  intro U V i
  ext x
  change SheafOfModules.scalarExtensionSection α' N V 1
    (β.hom.app V (M.val.map i x)) =
      (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} α' N).val.map i
        (SheafOfModules.scalarExtensionSection α' N U 1 (β.hom.app U x))
  erw [SheafOfModules.scalarExtensionSection_naturality, map_one]
  exact congrArg (SheafOfModules.scalarExtensionSection α' N V 1)
    (ConcreteCategory.congr_hom (β.hom.naturality i) x)

attribute [local irreducible] tensor_reduce

private theorem tensor_reduce_pure {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {R R' Q : Sheaf J CommRingCat.{u + 1}} (α : R ⟶ Q) (α' : R' ⟶ Q)
    (ρ : R ⟶ R') (h : ρ ≫ α' = α)
    (M : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (N : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R'))
    (β : (SheafOfModules.toSheaf
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)).obj M ⟶
      (SheafOfModules.toSheaf
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R')).obj N)
    (hb : ∀ (U : Cᵒᵖ) (a : R.obj.obj U) (x : M.val.obj U),
      β.hom.app U (a • x) =
        (show R'.obj.obj U from ρ.hom.app U a) • (show N.val.obj U from β.hom.app U x))
    (U : Cᵒᵖ) (b : Q.obj.obj U) (x : M.val.obj U) :
    (tensor_reduce J α α' ρ h M N β hb).val.app U
      (SheafOfModules.scalarExtensionSection α M U b x) =
      SheafOfModules.scalarExtensionSection α' N U b (β.hom.app U x) := by
  erw [tensor_reduce, SheafOfModules.scalarExtensionLift_tmul]
  exact (SheafOfModules.scalarExtensionSection_smul α' N U b 1 (β.hom.app U x)).trans
    (congrArg (fun z ↦ SheafOfModules.scalarExtensionSection α' N U z (β.hom.app U x))
      (mul_one _))

private def tensor_reduction (B : Type u) [CommRing B] [Algebra ℤ_[l] B]
    (n : ℕ) (hB : ((l ^ (n + 1) : ℕ) : B) = 0) (S : Scheme.{u}) :
    ambRootTensor l B S ⟶ ambRootFiniteTensor l B n hB S :=
  tensor_reduce (ProEt.topology S) (ambRootScalar l B S) (ambRootFiniteScalar l B n hB S)
    (purTwistZlReduction S l n) (killed_scalar_factor l B n hB S)
    (root_module l S) (purTwistRootsModule S l n)
    (limit.π (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)) (op n))
    (fun U a x ↦ root_action_projection l S n U a x)

attribute [local irreducible] tensor_reduction

private theorem tensor_reduction_pure (B : Type u) [CommRing B] [Algebra ℤ_[l] B]
    (n : ℕ) (hB : ((l ^ (n + 1) : ℕ) : B) = 0) (S : Scheme.{u}) (U : S.ProEt)
    (b : (proEtaleConstantRing S B).obj.obj (op U))
    (x : (purTwistZlOne S l).obj.obj (op U)) :
    (tensor_reduction l B n hB S).val.app (op U) (ambRootTensorPure l B S U b x) =
      ambRootFinitePure l B n hB S U b
        ((limit.π (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)) (op n)).hom.app
          (op U) x) := by
  unfold tensor_reduction
  exact tensor_reduce_pure (ProEt.topology S) _ _ _ _
    (root_module l S) (purTwistRootsModule S l n)
    (limit.π (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)) (op n))
    (fun V a y ↦ root_action_projection l S n V a y) (op U) b x

private theorem tensor_reduction_square (B : Type u) [CommRing B] [Algebra ℤ_[l] B]
    (n : ℕ) (hB : ((l ^ (n + 1) : ℕ) : B) = 0) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    tensor_root_direct l B f ≫
      (proEtaleConstantModuleDirectImage f B).map (tensor_reduction l B n hB X) =
    tensor_reduction l B n hB Y ≫ tensor_finite_direct l B n hB f := by
  apply SheafOfModules.scalarExtension_hom_ext.{u + 1, u, u + 1, u + 1} (ambRootScalar l B Y)
    (root_module l Y)
  intro U b x
  change (tensor_reduction l B n hB X).val.app _
      ((tensor_root_direct l B f).val.app U (ambRootTensorPure l B Y U.unop b x)) =
    (tensor_finite_direct l B n hB f).val.app U
      ((tensor_reduction l B n hB Y).val.app U (ambRootTensorPure l B Y U.unop b x))
  have h1 := congrArg (fun z : (ambRootTensor l B X).val.obj
    (op ((proEtaleBaseChange f).obj U.unop)) ↦
      (tensor_reduction l B n hB X).val.app
        (op ((proEtaleBaseChange f).obj U.unop)) z)
    (tensor_root_pure l B f U.unop b x)
  have h2 := tensor_reduction_pure l B n hB X ((proEtaleBaseChange f).obj U.unop)
    ((proEtaleCoefficientDirectImageMap f B).hom.app U b)
    ((root_direct l f).hom.app U x)
  have h3 := congrArg (fun z : (ambRootFiniteTensor l B n hB Y).val.obj U ↦
    (tensor_finite_direct l B n hB f).val.app U z)
      (tensor_reduction_pure l B n hB Y U.unop b x)
  have h4 := tensor_finite_pure l B n hB f U.unop b
    ((limit.π (proEtaleRootsOfUnityTower Y l (Fact.out : l.Prime)) (op n)).hom.app U x)
  have hp := congrArg (ambRootFinitePure l B n hB X ((proEtaleBaseChange f).obj U.unop)
    ((proEtaleCoefficientDirectImageMap f B).hom.app U b))
      (root_direct_project_value l f n U x)
  exact (h1.trans h2).trans (hp.trans (h3.trans h4).symm)

/-- Canonical root-tower pullback, its ordinary tensor extension, and the reduction square.
Source: Stacks Tags 03CO/03DB, 03CB, 03EL and 03D7; vector-bundle purity proof paragraph 1
(blueprint: lem-amb-root-tower-pullback-coherence).

Proof:
1. The constant sheaf adjunction composed with the inverse-image adjunction is the constant
sheaf adjunction on the target, since base change preserves the terminal object; uniqueness
of left adjoints makes the constant comparison maps invertible. Sheafification uniqueness
gives their naturality in the coefficient ring and their identity and composition laws.
2. The finite-root inverse-image lemma gives power-transition compatibility and
semilinearity. The finite direct-image root maps are pullback of units along the
fibre-product projection, so the fibre-product projection identities give their identity
and composition laws; the normalized finite-ring action makes them linear.
3. The pulled-back limit projections composed with the finite root comparisons form a cone
over the target root tower; its lift, transposed, is c. The lift equations give the
projection law, adjunction and the limit property give uniqueness, and joint injectivity of
the projections with step 2 gives the identity, composition and constant Z_l-linearity laws.
4. The map x |-> 1 tensor c(x) is linear into the restricted direct-image tensor module by
coefficient naturality, so the scalar-extension universal property gives h with
h(b tensor x) = b tensor c(x). Maps out of a scalar extension are determined on pure
sections, which proves the identity and composition laws of h.
5. If l^(r+1) B = 0, the algebra map Z_l -> B factors through Z/l^(r+1) by the cast
homomorphism. The root projection is semilinear for this reduction, so scalar extension
gives alpha; the same lift of the finite root map gives d. Both composites of the square
agree on pure sections by the projection law, which proves the square. Neither alpha nor
c_r is inverted.

The invertibility of l is retained as a hypothesis on the schemes. The construction itself
uses only the indicated roots, limits and ordinary tensors. -/
theorem ambRootTowerPullbackCoherence :
    Nonempty (AmbRootTowerPullbackCoherence.{u} l) := by
  refine ⟨{
    constant_iso := ?_
    root_transition := ?_
    root_linear := ?_
    root_id := ?_
    root_comp := ?_
    c := fun {_ _} _ _ f ↦ root_direct l f
    c_projection := ?_
    c_unique := ?_
    c_linear := ?_
    c_id := ?_
    c_comp := ?_
    h := fun B _ _ {_ _} _ _ f ↦ tensor_root_direct l B f
    h_pure := ?_
    h_id := ?_
    h_comp := ?_
    alpha := fun B _ _ n hB S _ ↦ tensor_reduction l B n hB S
    alpha_pure := ?_
    d := fun B _ _ n hB {_ _} _ _ f ↦ tensor_finite_direct l B n hB f
    d_pure := ?_
    square := ?_
  }⟩
  · intro T T' _ _ f
    exact ⟨constant_iso f _, fun s ↦ constant_iso f _, fun B _ _ ↦ constant_iso f _⟩
  · intro T T' _ _ f s
    let e := ((proEtaleRootsOfUnityInverseImageIso f).2.1 l (Fact.out : l.Prime)).choose
    have h := e.naturality (homOfLE (Nat.le_succ s)).op
    dsimp only [e] at h
    simpa only [Functor.comp_map,
      ((proEtaleRootsOfUnityInverseImageIso f).2.1 l (Fact.out : l.Prime)).choose_spec]
      using h
  · intro T T' _ _ f s U a x
    exact (proEtaleRootsOfUnityInverseImageIso f).2.2.1 _
      (pow_pos (Fact.out : l.Prime).pos _) U a x
  · intro T _ s U x
    exact roots_direct_id T _ U x
  · intro T T' T'' _ _ _ f g s U x
    exact roots_direct_comp g f _ U x
  · intro T T' _ _ f s
    exact root_direct_projection l f s
  · intro T T' _ _ f g hg
    exact root_direct_unique l f g hg
  · intro T T' _ _ f U a x
    exact root_limit_linear l f U a x
  · intro T _ U x
    exact root_direct_id l T U x
  · intro T T' T'' _ _ _ f g U x
    exact root_direct_comp l g f U x
  · intro B _ _ T T' _ _ f U b x
    exact tensor_root_pure l B f U b x
  · intro B _ _ T _ U x
    exact tensor_root_id l B T U x
  · intro B _ _ T T' T'' _ _ _ f g U x
    exact tensor_root_comp l B g f U x
  · intro B _ _ n hB T _ U b x
    exact tensor_reduction_pure l B n hB T U b x
  · intro B _ _ n hB T T' _ _ f U b x
    exact tensor_finite_pure l B n hB f U b x
  · intro B _ _ n hB T T' _ _ f
    exact tensor_reduction_square l B n hB f

-- Restore the imported instance priorities after the private proof constructions.
attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology

end AlgebraicGeometry.Scheme
