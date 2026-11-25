/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantNormalization
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicStalkModels
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicActualRealization

/-! # The actual-quotient half of a finite perfect normalization diagram

Source: Stacks Project, Tags 09AL, 09C6 and 06YY.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Descent and scalar comparisons for the actual quotient tower, against the explicit
constant diagram. This data has no Isom-presheaf reduction maps or constant-model
boundedness, lisse, or universality assertions.
Source: Stacks Tags 09AL and 09C6, finite quotient descent and balancing.
(blueprint: def-weil-pbc-finite-perfect-adic-actual-normalization). -/
structure FinitePerfectAdicActualNormalization
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale)
    (T : FinitePerfectAdicAlgebraTower d) where
  K : ∀ n : ℕ, DerivedCategory (Sheaf V.left.smallEtaleTopology
    (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))))
  boundedK : ∀ n : ℕ, ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero
    ((DerivedCategory.homologyFunctor (Sheaf V.left.smallEtaleTopology
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))) i).obj (K n))
  lisseK : ∀ (n : ℕ) (i : ℤ), IsFiniteLocallyConstantSheaf
    ((DerivedCategory.homologyFunctor (Sheaf V.left.smallEtaleTopology
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))) i).obj (K n))
  stalk : ∀ (n : ℕ) (Ω : Type t) [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ V.left), Nonempty
      ((pointSmallEtale x).sheafFiber.obj
        (derivedLocalIsomorphismSheaf (finitePerfectAdicEtaleConstant V.left T n) (K n)))
  dK : ∀ n : ℕ, K (n + 1) ⟶
    (normalizationRestrict V.left.smallEtaleTopology
      (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))).obj (K n)
  universalK : ∀ n : ℕ, EtaleUniversalNormalization V.left
    (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1))) (dK n)
  realization : ∀ (U : V.left.ProEt) (W : X.ProEt),
    (W ⟶ finitePerfectAdicChartObject V U) → ∀ n : ℕ,
    DerivedCategory (Sheaf (ProEt.topology U.left)
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))) ⥤
      DerivedCategory (SheafOfModules.{t + 1} ((completedAdicRing X d).over W))
  scalar : ∀ (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
    normalizationRestrict (ProEt.topology U.left)
        (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1))) ⋙
          realization U W f (n + 1) ≅
      realization U W f n
  actual : ∀ (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
    (realization U W f n).obj
        ((localProEtaleComparison U.hom (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))).obj (K n)) ≅
      (finitePerfectAdicRestrictedTower X d W ((completedAdicReduction X d).obj M)).obj
        (op n)
  model : ∀ (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
    (realization U W f n).obj
        ((localProEtaleComparison U.hom (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))).obj
          (finitePerfectAdicEtaleConstant V.left T n)) ≅
      (finitePerfectAdicModelDiagram X d W T).obj (op n)
  actual_normalized : ∀ (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
    (realization U W f (n + 1)).map (localProEtaleNormalization U.hom
        (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1))) (dK n)) ≫
      (scalar U W f n).hom.app
        ((localProEtaleComparison U.hom (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))).obj (K n)) ≫
      (actual U W f n).hom =
    (actual U W f (n + 1)).hom ≫
      (finitePerfectAdicRestrictedTower X d W ((completedAdicReduction X d).obj M)).map
        (homOfLE (Nat.le_succ n)).op
  model_normalized : ∀ (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
    (realization U W f (n + 1)).map (localProEtaleNormalization U.hom
        (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))
        (finitePerfectAdicEtaleConstantTransition V.left T n)) ≫
      (scalar U W f n).hom.app
        ((localProEtaleComparison U.hom (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))).obj
          (finitePerfectAdicEtaleConstant V.left T n)) ≫
      (model U W f n).hom =
    (model U W f (n + 1)).hom ≫
      (finitePerfectAdicModelDiagram X d W T).map (homOfLE (Nat.le_succ n)).op

/-- Descend actual finite quotients and compare their specified transitions with the
explicit constant diagram after forgetting finite scalars. This is the actual-quotient
and scalar-comparison part of the argument, before constructing any Isom-presheaf map.

Source: Stacks Project, Tag 09C6, the finite quotient levels and their consecutive
normalization maps; Tag 09AL, constructible derived comparison; Tag 06YY, balancing.
(blueprint: lem-weil-pbc-finite-perfect-adic-actual-normalization).

Proof: on the etale chart, the separate markings identify each actual quotient locally
with the supplied perfect constant level. Thus its cohomology is bounded and finite
locally constant. The exact finite-coefficient comparison descends it to an etale K_n;
full faithfulness descends its consecutive quotient arrow. Derived tensor balancing
for two consecutive completed quotients makes this arrow universal for restriction
of quotient scalars. The canonical coefficient mates for etale pullback give its
source-site universal arrows and their restriction coherence. Restrict a marking at
a geometric point; the resulting local derived isomorphism, followed by the
sheafification unit, supplies the required inhabited Isom stalk.

For a pro-etale U over the chart, realize a fixed finite-coefficient sheaf as a module
over the finite quotient ring sheaf, using the locally bijective constant-scalar
unit. Restrict its scalars along the completed-ring projection, and then restrict
along W to U. These exact functors localized termwise give realization. Restriction
of scalars in two steps gives scalar. The descent isomorphism of K gives actual;
the constant-sheaf comparison and universe lift give model for the explicitly
constructed constant algebraic level. The compatibility equations for phi identify
the two composites of coefficient homomorphisms. Their termwise restriction
comparisons, localized on complexes, identify the two realized consecutive arrows
with the strict actual and model transitions. These are actual_normalized and
model_normalized. All comparisons are the canonical ones, fixed by the scalar units;
no simultaneous marking or inverse limit is chosen. The argument remains valid for
zero rings and empty charts, where the stalk assertion has no geometric point. -/
theorem finitePerfectAdic_actual_normalization
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale)
    (T : FinitePerfectAdicAlgebraTower d)
    (hperfect : ∀ n : ℕ, DerivedCategory.IsPerfect (T.level n))
    (hmark : FinitePerfectAdicLevelMarkings X d φ M V T) :
    Nonempty (FinitePerfectAdicActualNormalization X d M V T) := by
  obtain ⟨L, ⟨R⟩⟩ :=
    finitePerfectAdic_actual_realization X d φ hφ hcompat M V T hperfect hmark
  exact ⟨{
    K := L.K
    boundedK := L.boundedK
    lisseK := L.lisseK
    stalk := L.stalk
    dK := L.dK
    universalK := L.universalK
    realization := R.realization
    scalar := R.scalar
    actual := R.actual
    model := R.model
    actual_normalized := R.actual_normalized
    model_normalized := R.model_normalized }⟩

end AlgebraicGeometry.Scheme
