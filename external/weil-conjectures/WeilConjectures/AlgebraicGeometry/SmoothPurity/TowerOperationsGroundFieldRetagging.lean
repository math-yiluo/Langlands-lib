/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekLevels
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowersAbelian
import all WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheafLocallyFree

/-! # Ground-field retagging of ordinary strict-tower operations

Source: blueprint main-20261015, chap-Smooth-purity,
sk-prop-sp-tower-geometric-gamma.proof.md, clauses (2)--(3), and
proposition-purity-trace-commute-frobenius, proof Step 1
(blueprint: lem-pur-tower-operations-ground-field-retagging).

Retagging is postcomposition of the structure map, not pullback of the scheme.
The equalities below concern entire strict systems and entire derived functors.
The parameters b and o fix the published, representative-normalized operations once
on the underlying schemes; they are not new geometric or normalization hypotheses.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale

/-- The actual ell-power quotient in commutative ring sheaves. Forgetting commutativity
recovers spCoefficientConstantQuotient; no coefficient action is changed by retagging.
Source: blueprint gamma proof (2), actual quotient coefficients
(blueprint: lem-pur-tower-operations-ground-field-retagging). -/
def spEllTwistQuotient (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ) :
    purTwistIntegralConstant T l E ⟶ SpTowerShriek.B l E T n :=
  (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((Ideal.Quotient.mk (spEllIdeal l E ^ (n + 1))).comp ULift.ringEquiv.toRingHom)))

/-- The ell-power quotient of the published integral Tate line, using the actual
constant quotient map. This is O_E(1) tensor_{O_E} O_E/ell^(n+1), before signed powers.
Source: blueprint gamma proof (2), coefficient twists and quotient transitions
(blueprint: lem-pur-tower-operations-ground-field-retagging). -/
def spEllTwistOne (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ) :=
  SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
    (spEllTwistQuotient l E T n) (purTwistIntegralOne T l E)

/-- Signed finite Tate lines at the ell-power levels of the strict tower. Positive
powers and internal duals are exactly those of the recorded coefficient-twist definition.
Source: blueprint gamma proof (2), signed Tate twists
(blueprint: lem-pur-tower-operations-ground-field-retagging). -/
def spEllTwistLine (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
    (n : ℕ) (m : ℤ) :=
  coefficientTwistLine T (R := SpTowerShriek.B l E T n) (spEllTwistOne l E T n) m

/-- The family of actual scalar-extension comparisons between adjacent signed lines.
Source: blueprint gamma proof (2), signed quotient transitions
(blueprint: lem-pur-tower-operations-ground-field-retagging). -/
abbrev SpEllTwistComparisons (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ) :=
  ∀ m : ℤ, SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
    (SpTowerShriek.tau l E T n)
    (spEllTwistLine l E T (n + 1) m) ≅ spEllTwistLine l E T n m

/-- The quotient comparisons are fixed at exponent one on ordinary local pure tensors;
all other signed powers use the published tensor/dual normalization. In particular the
negative formula precomposes with the inverse positive comparison, rather than dualizing
in the wrong direction.
Source: blueprint gamma proof (2), signed-line quotient construction
(blueprint: lem-pur-tower-operations-ground-field-retagging). -/
def SpEllTwistComparisonsNormalized (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ)
    (B : SpEllTwistComparisons l E T n) : Prop :=
  (∀ (U : T.ProEtᵒᵖ) (s : (SpTowerShriek.B l E T n).obj.obj U)
    (t : (SpTowerShriek.B l E T (n + 1)).obj.obj U)
    (x : (purTwistIntegralOne T l E).val.obj U),
    (B 1).hom.val.app U
      (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
        (SpTowerShriek.tau l E T n)
        (spEllTwistOne l E T (n + 1)) U s
        (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
        (spEllTwistQuotient l E T (n + 1))
          (purTwistIntegralOne T l E) U t x)) =
      SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
        (spEllTwistQuotient l E T n)
        (purTwistIntegralOne T l E) U
        (s * (SpTowerShriek.tau l E T n).hom.app U t) x) ∧
  SheafOfModules.SignedLineComparisonNormalized.{u + 1, u, u + 1}
    (SpTowerShriek.tau l E T n) (spEllTwistOne l E T (n + 1))
    (spEllTwistOne l E T n) (B 1) B

/-- The actual semilinear quotient transition, obtained from its scalar-extension
comparison by the canonical scalar unit. These are maps of sheaves, before derivation.
Source: blueprint gamma proof (2), strict quotient transitions
(blueprint: lem-pur-tower-operations-ground-field-retagging). -/
def spEllTwistTransition (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ)
    (B : SpEllTwistComparisons l E T n) (m : ℤ) :=
  SheafOfModules.scalarExtensionEmbedding.{u + 1, u, u + 1, u + 1}
    (SpTowerShriek.tau l E T n)
      (spEllTwistLine l E T (n + 1) m) ≫
    (SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (SpTowerShriek.tau l E T n))).map (B m).hom

end AlgebraicGeometry.ProEtale
