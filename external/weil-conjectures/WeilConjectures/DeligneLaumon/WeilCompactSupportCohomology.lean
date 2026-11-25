/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.WeilIndSheafCategory
public import WeilConjectures.SmoothPurity.Integral.IntegralRationalQbarCompactSupport
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.Compactification.Defs
import WeilConjectures.DeligneLaumon.WeilIndSheafCategory
import Mathlib.CategoryTheory.Abelian.RightDerived
import WeilConjectures.DeligneLaumon.WeilIndOpenRealization
import WeilConjectures.SmoothPurity.Sf.SfCommonStageWeilCohomology
import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientAction
import WeilConjectures.DeligneLaumon.ConstructibleTruncations
import WeilConjectures.DeligneLaumon.FieldShriekCompositionQcqs
import WeilConjectures.Compactification.CommonRefinement
import WeilConjectures.DeligneLaumon.WeilIndProperHigherRepresentability
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Higher compact-support images in the actual common-stage Weil heart

Source: blueprint main-20261015, chap-The-Deligne-Laumon-theorem-in-general,
sk-l-dl-general-composition, lem-zl-composition-weight-bound.proof.md,
first paragraph; SGA 4, XVII, §5--6; Bhatt--Scholze 6.7.6--6.7.7
(blueprint: def-zl-weil-compact-support-cohomology).

Extend by zero first, and then derive the proper direct image in the ambient
category of all equivariant ind-sheaves. Representability returns the result to
the existing common-stage Weil heart. This is an auxiliary resolution construction;
it does not replace the recorded category of Weil complexes.

## Main definitions

- `zlIndWeilHigherShriek`.
- `zlWeilHigherShriek`.
- `zlSourceWeilHeart`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The middle scheme of a compactification, with its inherited k₀-structure.
Source: SGA 4, XVII, compact-support construction
(blueprint: def-zl-weil-compact-support-cohomology). -/
def zlCompactificationMiddle {X₀ Y₀ : Over (Spec (.of D.k₀))}
    (f₀ : X₀ ⟶ Y₀) (c : Compactification f₀.left) : Over (Spec (.of D.k₀)) :=
  Over.mk (c.g ≫ Y₀.hom)

/-- The middle scheme is finite type over k₀ because its proper map has that property.
Source: blueprint compactification construction
(blueprint: def-zl-weil-compact-support-cohomology).
Proof: a proper map is finite type, and finite type is stable under composition. -/
@[instance]
theorem zlCompactificationMiddle_finiteType {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType Y₀.hom] (f₀ : X₀ ⟶ Y₀) (c : Compactification f₀.left) :
    LocallyOfFiniteType (zlCompactificationMiddle D f₀ c).hom := by
  change LocallyOfFiniteType (c.g ≫ Y₀.hom)
  infer_instance

/-- The middle scheme is quasi-compact over k₀ by properness and composition.
Source: blueprint compactification construction
(blueprint: def-zl-weil-compact-support-cohomology).
Proof: proper morphisms are quasi-compact, as are their composites. -/
@[instance]
theorem zlCompactificationMiddle_quasiCompact {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀) (c : Compactification f₀.left) :
    QuasiCompact (zlCompactificationMiddle D f₀ c).hom := by
  change QuasiCompact (c.g ≫ Y₀.hom)
  infer_instance

/-- The open part, over k₀, of the given compactification.
Source: blueprint compactification construction
(blueprint: def-zl-weil-compact-support-cohomology).
Proof: the equality f₀.left = c.i ≫ c.g and f₀.w show the structure-map equality. -/
theorem zlCompactificationOpen_w {X₀ Y₀ : Over (Spec (.of D.k₀))}
    (f₀ : X₀ ⟶ Y₀) (c : Compactification f₀.left) :
    c.i ≫ (zlCompactificationMiddle D f₀ c).hom = X₀.hom := by
  change c.i ≫ (c.g ≫ Y₀.hom) = X₀.hom
  rw [← Category.assoc, ← c.comm]
  exact f₀.w

/-- The open part as an arrow of k₀-schemes.
Source: blueprint compactification construction
(blueprint: def-zl-weil-compact-support-cohomology). -/
def zlCompactificationOpen {X₀ Y₀ : Over (Spec (.of D.k₀))}
    (f₀ : X₀ ⟶ Y₀) (c : Compactification f₀.left) :
    X₀ ⟶ zlCompactificationMiddle D f₀ c :=
  Over.homMk c.i (zlCompactificationOpen_w D f₀ c)

/-- The open part has its specified open-immersion property.
Source: blueprint compactification construction
(blueprint: def-zl-weil-compact-support-cohomology).
Proof: its underlying map is c.i, an open immersion by the compactification data. -/
@[instance]
theorem zlCompactificationOpen_isOpenImmersion {X₀ Y₀ : Over (Spec (.of D.k₀))}
    (f₀ : X₀ ⟶ Y₀) (c : Compactification f₀.left) :
    IsOpenImmersion (zlCompactificationOpen D f₀ c).left := by
  change IsOpenImmersion c.i
  infer_instance

/-- The proper part as an arrow of k₀-schemes.
Source: blueprint compactification construction
(blueprint: def-zl-weil-compact-support-cohomology). -/
def zlCompactificationProper {X₀ Y₀ : Over (Spec (.of D.k₀))}
    (f₀ : X₀ ⟶ Y₀) (c : Compactification f₀.left) :
    zlCompactificationMiddle D f₀ c ⟶ Y₀ :=
  Over.homMk c.g

/-- The geometric fibre has its specified structure over the chosen algebraic closure.
Source: blueprint finite-field geometric-fibre convention
(blueprint: def-zl-weil-compact-support-cohomology). -/
instance zlGeometricFiberOver (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    (D.geometricFiber X₀).left.Over (Spec (.of D.k)) :=
  ⟨(D.geometricFiber X₀).hom⟩

/-- The base-changed map respects the specified geometric structure maps.
Source: blueprint geometric-fibre convention
(blueprint: def-zl-weil-compact-support-cohomology).
Proof: this is the Over.w equation of the image of f₀ under Over.pullback. -/
@[instance]
theorem zlFiberMap_isOver {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀) :
    (zlFiberMap D f₀).IsOver (Spec (.of D.k)) := by
  exact ⟨((Over.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).w⟩

/-- Separatedness survives geometric base change.
Source: Stacks 01L4; blueprint compact-support geometric fibre
(blueprint: def-zl-weil-compact-support-cohomology).
Proof: the square of f₀ with its geometric-fibre map is Cartesian. Base change
preserves closed diagonals, which characterize separatedness. -/
@[instance]
theorem zlFiberMap_separated {X₀ Y₀ : Over (Spec (.of D.k₀))}
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left] : IsSeparated (zlFiberMap D f₀) := by
  exact MorphismProperty.overPullbackMap (P := @IsSeparated)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) f₀ inferInstance

/-- Local finite type survives geometric base change.
Source: Stacks 01T6; blueprint compact-support geometric fibre
(blueprint: def-zl-weil-compact-support-cohomology).
Proof: f₀.left and zlFiberMap D f₀ form the base-change square of the two
structure-map pullbacks. Apply locally finite type stability under base change. -/
@[instance]
theorem zlFiberMap_finiteType {X₀ Y₀ : Over (Spec (.of D.k₀))}
    (f₀ : X₀ ⟶ Y₀) [LocallyOfFiniteType f₀.left] :
    LocallyOfFiniteType (zlFiberMap D f₀) := by
  exact MorphismProperty.overPullbackMap (P := @LocallyOfFiniteType)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) f₀ inferInstance

/-- Quasi-compactness survives geometric base change.
Source: Stacks 01K0; blueprint compact-support geometric fibre
(blueprint: def-zl-weil-compact-support-cohomology).
Proof: use the same Cartesian square and quasi-compact base-change stability. -/
@[instance]
theorem zlFiberMap_quasiCompact {X₀ Y₀ : Over (Spec (.of D.k₀))}
    (f₀ : X₀ ⟶ Y₀) [QuasiCompact f₀.left] : QuasiCompact (zlFiberMap D f₀) := by
  exact MorphismProperty.overPullbackMap (P := @QuasiCompact)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) f₀ inferInstance

include hl in
/-- The coefficient prime is a unit in the closure field itself.
Source: blueprint finite-field coefficient convention
(blueprint: def-zl-weil-compact-support-cohomology).
Proof: D.card_base and D.cardinality_eq give characteristic D.p in D.k₀ and
hence D.k. The prime l differs from D.p, so its image in that field is nonzero,
and therefore invertible. -/
theorem zlClosurePrimeUnit : IsUnit (l : D.k) := by
  let := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
      (D.card_base.trans D.cardinality_eq))
  have : CharP D.k D.p :=
    charP_of_injective_algebraMap (algebraMap D.k₀ D.k).injective D.p
  exact (CharP.isUnit_natCast_iff (R := D.k) D.prime).2
    (fun h ↦ hl ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : l.Prime)).1 h).symm)

end WeilConjectures
