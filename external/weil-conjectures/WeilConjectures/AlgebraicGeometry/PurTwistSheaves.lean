/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf
public import WeilConjectures.AlgebraicGeometry.PurTwistCoefficientRings
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import WeilConjectures.AlgebraicGeometry.LisseLatticeCoefficients

/-! # The integral Tate line on the pro-etale site

Source: Stacks Project, Tag 03PK; the coefficient-twist blueprint, order 1505
(auxiliary; not a blueprint node).

The auxiliary constructions retain the root tower, constant scalar extension and completed
scalar action. All choices below have a uniqueness specification. The tensor of commutative
ring sheaves is their pushout, so the coefficient comparison is a morphism of ring sheaves.
The natural-number level `n` means positive exponent `n + 1` throughout.

## Main definitions

* `purTwistZlOne` and `purTwistZlModule`: the root limit and its completed scalar action.
* `purTwistIntegralOne` and `purTwistIntegralModule`: the prescribed integral tensor line.
* `purTwistFiniteOne`: its prescribed ordinary finite-coefficient tensor reduction.
The coefficient rings and their comparison are reexported from
`WeilConjectures.AlgebraicGeometry.PurTwistCoefficientRings`. Local freeness and derived
completeness
are proved in `Sheaf.Paper.PurTwistSheafLocallyFree`.
-/

@[expose] public section

set_option autoImplicit false

universe u d

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings TensorProduct

namespace AlgebraicGeometry.Scheme

-- The universe-polymorphic `{max u (t + 1)}` sheafification instances get stuck on
-- universe constraints for the `CommRingCat.{u + 1}` sheaves of this file.
attribute [-instance] WeilConjectures.integralCoefficientRingSheafify
  WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective

variable (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]

/-- Forgetting commutativity preserves sheafification on the small pro-etale site.
Source: Stacks Tag 00W1 (auxiliary; not a blueprint node).
Proof: sheafification uses covering-compatible families and their local equality relation.
Forgetting commutativity preserves the finite limits and filtered colimits in this
construction. Thus the same sheafification is obtained before and after forgetting. -/
theorem purTwistForgetPreservesSheafification :
    (ProEt.topology S).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := by
  have : EssentiallySmall.{u + 1} S.ProEt := essentiallySmallSelf.{0} _
  constructor
  intro P Q f hf
  change (ProEt.topology S).W
    (Functor.whiskerRight f (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
  have hi : Presheaf.IsLocallyInjective (ProEt.topology S) f := hf.isLocallyInjective
  have hs : Presheaf.IsLocallySurjective (ProEt.topology S) f := hf.isLocallySurjective
  apply ((ProEt.topology S).W_iff_isLocallyBijective _).mpr
  constructor
  · exact ⟨fun x y h ↦ Presheaf.equalizerSieve_mem (ProEt.topology S) f x y h⟩
  · exact ⟨fun x ↦ Presheaf.imageSieve_mem (ProEt.topology S) f x⟩

/-- The constant-ring comparison coming from commutation with forgetting commutativity.
Source: Stacks Tags 03CY and 03PK (auxiliary; not a blueprint node). -/
noncomputable def purTwistFiniteRingIso (n : ℕ) :
    purTwistRing S (purTwistFiniteRing S l n) ≅
      proEtaleRootsOfUnityCoefficientRing S (l ^ (n + 1)) :=
  letI := purTwistForgetPreservesSheafification S
  (constantCommuteCompose (ProEt.topology S)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app _

/-- The recorded finite roots module, transported along the canonical coefficient comparison.
Source: Stacks Tags 03CY and 03PK (auxiliary; not a blueprint node). -/
noncomputable def purTwistRootsModule (n : ℕ) :=
  (SheafOfModules.restrictScalars (purTwistFiniteRingIso S l n).hom).obj
    (proEtaleRootsOfUnityModule S (l ^ (n + 1)) (pow_pos (Fact.out : l.Prime).pos _))

variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

end AlgebraicGeometry.Scheme
