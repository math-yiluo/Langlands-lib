/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory

/-!
# Derived tensor product on the small pro-etale site

Source: the Weil conjectures blueprint, `prose-03-02`, order 663;
Stacks Project, Cohomology on Sites, Tags 06YN, 06YS and 06YU
(blueprint: prose-03-02).

The constant sheaf is formed in commutative rings before forgetting to rings,
so the recorded K-flat predicate and sheaf tensor product apply directly.
-/

@[expose] public section

universe w

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme

variable (Y : Scheme.{w}) (A : Type w) [CommRing A]

set_option hygiene false in
set_option quotPrecheck false in
local notation "𝓡" =>
  (constantSheaf (ProEt.topology Y) CommRingCat.{w + 1}).obj
    (CommRingCat.of (ULift.{w + 1, w} A))
set_option hygiene false in
set_option quotPrecheck false in
local notation "𝓢" =>
  (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{w + 1} RingCat.{w + 1})).obj 𝓡

/-- Derived tensor with a chosen K-flat resolution `f : P ⟶ K₁`.

The K-flat condition is the existing `CochainComplex.IsKFlatTensor` for the constant
sheaf of commutative rings.
The representative is the total complex with degree `n` term `⨁ p + q = n, Pᵖ ⊗ K₂ᵠ`
and differential `d_P ⊗ 1 + (-1)^p 1 ⊗ d_K₂`, mapped into the derived category.
No independence-of-resolution theorem is asserted here.

Source: blueprint `prose-03-02`, order 663; Stacks Project, Tags 06YN,
06YS and 06YU (blueprint: prose-03-02). -/
noncomputable def derivedTensor
    (K₁ K₂ P : CochainComplex (SheafOfModules.{w + 1} 𝓢) ℤ)
    (_f : P ⟶ K₁) (_hf : QuasiIso _f)
    (_hP : CochainComplex.IsKFlatTensor.{w + 1, w} (R := 𝓡) P) :
    proEtaleDerivedCategory Y A :=
  letI := SheafOfModules.monoidalCategory 𝓡
  letI := HasDerivedCategory.standard (SheafOfModules.{w + 1} 𝓢)
  DerivedCategory.Q.obj (CochainComplex.mapBifunctor P K₂ (curriedTensor _))

end AlgebraicGeometry.Scheme
