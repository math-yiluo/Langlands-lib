/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.Single
public import WeilConjectures.Algebra.Homology.DerivedTensor

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


/-- Derived tensor with the constant ring `B` along a ring map `φ : A →+* B`.

The constant ring sheaf `B_Y`, as a module over itself, is restricted along the
constant-sheaf image of `φ` and placed in degree zero. Applying `derivedTensor`
uses exactly the same chosen K-flat resolution of `K₁`.

Source: blueprint `prose-03-02`, order 663, last sentence;
Stacks Project, Tag 06YU (blueprint: prose-03-02). -/
noncomputable def derivedTensorRing
    (B : Type w) [CommRing B] (φ : A →+* B)
    (K₁ P : CochainComplex (SheafOfModules.{w + 1} 𝓢) ℤ)
    (f : P ⟶ K₁) (hf : QuasiIso f)
    (hP : CochainComplex.IsAcyclicTensorKFlat.{w + 1, w} (R := 𝓡) P) :
    proEtaleDerivedCategory Y A :=
  let RB := (constantSheaf (ProEt.topology Y) CommRingCat.{w + 1}).obj
    (CommRingCat.of (ULift.{w + 1, w} B))
  let SB := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{w + 1} RingCat.{w + 1})).obj RB
  let α : 𝓢 ⟶ SB := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{w + 1} RingCat.{w + 1})).map
      ((constantSheaf (ProEt.topology Y) CommRingCat.{w + 1}).map
        (CommRingCat.ofHom (RingHom.ulift φ)))
  let M := (SheafOfModules.restrictScalars.{w + 1} α).obj (SheafOfModules.unit SB)
  derivedTensor Y A K₁ ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj M) P f hf hP

end AlgebraicGeometry.Scheme
