/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.Algebra.Homology.DerivedTensor
public import WeilConjectures.CategoryTheory.RingedSiteModules

/-!
# Tor amplitude on the small pro-etale site

Source: Stacks Project, Cohomology on Sites, Definition 21.46.1, Tag 08FZ, (1)--(2)
(auxiliary; not a blueprint node).

The tensor dependency is given on cochain representatives with a K-flat resolution.
Accordingly the vanishing condition is tested on all such resolutions of representatives
of the given derived object. K-flat resolutions exist and their tensors compute the same
derived tensor product, so this is independent of any representative or resolution choice.
-/

@[expose] public section

universe t

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Tor amplitude in the ordered interval `[a,b]` on the small pro-etale site.
For every module sheaf in degree zero, the cohomology of the derived tensor vanishes
outside the interval. We use the recorded `derivedTensor` on every K-flat resolution
of every cochain representative isomorphic to `K`; this imposes no choice of resolution.

Source: Stacks Project, Cohomology on Sites, Definition 21.46.1 (1), Tag 08FZ
(auxiliary; not a blueprint node). -/
noncomputable def HasProEtaleTorAmplitude (Y : Scheme.{t}) (A : Type t) [CommRing A]
    (K : proEtaleDerivedCategory Y A) (a b : ℤ) : Prop :=
  let R := (constantSheaf (ProEt.topology Y) CommRingCat.{t + 1}).obj
    (CommRingCat.of (ULift.{t + 1, t} A))
  let S := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R
  let C := ringedSiteModules.{t + 1} S
  letI := HasDerivedCategory.standard C
  a ≤ b ∧ ∀ (L P : CochainComplex C ℤ),
    Nonempty (DerivedCategory.Q.obj L ≅ K) →
    ∀ (f : P ⟶ L) (hf : QuasiIso f)
      (hP : CochainComplex.IsKFlatTensor.{t + 1, t} (R := R) P)
      (M : C) (i : ℤ),
      (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor C i).obj
        (derivedTensor Y A L
          ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M) P f hf hP))

end AlgebraicGeometry.Scheme
