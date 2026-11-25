/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.Algebra.Homology.StalkTensorComplex
import WeilConjectures.Topology.SkyscraperComplex
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-!
# K-flatness detected on stalks

Source: Stacks Project, Cohomology, Lemma 06YB, label `lemma-check-K-flat-stalks`
(blueprint: lem-pc-kflat-stalk-criterion).
-/

@[expose] public section

universe v

open CategoryTheory MonoidalCategory TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

private theorem acyclic_iff_stalk (X : RingedSpace.{v})
    (F : CochainComplex (Modules X) ℤ) :
    F.Acyclic ↔ ∀ x : X,
      (((moduleStalkFunctor X x).mapHomologicalComplex (.up ℤ)).obj F).Acyclic := by
  constructor
  · intro h x i
    exact ((module_stalk_exact X (F.sc i).f).2.2.2.2
      (F.sc i).X₃ (F.sc i).f (F.sc i).g (F.sc i).zero).mp (h i) x
  · intro h i
    exact ((module_stalk_exact X (F.sc i).f).2.2.2.2
      (F.sc i).X₃ (F.sc i).f (F.sc i).g (F.sc i).zero).mpr (fun x ↦ h x i)

/-- (blueprint: lem-pc-kflat-stalk-criterion) A complex of sheaves of modules on a
ringed space is K-flat precisely when every stalk complex is K-flat over its
stalk ring (Stacks, Cohomology, Lemma 06YB).

Proof, forward: for an acyclic stalk complex, take its termwise skyscraper
complex (`lem-pc-skyscraper-complex`). K-flatness makes its total tensor with
`K` acyclic. Exactness can be checked on stalks
(`lem-weil-pbc-module-stalk-exact`, `def-pc-acyclic-complex-modules`), and the
stalk of the total tensor is the total tensor of stalks
(`lem-pc-stalk-tensor-complex`).

Proof, reverse: an acyclic sheaf complex has acyclic stalk complexes by
`lem-weil-pbc-module-stalk-exact`. K-flatness at every stalk and the tensor
identification show that the total tensor is acyclic at every stalk; stalkwise
exactness then gives its acyclicity, as required by `def-pc-kflat-complex`. -/
theorem isKFlat_iff_stalk_isKFlat (X : RingedSpace.{v})
    (K : CochainComplex (SheafOfModules.{v}
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{v} RingCat.{v})).obj X.sheaf)) ℤ) :
    K.IsKFlatTensor ↔ ∀ x : X,
      ∀ F : CochainComplex (ModuleCat.{v} (X.presheaf.stalk x)) ℤ,
        F.Acyclic →
          (CochainComplex.mapBifunctor F
            (((moduleStalkFunctor X x).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K) (curriedTensor _)).Acyclic := by
  let := SheafOfModules.monoidalCategory X.sheaf
  constructor
  · intro hK x F hF
    let S := (moduleStalkFunctor X x).mapHomologicalComplex (.up ℤ)
    let G := ((SheafOfModules.ringedModuleSkyscraperFunctor X x).mapHomologicalComplex
      (.up ℤ)).obj F
    obtain ⟨⟨e⟩, hG⟩ := SheafOfModules.skyscraper_complex X x F
    obtain ⟨t, _⟩ := CochainComplex.exists_stalk_tensor_complex_iso X x
    have hT := (acyclic_iff_stalk X _).mp (hK G (hG hF)) x
    have hTK : (CochainComplex.mapBifunctor (S.obj G) (S.obj K)
        (curriedTensor _)).Acyclic := fun i ↦ (hT i).of_iso (t G K)
    let eT := (((curriedTensor _).map₂CochainComplex).mapIso e).app (S.obj K)
    exact fun i ↦ (hTK i).of_iso eT
  · intro hK F hF
    apply (acyclic_iff_stalk X _).mpr
    intro x
    obtain ⟨t, _⟩ := CochainComplex.exists_stalk_tensor_complex_iso X x
    have h := hK x _ ((acyclic_iff_stalk X F).mp hF x)
    exact fun i ↦ (h i).of_iso (t F K).symm

end AlgebraicGeometry.RingedSpace
