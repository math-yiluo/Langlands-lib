/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.AlgebraicGeometry.IntrinsicFlatModuleStalkTensorPresentation
import Mathlib.RingTheory.Flat.Localization

/-! # Recovering relative flatness from stalks

Source: Stacks Project, Morphisms, Tag 01U4, implication (1) to (2).
(blueprint: lem-pc-relative-flat-of-stalks).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- A quasi-coherent module with relatively flat stalks satisfies the affine-section
relative-flatness criterion.
Source: Stacks Project, Morphisms, Tag 01U4, implication (1) to (2).
(blueprint: lem-pc-relative-flat-of-stalks).

Proof: Fix affine opens V of S and U of X with U contained in f inverse V.
Put R = O_S(V), A = O_X(U), and N = G(U), using the ring map f.appLE.
For each prime q of A, let x be its point of U and p its inverse image in R.
Quasi-coherence identifies N localized at q with G_x as an A_q-module.
The stalk of S at f(x) is R_p, compatibly with f.appLE and f.stalkMap.
By the hypothesis G_x is R_p-flat. Since R_p is a flat R-algebra, G_x is
R-flat by transitivity. Thus all the localizations N_q are R-flat.
The local criterion for flatness of an A-module over R now makes N R-flat
(Algebra Tag 00HT). This proves each test in IsFlatOver. Empty affine opens
have zero sections, which are flat; an empty source has no stalk tests. -/
theorem relative_flat_of_stalks {X S : Scheme.{u}} (f : X ⟶ S)
    (G : X.Modules) [G.IsQuasicoherent]
    (h : ∀ x : X, Module.Flat (S.presheaf.stalk (f x))
      ((ModuleCat.restrictScalars (f.stalkMap x).hom).obj
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj G))) :
    G.IsFlatOver f := by
  classical
  intro V U hUV
  let R := Γ(S, V.1)
  let A := Γ(X, U.1)
  let N := Γ(G, U.1)
  let : Algebra R A := (f.appLE V.1 U.1 hUV).hom.toAlgebra
  let : Module R N := Module.compHom N (algebraMap R A)
  have : IsScalarTower R A N := IsScalarTower.of_compHom R A N
  let x (q : Ideal A) [q.IsMaximal] : U.1 :=
    U.2.isoSpec.inv ⟨q, inferInstance⟩
  let P (q : Ideal A) [q.IsMaximal] : Type u :=
    (RingedSpace.moduleStalkFunctor X.toRingedSpace (x q).1).obj G
  let astalk (q : Ideal A) [q.IsMaximal] : Algebra A (X.presheaf.stalk (x q).1) :=
    X.presheaf.algebra_section_stalk (x q)
  let amod (q : Ideal A) [q.IsMaximal] : Module A (P q) :=
    Module.compHom _ (algebraMap A (X.presheaf.stalk (x q).1))
  have towerA (q : Ideal A) [q.IsMaximal] :
      IsScalarTower A (X.presheaf.stalk (x q).1) (P q) :=
    IsScalarTower.of_compHom A (X.presheaf.stalk (x q).1) (P q)
  let rmod (q : Ideal A) [q.IsMaximal] : Module R (P q) :=
    Module.compHom _ (algebraMap R A)
  have tower (q : Ideal A) [q.IsMaximal] : IsScalarTower R A (P q) :=
    IsScalarTower.of_compHom R A (P q)
  have prime (q : Ideal A) [q.IsMaximal] : (U.2.primeIdealOf (x q)).asIdeal = q := by
    change (U.2.isoSpec.hom (U.2.isoSpec.inv ⟨q, inferInstance⟩)).asIdeal = q
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  have loc (q : Ideal A) [q.IsMaximal] :
      IsLocalization.AtPrime (X.presheaf.stalk (x q).1) q := by
    have hl := U.2.isLocalization_stalk (x q)
    simpa only [IsLocalization.AtPrime, prime q] using hl
  have hid : ((𝟙 X : X ⟶ X).appLE U.1 U.1 le_rfl).hom = RingHom.id A := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_base, Scheme.Hom.id_app,
      homOfLE_refl, CategoryTheory.op_id, Category.id_comp]
    exact congrArg CommRingCat.Hom.hom (X.presheaf.map_id (Opposite.op U.1))
  have hmod : Module.compHom N ((𝟙 X : X ⟶ X).appLE U.1 U.1 le_rfl).hom =
      (inferInstance : Module A N) := by
    rw [hid]
    rfl
  let E (q : Ideal A) [q.IsMaximal] :
      TensorProduct A (X.presheaf.stalk (x q).1) N ≃ₗ[X.presheaf.stalk (x q).1] P q := by
    have he := affine_sections_stalk_tensor_presentation G U (x q).1 (x q).2
    rw [hmod] at he
    exact he.some
  let ell (q : Ideal A) [q.IsMaximal] : N →ₗ[A] P q :=
    ((E q).restrictScalars A).toLinearMap ∘ₗ TensorProduct.mk A (X.presheaf.stalk (x q).1) N 1
  have hlocal (q : Ideal A) [q.IsMaximal] : IsLocalizedModule.AtPrime q (ell q) := by
    exact IsLocalizedModule.of_linearEquiv q.primeCompl
      (TensorProduct.mk A (X.presheaf.stalk (x q).1) N 1) ((E q).restrictScalars A)
  apply @Module.flat_of_isLocalized_maximal R A _ _ _ N _ _ _ _ P _ rmod amod
    tower ell hlocal
  intro q hq
  let y := (x q).1
  have hy : f y ∈ V.1 := hUV (x q).2
  let B := S.presheaf.stalk (f y)
  let : Algebra R B := S.presheaf.algebra_section_stalk ⟨f y, hy⟩
  let : Module B (P q) := Module.compHom _ (f.stalkMap y).hom
  have hf : Module.Flat B (P q) := h y
  have := V.2.isLocalization_stalk ⟨f y, hy⟩
  have : Module.Flat R B := IsLocalization.flat B
    (V.2.primeIdealOf ⟨f y, hy⟩).asIdeal.primeCompl
  have ht : IsScalarTower R B (P q) := by
    apply IsScalarTower.of_algebraMap_smul
    intro r m
    change (f.stalkMap y).hom ((S.presheaf.germ V.1 (f y) hy).hom r) • m =
      (X.presheaf.germ U.1 y (x q).2).hom ((f.appLE V.1 U.1 hUV).hom r) • m
    rw [f.germ_stalkMap_apply]
    congr 1
    exact (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hUV) y
      (x q).2 (f.app V.1 r)).symm
  exact Module.Flat.trans R B (P q)

end AlgebraicGeometry
