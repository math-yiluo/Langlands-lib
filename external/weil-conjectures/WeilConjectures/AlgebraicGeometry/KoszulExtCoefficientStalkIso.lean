/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk

import WeilConjectures.AlgebraicGeometry.KoszulExtCoefficientStalkModel
import WeilConjectures.RingTheory.KoszulCoefficientTopHomology

/-! # Coefficient comparison for scalar Koszul Ext

Source: Stacks Project, Tag 0BQZ, lemma-regular-immersion-ext. -/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The scalar coefficient comparison, induced by O_Y -> i_* O_Z. Pullback is
applied only to the degree-n cohomology map, not to the Hom complex.

Source: Stacks Project, Tag 0BQZ, coefficient map in lemma-regular-immersion-ext.
(blueprint: lem-sc-koszul-ext-coefficient-stalk-iso). -/
noncomputable def koszulScalarExtCoefficientMap
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (n : ℕ) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
    let F := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (n : ℤ)).obj
        (H.obj (op (S.obj B), S.obj (SheafOfModules.unit Y.ringCatSheaf)))
    let G := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (n : ℤ)).obj
        (H.obj (op (S.obj B), S.obj B))
    (Scheme.Modules.tensorPullback i).obj F ⟶
      (Scheme.Modules.tensorPullback i).obj G := by
  dsimp only
  let μ : SheafOfModules.unit Y.ringCatSheaf ⟶
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf) :=
    (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app _ ≫
      (Scheme.Modules.pushforward i).map (Scheme.Modules.pullbackObjUnitIso i).hom
  exact (Scheme.Modules.tensorPullback i).map
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (n : ℤ)).map
      ((derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).map
        (𝟙 _, (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map μ)))

private theorem koszul_bijective_of_square
    {A B C D : Type*} (f : A → B) (g : C → D) (eF : A ≃ C) (eG : B ≃ D)
    (hcomm : ∀ x, eG (f x) = g (eF x)) (hbase : Function.Bijective g) :
    Function.Bijective f := by
  have h : eG ∘ f = g ∘ eF := funext hcomm
  apply (eG.bijective.of_comp_iff' f).mp
  rw [h]
  exact hbase.comp eF.bijective

-- Matching the derived stalk model unfolds both coefficient objects and tensor pullback.
/-- The canonical coefficient comparison is bijective on a stalk in a length-n
Koszul-regular affine chart. This is solely a local assertion about a specified map.

Source: Stacks Project, Tag 0BQZ, lemma-regular-immersion-ext, final coefficient
comparison between the two dual Koszul complexes.
(blueprint: lem-sc-koszul-ext-coefficient-stalk-iso).

Proof: Write A = O_Y(U), I = ker(i)(U), and B = A/I. The closed immersion
identifies the closed preimage with Spec B. The sheafified augmented Koszul
complex resolves i_* O_Z on U, and its terms are finite free. Restriction of
derived internal Hom and the bounded finite free Hom comparison compute the
coefficient morphism by Hom(K,A) -> Hom(K,B). Naturality identifies the specified
map induced by the adjunction unit with reduction of cochains modulo I.
The degree-n top term of Hom(K,A) is free of rank one, its incoming differential
has image I times that term, and its outgoing term is zero. Hom(K,B) has zero
differential; its degree-n term is the same rank-one module modulo I. Thus
reduction induces a bijection in top cohomology. Exact associated-module
sheafification preserves this comparison. These cohomology modules are already
B-modules, so tensor pullback along Spec B -> Spec A preserves the bijection.
Taking the stalk at z and restricting to V preserves it. Use the common
K-injective Hom complex to transport the computation to the supplied derived
universe. For n = 0, I = 0 and reduction is identity. The point z excludes an
empty chart preimage; there are no assumptions at other points. -/
theorem koszulRegularImmersion_ext_coefficient_stalk_iso
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (V : Z.Opens) (n : ℕ) (z : V.toScheme)
    (U : Y.affineOpens) (hzU : i z.1 ∈ U.1) (f : Fin n → Γ(Y, U.1))
    (hf : Ideal.span (Set.range f) = i.ker.ideal U)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) :
    Function.Bijective
      (((Scheme.Modules.restrictFunctor V.ι).map
        (koszulScalarExtCoefficientMap i n)).stalkLinearMap z) := by
  let A := (Γ(Y, U.1) : Type u)
  let R := (V.toScheme.presheaf.stalk z : Type u)
  let ρ : A →+* R := ((Y.presheaf.germ U.1 (i z.1) hzU) ≫
    i.stalkMap z.1 ≫ V.ι.stalkMap z).hom
  let : Algebra A R := ρ.toAlgebra
  let a : SheafOfModules.unit Y.ringCatSheaf ⟶
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf) :=
    (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app _ ≫
      (Scheme.Modules.pushforward i).map (Scheme.Modules.pullbackObjUnitIso i).hom
  obtain ⟨eF, eG, hcomm⟩ :=
    koszulExtCoefficient_stalk_model i V n n z U hzU f hf hreg a rfl
  let q := HomologicalComplex.homologyMap
    (ExteriorAlgebra.koszulCoefficientReduction A (i.ker.ideal U) n f) n
  have hq : IsIso q :=
    ExteriorAlgebra.koszulCoefficientReduction_isIso_top_homology A (i.ker.ideal U) n f hf
  have hbij : Function.Bijective q.hom := by
    exact (ConcreteCategory.isIso_iff_bijective q).mp hq
  let e := LinearEquiv.ofBijective q.hom hbij
  have hbase : Function.Bijective (q.hom.baseChange R) := by
    exact (LinearEquiv.baseChange A R _ _ e).bijective
  exact koszul_bijective_of_square _ _ eF.toEquiv eG.toEquiv hcomm hbase

end AlgebraicGeometry
