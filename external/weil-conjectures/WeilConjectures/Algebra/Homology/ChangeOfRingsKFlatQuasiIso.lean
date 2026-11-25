/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.Algebra.Homology.ChangeOfRingsAcyclicKFlat
import WeilConjectures.Algebra.Homology.KFlatClosure
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-!
# Change of rings preserves quasi-isomorphisms between K-flat complexes

Source: Stacks Project, Cohomology on Sites, Tag 06YT.
-/

@[expose] public section

universe u

open CategoryTheory

namespace SheafOfModules

set_option hygiene false in
local notation "𝓡" R => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

/-- Termwise extension of scalars preserves quasi-isomorphisms between K-flat complexes.
Source: Stacks Project, Cohomology on Sites, Tag 06YT, with the second complex the
new ring in degree zero; Tag 06YY applies this to change of rings.

Proof: Regard O' as an O-module by restriction of scalars and choose a K-flat resolution
R → O' using Tag 06YS. Its cone is acyclic. Form the natural commuting square of total
tensor maps with rows R ⊗ P → R ⊗ Q and O' ⊗ P → O' ⊗ Q. The cone of the top map is
R ⊗ Cone(α), acyclic by K-flatness of R and the signed symmetry of total tensor complexes.
The cones of the vertical maps are Cone(R → O') ⊗ P and Cone(R → O') ⊗ Q, acyclic by
K-flatness of P and Q. Tensor commutes with mapping cones, so these three maps are
quasi-isomorphisms. Applying cohomology to the square shows that its bottom map is an
isomorphism on cohomology in every degree. Tensoring with O' in degree zero is termwise
extension of scalars after forgetting the O'-action. The forgetful restriction functor
is exact and faithful, and reflects vanishing of cohomology, so the same map is a
quasi-isomorphism as a complex of O'-modules. The supplied object and morphism equalities
identify E's map of complexes with this map, including the equality transports.
(blueprint: lem-pur-change-of-rings-kflat-quasi-iso) -/
theorem changeOfRings_kFlat_quasiIso
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    {O O' : Sheaf J CommRingCat.{u}} (φ : O ⟶ O')
    (E : SheafOfModules.{u} (𝓡 O) ⥤ SheafOfModules.{u} (𝓡 O'))
    (h : ∀ M : SheafOfModules.{u} (𝓡 O), E.obj M = changeOfRings.{u, u, u} φ M)
    (hm : ∀ {M N : SheafOfModules.{u} (𝓡 O)} (a : M ⟶ N),
      E.map a = eqToHom (h M) ≫ changeOfRingsHom.{u, u, u} φ M a ≫ eqToHom (h N).symm)
    [E.Additive] :
    ∀ {P Q : CochainComplex (SheafOfModules.{u} (𝓡 O)) ℤ} (α : P ⟶ Q),
      P.IsKFlatTensor → Q.IsKFlatTensor → QuasiIso α →
        QuasiIso ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map α) := by
  intro P Q α hP hQ hα
  have hcone : (CochainComplex.mappingCone α).Acyclic :=
    (CochainComplex.mappingCone.quasiIso_iff_acyclic α).1 hα
  have hkcone : (CochainComplex.mappingCone α).IsKFlatTensor :=
    CochainComplex.isKFlat_mappingCone α hP hQ
  have hEcone := changeOfRings_acyclic_of_isKFlat φ E h hm
    (CochainComplex.mappingCone α) hkcone hcone
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic _).2
  intro i
  apply (HomologicalComplex.exactAt_iff_isZero_homology _ i).2
  exact ((HomologicalComplex.exactAt_iff_isZero_homology _ i).1 (hEcone i)).of_iso
    ((HomologicalComplex.homologyFunctor _ _ i).mapIso
      (CochainComplex.mappingCone.mapHomologicalComplexIso α E)).symm

end SheafOfModules
