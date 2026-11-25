/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorComparison
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Detecting acyclicity of change of rings by total tensor

Source: Stacks Project, Tag 06YY.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace SheafOfModules

set_option hygiene false in
local notation "𝓡" R => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

private theorem acyclic_of_restriction
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    {R R' : Sheaf J RingCat.{u}} (α : R ⟶ R')
    (L : CochainComplex (SheafOfModules.{u} R') ℤ)
    (hL : (((restrictScalars α).mapHomologicalComplex (.up ℤ)).obj L).Acyclic) :
    L.Acyclic := by
  intro i
  apply ((L.sc i).exact_map_iff_of_faithful (toSheaf R')).mp
  exact (hL i).map (toSheaf R)

/-- Universal tensor acyclicity implies acyclicity after extension of scalars.
Source: Stacks Project, Tag 06YY, and the degree-zero total tensor comparison.

Proof: Regard O' as an O-module S by restriction of scalars, and take its single
complex in degree zero. Apply hT to this single complex. The degree-n total is
S ⊗ K^n, since all other S-degrees are zero, and its differential is id_S ⊗ d_K.
Sheafification of the sectionwise tensor identifies this with restriction of the
termwise change of rings, naturally in K^n and d_K. This remains valid for the zero
ring and zero modules. Restriction of scalars is exact and faithful: its underlying
abelian sheaf is unchanged, so it preserves and reflects kernels, cokernels and
vanishing of homology. It therefore reflects acyclicity of the extended complex.
Finally the components eqToIso (h M) form a natural isomorphism, since hm is precisely
its naturality square after cancelling equality transports. Map this isomorphism
termwise to identify the prescribed E-complex with that extension of scalars complex.
No K-flatness, acyclicity of K, or flatness of O' is assumed in this comparison lemma.
(blueprint: lem-pur-change-of-rings-tensor-acyclic) -/
theorem changeOfRings_acyclic_of_tensor_acyclic
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    {O O' : Sheaf J CommRingCat.{u}} (φ : O ⟶ O')
    (E : SheafOfModules.{u} (𝓡 O) ⥤ SheafOfModules.{u} (𝓡 O'))
    (h : ∀ M : SheafOfModules.{u} (𝓡 O), E.obj M = changeOfRings.{u, u, u} φ M)
    (hm : ∀ {M N : SheafOfModules.{u} (𝓡 O)} (a : M ⟶ N),
      E.map a = eqToHom (h M) ≫ changeOfRingsHom.{u, u, u} φ M a ≫ eqToHom (h N).symm)
    [E.Additive]
    (K : CochainComplex (SheafOfModules.{u} (𝓡 O)) ℤ)
    (hT : ∀ F : CochainComplex (SheafOfModules.{u} (𝓡 O)) ℤ,
      letI := monoidalCategory O
      (CochainComplex.mapBifunctor F K (curriedTensor _)).Acyclic) :
    ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic := by
  let := monoidalCategory O
  let U := restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)
  let S := U.obj (unit (𝓡 O'))
  obtain ⟨e, he⟩ := exists_changeOfRings_tensor_comparison φ
  let q (i : ℤ) : U.obj (E.obj (K.X i)) ≅ S ⊗ K.X i :=
    U.mapIso (eqToIso (h (K.X i))) ≪≫ e (K.X i)
  let L := ((E.mapHomologicalComplex (.up ℤ)).obj K)
  let Q := (((curriedTensor _).obj S).mapHomologicalComplex (.up ℤ)).obj K
  have hq : ((U.mapHomologicalComplex (.up ℤ)).obj L) ≅ Q :=
    HomologicalComplex.Hom.isoOfComponents q (by
      intro i j hij
      change (q i).hom ≫ S ◁ K.d i j = U.map (E.map (K.d i j)) ≫ (q j).hom
      dsimp [q]
      rw [hm, Functor.map_comp, Functor.map_comp]
      simp only [Category.assoc]
      rw [← he]
      simp [U])
  let t := CochainComplex.mapBifunctorSingle₁Iso (curriedTensor _) S K
  have ht := hT ((HomologicalComplex.single _ (.up ℤ) 0).obj S)
  have hL : ((U.mapHomologicalComplex (.up ℤ)).obj L).Acyclic := by
    intro i
    exact ((ht i).of_iso t).of_iso hq.symm
  exact acyclic_of_restriction
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ) L hL

end SheafOfModules
