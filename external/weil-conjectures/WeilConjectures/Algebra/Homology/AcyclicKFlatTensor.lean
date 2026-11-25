/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.KFlat
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-!
# Total tensor with an acyclic K-flat complex

Source: Stacks Project, Tags 06Y0 and 06YT.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules

set_option hygiene false in
local notation "𝓡" R => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

private noncomputable def tensor_symmetry
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {O : Sheaf J CommRingCat.{u}}
    (K L : CochainComplex (SheafOfModules.{u} (𝓡 O)) ℤ) :
    letI := monoidalCategory O
    CochainComplex.mapBifunctor K L (curriedTensor _) ≅
      CochainComplex.mapBifunctor L K (curriedTensor _) := by
  letI := monoidalCategory O
  letI := symmetricCategory O
  let T := curriedTensor (SheafOfModules.{u} (𝓡 O))
  let A := ((T.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj K).obj L
  let B := ((T.flip.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj K).obj L
  let e : A ≅ B := HomologicalComplex.Hom.isoOfComponents
    (fun p ↦ HomologicalComplex.Hom.isoOfComponents
      (fun q ↦ β_ (K.X p) (L.X q)) (by
        intro q q' hq
        exact (BraidedCategory.braiding_naturality_right (K.X p) (L.d q q')).symm))
    (by
      intro p p' hp
      ext q : 1
      exact (BraidedCategory.braiding_naturality_left (K.d p p') (L.X q)).symm)
  exact (HomologicalComplex₂.total.mapIso e (.up ℤ)) ≪≫
    HomologicalComplex.mapBifunctorFlipIso L K T (.up ℤ)

/-- An acyclic K-flat complex has acyclic total tensor with every complex.
Source: Stacks Project, Tags 06Y0 and 06YT, proof by a K-flat resolution.

Proof: Choose a K-flat resolution r : P → F (Tag 06YS). The cone of r is acyclic.
K-flatness of K makes Tot(Cone(r) ⊗ K) acyclic; the tensor-cone isomorphism
and the cone criterion imply that Tot(r ⊗ id_K) is a quasi-isomorphism.
K-flatness of P applied to the acyclic K makes Tot(K ⊗ P) acyclic.
The signed symmetry sends the (p,q) summand by (-1)^(pq) times the module braiding
and identifies this with Tot(P ⊗ K). It is a chain isomorphism because
(p+1)q = pq+q and p+p(q+1) = pq modulo two. Thus the quasi-isomorphism
Tot(P ⊗ K) → Tot(F ⊗ K) transports vanishing of every homology object.
This also covers F = 0 and K = 0 without any nonzero hypothesis.
(blueprint: lem-pur-acyclic-kflat-tensor-arbitrary) -/
theorem tensor_acyclic_of_isKFlat
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {O : Sheaf J CommRingCat.{u}}
    (K : CochainComplex (SheafOfModules.{u} (𝓡 O)) ℤ)
    (hK : K.IsKFlatTensor) (hA : K.Acyclic)
    (F : CochainComplex (SheafOfModules.{u} (𝓡 O)) ℤ) :
    (letI := monoidalCategory O
     (CochainComplex.mapBifunctor F K (curriedTensor _)).Acyclic) := by
  let := monoidalCategory O
  let := Classical.choice (tensorClosed O).1
  obtain ⟨P, r, hP, _, hr, _⟩ := CochainComplex.exists_isKFlatResolution F
  have hcone : (CochainComplex.mappingCone r).Acyclic :=
    (CochainComplex.mappingCone.quasiIso_iff_acyclic r).1 hr
  have hc := hK (CochainComplex.mappingCone r) hcone
  let g := HomologicalComplex.mapBifunctorMap r (𝟙 K) (curriedTensor _) (.up ℤ)
  have : QuasiIso g := by
    apply (CochainComplex.mappingCone.quasiIso_iff_acyclic g).2
    exact HomologicalComplex.Acyclic.of_iso hc
      (CochainComplex.mapBifunctorMappingCone₁Iso r K (curriedTensor _))
  have hp : (CochainComplex.mapBifunctor P K (curriedTensor _)).Acyclic :=
    HomologicalComplex.Acyclic.of_iso (hP K hA) (tensor_symmetry K P)
  intro i
  exact (quasiIsoAt_iff_exactAt g i (hp i)).1 inferInstance

end SheafOfModules
