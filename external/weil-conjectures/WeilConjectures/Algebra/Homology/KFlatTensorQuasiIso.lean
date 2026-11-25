/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-!
# Tensoring a K-flat quasi-isomorphism with an arbitrary complex

Source: Stacks Project, Lemma 15.60.12, Tag 064L
(blueprint: lem-pc-kflat-tensor-quasi-iso).

The ring is regarded as a constant sheaf on the one-point site with the bottom topology.
K-flatness is the existing `CochainComplex.IsKFlatTensor` for sheaves of modules on this site.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CochainComplex

variable {R : Type u} [CommRing R]

/-- (blueprint: lem-pc-kflat-tensor-quasi-iso) The commutative ring `R` regarded as a
sheaf on the one-point site, as in the node's interpretation of Stacks, Tag 064L.
The bottom topology imposes no additional sheaf condition; the constant presheaf
has value `R` at the unique object. -/
def onePointRingSheaf (R : Type u) [CommRing R] :
    Sheaf (⊥ : GrothendieckTopology (Discrete PUnit.{u+1})) CommRingCat.{u} :=
  ⟨(Functor.const _).obj (CommRingCat.of R), Presheaf.isSheaf_bot _⟩

private theorem quasiIso_of_commuting_square
    {A B C D : CochainComplex (SheafOfModules.{u}
      ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj (onePointRingSheaf R))) ℤ}
    (f : A ⟶ B) (g : A ⟶ C) (h : B ⟶ D) (k : C ⟶ D)
    (hf : QuasiIso f) (hg : QuasiIso g) (hh : QuasiIso h)
    (comm : f ≫ h = g ≫ k) : QuasiIso k := by
  have := hf
  have := hg
  have := hh
  have hcomp : QuasiIso (g ≫ k) := by
    rw [← comm]
    infer_instance
  have := hcomp
  exact quasiIso_of_comp_left g k

private theorem kFlat_tensor_right_of_quasiIso
    {E E' K : CochainComplex
      (SheafOfModules.{u}
        ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj (onePointRingSheaf R))) ℤ}
    (α : E ⟶ E') (hα : QuasiIso α) (hK : K.IsKFlatTensor) :
    (letI := SheafOfModules.monoidalCategory (onePointRingSheaf R)
     QuasiIso (HomologicalComplex.mapBifunctorMap α (𝟙 K) (curriedTensor _) (.up ℤ))) := by
  let := SheafOfModules.monoidalCategory (onePointRingSheaf R)
  let := (SheafOfModules.tensorClosed (onePointRingSheaf R)).1.some
  have hc := (mappingCone.quasiIso_iff_acyclic α).1 hα
  have ht := hK (mappingCone α) hc
  apply (mappingCone.quasiIso_iff_acyclic _).2
  intro i
  exact (ht i).of_iso (mapBifunctorMappingCone₁Iso α K (curriedTensor _))

private theorem kFlat_tensor_left_of_quasiIso
    {K L L' : CochainComplex
      (SheafOfModules.{u}
        ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj (onePointRingSheaf R))) ℤ}
    (α : L ⟶ L') (hα : QuasiIso α) (hK : K.IsKFlatTensor) :
    (letI := SheafOfModules.monoidalCategory (onePointRingSheaf R)
     QuasiIso (HomologicalComplex.mapBifunctorMap (𝟙 K) α (curriedTensor _) (.up ℤ))) := by
  let := SheafOfModules.monoidalCategory (onePointRingSheaf R)
  let := SheafOfModules.symmetricCategory (onePointRingSheaf R)
  let := (SheafOfModules.tensorClosed (onePointRingSheaf R)).1.some
  have hc := (mappingCone.quasiIso_iff_acyclic α).1 hα
  have ht := hK (mappingCone α) hc
  let F := curriedTensor (SheafOfModules.{u}
    ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj (onePointRingSheaf R)))
  let e : (((F.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
      (mappingCone α)).obj K) ≅
      (((F.flip.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
      (mappingCone α)).obj K) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun p ↦ HomologicalComplex.Hom.isoOfComponents
        (fun q ↦ β_ ((mappingCone α).X p) (K.X q)) (by
          intro q q' hqq'
          exact (BraidedCategory.braiding_naturality_right
            ((mappingCone α).X p) (K.d q q')).symm)) (by
        intro p p' hpp'
        ext q : 1
        exact (BraidedCategory.braiding_naturality_left
          ((mappingCone α).d p p') (K.X q)).symm)
  have ht' : (mapBifunctor K (mappingCone α) F).Acyclic := by
    intro i
    exact (ht i).of_iso (HomologicalComplex₂.total.mapIso e (.up ℤ) ≪≫
      HomologicalComplex.mapBifunctorFlipIso K (mappingCone α) F (.up ℤ))
  apply (mappingCone.quasiIso_iff_acyclic _).2
  intro i
  exact (ht' i).of_iso (mapBifunctorMappingCone₂Iso K α F)

/-- (blueprint: lem-pc-kflat-tensor-quasi-iso) Stacks, Tag 064L: if `α` is a
quasi-isomorphism between K-flat complexes of `R`-modules, then `Tot(α ⊗ 1_N)`
is a quasi-isomorphism for every complex `N`. Here `R` is a sheaf on the one-point site.

Proof (the node's five steps):

1. Symmetry: on the summand `F^p ⊗ G^q`, define `σ(F,G)` by
   `x ⊗ y ↦ (-1)^(pq) y ⊗ x` (Stacks, Tag 0FNI). The total differential is
   `d_F x ⊗ y + (-1)^p x ⊗ d_G y`. Applying `σ` gives coefficients
   `(-1)^((p+1)q)` on `y ⊗ d_F x` and `(-1)^(p+p(q+1))` on `d_G y ⊗ x`;
   these equal `(-1)^(pq+q)` and `(-1)^(pq)`, respectively, as obtained by
   differentiating `σ(x ⊗ y)`. Thus `σ` is a chain map. Its inverse is `σ(G,F)`.
   It is natural in both variables since chain maps preserve degrees. Consequently
   the total tensor maps in the two orders are conjugate by these isomorphisms,
   and acyclicity of the total complexes is equivalent in the two orders.
   Mathlib provides `HomologicalComplex.mapBifunctorFlipIso` and its naturality.
2. Tag 06Y0 in both variables: if `K` is K-flat and `s : L ⟶ L'` is a
   quasi-isomorphism, its cone is acyclic (`lem-pur-quasi-iso-cone-acyclic`).
   By `def-pc-kflat-complex`, `Tot(Cone(s) ⊗ K)` is acyclic, and step 1 gives
   acyclicity of `Tot(K ⊗ Cone(s))`. The tensor-cone identification
   `lem-pc-tensor-mapping-cone-iso` identifies this with the cone of
   `Tot(1_K ⊗ s)`. The cone criterion therefore makes this map a quasi-isomorphism;
   step 1 then gives the same result for `Tot(s ⊗ 1_K)`.
3. Choose a K-flat resolution `s : K ⟶ N` using `lem-pc-kflat-resolution`
   (Stacks, Tag 06Y4) on the one-point site: `K` is K-flat and `s` is a quasi-isomorphism.
4. Form the square with top map `Tot(α ⊗ 1_K)`, bottom map `Tot(α ⊗ 1_N)`,
   and vertical maps `Tot(1_E ⊗ s)` and `Tot(1_E' ⊗ s)`.
   Both composites are `Tot(α ⊗ s)` by functoriality of the total tensor complex
   (`def-pc-tensor-complex-sheaves`): on each summand they are `α^p ⊗ s^q`.
5. By step 2, the vertical maps are quasi-isomorphisms because `E` and `E'` are
   K-flat, and the top map is a quasi-isomorphism because `K` is K-flat.
   Taking cohomology in any degree gives a commuting square with those three
   maps isomorphisms. Two-of-three, or solving for the bottom map using their
   inverses, makes the bottom map an isomorphism in every degree. This is
   `QuasiIso` by `def-pc-quasi-iso-modules`. Stacks places `α` in the second
   variable; step 1 converts that formulation to the first-variable form here. -/
theorem kFlat_tensor_quasiIso
    {E E' N : CochainComplex
      (SheafOfModules.{u}
        ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj (onePointRingSheaf R))) ℤ}
    (α : E ⟶ E')
    (hα : QuasiIso α)
    (hE : E.IsKFlatTensor)
    (hE' : E'.IsKFlatTensor) :
    (letI := SheafOfModules.monoidalCategory (onePointRingSheaf R)
     QuasiIso (HomologicalComplex.mapBifunctorMap α (𝟙 N) (curriedTensor _) (.up ℤ))) := by
  let := SheafOfModules.monoidalCategory (onePointRingSheaf R)
  obtain ⟨K, s, hK, _, hs, _⟩ := exists_isKFlatResolution N
  let f := HomologicalComplex.mapBifunctorMap α (𝟙 K) (curriedTensor _) (.up ℤ)
  let g := HomologicalComplex.mapBifunctorMap (𝟙 E) s (curriedTensor _) (.up ℤ)
  let h := HomologicalComplex.mapBifunctorMap (𝟙 E') s (curriedTensor _) (.up ℤ)
  let k := HomologicalComplex.mapBifunctorMap α (𝟙 N) (curriedTensor _) (.up ℤ)
  apply quasiIso_of_commuting_square f g h k
  · exact kFlat_tensor_right_of_quasiIso α hα hK
  · exact kFlat_tensor_left_of_quasiIso s hs hE
  · exact kFlat_tensor_left_of_quasiIso s hs hE'
  · change ((curriedTensor _).map₂CochainComplex.map α).app K ≫
        ((curriedTensor _).map₂CochainComplex.obj E').map s =
      ((curriedTensor _).map₂CochainComplex.obj E).map s ≫
        ((curriedTensor _).map₂CochainComplex.map α).app N
    exact (((curriedTensor _).map₂CochainComplex.map α).naturality s).symm

end CochainComplex
