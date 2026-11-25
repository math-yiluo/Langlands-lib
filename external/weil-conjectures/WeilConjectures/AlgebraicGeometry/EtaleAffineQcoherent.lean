/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
import WeilConjectures.AlgebraicGeometry.EtaleAffineQcoherentULift
import WeilConjectures.AlgebraicGeometry.EtaleULiftInjectiveResolution
import WeilConjectures.CategoryTheory.Sites.CohomologyDerivedEvaluation

/-!
# Étale acyclicity of a quasi-coherent module on an affine scheme

Source: blueprint `lemma-p-torsion-affine-curve-characteristic--4`, order 959;
Stacks Project, Étale Cohomology, Theorem 03P2 (affine case)
(blueprint: lemma-p-torsion-affine-curve-characteristic--4).
-/

@[expose] public section

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false in
/-- Higher étale cohomology of the associated quasi-coherent sheaf vanishes on an affine.

Source: Stacks Project, Étale Cohomology, Theorem 03P2 (affine case)
(blueprint: lemma-p-torsion-affine-curve-characteristic--4).
Proof:
1. Take the affine objects of the small étale site and finite jointly surjective affine
   étale covering families. Iterated fibre products are affine by
   `lem-weil-pbc-fibre-product-affine-spectra`, and every covering of an affine object
   admits such a refinement by `lem-weil-pbc-etale-covering-affine-refinement`.
   These verify conditions (1) and (2) of `lem-weil-pbc-cech-vanishing-criterion`.
2. On an affine object `u : U ⟶ X`, the module `u^*F` is quasi-coherent by
   `lem-weil-pbc-module-pullback-quasi-coherent`, and its associated presheaf is a sheaf
   by `proposition-p-torsion-smooth-proper-curve`. The composition isomorphisms of
   `lem-pc-module-pullback-identity-composition` identify its restrictions and Čech
   complex with those of `F_et` over `U`, using `proposition-p-torsion-smooth-proper-curve` and
   `def-weil-pbc-etale-site`. By `lem-sc-etale-standard-cover-cech`, replace the finite
   cover by its affine disjoint union `Spec B ⟶ Spec A`, with `A ⟶ B` faithfully flat.
   With `M = Γ(U,u^*F)`, `lem-weil-pbc-fibre-product-affine-spectra` and
   `lem-weil-pbc-module-pullback-affine-sections` identify the terms with
   `M ⊗_A B^{⊗_A(p+1)}`. Pullback coherence identifies the face maps with the Amitsur
   maps. By `proposition-p-torsion-smooth-proper-curve` the positive Čech cohomology vanishes,
   verifying condition (3) of `lem-weil-pbc-cech-vanishing-criterion`.
3. Apply that criterion at the final affine object `X`. Evaluation there is global
   sections by `def-weil-pbc-global-sections-functor`. An injective resolution is
   bounded below and K-injective by `prop-weil-pbc-kinjective-resolutions-exist`;
   thus derived evaluation computes the étale cohomology of
   `def-weil-pbc-etale-cohomology`, which vanishes in every positive degree.

For every `n`, this gives affine acyclicity in degree `n + 1`: the affine Cech
criterion and faithfully flat Amitsur exactness establish vanishing in every positive
degree, and the injective K-injective resolution identifies derived evaluation with
`Sheaf.H`. (blueprint: lem-sc-etale-affine-qcoherent-succ)

Proof: write `q = n + 1`. The Čech argument above is carried out for the universe
lift of the sheaf in `etale_affine_qcoherent_ulift`. An injective resolution of the
sheaf lifts to one of its universe lift, so the lifted cohomology is the lift of the
cohomology computed by derived evaluation at the terminal affine object. Its vanishing
therefore gives the vanishing of `Sheaf.H` in degree `n + 1`.
-/
theorem etale_affine_qcoherent
    (X : Scheme.{u}) [IsAffine X]
    (F : X.Modules) [F.IsQuasicoherent] (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H (AlgebraicGeometry.Scheme.Modules.etaleTensorSectionsSheaf F) q) := by
  classical
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  let G := Scheme.Modules.etaleTensorSectionsSheaf F
  let L := AddCommGrpCat.uliftFunctor.{u + 1, u}
  let G' := (sheafCompose X.smallEtaleTopology L).obj G
  let T : X.Etale := Scheme.Etale.mk (𝟙 X)
  have hT : CategoryTheory.Limits.IsTerminal T :=
    CategoryTheory.MorphismProperty.Over.mkIdTerminal _ _
  let E := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙
    (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u}).obj (Opposite.op T)
  let E' := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (Opposite.op T)
  let R := injectiveResolution G
  obtain ⟨S, hS⟩ := Scheme.exists_etale_ulift_injectiveResolution X G R
  obtain ⟨eS⟩ := hS T
  have hG' : Subsingleton (Sheaf.H G' (n + 1)) :=
    etale_affine_qcoherent_ulift X F (n + 1) (Nat.zero_lt_succ n)
  obtain ⟨e'⟩ := Sheaf.cohomology_nonempty_addEquiv_rightDerived_evaluation_succ
    X.smallEtaleTopology T hT G' n
  let := hG'
  let : Subsingleton ((E'.rightDerived (n + 1)).obj G') :=
    Function.Injective.subsingleton e'.symm.injective
  have hz : CategoryTheory.Limits.IsZero
      (((E'.mapHomologicalComplex (.up ℕ)).obj S.cocomplex).homology (n + 1)) :=
    CategoryTheory.Limits.IsZero.of_iso
      (AddCommGrpCat.isZero_iff_subsingleton.mpr inferInstance)
      (S.isoRightDerivedObj E' (n + 1)).symm
  have hc := (HomologicalComplex.homologyFunctor _ _ (n + 1)).mapIso eS
  let hm := ((E.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).sc (n + 1)
  have ei := (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ L))
    (.up ℕ)).app R.cocomplex
  have hj := (HomologicalComplex.homologyFunctor _ _ (n + 1)).mapIso ei
  have hl : CategoryTheory.Limits.IsZero
      (L.obj (((E.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).homology (n + 1))) :=
    CategoryTheory.Limits.IsZero.of_iso hz
      (hc ≪≫ hj.symm ≪≫ hm.mapHomologyIso L).symm
  let : Subsingleton (ULift.{u + 1}
      (((E.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).homology (n + 1))) :=
    AddCommGrpCat.isZero_iff_subsingleton.mp hl
  have hsmall : Subsingleton
      (((E.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).homology (n + 1)) :=
    Function.Injective.subsingleton (f := fun x ↦
      (ULift.up x : L.obj
        (((E.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).homology (n + 1))))
      ULift.up_injective
  obtain ⟨e⟩ := Sheaf.cohomology_nonempty_addEquiv_rightDerived_evaluation_succ
    X.smallEtaleTopology T hT G n
  exact @Function.Injective.subsingleton _ _ _
    ((R.isoRightDerivedObj E (n + 1)).addCommGroupIsoToAddEquiv.injective.comp e.injective)
    hsmall

end AlgebraicGeometry.Etale
