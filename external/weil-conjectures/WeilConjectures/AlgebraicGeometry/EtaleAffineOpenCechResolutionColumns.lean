/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleOpenCechResolutionDoubleComplex
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.Functor

/-! # Vertical homology of the affine-open Čech resolution

Source: Stacks Project, Tags 03AZ and 03P2.
(blueprint: lem-sc-etale-affine-open-cech-resolution-columns)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem cechEvaluation_preservesHomology (X : Scheme.{u})
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    (cechComplexFunctor (A := AddCommGrpCat.{u + 1}) U ⋙
      HomologicalComplex.eval _ (.up ℕ) n).PreservesHomology := by
  let V := (Limits.FormalCoproduct.mk _ U).cech.obj (op (SimplexCategory.mk n))
  let T : Discrete V.I ⥤ X.Opensᵒᵖ :=
    Discrete.functor (fun t ↦ op (V.obj t))
  let F := cechComplexFunctor (A := AddCommGrpCat.{u + 1}) U ⋙
    HomologicalComplex.eval _ (.up ℕ) n
  let L := (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj T ⋙ lim
  let e : F ≅ L := NatIso.ofComponents (fun P ↦ Pi.isoLimit (T ⋙ P)) (by
    intro P Q α
    apply limit.hom_ext
    intro ⟨t⟩
    simp [F, L, T, V, cechComplexFunctor, Limits.FormalCoproduct.cochainComplexFunctor,
      Limits.FormalCoproduct.cosimplicialObjectFunctor, Pi.isoLimit_hom_π,
      Limits.FormalCoproduct.evalOp])
  have : AB4StarOfSize.{u} AddCommGrpCat.{u + 1} :=
    AB4StarOfSize_shrink.{u, u + 1} _
  have : PreservesFiniteLimits L := inferInstance
  have : PreservesFiniteColimits L := inferInstance
  have := preservesFiniteLimits_of_natIso e.symm
  have := preservesFiniteColimits_of_natIso e.symm
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem cechResolution_columnIso (X : Scheme.{u})
    {ι : Type u} (U : ι → X.Opens)
    (K : CochainComplex (X.Opensᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ℕ) (q : ℕ) :
    Nonempty
      (((HomologicalComplex.homologyFunctor _ (.up ℕ) q).mapHomologicalComplex
        (.up ℕ)).obj
        (HomologicalComplex₂.flip
          (((cechComplexFunctor U).mapHomologicalComplex (.up ℕ)).obj K)) ≅
        (cechComplexFunctor U).obj (K.homology q)) := by
  have : ∀ n, (cechComplexFunctor (A := AddCommGrpCat.{u + 1}) U ⋙
      HomologicalComplex.eval _ (.up ℕ) n).PreservesHomology :=
    fun n ↦ cechEvaluation_preservesHomology X U n
  let S := K.sc q
  let F (n : ℕ) := cechComplexFunctor (A := AddCommGrpCat.{u + 1}) U ⋙
    HomologicalComplex.eval _ (.up ℕ) n
  refine ⟨HomologicalComplex.Hom.isoOfComponents (fun n ↦ S.mapHomologyIso (F n)) ?_⟩
  intro a b hab
  let τ : F a ⟶ F b :=
    { app := fun P ↦ ((cechComplexFunctor U).obj P).d a b
      naturality := fun P Q α ↦ ((cechComplexFunctor U).map α).comm a b }
  have hh := NatTrans.app_homology τ S
  change (S.mapHomologyIso (F a)).hom ≫ τ.app S.homology = _
  rw [hh]
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rfl

/-- The bottom vertical homology is the sections Čech complex and all positive
vertical homology rows of the affine-open resolution are zero.

Source: Stacks Project, Tag 03AZ, computation of the vertical cohomology, and
Tag 03P2, separated-case proof.
(blueprint: lem-sc-etale-affine-open-cech-resolution-columns)

Proof: In horizontal degree p the vertical complex is the product, over tuples
of p+1 opens, of the resolution evaluated at i of their categorical product.
These products are nonempty intersections of opens. The equality hi identifies
the underlying schemes of their images with the open subschemes of these
intersections. Iterating IsAffineOpen.inf proves affineness because X is
separated. The injective-resolution formula for rightDerived identifies the
positive homology of each evaluated resolution with the corresponding derived
evaluation of G, zero by hvan. Products of abelian groups are exact, so homology
commutes with these products: kernels are componentwise and choice supplies
componentwise preimages for the images. Thus every term of each positive
vertical-homology row is zero. In degree zero, left exactness of sheaf evaluation
identifies vertical homology with evaluation of G, naturally for restriction
maps. Those natural identifications commute with product projections and hence
with the cofaces and their alternating sums, giving the bottom-row complex
isomorphism. No covering hypothesis, global cohomology or total complex is used.
If the family is empty, all tuple products are indexed by the empty set and are
zero. Repeated opens and empty intersections cause no exception. -/
theorem etale_affineOpenCech_resolution_columns
    (X : Scheme.{u}) [X.IsSeparated]
    (i : X.Opens ⥤ X.Etale)
    (hi : i ⋙ Scheme.Etale.forget X = X.restrictFunctor)
    {ι : Type u} (U : ι → X.Opens)
    (hU : ∀ j, IsAffineOpen (U j))
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (hvan : ∀ (W : X.Etale), IsAffine W.left → ∀ (q : ℕ), 0 < q →
      IsZero (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
          (op W)).rightDerived q).obj G))
    (I : InjectiveResolution G) :
    Nonempty
      (((HomologicalComplex.homologyFunctor _ (.up ℕ) 0).mapHomologicalComplex
        (.up ℕ)).obj (etaleOpenCechResolutionDoubleComplex X i U I) ≅
        (cechComplexFunctor U).obj (i.op ⋙ G.obj)) ∧
    (∀ (q : ℕ), 0 < q → ∀ (p : ℕ),
      IsZero ((((HomologicalComplex.homologyFunctor _ (.up ℕ) q).mapHomologicalComplex
        (.up ℕ)).obj (etaleOpenCechResolutionDoubleComplex X i U I)).X p)) := by
  let A := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj i.op
  let K := (A.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  have hcol (q : ℕ) :
      Nonempty
        (((HomologicalComplex.homologyFunctor _ (.up ℕ) q).mapHomologicalComplex
          (.up ℕ)).obj (etaleOpenCechResolutionDoubleComplex X i U I) ≅
          (cechComplexFunctor U).obj (K.homology q)) := by
    exact cechResolution_columnIso X U K q
  constructor
  · obtain ⟨e⟩ := hcol 0
    let f : K.homology 0 ≅ A.obj G :=
      (I.isoRightDerivedObj A 0).symm ≪≫ A.rightDerivedZeroIsoSelf.app G
    exact ⟨e ≪≫ (cechComplexFunctor U).mapIso f⟩
  · intro q hq p
    obtain ⟨e⟩ := hcol q
    apply (HomologicalComplex.eval _ (.up ℕ) p).mapIso e |>.isZero_iff.mpr
    have hval (V : X.Opens) (hV : IsAffineOpen V) :
        IsZero ((K.homology q).obj (op V)) := by
      let E := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (op (i.obj V))
      have haff : IsAffine (i.obj V).left := by
        have heq := congrArg (fun F ↦ (F.obj V).left) hi
        change (i.obj V).left = (V : Scheme) at heq
        rw [heq]
        exact hV
      have hE := (I.isoRightDerivedObj E q).isZero_iff.mp (hvan (i.obj V) haff q hq)
      let ev := (CategoryTheory.evaluation X.Opensᵒᵖ AddCommGrpCat.{u + 1}).obj (op V)
      exact ((K.sc q).mapHomologyIso ev).isZero_iff.mp hE
    apply (IsZero.iff_id_eq_zero _).mpr
    apply Pi.hom_ext
    intro t
    have hprod : (∏ᶜ fun a : Fin (p + 1) ↦ U (t a)) = ⨅ a, U (t a) := by
      apply le_antisymm
      · exact le_iInf fun a ↦ leOfHom (Pi.π _ a)
      · exact leOfHom (Pi.lift (fun a ↦ homOfLE (iInf_le _ a)))
    have haff : IsAffineOpen (∏ᶜ fun a : Fin (p + 1) ↦ U (t a)) := by
      rw [hprod]
      exact IsAffineOpen.iInf fun a ↦ hU (t a)
    exact (hval _ haff).eq_of_tgt _ _

end AlgebraicGeometry.Scheme
