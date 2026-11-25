/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import WeilConjectures.Algebra.Homology.HomComplexDualTotalComparison
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom

/-! # Finite-diagonal Hom totalization of exact columns is acyclic

Source: Stacks Project, Tag 0GM8 via Tag 0GM7; the explicit proof is the
explicit calculation described below (blueprint: lem-sc-bounded-hom-exact-columns). -/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CochainComplex

section Helpers

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {R : Sheaf J CommRingCat.{w}}

private lemma homMap_zero_left
    {P P' Q Q' : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)} (g : Q ⟶ Q') :
    SheafOfModules.homObjMap (0 : P' ⟶ P) g = 0 := by
  apply SheafOfModules.hom_ext
  ext X φ : 3
  change (PresheafOfModules.restrictOver R.obj X.unop).map 0 ≫ φ ≫
    (PresheafOfModules.restrictOver R.obj X.unop).map g.val = 0
  ext W x
  change ((g.val.app _).hom) ((φ.app W).hom (0)) = 0
  rw [map_zero, map_zero]

private lemma homMap_zero_right
    {P P' Q Q' : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)} (f : P' ⟶ P) :
    SheafOfModules.homObjMap f (0 : Q ⟶ Q') = 0 := by
  apply SheafOfModules.hom_ext
  ext X φ : 3
  change (PresheafOfModules.restrictOver R.obj X.unop).map f.val ≫ φ ≫
    (PresheafOfModules.restrictOver R.obj X.unop).map 0 = 0
  ext W x
  rfl

private lemma hom_isZero_left
    {P : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)} (h : IsZero P)
    (Q : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) :
    IsZero (SheafOfModules.homObj P Q) := by
  rw [IsZero.iff_id_eq_zero, ← SheafOfModules.homObjMap_id]
  rw [h.eq_of_src (𝟙 P) 0, homMap_zero_left]

private lemma hom_isZero_right
    (P : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
    {Q : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)} (h : IsZero Q) :
    IsZero (SheafOfModules.homObj P Q) := by
  rw [IsZero.iff_id_eq_zero, ← SheafOfModules.homObjMap_id]
  rw [h.eq_of_src (𝟙 Q) 0, homMap_zero_right]

private noncomputable def dualHomBicomplex
    (E A : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ) :
    HomologicalComplex₂ (SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))ᵒᵖ
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  HomologicalComplex₂.ofGradedObject _ _
    (fun pq ↦ op (SheafOfModules.homObj (E.X pq.1) (A.X (-pq.2))))
    (fun p p' q ↦ (SheafOfModules.homObjMap (E.d p p') (𝟙 (A.X (-q)))).op)
    (fun p q q' ↦ (SheafOfModules.homObjMap (𝟙 (E.X p)) (A.d (-q') (-q))).op)
    (by
      intro p p' h q
      rw [E.shape p p' h, homMap_zero_left, op_zero])
    (by
      intro p q q' h
      rw [A.shape (-q') (-q) (by simp only [ComplexShape.up_Rel] at *; omega),
        homMap_zero_right, op_zero])
    (by
      intro p p' p'' q
      rw [← op_comp, SheafOfModules.homObjMap_comp_homObjMap,
        HomologicalComplex.d_comp_d, homMap_zero_left, op_zero])
    (by
      intro p q q' q''
      rw [← op_comp, SheafOfModules.homObjMap_comp_homObjMap,
        HomologicalComplex.d_comp_d, homMap_zero_right, op_zero])
    (by
      intro p p' q q'
      rw [← op_comp, ← op_comp, SheafOfModules.homObjMap_comp_homObjMap,
        SheafOfModules.homObjMap_comp_homObjMap]
      simp)

end Helpers

/-- Exact internal-Hom columns imply exactness of the total Hom when its diagonals
are finite. The hypothesis concerns only the differentials of the second complex;
no freeness or acyclicity hypothesis is imposed on either input.
Source: Stacks Project, cohomology.tex, Tag 0GM8, case (2), descending Hom calculation.
(blueprint: lem-sc-bounded-hom-exact-columns)

Proof: form the commuting bicomplex in opposite module sheaves with term
op Hom(E^p,A^(-q)). Its horizontal differential is opposite precomposition by d_E,
and its vertical differential is opposite postcomposition by d_A. The two bounds
become upper bounds N and -M. Internal Hom with a zero source or target is zero,
so the finite-diagonal total exists. Each column short complex is the opposite
of the assumed exact Hom column, hence each column is acyclic. Compare the zero
bicomplex with this bicomplex using the already proved bounded-above columnwise
total quasi-isomorphism theorem: its total is acyclic. Finally the signed product
comparison identifies the Hom short complex at n with the unop total short
complex at -n. Exactness transports through unop and this isomorphism. This
argument includes empty diagonals and preserves the original universes. -/
theorem acyclic_homComplex_of_bounded_exact_columns
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify J AddCommGrpCat.{max u v w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    {R : Sheaf J CommRingCat.{w}}
    (E A : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ)
    (N M : ℤ)
    (hE : ∀ p : ℤ, N < p → IsZero (E.X p))
    (hA : ∀ q : ℤ, q < M → IsZero (A.X q))
    (hcolumns : ∀ p q : ℤ,
      ∃ hz : SheafOfModules.homObjMap (𝟙 (E.X p)) (A.sc q).f ≫
          SheafOfModules.homObjMap (𝟙 (E.X p)) (A.sc q).g = 0,
        (ShortComplex.mk (SheafOfModules.homObjMap (𝟙 (E.X p)) (A.sc q).f)
          (SheafOfModules.homObjMap (𝟙 (E.X p)) (A.sc q).g) hz).Exact) :
    (CategoryTheory.homComplex E A).Acyclic := by
  have (X : C) : PreservesColimitsOfShape (J.Cover X)ᵒᵖ
      (forget AddCommGrpCat.{max u v w}) := by
    have : IsFiltered (SmallModel.{max u v w} (J.Cover X)ᵒᵖ) :=
      IsFiltered.of_equivalence (equivSmallModel.{max u v w} (J.Cover X)ᵒᵖ)
    exact preservesColimitsOfShape_of_equiv
      (equivSmallModel.{max u v w} (J.Cover X)ᵒᵖ).symm _
  have sheafify : HasSheafify J AddCommGrpCat.{max u v w} :=
    HasSheafify.mk' J AddCommGrpCat.{max u v w}
      (plusPlusAdjunction J AddCommGrpCat.{max u v w})
  let sheafAbelian : Abelian (SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) := inferInstance
  let oppositeAbelian : Abelian (SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))ᵒᵖ := inferInstance
  have homologyCategory : CategoryWithHomology (SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))ᵒᵖ := inferInstance
  let K := dualHomBicomplex E A
  have htop : IsStrictlyLE K N := by
    rw [isStrictlyLE_iff]
    intro p hp
    rw [IsZero.iff_id_eq_zero]
    ext q : 1
    exact (hom_isZero_left (hE p hp) (A.X (-q))).op.eq_of_src _ _
  have hright (p : ℤ) : IsStrictlyLE (K.X p) (-M) := by
    rw [isStrictlyLE_iff]
    intro q hq
    exact (hom_isZero_right (E.X p) (hA (-q) (by omega))).op
  have totalK : K.HasTotal (ComplexShape.up ℤ) := K.hasTotal_of_isStrictlyLE N (-M)
  have hcol (p : ℤ) : (K.X p).Acyclic := by
    intro q
    rw [HomologicalComplex.exactAt_iff' _ (q - 1) q (q + 1) (by simp) (by simp)]
    obtain ⟨hz, hex⟩ := hcolumns p (-q)
    have he := hex.op
    convert he using 1
    simp [K, dualHomBicomplex, HomologicalComplex.sc', HomologicalComplex.sc,
      HomologicalComplex.shortComplexFunctor, HomologicalComplex.shortComplexFunctor',
      ShortComplex.op, show -(q - 1) = -q + 1 by omega,
      show -(q + 1) = -q - 1 by omega]
    constructor <;> congr 3 <;> simp <;> omega
  have zeroObject : HasZeroObject (SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) :=
    hasZeroObject_of_hasTerminal_object
  let Z : HomologicalComplex₂ (SheafOfModules.{max u v w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R))ᵒᵖ
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) := HasZeroObject.zero.choose
  have boundZ : IsStrictlyLE Z N := by
    rw [isStrictlyLE_iff]
    intro p hp
    exact (HomologicalComplex.eval _ _ p).map_isZero (isZero_zero _)
  have (p : ℤ) : IsStrictlyLE (Z.X p) (-M) := by
    rw [isStrictlyLE_iff]
    intro q hq
    exact (HomologicalComplex.eval _ _ q).map_isZero
      ((HomologicalComplex.eval _ _ p).map_isZero (isZero_zero _))
  have totalZ : Z.HasTotal (ComplexShape.up ℤ) := Z.hasTotal_of_isStrictlyLE N (-M)
  let f : Z ⟶ K := 0
  have hf (p : ℤ) : QuasiIso (f.f p) := by
    rw [quasiIso_iff]
    intro q
    apply (quasiIsoAt_iff_exactAt (f.f p) q ?_).2 (hcol p q)
    exact HomologicalComplex.acyclic_of_isZero (Z.X p)
      ((HomologicalComplex.eval _ _ p).map_isZero (isZero_zero _)) q
  have totalComparison : QuasiIso (HomologicalComplex₂.total.map f (ComplexShape.up ℤ)) :=
    HomologicalComplex₂.total.quasiIso_map_of_isStrictlyGE_of_isStrictlyLE
      (K := Z) (L := K) f N (-M) hf
  have hz : (Z.total (ComplexShape.up ℤ)).Acyclic :=
    HomologicalComplex.acyclic_of_isZero _
      (HomologicalComplex₂.total.isZero Z (ComplexShape.up ℤ) (isZero_zero _))
  intro n
  obtain ⟨e⟩ := homComplex_sc_iso_dual_total E A K
    (fun _ _ ↦ Iso.refl _) (by intros; simp [K, dualHomBicomplex])
    (by intros; simp [K, dualHomBicomplex]) n
  rw [HomologicalComplex.exactAt_iff, ShortComplex.exact_iff_of_iso e]
  have ht := (quasiIsoAt_iff_exactAt
    (HomologicalComplex₂.total.map f (ComplexShape.up ℤ)) (-n) (hz (-n))).1 inferInstance
  exact ht.unop

end CochainComplex
