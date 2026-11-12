import Langlands.Cohomology.ExtRightDerivedNaturality
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # Hom-complex cohomology and derived morphisms into K-injectives -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Localization Opposite
open CochainComplex HomComplex

namespace Langlands.Cohomology.EquivariantComposite

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- Cohomology classes into a K-injective complex are additive derived morphisms. -/
def classDerivedAddEquiv (K L : CochainComplex C ℤ) [L.IsKInjective] (n : ℤ) :
    CohomologyClass K L n ≃+ ShiftedHom (DerivedCategory.Q.obj K)
      (DerivedCategory.Q.obj L) n := by
  letI : HasSmallLocalizedShiftedHom.{w}
      (HomologicalComplex.quasiIso C (.up ℤ)) ℤ K L :=
    (hasSmallLocalizedShiftedHom_iff _ ℤ DerivedCategory.Q K L).2 (fun _ _ => inferInstance)
  refine
    { toEquiv := (CohomologyClass.equivOfIsKInjective (K := K) (L := L) (n := n)).trans
        (SmallShiftedHom.equiv _ DerivedCategory.Q)
      map_add' := ?_ }
  intro x y
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨y, rfl⟩ := y.mk_surjective
  change SmallShiftedHom.equiv _ DerivedCategory.Q
      (CohomologyClass.equivOfIsKInjective (CohomologyClass.mk x + CohomologyClass.mk y)) =
    SmallShiftedHom.equiv _ DerivedCategory.Q
      (CohomologyClass.equivOfIsKInjective (CohomologyClass.mk x)) +
    SmallShiftedHom.equiv _ DerivedCategory.Q
      (CohomologyClass.equivOfIsKInjective (CohomologyClass.mk y))
  simp only [CohomologyClass.equivOfIsKInjective_apply,
    ← CohomologyClass.mk_add, CohomologyClass.equiv_toSmallShiftedHom_mk,
    map_add, ShiftedHom.map_add]

/-- On a cocycle class the comparison is localization of its shifted chain map. -/
lemma classDerivedAddEquiv_mk (K L : CochainComplex C ℤ) [L.IsKInjective] (n : ℤ)
    (z : Cocycle K L n) :
    classDerivedAddEquiv K L n (CohomologyClass.mk z) =
      ShiftedHom.map (Cocycle.equivHomShift.symm z) DerivedCategory.Q := by
  simp [classDerivedAddEquiv, CohomologyClass.equivOfIsKInjective_apply]

/-- Homology of termwise Hom into a K-injective complex computes derived morphisms. -/
def homologyDerivedAddEquiv (X : C) (L : CochainComplex C ℤ) [L.IsKInjective] (n : ℤ) :
    (((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (.up ℤ)).obj L).homology n ≃+
      ShiftedHom ((DerivedCategory.singleFunctor C 0).obj X) (DerivedCategory.Q.obj L) n :=
  (ExtRightDerived.coyonedaHomologyAddEquiv X L n).trans
    ((classDerivedAddEquiv ((CochainComplex.singleFunctor C 0).obj X) L n).trans
      { toEquiv := ((DerivedCategory.singleFunctorIsoCompQ C 0).app X).symm.homFromEquiv
        map_add' := fun _ _ => CategoryTheory.Preadditive.comp_add _ _ _ _ _ _ })

/-- The comparison with derived morphisms is natural in the K-injective complex. -/
lemma homologyDerivedAddEquiv_naturality (X : C)
    {K L : CochainComplex C ℤ} [K.IsKInjective] [L.IsKInjective]
    (f : K ⟶ L) (n : ℤ)
    (x : (((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (.up ℤ)).obj K).homology n) :
    homologyDerivedAddEquiv X L n
        (HomologicalComplex.homologyMap
          (((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (.up ℤ)).map f) n x) =
      homologyDerivedAddEquiv X K n x ≫ (DerivedCategory.Q.map f)⟦n⟧' := by
  let P := preadditiveCoyoneda.obj (op X)
  let A := (P.mapHomologicalComplex (.up ℤ)).obj K
  let B := (P.mapHomologicalComplex (.up ℤ)).obj L
  let g := (P.mapHomologicalComplex (.up ℤ)).map f
  obtain ⟨c, rfl⟩ := (AddCommGrpCat.epi_iff_surjective (A.homologyπ n)).1 inferInstance x
  have h :
      (HomComplex.leftHomologyData ((singleFunctor C 0).obj X) L n).cyclesIso.hom
        (HomologicalComplex.cyclesMap (ExtRightDerived.coyonedaHomComplexIso X L).hom n
          (HomologicalComplex.cyclesMap g n c)) =
      ((HomComplex.leftHomologyData ((singleFunctor C 0).obj X) K n).cyclesIso.hom
        (HomologicalComplex.cyclesMap (ExtRightDerived.coyonedaHomComplexIso X K).hom n c)).postcomp f := by
    apply Subtype.ext
    change _ = (((HomComplex.leftHomologyData ((singleFunctor C 0).obj X) K n).cyclesIso.hom
      (HomologicalComplex.cyclesMap (ExtRightDerived.coyonedaHomComplexIso X K).hom n c)).1).comp
        (Cochain.ofHom f) (add_zero n)
    erw [ExtRightDerived.coyonedaHomComplex_cycles_coe,
      ExtRightDerived.coyonedaHomComplex_cycles_coe]
    change Cochain.fromSingleMk (B.iCycles n (HomologicalComplex.cyclesMap g n c))
      (zero_add n) = (Cochain.fromSingleMk (A.iCycles n c) (zero_add n)).comp
        (Cochain.ofHom f) (add_zero n)
    rw [← Cochain.fromSingleMk_postcomp]
    congr 1
    exact ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i g n) c
  change homologyDerivedAddEquiv X L n
    ((A.homologyπ n ≫ HomologicalComplex.homologyMap g n) c) = _
  erw [HomologicalComplex.homologyπ_naturality]
  change ((DerivedCategory.singleFunctorIsoCompQ C 0).app X).hom ≫
      classDerivedAddEquiv _ L n (ExtRightDerived.coyonedaHomologyAddEquiv X L n
        (B.homologyπ n (HomologicalComplex.cyclesMap g n c))) =
    (((DerivedCategory.singleFunctorIsoCompQ C 0).app X).hom ≫
      classDerivedAddEquiv _ K n (ExtRightDerived.coyonedaHomologyAddEquiv X K n
        (A.homologyπ n c))) ≫ _
  erw [ExtRightDerived.coyonedaHomologyAddEquiv_homologyπ,
    ExtRightDerived.coyonedaHomologyAddEquiv_homologyπ, h,
    classDerivedAddEquiv_mk, classDerivedAddEquiv_mk,
    Cocycle.equivHomShift_symm_postcomp]
  change _ ≫ (DerivedCategory.Q.map (_ ≫ f⟦n⟧') ≫ _) =
    (_ ≫ (DerivedCategory.Q.map _ ≫ _)) ≫ _
  simp only [Functor.map_comp, Category.assoc]
  congr 1
  congr 1
  exact (DerivedCategory.Q.commShiftIso n).hom.naturality f

end Langlands.Cohomology.EquivariantComposite
