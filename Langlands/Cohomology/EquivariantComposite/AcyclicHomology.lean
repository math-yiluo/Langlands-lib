import Langlands.Cohomology.EquivariantComposite.KInjectiveHomology
import Langlands.Cohomology.AcyclicTermsDerivedUnitProof

/-! # Derived Hom from a single object on complexes of Hom-acyclic terms -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Localization Opposite
open CochainComplex HomComplex

namespace Langlands.Cohomology.EquivariantComposite

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- The canonical additive localization map on arbitrary cohomology classes. -/
def classDerivedMap (K L : CochainComplex C ℤ) (n : ℤ) :
    CohomologyClass K L n →+ ShiftedHom (DerivedCategory.Q.obj K)
      (DerivedCategory.Q.obj L) n := by
  letI : HasSmallLocalizedShiftedHom.{w}
      (HomologicalComplex.quasiIso C (.up ℤ)) ℤ K L :=
    (hasSmallLocalizedShiftedHom_iff _ ℤ DerivedCategory.Q K L).2 (fun _ _ => inferInstance)
  refine AddMonoidHom.mk' (fun x => SmallShiftedHom.equiv _ DerivedCategory.Q
    (CohomologyClass.toSmallShiftedHom x)) ?_
  intro x y
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨y, rfl⟩ := y.mk_surjective
  simp only [← CohomologyClass.mk_add, CohomologyClass.equiv_toSmallShiftedHom_mk,
    map_add, ShiftedHom.map_add]

/-- On a cocycle the map localizes its shifted chain map. -/
lemma classDerivedMap_mk (K L : CochainComplex C ℤ) (n : ℤ) (z : Cocycle K L n) :
    classDerivedMap K L n (CohomologyClass.mk z) =
      ShiftedHom.map (Cocycle.equivHomShift.symm z) DerivedCategory.Q := by
  simp [classDerivedMap]

/-- K-injectivity makes the canonical class map bijective. -/
lemma classDerivedMap_eq (K L : CochainComplex C ℤ) [L.IsKInjective] (n : ℤ) :
    (classDerivedMap K L n : CohomologyClass K L n → _) = classDerivedAddEquiv K L n := rfl

/-- Cohomology of termwise Hom canonically maps to derived morphisms. -/
def homologyDerivedMap (X : C) (L : CochainComplex C ℤ) (n : ℤ) :
    (((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (.up ℤ)).obj L).homology n →+
      ShiftedHom ((DerivedCategory.singleFunctor C 0).obj X) (DerivedCategory.Q.obj L) n where
  toFun x := ((DerivedCategory.singleFunctorIsoCompQ C 0).app X).hom ≫
    classDerivedMap _ L n (ExtRightDerived.coyonedaHomologyAddEquiv X L n x)
  map_zero' := by simp
  map_add' x y := by simp [map_add, CategoryTheory.Preadditive.comp_add]

/-- The canonical map is the published equivalence when the target is K-injective. -/
lemma homologyDerivedMap_eq (X : C) (L : CochainComplex C ℤ) [L.IsKInjective] (n : ℤ) :
    (homologyDerivedMap X L n : _ → _) = homologyDerivedAddEquiv X L n := rfl

/-- The canonical map is natural for every chain map. -/
lemma homologyDerivedMap_naturality (X : C) {K L : CochainComplex C ℤ}
    (f : K ⟶ L) (n : ℤ)
    (x : (((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (.up ℤ)).obj K).homology n) :
    homologyDerivedMap X L n
        (HomologicalComplex.homologyMap
          (((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (.up ℤ)).map f) n x) =
      homologyDerivedMap X K n x ≫ (DerivedCategory.Q.map f)⟦n⟧' := by
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
  change homologyDerivedMap X L n
    ((A.homologyπ n ≫ HomologicalComplex.homologyMap g n) c) = _
  erw [HomologicalComplex.homologyπ_naturality]
  change ((DerivedCategory.singleFunctorIsoCompQ C 0).app X).hom ≫
      classDerivedMap _ L n (ExtRightDerived.coyonedaHomologyAddEquiv X L n
        (B.homologyπ n (HomologicalComplex.cyclesMap g n c))) =
    (((DerivedCategory.singleFunctorIsoCompQ C 0).app X).hom ≫
      classDerivedMap _ K n (ExtRightDerived.coyonedaHomologyAddEquiv X K n
        (A.homologyπ n c))) ≫ _
  erw [ExtRightDerived.coyonedaHomologyAddEquiv_homologyπ,
    ExtRightDerived.coyonedaHomologyAddEquiv_homologyπ, h,
    classDerivedMap_mk, classDerivedMap_mk,
    Cocycle.equivHomShift_symm_postcomp]
  change _ ≫ (DerivedCategory.Q.map (_ ≫ f⟦n⟧') ≫ _) =
    (_ ≫ (DerivedCategory.Q.map _ ≫ _)) ≫ _
  simp only [Functor.map_comp, Category.assoc]
  congr 1
  congr 1
  exact (DerivedCategory.Q.commShiftIso n).hom.naturality f


variable [EnoughInjectives C]

/-- On bounded below complexes of Hom-acyclic terms the canonical map is bijective. -/
theorem homologyDerivedMap_bijective (X : C) (K : CochainComplex.Plus C)
    (hK : ∀ (i : ℤ) (q : ℕ), IsZero
      (((preadditiveCoyoneda.obj (op X)).rightDerived (q + 1)).obj (K.obj.X i)))
    (n : ℤ) : Function.Bijective (homologyDerivedMap X K.obj n) := by
  let := HasDerivedCategory.standard AddCommGrpCat.{v}
  let P := preadditiveCoyoneda.obj (op X)
  have : PreservesFiniteLimits P := by
    have : PreservesFiniteLimits (P ⋙ forget AddCommGrpCat.{v}) :=
      inferInstanceAs (PreservesFiniteLimits (coyoneda.obj (op X)))
    exact preservesFiniteLimits_of_reflects_of_preserves P (forget AddCommGrpCat.{v})
  obtain ⟨m, hm⟩ := K.property
  obtain ⟨L, hL, i, hi⟩ := CochainComplex.Plus.exists_quasiIso_injective K m
  have : QuasiIso i.hom := hi
  let L' := (InjectiveObject.ι C).mapCochainComplexPlus.obj L
  have hinj (j : ℤ) : Injective (L'.obj.X j) := (L.obj.X j).property
  have : L'.obj.IsKInjective := inferInstanceAs (CochainComplex.IsKInjective
    (((InjectiveObject.ι C).mapHomologicalComplex (.up ℤ)).obj L.obj))
  have hacyclic : ∀ (j : ℤ) (q : ℕ), IsZero ((P.rightDerived (q + 1)).obj (L'.obj.X j)) :=
    fun j q => P.isZero_rightDerived_obj_injective_succ q _
  have : QuasiIso ((P.mapHomologicalComplex (.up ℤ)).map i.hom) :=
    AcyclicComparison.quasiIso_map_of_acyclic_terms P i hK hacyclic
  let a := HomologicalComplex.homologyMap
    ((P.mapHomologicalComplex (.up ℤ)).map i.hom) n
  have : IsIso a := by dsimp [a]; infer_instance
  have ha : Function.Bijective a := (asIso a).addCommGroupIsoToAddEquiv.bijective
  have : IsIso (DerivedCategory.Q.map i.hom) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (C := C) i.hom).2 hi
  let e := (CategoryTheory.shiftFunctor (DerivedCategory C) n).mapIso (asIso (DerivedCategory.Q.map i.hom))
  let post : ShiftedHom ((DerivedCategory.singleFunctor C 0).obj X)
      (DerivedCategory.Q.obj K.obj) n ≃+
      ShiftedHom ((DerivedCategory.singleFunctor C 0).obj X) (DerivedCategory.Q.obj L'.obj) n :=
    { toEquiv := e.homToEquiv
      map_add' x y := CategoryTheory.Preadditive.add_comp _ _ _ _ _ _ }
  have hcomp : (post ∘ homologyDerivedMap X K.obj n) =
      (homologyDerivedMap X L'.obj n ∘ a) := by
    funext x
    exact (homologyDerivedMap_naturality X i.hom n x).symm
  apply (post.bijective.of_comp_iff' (homologyDerivedMap X K.obj n)).1
  rw [hcomp, homologyDerivedMap_eq]
  exact (homologyDerivedAddEquiv X L'.obj n).bijective.comp ha

/-- Homology of termwise Hom computes derived Hom for bounded below Hom-acyclic terms. -/
def acyclicHomologyDerivedAddEquiv (X : C) (K : CochainComplex.Plus C)
    (hK : ∀ (i : ℤ) (q : ℕ), IsZero
      (((preadditiveCoyoneda.obj (op X)).rightDerived (q + 1)).obj (K.obj.X i))) (n : ℤ) :
    (((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (.up ℤ)).obj K.obj).homology n ≃+
      ShiftedHom ((DerivedCategory.singleFunctor C 0).obj X) (DerivedCategory.Q.obj K.obj) n :=
  AddEquiv.ofBijective (homologyDerivedMap X K.obj n) (homologyDerivedMap_bijective X K hK n)

/-- The acyclic-term equivalence is natural in its target complex. -/
theorem acyclicHomologyDerivedAddEquiv_naturality (X : C)
    {K L : CochainComplex.Plus C} (f : K ⟶ L)
    (hK : ∀ (i : ℤ) (q : ℕ), IsZero
      (((preadditiveCoyoneda.obj (op X)).rightDerived (q + 1)).obj (K.obj.X i)))
    (hL : ∀ (i : ℤ) (q : ℕ), IsZero
      (((preadditiveCoyoneda.obj (op X)).rightDerived (q + 1)).obj (L.obj.X i)))
    (n : ℤ) (x : (((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (.up ℤ)).obj
      K.obj).homology n) :
    acyclicHomologyDerivedAddEquiv X L hL n
        (HomologicalComplex.homologyMap
          (((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (.up ℤ)).map f.hom) n x) =
      acyclicHomologyDerivedAddEquiv X K hK n x ≫ (DerivedCategory.Q.map f.hom)⟦n⟧' :=
  homologyDerivedMap_naturality X f.hom n x

end Langlands.Cohomology.EquivariantComposite
