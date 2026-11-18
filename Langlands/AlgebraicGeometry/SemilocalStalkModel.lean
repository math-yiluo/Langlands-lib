import Langlands.AlgebraicGeometry.AffineStalkModelNeighbourhood

/-! # Affine stalk models from semilocal localization data -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry

section FractionField

variable {A : Type u} [CommRing A] [IsDomain A]
  {X : Scheme.{u}} [IsIntegral X] [Algebra A X.functionField]
  [IsFractionRing A X.functionField]

local instance : Algebra A (Spec (CommRingCat.of A)).functionField :=
  (StructureSheaf.toStalk (CommRingCat.of A)
    (genericPoint (Spec (CommRingCat.of A)))).hom.toAlgebra

local instance : IsFractionRing A (Spec (CommRingCat.of A)).functionField :=
  functionField_isFractionRing_of_affine (CommRingCat.of A)

/-- Compare the function field of the affine model with the function field
of the integral scheme. -/
def affineModelFieldEquiv :
    (Spec (CommRingCat.of A)).functionField ≃ₐ[A] X.functionField :=
  IsLocalization.algEquiv (nonZeroDivisors A)
    (Spec (CommRingCat.of A)).functionField X.functionField

set_option backward.isDefEq.respectTransparency false in
theorem affineModelFieldEquiv_specMap :
    Spec.map (CommRingCat.ofHom (affineModelFieldEquiv (A := A) (X := X)).symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A X.functionField)) =
      (Spec (CommRingCat.of A)).fromSpecStalk
        (genericPoint (Spec (CommRingCat.of A))) := by
  rw [← Spec.map_comp, Spec.fromSpecStalk_eq']
  congr 1
  ext a
  exact (affineModelFieldEquiv (A := A) (X := X)).symm.commutes a

/-- The generic map from the function field of the affine model into `X`. -/
def affineModelGenericMap :
    Spec (Spec (CommRingCat.of A)).functionField ⟶ X :=
  Spec.map (CommRingCat.ofHom (affineModelFieldEquiv (A := A) (X := X)).symm.toRingHom) ≫
    X.fromSpecStalk (genericPoint X)

set_option backward.isDefEq.respectTransparency false in
theorem affineModelGenericMap_over
    {R : Type u} [CommRing R] [Algebra R A]
    (p : X ⟶ Spec (CommRingCat.of R))
    (hbase : Spec.map (CommRingCat.ofHom (algebraMap A X.functionField)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      X.fromSpecStalk (genericPoint X) ≫ p) :
    affineModelGenericMap (A := A) (X := X) ≫ p =
      (Spec (CommRingCat.of A)).fromSpecStalk
          (genericPoint (Spec (CommRingCat.of A))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  dsimp only [affineModelGenericMap]
  rw [Category.assoc, ← hbase, ← Category.assoc, affineModelFieldEquiv_specMap]

set_option backward.isDefEq.respectTransparency false in
omit [IsDomain A] [IsFractionRing A X.functionField] in
/-- A compatible map from the affine model to a stalk is automatically a
map over the original affine base. -/
theorem specMap_stalk_over_of_field_compatibility
    [X.IsSeparated] {R : Type u} [CommRing R] [Algebra R A]
    (p : X ⟶ Spec (CommRingCat.of R))
    (hbase : Spec.map (CommRingCat.ofHom (algebraMap A X.functionField)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      X.fromSpecStalk (genericPoint X) ≫ p)
    (x : X) (κ : A →+* X.presheaf.stalk x)
    (hκ : (algebraMap (X.presheaf.stalk x) X.functionField).comp κ =
      algebraMap A X.functionField) :
    Spec.map (CommRingCat.ofHom κ) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      X.fromSpecStalk x ≫ p := by
  let j := Spec.map (CommRingCat.ofHom
    (algebraMap (X.presheaf.stalk x) X.functionField))
  have : IsDominant j := isDominant_specMap_of_injective _
    (IsFractionRing.injective (X.presheaf.stalk x) X.functionField)
  have hjκ : j ≫ Spec.map (CommRingCat.ofHom κ) =
      Spec.map (CommRingCat.ofHom (algebraMap A X.functionField)) := by
    dsimp only [j]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hκ]
  have hjx : j ≫ X.fromSpecStalk x = X.fromSpecStalk (genericPoint X) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes x)
  apply ext_of_isDominant j
  rw [← Category.assoc, hjκ, hbase, ← hjx, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- A stalk realizing the localization at a maximal ideal of the model
extends the generic map to that maximal stalk of the affine scheme. -/
theorem exists_affineModel_stalk_extension
    [X.IsSeparated] {R : Type u} [CommRing R] [Algebra R A]
    (p : X ⟶ Spec (CommRingCat.of R))
    (hbase : Spec.map (CommRingCat.ofHom (algebraMap A X.functionField)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      X.fromSpecStalk (genericPoint X) ≫ p)
    (m : PrimeSpectrum A) (x : X) (κ : A →+* X.presheaf.stalk x)
    (hκ : (algebraMap (X.presheaf.stalk x) X.functionField).comp κ =
      algebraMap A X.functionField)
    (hloc : letI := κ.toAlgebra;
      IsLocalization.AtPrime (X.presheaf.stalk x) m.asIdeal) :
    ∃ φ : Spec ((Spec (CommRingCat.of A)).presheaf.stalk m) ⟶ X,
      φ ≫ p = (Spec (CommRingCat.of A)).fromSpecStalk m ≫
          Spec.map (CommRingCat.ofHom (algebraMap R A)) ∧
      Spec.map ((Spec (CommRingCat.of A)).presheaf.stalkSpecializes
          (genericPoint_specializes m)) ≫ φ =
        affineModelGenericMap (A := A) (X := X) := by
  let := κ.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk x) m.asIdeal := hloc
  let Y := Spec (CommRingCat.of A)
  let B := Y.presheaf.stalk m
  let : Algebra A B := (StructureSheaf.toStalk (CommRingCat.of A) m).hom.toAlgebra
  have : IsLocalization.AtPrime B m.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (CommRingCat.of A) m
  let e : B ≃ₐ[A] X.presheaf.stalk x :=
    IsLocalization.algEquiv m.asIdeal.primeCompl B (X.presheaf.stalk x)
  let ψ := Spec.map (CommRingCat.ofHom e.symm.toRingHom)
  let φ := ψ ≫ X.fromSpecStalk x
  have he : ψ ≫ Spec.map (CommRingCat.ofHom κ) = Y.fromSpecStalk m := by
    dsimp only [ψ]
    rw [← Spec.map_comp, Spec.fromSpecStalk_eq']
    congr 1
    ext a
    exact e.symm.commutes a
  refine ⟨φ, ?_, ?_⟩
  · dsimp only [φ]
    rw [Category.assoc, ← specMap_stalk_over_of_field_compatibility p hbase x κ hκ,
      ← Category.assoc, he]
  · let σ := (Y.presheaf.stalkSpecializes (genericPoint_specializes m)).hom
    let c := affineModelFieldEquiv (A := A) (X := X)
    have hσ : σ.comp (algebraMap A B) =
        algebraMap A Y.functionField := by
      exact congrArg CommRingCat.Hom.hom
        (StructureSheaf.toStalk_stalkSpecializes (genericPoint_specializes m))
    have hc : c.toRingHom.comp σ =
        (algebraMap (X.presheaf.stalk x) X.functionField).comp e.toRingHom := by
      apply IsLocalization.ringHom_ext m.asIdeal.primeCompl
      ext a
      change c (σ (algebraMap A B a)) =
        algebraMap (X.presheaf.stalk x) X.functionField (e (algebraMap A B a))
      rw [show σ (algebraMap A B a) = algebraMap A Y.functionField a from
        congrArg (fun k : A →+* Y.functionField ↦ k a) hσ, c.commutes, e.commutes]
      exact (congrArg (fun k : A →+* X.functionField ↦ k a) hκ).symm
    have hc' : c.toRingHom.comp (σ.comp e.symm.toRingHom) =
        algebraMap (X.presheaf.stalk x) X.functionField := by
      ext a
      change c (σ (e.symm a)) = algebraMap (X.presheaf.stalk x) X.functionField a
      exact (congrArg (fun k : B →+* X.functionField ↦ k (e.symm a)) hc).trans
        (congrArg (algebraMap (X.presheaf.stalk x) X.functionField) (e.apply_symm_apply a))
    let t := Spec.map (CommRingCat.ofHom c.toRingHom)
    have : IsDominant t := isDominant_specMap_of_injective _ c.injective
    apply ext_of_isDominant t
    have ht : t ≫ Spec.map (CommRingCat.ofHom c.symm.toRingHom) = 𝟙 _ := by
      rw [← Spec.map_comp]
      convert Spec.map_id X.functionField using 2
      ext a
      exact c.apply_symm_apply a
    dsimp only [φ, ψ, affineModelGenericMap]
    change t ≫ Spec.map (CommRingCat.ofHom σ) ≫
        Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ X.fromSpecStalk x =
      t ≫ Spec.map (CommRingCat.ofHom c.symm.toRingHom) ≫
        X.fromSpecStalk (genericPoint X)
    have hc'' : (c.toRingHom.comp σ).comp e.symm.toRingHom =
        algebraMap (X.presheaf.stalk x) X.functionField := hc'
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
      ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    rw [hc'']
    rw [← Category.assoc, ht, Category.id_comp]
    exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes x)

/-- Globalization of an everywhere defined rational map retains its generic
restriction. -/
theorem rationalMapToHomOfDomainEqTop_generic
    {Y Z : Scheme.{u}} [IsIntegral Y] [Z.IsSeparated]
    (r : Y.RationalMap Z) (h : r.domain = ⊤) :
    Y.fromSpecStalk (genericPoint Y) ≫ rationalMapToHomOfDomainEqTop r h =
      r.fromFunctionField := by
  let q := r.toPartialMap
  have hη : genericPoint Y ∈ q.domain :=
    (genericPoint_specializes _).mem_open q.domain.isOpen
      q.dense_domain.nonempty.choose_spec
  have hf : q.domain.ι ≫ rationalMapToHomOfDomainEqTop r h = q.hom :=
    rationalMapToHomOfDomainEqTop_fac r h
  calc
    Y.fromSpecStalk (genericPoint Y) ≫ rationalMapToHomOfDomainEqTop r h =
        q.domain.fromSpecStalkOfMem (genericPoint Y) hη ≫
          q.domain.ι ≫ rationalMapToHomOfDomainEqTop r h := by
      rw [← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
    _ = q.fromFunctionField := by rw [hf]; rfl
    _ = r.fromFunctionField :=
      congrArg Scheme.RationalMap.fromFunctionField r.toRationalMap_toPartialMap

set_option backward.isDefEq.respectTransparency false in
/-- Compatible stalk localizations at every maximal ideal construct an
actual affine stalk model, rather than assuming its morphism to `X`. -/
def affineStalkModelOfLocalizations
    [X.IsSeparated] {R : Type u} [CommRing R] [Algebra R A]
    (p : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType p]
    (hbase : Spec.map (CommRingCat.ofHom (algebraMap A X.functionField)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      X.fromSpecStalk (genericPoint X) ≫ p)
    (E : Set X) (κ : ∀ x, x ∈ E → A →+* X.presheaf.stalk x)
    (hκ : ∀ x hx, (algebraMap (X.presheaf.stalk x) X.functionField).comp (κ x hx) =
      algebraMap A X.functionField)
    (hloc : ∀ m : PrimeSpectrum A, m.asIdeal.IsMaximal →
      ∃ x, ∃ hx : x ∈ E, letI := (κ x hx).toAlgebra;
        IsLocalization.AtPrime (X.presheaf.stalk x) m.asIdeal) :
    AffineStalkModel p E := by
  let Y := Spec (CommRingCat.of A)
  let t : Y ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R A))
  letI : Y.Over (Spec (CommRingCat.of R)) := ⟨t⟩
  letI : X.Over (Spec (CommRingCat.of R)) := ⟨p⟩
  let a := affineModelGenericMap (A := A) (X := X)
  have ha : a ≫ p = Y.fromSpecStalk (genericPoint Y) ≫ t :=
    affineModelGenericMap_over p hbase
  let r := Scheme.RationalMap.ofFunctionField t p a ha
  have hr : r.fromFunctionField = a :=
    Scheme.RationalMap.fromFunctionField_ofFunctionField t p a ha
  have hclosed : ∀ m : PrimeSpectrum A, m.asIdeal.IsMaximal →
      ∃ φ : Spec (Y.presheaf.stalk m) ⟶ X,
        φ ≫ p = Y.fromSpecStalk m ≫ t ∧
        Spec.map (Y.presheaf.stalkSpecializes (genericPoint_specializes m)) ≫ φ =
          r.fromFunctionField := by
    intro m hm
    obtain ⟨x, hx, hxloc⟩ := hloc m hm
    obtain ⟨φ, hφ, hη⟩ :=
      exists_affineModel_stalk_extension p hbase m x (κ x hx) (hκ x hx) hxloc
    exact ⟨φ, hφ, hη.trans hr.symm⟩
  have htop : r.domain = ⊤ :=
    rationalMap_domain_eq_top_of_closed_stalk_extensions t p r hclosed
  let f := rationalMapToHomOfDomainEqTop r htop
  have hrover : r.IsOver (Spec (CommRingCat.of R)) := by
    have : (Scheme.PartialMap.ofFromSpecStalk t p a ha).IsOver
        (Spec (CommRingCat.of R)) :=
      ⟨Scheme.PartialMap.ofFromSpecStalk_comp t p a ha⟩
    change (Scheme.PartialMap.ofFromSpecStalk t p a ha).toRationalMap.IsOver _
    infer_instance
  have hfover : f ≫ p = t := by
    have := hrover
    apply rationalMapToHomOfDomainEqTop_comp r htop t p
    exact (Scheme.Hom.isOver_iff (Spec (CommRingCat.of R))).mp
      (inferInstance : r.toPartialMap.hom.IsOver (Spec (CommRingCat.of R)))
  let j := Spec.map (CommRingCat.ofHom (algebraMap A X.functionField))
  have hj : IsDominant j :=
    isDominant_specMap_of_injective _ (IsFractionRing.injective A X.functionField)
  let c := affineModelFieldEquiv (A := A) (X := X)
  have hc : Spec.map (CommRingCat.ofHom c.toRingHom) ≫
      Y.fromSpecStalk (genericPoint Y) = j := by
    rw [Spec.fromSpecStalk_eq', ← Spec.map_comp]
    congr 1
    ext z
    exact c.commutes z
  have hcinv : Spec.map (CommRingCat.ofHom c.toRingHom) ≫
      Spec.map (CommRingCat.ofHom c.symm.toRingHom) = 𝟙 _ := by
    rw [← Spec.map_comp]
    convert Spec.map_id X.functionField using 2
    ext z
    exact c.apply_symm_apply z
  have hjf : j ≫ f = X.fromSpecStalk (genericPoint X) := by
    rw [← hc, Category.assoc, rationalMapToHomOfDomainEqTop_generic, hr]
    change Spec.map (CommRingCat.ofHom c.toRingHom) ≫
      Spec.map (CommRingCat.ofHom c.symm.toRingHom) ≫ X.fromSpecStalk (genericPoint X) = _
    rw [← Category.assoc, hcinv, Category.id_comp]
  exact
    { ring := CommRingCat.of A
      algebra := inferInstance
      domain := inferInstance
      hom := f
      over_base := hfover
      generic := j
      dominant_generic := hj
      generic_hom := hjf
      local_maps := fun x hx ↦
        ⟨Spec.map (CommRingCat.ofHom (κ x hx)),
          specMap_stalk_over_of_field_compatibility p hbase x (κ x hx) (hκ x hx),
          by
            have hm : CommRingCat.ofHom (κ x hx) ≫
                X.presheaf.stalkSpecializes (genericPoint_specializes x) =
                CommRingCat.ofHom (algebraMap A X.functionField) := by
              ext z
              exact congrArg (fun k : A →+* X.functionField ↦ k z) (hκ x hx)
            rw [← Spec.map_comp, hm]⟩ }

end FractionField

end Langlands.AlgebraicGeometry
