import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_PartialMap_mem_domain_toRationalMap_of_valuationRing_stalk

/-! # Extending rational maps from stalks at closed points -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry

/-- A stalk extension compatible at the generic point puts that point into
the domain of definition of a rational map. -/
theorem rationalMap_mem_domain_of_stalk_extension
    {X Y S : Scheme.{u}} [IsIntegral X]
    (sX : X ⟶ S) (sY : Y ⟶ S) [LocallyOfFiniteType sY]
    (r : X.RationalMap Y) (x : X)
    (φ : Spec (X.presheaf.stalk x) ⟶ Y)
    (hφ : φ ≫ sY = X.fromSpecStalk x ≫ sX)
    (hη : Spec.map (X.presheaf.stalkSpecializes (genericPoint_specializes x)) ≫ φ =
      r.fromFunctionField) : x ∈ r.domain := by
  let q := Scheme.PartialMap.ofFromSpecStalk sX sY φ hφ
  have hx : x ∈ q.domain := Scheme.PartialMap.mem_domain_ofFromSpecStalk _ _ _ _
  have hq : q.toRationalMap = r := by
    apply Scheme.RationalMap.eq_of_fromFunctionField_eq
    change q.fromFunctionField = r.fromFunctionField
    rw [P2MW.S_AlgebraicGeometry_Scheme_PartialMap_mem_domain_toRationalMap_of_valuationRing_stalk.ValuativePartialMap.partialMap_fromFunctionField_eq_of_mem q hx]
    rw [Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk]
    exact hη
  rw [← hq]
  exact q.le_domain_toRationalMap hx

/-- An open of an affine scheme containing every closed point is the whole
scheme. -/
theorem spec_open_eq_top_of_contains_maximal
    {A : Type u} [CommRing A] (U : (Spec (CommRingCat.of A)).Opens)
    (hU : ∀ x : PrimeSpectrum A, x.asIdeal.IsMaximal → x ∈ U) : U = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨m, hm, hxm⟩ := x.asIdeal.exists_le_maximal x.isPrime.ne_top
  exact ((PrimeSpectrum.le_iff_specializes x ⟨m, hm.isPrime⟩).mp hxm).mem_open
    U.isOpen (hU ⟨m, hm.isPrime⟩ hm)

/-- Stalk extensions at all closed points of an integral affine source make
the domain of definition of a rational map the whole source. -/
theorem rationalMap_domain_eq_top_of_closed_stalk_extensions
    {A : Type u} [CommRing A] [IsDomain A] {Y S : Scheme.{u}}
    (sA : Spec (CommRingCat.of A) ⟶ S) (sY : Y ⟶ S) [LocallyOfFiniteType sY]
    (r : (Spec (CommRingCat.of A)).RationalMap Y)
    (h : ∀ x : PrimeSpectrum A, x.asIdeal.IsMaximal →
      ∃ φ : Spec ((Spec (CommRingCat.of A)).presheaf.stalk x) ⟶ Y,
        φ ≫ sY = (Spec (CommRingCat.of A)).fromSpecStalk x ≫ sA ∧
        Spec.map ((Spec (CommRingCat.of A)).presheaf.stalkSpecializes
          (genericPoint_specializes x)) ≫ φ = r.fromFunctionField) :
    r.domain = ⊤ := by
  apply spec_open_eq_top_of_contains_maximal
  intro x hx
  obtain ⟨φ, hφ, hη⟩ := h x hx
  exact rationalMap_mem_domain_of_stalk_extension sA sY r x φ hφ hη

/-- An everywhere defined rational map to a separated scheme as an actual
scheme morphism. -/
def rationalMapToHomOfDomainEqTop
    {X Y : Scheme.{u}} [IsReduced X] [Y.IsSeparated]
    (r : X.RationalMap Y) (h : r.domain = ⊤) : X ⟶ Y :=
  X.topIso.inv ≫ (X.isoOfEq h).inv ≫ r.toPartialMap.hom

set_option backward.isDefEq.respectTransparency false in
theorem rationalMapToHomOfDomainEqTop_fac
    {X Y : Scheme.{u}} [IsReduced X] [Y.IsSeparated]
    (r : X.RationalMap Y) (h : r.domain = ⊤) :
    r.domain.ι ≫ rationalMapToHomOfDomainEqTop r h = r.toPartialMap.hom := by
  dsimp only [rationalMapToHomOfDomainEqTop]
  rw [← Category.assoc, ← Category.assoc]
  have he : r.domain.ι = (X.isoOfEq h).hom ≫ X.topIso.hom := by
    simp
  rw [he]
  simp only [Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- The global morphism represents the original rational map. -/
theorem rationalMapToHomOfDomainEqTop_toRationalMap
    {X Y : Scheme.{u}} [IsReduced X] [Y.IsSeparated]
    (r : X.RationalMap Y) (h : r.domain = ⊤) :
    (rationalMapToHomOfDomainEqTop r h).toRationalMap = r := by
  calc
    (rationalMapToHomOfDomainEqTop r h).toRationalMap =
        r.toPartialMap.toRationalMap := by
      apply Eq.symm
      apply Scheme.PartialMap.toRationalMap_eq_iff.mpr
      apply (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated
        (S := ⊤_ Scheme)).mpr
      exact (rationalMapToHomOfDomainEqTop_fac r h).symm
    _ = r := r.toRationalMap_toPartialMap

set_option backward.isDefEq.respectTransparency false in
/-- Compatibility with a structure morphism is preserved on globalization. -/
theorem rationalMapToHomOfDomainEqTop_comp
    {X Y S : Scheme.{u}} [IsReduced X] [Y.IsSeparated]
    (r : X.RationalMap Y) (h : r.domain = ⊤)
    (sX : X ⟶ S) (sY : Y ⟶ S)
    (hr : r.toPartialMap.hom ≫ sY = r.domain.ι ≫ sX) :
    rationalMapToHomOfDomainEqTop r h ≫ sY = sX := by
  have : IsIso r.domain.ι := by
    have he : r.domain.ι = (X.isoOfEq h).hom ≫ X.topIso.hom := by simp
    rw [he]
    infer_instance
  apply (cancel_epi r.domain.ι).mp
  rw [← Category.assoc, rationalMapToHomOfDomainEqTop_fac]
  exact hr

/-- Globalize compatible closed-point stalk extensions over an integral
affine source. -/
def morphismOfClosedStalkExtensions
    {A : Type u} [CommRing A] [IsDomain A] {Y S : Scheme.{u}} [Y.IsSeparated]
    (sA : Spec (CommRingCat.of A) ⟶ S) (sY : Y ⟶ S) [LocallyOfFiniteType sY]
    (r : (Spec (CommRingCat.of A)).RationalMap Y)
    (h : ∀ x : PrimeSpectrum A, x.asIdeal.IsMaximal →
      ∃ φ : Spec ((Spec (CommRingCat.of A)).presheaf.stalk x) ⟶ Y,
        φ ≫ sY = (Spec (CommRingCat.of A)).fromSpecStalk x ≫ sA ∧
        Spec.map ((Spec (CommRingCat.of A)).presheaf.stalkSpecializes
          (genericPoint_specializes x)) ≫ φ = r.fromFunctionField) :
    Spec (CommRingCat.of A) ⟶ Y :=
  rationalMapToHomOfDomainEqTop r
    (rationalMap_domain_eq_top_of_closed_stalk_extensions sA sY r h)

end Langlands.AlgebraicGeometry
