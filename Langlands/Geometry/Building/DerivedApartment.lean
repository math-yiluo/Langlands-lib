import Langlands.Geometry.Building.DerivedFunctionsAction
import Langlands.Geometry.Building.DerivedValuation

/-! # Actual apartment pullback through a derived inclusion -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k]
    {T A S : CommGroupScheme (Spec (CommRingCat.of k))}
    {D G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom]
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (e : T ⟶ S) (c : A ⟶ S) (j : T.toGrp ⟶ D) (i : S.toGrp ⟶ G)
    (d : D ⟶ G) (hd : IsDerivedSubgroup d)
    (h : j ≫ d = CommGroupScheme.groupHom e ≫ i)
    (hT : IsSplitTorus T.toGrp) (hS : IsSplitTorus S.toGrp)
    (hA : IsSplitTorus A.toGrp)
    [Flat (RelativeRoot.centralComplementProduct e c).hom.hom.left]
    [Surjective (RelativeRoot.centralComplementProduct e c).hom.hom.left]
    (hc : IsCentral (CommGroupScheme.groupHom c ≫ i))

open RootFunctionFamily

namespace KPApartmentData

variable [Mono i.hom.hom.left] [Mono j.hom.hom.left]
    (hi : IsMaximalSplitTorus i) {ω : kˣ → ℝ}

/-- The actual derived apartment class is the image of the entire original
ambient class under normalized derived pullback. -/
def derivedPullback (P : KPApartmentData i ω) : KPApartmentData j ω where
  carrier := RootFunctionFamily.derivedPullback e c j i d hd h hT hS hA hc '' P.carrier
  exists_eq_orbit := by
    obtain ⟨φ, hφ, hω, hclass⟩ := P.exists_eq_orbit
    refine ⟨RootFunctionFamily.derivedPullback e c j i d hd h hT hS hA hc φ,
      hφ.derivedPullback_isRootDatumValuation e c j i d hd h hT hS hA hc hi,
      hω.derivedPullback e c j i d hd h hT hS hA hc, ?_⟩
    rw [hclass]
    ext ψ
    constructor
    · rintro ⟨ψ, ⟨w, rfl⟩, rfl⟩
      obtain ⟨v, z, rfl⟩ :=
        exists_eq_cocharacterMapReal_add_of_centralComplement e c hT hA hS w
      dsimp only
      rw [add_vadd, hφ.isNormalized.centralComplement_vadd c i hA hc z]
      exact ⟨v, (RootFunctionFamily.derivedPullback_vadd
        e c j i d hd h hT hS hA hc φ v).symm⟩
    · rintro ⟨v, rfl⟩
      exact ⟨cocharacterMapReal e v +ᵥ φ, ⟨cocharacterMapReal e v, rfl⟩,
        RootFunctionFamily.derivedPullback_vadd e c j i d hd h hT hS hA hc φ v⟩
  smul_mem n ψ hψ := by
    obtain ⟨φ, hφ, rfl⟩ := hψ
    exact ⟨DerivedNormalizerMap.normalizerPointsHom e c j i d h hT hA hi hc n • φ,
      P.smul_mem _ _ hφ,
      RootFunctionFamily.derivedPullback_smul e c j i d hd h hT hS hA hc hi n φ⟩

variable (P : KPApartmentData i ω)

/-- Normalized ambient families are determined by their actual derived
pullbacks. -/
private theorem apartmentPullback_injective :
    Function.Injective (fun x : P.Apartment =>
      (⟨RootFunctionFamily.derivedPullback e c j i d hd h hT hS hA hc x.val,
        ⟨x.val, x.mem, rfl⟩⟩ :
        (P.derivedPullback e c j i d hd h hT hS hA hc hi).Apartment)) := by
  intro x y he
  apply Apartment.ext
  exact RootFunctionFamily.derivedPullback_injective e c j i d hd h hT hS hA hc
    x.isValuation.isNormalized y.isValuation.isNormalized (congrArg Apartment.val he)

/-- The literal pullback reindexes all actual valuation points of the class. -/
def derivedApartmentEquiv :
    P.Apartment ≃ (P.derivedPullback e c j i d hd h hT hS hA hc hi).Apartment :=
  Equiv.ofBijective
    (fun x => ⟨RootFunctionFamily.derivedPullback e c j i d hd h hT hS hA hc x.val,
      ⟨x.val, x.mem, rfl⟩⟩)
    ⟨P.apartmentPullback_injective e c j i d hd h hT hS hA hc hi, by
      rintro ⟨ψ, φ, hφ, rfl⟩
      exact ⟨⟨φ, hφ⟩, rfl⟩⟩

@[simp] theorem derivedApartmentEquiv_val (x : P.Apartment) :
    (P.derivedApartmentEquiv e c j i d hd h hT hS hA hc hi x).val =
      RootFunctionFamily.derivedPullback e c j i d hd h hT hS hA hc x.val := rfl

/-- Pullback intertwines the original reduced translation-space actions. -/
theorem derivedApartmentEquiv_vadd (v : TranslationSpace j) (x : P.Apartment) :
    P.derivedApartmentEquiv e c j i d hd h hT hS hA hc hi
        (derivedTranslationEquiv e c j i d hd h hT hS hA hc v +ᵥ x) =
      v +ᵥ P.derivedApartmentEquiv e c j i d hd h hT hS hA hc hi x := by
  refine Submodule.Quotient.induction_on _ v fun w => ?_
  apply Apartment.ext
  exact RootFunctionFamily.derivedPullback_vadd e c j i d hd h hT hS hA hc x.val w

/-- Point pullback commutes with the two original actual normalizer actions. -/
theorem derivedApartmentEquiv_smul (n : normalizerPoints j) (x : P.Apartment) :
    P.derivedApartmentEquiv e c j i d hd h hT hS hA hc hi
        (DerivedNormalizerMap.normalizerPointsHom e c j i d h hT hA hi hc n • x) =
      n • P.derivedApartmentEquiv e c j i d hd h hT hS hA hc hi x := by
  apply Apartment.ext
  exact RootFunctionFamily.derivedPullback_smul e c j i d hd h hT hS hA hc hi n x.val

/-- The original point pullback is affine, with inverse derived quotient
cocharacter map as derivative. -/
def derivedApartmentAffineEquiv :
    P.Apartment ≃ᵃ[ℝ] (P.derivedPullback e c j i d hd h hT hS hA hc hi).Apartment where
  toEquiv := P.derivedApartmentEquiv e c j i d hd h hT hS hA hc hi
  linear := (derivedTranslationEquiv e c j i d hd h hT hS hA hc).symm
  map_vadd' x v := by
    obtain ⟨v, rfl⟩ := (derivedTranslationEquiv e c j i d hd h hT hS hA hc).surjective v
    simpa only [LinearEquiv.symm_apply_apply] using
      P.derivedApartmentEquiv_vadd e c j i d hd h hT hS hA hc hi v x

@[simp] theorem derivedApartmentAffineEquiv_val (x : P.Apartment) :
    (P.derivedApartmentAffineEquiv e c j i d hd h hT hS hA hc hi x).val =
      RootFunctionFamily.derivedPullback e c j i d hd h hT hS hA hc x.val := rfl

/-- The actual affine normalizer maps are intertwined by the constructed
affine equivalence. -/
theorem derivedApartmentAffineEquiv_normalizer (n : normalizerPoints j) :
    (P.normalizerAffineEquiv
        (DerivedNormalizerMap.normalizerPointsHom e c j i d h hT hA hi hc n)).trans
        (P.derivedApartmentAffineEquiv e c j i d hd h hT hS hA hc hi) =
      (P.derivedApartmentAffineEquiv e c j i d hd h hT hS hA hc hi).trans
        ((P.derivedPullback e c j i d hd h hT hS hA hc hi).normalizerAffineEquiv n) := by
  apply AffineEquiv.ext
  exact P.derivedApartmentEquiv_smul e c j i d hd h hT hS hA hc hi n

end KPApartmentData

end Langlands.Geometry.Building
