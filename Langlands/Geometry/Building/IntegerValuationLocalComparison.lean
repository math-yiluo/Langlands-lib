import Langlands.Geometry.Building.IntegerValuationBuildingData

/-! # Exact local-field comparisons for integer-valued building data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

namespace KPApartmentData

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] {ω ω' : kˣ → ℝ}

/-- Transport the existing equipollence class along an equality of field orders. -/
def reindexOrder (D : KPApartmentData i ω) (h : ω = ω') : KPApartmentData i ω' :=
  h ▸ D

@[simp] theorem reindexOrder_carrier (D : KPApartmentData i ω) (h : ω = ω') :
    (D.reindexOrder h).carrier = D.carrier := by
  cases h
  rfl

@[simp] theorem reindexOrder_symm (D : KPApartmentData i ω) (h : ω = ω') :
    (D.reindexOrder h).reindexOrder h.symm = D := by
  cases h
  rfl

/-- The apartment identification preserves the affine space over the same translation space. -/
def reindexOrderApartment (D : KPApartmentData i ω) (h : ω = ω') :
    D.Apartment ≃ᵃ[ℝ] (D.reindexOrder h).Apartment := by
  cases h
  exact AffineEquiv.refl ℝ D.Apartment

@[simp] theorem reindexOrderApartment_val (D : KPApartmentData i ω) (h : ω = ω')
    (x : D.Apartment) : (D.reindexOrderApartment h x).val = x.val := by
  cases h
  rfl

theorem reindexOrderApartment_vadd (D : KPApartmentData i ω) (h : ω = ω')
    (w : TranslationSpace i) (x : D.Apartment) :
    D.reindexOrderApartment h (w +ᵥ x) = w +ᵥ D.reindexOrderApartment h x := by
  cases h
  rfl

theorem reindexOrderApartment_smul (D : KPApartmentData i ω) (h : ω = ω')
    (n : normalizerPoints i) (x : D.Apartment) :
    D.reindexOrderApartment h (n • x) = n • D.reindexOrderApartment h x := by
  cases h
  rfl

theorem reindexOrder_filtration (D : KPApartmentData i ω) (h : ω = ω')
    (x : D.Apartment) (a : characterLattice S) (r : ℝ) :
    (D.reindexOrder h).filtration (D.reindexOrderApartment h x) a r =
      D.filtration x a r := by
  cases h
  rfl

theorem reindexOrder_filtrationPlus (D : KPApartmentData i ω) (h : ω = ω')
    (x : D.Apartment) (a : characterLattice S) (r : ℝ) :
    (D.reindexOrder h).filtrationPlus (D.reindexOrderApartment h x) a r =
      D.filtrationPlus x a r := by
  cases h
  rfl

theorem reindexOrder_rootFixer (D : KPApartmentData i ω) (h : ω = ω')
    (a : characterLattice S) (Ω : Set D.Apartment) :
    (D.reindexOrder h).rootFixer a (D.reindexOrderApartment h '' Ω) = D.rootFixer a Ω := by
  cases h
  change D.rootFixer a (id '' Ω) = D.rootFixer a Ω
  rw [Set.image_id]

theorem reindexOrder_rootFixerPlus (D : KPApartmentData i ω) (h : ω = ω')
    (a : characterLattice S) (Ω : Set D.Apartment) :
    (D.reindexOrder h).rootFixerPlus a (D.reindexOrderApartment h '' Ω) =
      D.rootFixerPlus a Ω := by
  cases h
  change D.rootFixerPlus a (id '' Ω) = D.rootFixerPlus a Ω
  rw [Set.image_id]

theorem reindexOrder_sharpFixer (D : KPApartmentData i ω) (h : ω = ω')
    (Ω : Set D.Apartment) :
    (D.reindexOrder h).sharpFixer (D.reindexOrderApartment h '' Ω) = D.sharpFixer Ω := by
  cases h
  change D.sharpFixer (id '' Ω) = D.sharpFixer Ω
  rw [Set.image_id]

/-- Identify the existing reduced quotients by equality transport, without a new quotient. -/
def reindexOrderBuilding (D : KPApartmentData i ω) (h : ω = ω') :
    D.ReducedBuilding ≃ (D.reindexOrder h).ReducedBuilding := by
  cases h
  exact Equiv.refl D.ReducedBuilding

theorem reindexOrderBuilding_smul (D : KPApartmentData i ω) (h : ω = ω')
    (g : rationalPoints G) (y : D.ReducedBuilding) :
    D.reindexOrderBuilding h (g • y) = g • D.reindexOrderBuilding h y := by
  cases h
  rfl

theorem reindexOrderBuilding_apartmentMap (D : KPApartmentData i ω) (h : ω = ω')
    (x : D.Apartment) :
    D.reindexOrderBuilding h (D.apartmentMap x) =
      (D.reindexOrder h).apartmentMap (D.reindexOrderApartment h x) := by
  cases h
  rfl

theorem reindexOrder_reducedFixer (D : KPApartmentData i ω) (h : ω = ω')
    (y : D.ReducedBuilding) :
    (D.reindexOrder h).reducedFixer (D.reindexOrderBuilding h y) = D.reducedFixer y := by
  cases h
  rfl

theorem reindexOrder_pointwiseFixer (D : KPApartmentData i ω) (h : ω = ω')
    (Y : Set D.ReducedBuilding) :
    (D.reindexOrder h).pointwiseFixer (D.reindexOrderBuilding h '' Y) = D.pointwiseFixer Y := by
  cases h
  change D.pointwiseFixer (id '' Y) = D.pointwiseFixer Y
  rw [Set.image_id]

section LocalField

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left]

/-- Full V6 on the same equipollence class agrees after the proved order transport. -/
theorem isOmegaCompatible_normalized (D : KPApartmentData i (localFieldOrder F))
    (C : CentralizerDatum i) :
    IntegerValuation.IsOmegaCompatible (FML.normalizedMultiplicativeValuation F)
        (D.reindexOrder (IntegerValuation.order_normalized F).symm) C ↔
      D.IsOmegaCompatible C := by
  simp only [IntegerValuation.IsOmegaCompatible, IsOmegaCompatible, IsCentralizerCompatible,
    reindexOrder_carrier, IntegerValuation.isCentralizerCompatible_normalized]

end LocalField

end KPApartmentData

namespace IntegerValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

/-- Convert the existing local data using the proved equality of normalized field orders. -/
abbrev ofLocal (B : ValuationBuildingData G) :
    IntegerValuationBuildingData (FML.normalizedMultiplicativeValuation F) G where
  isConnectedReductive := B.isConnectedReductive
  S := B.S
  i := B.i
  isMaximalSplitTorus := B.isMaximalSplitTorus
  apartment := B.apartment.reindexOrder (IntegerValuation.order_normalized F).symm
  centralizer := B.centralizer
  isOmegaCompatible := by
    intro φ hφ
    apply (IntegerValuation.isCentralizerCompatible_normalized F B.i B.centralizer.j
      B.centralizer.s B.centralizer.bijective φ).2
    exact B.isOmegaCompatible φ (by simpa only [KPApartmentData.reindexOrder_carrier] using hφ)

/-- Recover the existing local bundle, with compatibility discharged by the comparison laws. -/
abbrev toLocal (B : IntegerValuationBuildingData (FML.normalizedMultiplicativeValuation F) G) :
    ValuationBuildingData G where
  isConnectedReductive := B.isConnectedReductive
  S := B.S
  i := B.i
  isMaximalSplitTorus := B.isMaximalSplitTorus
  apartment := B.apartment.reindexOrder (IntegerValuation.order_normalized F)
  centralizer := B.centralizer
  isOmegaCompatible := by
    intro φ hφ
    apply (IntegerValuation.isCentralizerCompatible_normalized F B.i B.centralizer.j
      B.centralizer.s B.centralizer.bijective φ).1
    exact B.isOmegaCompatible φ (by simpa only [KPApartmentData.reindexOrder_carrier] using hφ)

@[simp] theorem toLocal_ofLocal (B : ValuationBuildingData G) :
    (ofLocal B).toLocal = B := by
  cases B
  dsimp only [toLocal, ofLocal]
  congr 1

@[simp] theorem ofLocal_toLocal
    (B : IntegerValuationBuildingData (FML.normalizedMultiplicativeValuation F) G) :
    ofLocal B.toLocal = B := by
  cases B
  dsimp only [toLocal, ofLocal]
  congr 1

/-- The local and explicit normalized-valuation bundles are equivalent types of supplied data. -/
def localEquiv :
    ValuationBuildingData G ≃
      IntegerValuationBuildingData (FML.normalizedMultiplicativeValuation F) G where
  toFun := ofLocal
  invFun := toLocal
  left_inv := toLocal_ofLocal
  right_inv := ofLocal_toLocal

variable (B : ValuationBuildingData G)

/-- The local apartment is the same affine space after the proved change of order index. -/
abbrev ofLocalApartmentEquiv : B.Apartment ≃ᵃ[ℝ] (ofLocal B).Apartment :=
  B.apartment.reindexOrderApartment (IntegerValuation.order_normalized F).symm

/-- The local reduced building is identified with the same transported KP quotient. -/
abbrev ofLocalBuildingEquiv : B.ReducedBuilding ≃ (ofLocal B).ReducedBuilding :=
  B.apartment.reindexOrderBuilding (IntegerValuation.order_normalized F).symm

theorem ofLocalApartmentEquiv_val (x : B.Apartment) :
    (ofLocalApartmentEquiv B x).val = x.val :=
  B.apartment.reindexOrderApartment_val _ x

theorem ofLocalApartmentEquiv_vadd (w : TranslationSpace B.i) (x : B.Apartment) :
    ofLocalApartmentEquiv B (w +ᵥ x) = w +ᵥ ofLocalApartmentEquiv B x :=
  B.apartment.reindexOrderApartment_vadd _ w x

theorem ofLocalApartmentEquiv_smul (n : normalizerPoints B.i) (x : B.Apartment) :
    ofLocalApartmentEquiv B (n • x) = n • ofLocalApartmentEquiv B x :=
  B.apartment.reindexOrderApartment_smul _ n x

theorem ofLocalBuildingEquiv_smul (g : rationalPoints G) (y : B.ReducedBuilding) :
    ofLocalBuildingEquiv B (g • y) = g • ofLocalBuildingEquiv B y :=
  B.apartment.reindexOrderBuilding_smul _ g y

theorem ofLocalBuildingEquiv_apartmentMap (x : B.Apartment) :
    ofLocalBuildingEquiv B (B.apartmentMap x) =
      (ofLocal B).apartmentMap (ofLocalApartmentEquiv B x) :=
  B.apartment.reindexOrderBuilding_apartmentMap _ x

theorem ofLocal_rootGroup (a : characterLattice B.S) :
    (ofLocal B).rootGroup a = B.rootGroup a := rfl

theorem ofLocal_filtration (x : B.Apartment) (a : characterLattice B.S) (r : ℝ) :
    (ofLocal B).filtration (ofLocalApartmentEquiv B x) a r = B.filtration x a r :=
  B.apartment.reindexOrder_filtration _ x a r

theorem ofLocal_filtrationPlus (x : B.Apartment) (a : characterLattice B.S) (r : ℝ) :
    (ofLocal B).filtrationPlus (ofLocalApartmentEquiv B x) a r = B.filtrationPlus x a r :=
  B.apartment.reindexOrder_filtrationPlus _ x a r

theorem ofLocal_rootFixer (a : characterLattice B.S) (Ω : Set B.Apartment) :
    (ofLocal B).rootFixer a (ofLocalApartmentEquiv B '' Ω) = B.rootFixer a Ω :=
  B.apartment.reindexOrder_rootFixer _ a Ω

theorem ofLocal_rootFixerPlus (a : characterLattice B.S) (Ω : Set B.Apartment) :
    (ofLocal B).rootFixerPlus a (ofLocalApartmentEquiv B '' Ω) = B.rootFixerPlus a Ω :=
  B.apartment.reindexOrder_rootFixerPlus _ a Ω

theorem ofLocal_sharpFixer (Ω : Set B.Apartment) :
    (ofLocal B).sharpFixer (ofLocalApartmentEquiv B '' Ω) = B.sharpFixer Ω :=
  B.apartment.reindexOrder_sharpFixer _ Ω

theorem ofLocal_fixer (y : B.ReducedBuilding) :
    (ofLocal B).fixer (ofLocalBuildingEquiv B y) = B.fixer y :=
  B.apartment.reindexOrder_reducedFixer _ y

theorem ofLocal_pointwiseFixer (Y : Set B.ReducedBuilding) :
    (ofLocal B).pointwiseFixer (ofLocalBuildingEquiv B '' Y) = B.pointwiseFixer Y :=
  B.apartment.reindexOrder_pointwiseFixer _ Y

theorem ofLocal_translation : (ofLocal B).translation = B.translation :=
  IntegerValuation.centralizerTranslation_normalized F B.centralizer.s B.centralizer.bijective

/-- The generic one-group stabilizer is exactly the existing local stabilizer subgroup. -/
theorem ofLocal_oneStabilizer (y : B.ReducedBuilding) :
    (ofLocal B).oneStabilizer (ofLocalBuildingEquiv B y) = B.compactStabilizer y := by
  change characterValuationKernel (FML.normalizedMultiplicativeValuation F) G ⊓
      (B.apartment.reindexOrder _).reducedFixer (B.apartment.reindexOrderBuilding _ y) =
    Plancherel.rationalCommonNormKernel G ⊓ B.apartment.reducedFixer y
  rw [KPApartmentData.reindexOrder_reducedFixer, IntegerValuation.characterValuationKernel_normalized]

end IntegerValuationBuildingData

end Langlands.Geometry.Building
