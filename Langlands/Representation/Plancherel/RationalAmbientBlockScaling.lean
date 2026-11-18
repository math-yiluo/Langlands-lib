import Langlands.Representation.Plancherel.RationalValuationKernelCoordinates
import Langlands.Representation.Plancherel.UnramifiedScalarTranslation

/-! # Ambient unramified twists in valuation-kernel product coordinates -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel.ValuationKernelCoordinates

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]

local instance sourcePointTopology : TopologicalSpace (rationalPoints H) :=
  rationalPointTopology F H.X
local instance targetPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

variable {r n : ℕ}
  (e : Additive (rationalDiscreteValuationImage H) ≃ₗ[ℤ]
    (Fin r → ℤ) × (Fin n → ℤ))

/-- A character varying only on the complement block of the actual lattice. -/
def complementImageCharacter (c : Fin n → ℂˣ) : rationalImageCharacters H where
  toFun a := ∏ i, c i ^ (e (Additive.ofMul a)).2 i
  map_one' := by
    change (∏ i, c i ^ (e 0).2 i) = 1
    simp
  map_mul' a b := by
    change (∏ i, c i ^ (e (Additive.ofMul a + Additive.ofMul b)).2 i) = _
    simp [zpow_add, Finset.prod_mul_distrib]
  continuous_toFun := continuous_of_discreteTopology

/-- The corresponding existing actual unramified character. -/
def complementParameter (c : Fin n → ℂˣ) :
    unramifiedCharacters (fun chi => (rationalNormCharacters H chi).toMul) :=
  rationalCanonicalImageUnramifiedContinuousEquiv H (complementImageCharacter e c)

@[simp]
theorem complementParameter_apply (c : Fin n → ℂˣ) (h : rationalPoints H) :
    (complementParameter e c).val h =
      ∏ i, c i ^ (e (Additive.ofMul (rationalValuationImageProjection H h))).2 i := rfl

/-- Every complement-block scaling is the restriction of an actual ambient
unramified character when the first block is the valuation kernel. -/
theorem complementParameter_ambient (f : H ⟶ G)
    (he : ∀ x : Additive (rationalDiscreteValuationImage H),
      (e x).2 = 0 ↔ rationalValuationImageMap f x.toMul = 1)
    (c : Fin n → ℂˣ) :
    ∃ eta : unramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul),
      rationalUnramifiedCharacterRestrict f eta = complementParameter e c := by
  apply (rationalUnramifiedValuationKernelRestrict_eq_one_iff f _).mp
  apply MonoidHom.ext
  intro a
  have hd : rationalImageUnramifiedDescend H (complementParameter e c) =
      complementImageCharacter e c :=
    (rationalCanonicalImageUnramifiedContinuousEquiv H).symm_apply_apply _
  change rationalImageUnramifiedDescend H (complementParameter e c) a.val = 1
  rw [hd]
  change (∏ i, c i ^ (e (Additive.ofMul a.val)).2 i) = 1
  rw [(he (Additive.ofMul a.val)).mpr a.property]
  simp

/-- Product coordinates on the existing actual regular scalar algebra. -/
def productLaurentAlgebraEquiv :
    AddMonoidAlgebra ℂ ((Fin r → ℤ) × (Fin n → ℤ)) ≃ₐ[ℂ]
      unramifiedRegularFunctions (fun chi => (rationalNormCharacters H chi).toMul) :=
  (AddMonoidAlgebra.domCongr ℂ ℂ e.symm.toAddEquiv).trans
    (rationalCanonicalUnramifiedCoordinateAlgebraEquiv H)

/-- On one monomial, the coordinate equivalence is evaluation at the exact
corresponding element of the actual valuation image. -/
theorem productLaurentAlgebraEquiv_single_eval
    (m : (Fin r → ℤ) × (Fin n → ℤ)) (a : ℂ)
    (chi : unramifiedCharacters (fun psi => (rationalNormCharacters H psi).toMul)) :
    (productLaurentAlgebraEquiv e (AddMonoidAlgebra.single m a)).val chi =
      a * (rationalImageUnramifiedDescend H chi (e.symm m).toMul : ℂ) := by
  change (rationalCanonicalUnramifiedCoordinateAlgebraEquiv H
    (AddMonoidAlgebra.domCongr ℂ ℂ e.symm.toAddEquiv
      (AddMonoidAlgebra.single m a))).val chi = _
  rw [AddMonoidAlgebra.domCongr_single]
  exact rationalImageCoordinateEvaluation_single H _ _ _

/-- Complement-block scaling on the product Laurent algebra is the exact
conjugate of translation by its actual unramified parameter. -/
def productRegularScaling (c : Fin n → ℂˣ) :
    AddMonoidAlgebra ℂ ((Fin r → ℤ) × (Fin n → ℤ)) ≃ₐ[ℂ]
      AddMonoidAlgebra ℂ ((Fin r → ℤ) × (Fin n → ℤ)) :=
  (productLaurentAlgebraEquiv e).trans
    ((unramifiedRegularTranslation (fun chi => (rationalNormCharacters H chi).toMul)
      (complementParameter e c)).trans (productLaurentAlgebraEquiv e).symm)

/-- The exact monomial action scales only the second block of coordinates. -/
theorem productRegularScaling_single (c : Fin n → ℂˣ)
    (m : (Fin r → ℤ) × (Fin n → ℤ)) (a : ℂ) :
    productRegularScaling e c (AddMonoidAlgebra.single m a) =
      AddMonoidAlgebra.single m (a * ((∏ i, c i ^ m.2 i : ℂˣ) : ℂ)) := by
  apply (productLaurentAlgebraEquiv e).injective
  change (productLaurentAlgebraEquiv e)
      ((productLaurentAlgebraEquiv e).symm
        (unramifiedRegularTranslation _ (complementParameter e c)
          (productLaurentAlgebraEquiv e (AddMonoidAlgebra.single m a)))) = _
  rw [AlgEquiv.apply_symm_apply]
  apply Subtype.ext
  funext chi
  rw [unramifiedRegularTranslation_apply, productLaurentAlgebraEquiv_single_eval,
    productLaurentAlgebraEquiv_single_eval]
  obtain ⟨h, hh⟩ := rationalValuationImageProjection_surjective H (e.symm m).toMul
  rw [← hh, rationalImageUnramifiedDescend_projection,
    rationalImageUnramifiedDescend_projection]
  change a * (((complementParameter e c).val h * chi.val h : ℂˣ) : ℂ) = _
  rw [complementParameter_apply, hh]
  change a * (((∏ i, c i ^ (e (e.symm m)).2 i) * chi.val h : ℂˣ) : ℂ) = _
  rw [LinearEquiv.apply_symm_apply, Units.val_mul, mul_assoc]

variable (hH : IsConnectedReductive H)

/-- Product Laurent fractions and the existing actual scalar field are
isomorphic without choosing values at poles. -/
def productFunctionFieldEquiv :
    FractionRing (AddMonoidAlgebra ℂ ((Fin r → ℤ) × (Fin n → ℤ))) ≃+*
      rationalUnramifiedFunctionField H (continuous_rationalValuationImageProjection H) hH :=
  IsFractionRing.ringEquivOfRingEquiv (productLaurentAlgebraEquiv e).toRingEquiv

/-- Scaling on Laurent fractions, obtained from the exact actual translation. -/
def productFractionScaling (c : Fin n → ℂˣ) :
    FractionRing (AddMonoidAlgebra ℂ ((Fin r → ℤ) × (Fin n → ℤ))) ≃+*
      FractionRing (AddMonoidAlgebra ℂ ((Fin r → ℤ) × (Fin n → ℤ))) :=
  (productFunctionFieldEquiv e hH).trans
    ((rationalUnramifiedFunctionFieldTranslation H
      (continuous_rationalValuationImageProjection H) hH (complementParameter e c)).trans
        (productFunctionFieldEquiv e hH).symm)

@[simp]
theorem productFractionScaling_algebraMap (c : Fin n → ℂˣ)
    (p : AddMonoidAlgebra ℂ ((Fin r → ℤ) × (Fin n → ℤ))) :
    productFractionScaling e hH c (algebraMap _
      (FractionRing (AddMonoidAlgebra ℂ ((Fin r → ℤ) × (Fin n → ℤ)))) p) =
      algebraMap _
        (FractionRing (AddMonoidAlgebra ℂ ((Fin r → ℤ) × (Fin n → ℤ))))
          (productRegularScaling e c p) := by
  apply (productFunctionFieldEquiv e hH).injective
  simp only [productFractionScaling, RingEquiv.trans_apply,
    RingEquiv.apply_symm_apply, productFunctionFieldEquiv,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap,
    rationalUnramifiedFunctionFieldTranslation_algebraMap,
    productRegularScaling, AlgEquiv.trans_apply]
  exact congrArg (algebraMap _ _)
    ((productLaurentAlgebraEquiv e).apply_symm_apply _).symm

/-- The fraction-field scaling has the same exact action on each Laurent
monomial as the regular scalar translation. -/
theorem productFractionScaling_single (c : Fin n → ℂˣ)
    (m : (Fin r → ℤ) × (Fin n → ℤ)) (a : ℂ) :
    productFractionScaling e hH c (algebraMap _
      (FractionRing (AddMonoidAlgebra ℂ ((Fin r → ℤ) × (Fin n → ℤ))))
        (AddMonoidAlgebra.single m a)) =
      algebraMap _
        (FractionRing (AddMonoidAlgebra ℂ ((Fin r → ℤ) × (Fin n → ℤ))))
          (AddMonoidAlgebra.single m (a * ((∏ i, c i ^ m.2 i : ℂˣ) : ℂ))) := by
  rw [productFractionScaling_algebraMap, productRegularScaling_single]

/-- An ambient-invariant actual fraction becomes invariant under every scaling
on the complement block in these product coordinates. -/
theorem productFractionScaling_fixed_of_ambient_fixed
    (f : H ⟶ G)
    (he : ∀ x : Additive (rationalDiscreteValuationImage H),
      (e x).2 = 0 ↔ rationalValuationImageMap f x.toMul = 1)
    (z : rationalUnramifiedFunctionField H
      (continuous_rationalValuationImageProjection H) hH)
    (hz : ∀ eta : unramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul),
      rationalUnramifiedFunctionFieldTranslation H
        (continuous_rationalValuationImageProjection H) hH
          (rationalUnramifiedCharacterRestrict f eta) z = z)
    (c : Fin n → ℂˣ) :
    productFractionScaling e hH c ((productFunctionFieldEquiv e hH).symm z) =
      (productFunctionFieldEquiv e hH).symm z := by
  obtain ⟨eta, heta⟩ := complementParameter_ambient e f he c
  change (productFunctionFieldEquiv e hH).symm
    (rationalUnramifiedFunctionFieldTranslation H
      (continuous_rationalValuationImageProjection H) hH (complementParameter e c)
        ((productFunctionFieldEquiv e hH) ((productFunctionFieldEquiv e hH).symm z))) = _
  rw [RingEquiv.apply_symm_apply, ← heta, hz eta]

end Langlands.Plancherel.ValuationKernelCoordinates
