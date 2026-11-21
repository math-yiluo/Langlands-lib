import Langlands.GroupScheme.Cartier.FiniteDualSchemes
import Langlands.GroupScheme.Cartier.FiniteDualRelativePairing

/-! # Naturality of evaluation under the actual finite dual maps -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry Module TensorProduct WithConv
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.Cartier.FiniteDual

section Coefficients

variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
variable [HopfAlgebra R A] [HopfAlgebra R B] [Algebra R C]
variable [Module.Finite R A] [Module.Projective R A] [Module.Finite R B] [Module.Projective R B]

private theorem coefficients_map_left (φ : A →ₐc[R] B) (t : A ⊗[R] C) (f : Dual R B) :
    coefficients R B C (Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id R C) t) f =
      coefficients R A C t (dualBialgHom φ f) := by
  induction t using TensorProduct.inductionOn with
  | tmul a c => simp
  | add t s ht hs => simp [ht, hs]

/-- Evaluating at the original map on a point equals evaluating at the dual map
on the character. -/
theorem pointCharacter_dualMap (φ : A →ₐc[R] B) (x : B →ₐ[R] C) (y : Dual R A →ₐ[R] C) :
    pointCharacter (toConv y) (toConv (x.comp φ.toAlgHom)) =
      pointCharacter (toConv (y.comp (dualBialgHom φ).toAlgHom)) (toConv x) := by
  let t := (coefficients R A C).symm y.toLinearMap
  have h : (coefficients R B C).symm (y.comp (dualBialgHom φ).toAlgHom).toLinearMap =
      Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id R C) t := by
    apply coefficients_ext
    intro f
    rw [LinearEquiv.apply_symm_apply, coefficients_map_left]
    have ht := LinearMap.congr_fun ((coefficients R A C).apply_symm_apply y.toLinearMap)
      (dualBialgHom φ f)
    exact ht.symm
  apply Units.ext
  simp only [pointCharacter_val, h]
  change evalTensor (x.comp φ.toAlgHom) t =
    evalTensor x (Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id R C) t)
  induction t using TensorProduct.inductionOn with
  | tmul a c => simp
  | add t s ht hs => simp [ht, hs]

end Coefficients

section Spectra

variable {R : CommRingCat.{u}} {A B : Type u} [CommRing A] [CommRing B]
variable [HopfAlgebra R A] [HopfAlgebra R B] [Coalgebra.IsCocomm R A] [Coalgebra.IsCocomm R B]
variable [Module.Finite R A] [Module.Projective R A] [Module.Finite R B] [Module.Projective R B]

/-- The actual evaluation pairing on spectra is natural under the original and dual maps. -/
theorem schemePairing_dualMap (φ : A →ₐc[R] B) (T : Over (Spec R))
    (x : T ⟶ specOver R B) (y : T ⟶ specOver R (Dual R A)) :
    schemePairing R A T y (x ≫ specMap φ.toAlgHom) =
      schemePairing R B T (y ≫ specMap (dualBialgHom φ).toAlgHom) x := by
  apply (Gm.pointsEquiv (Spec R) T).injective
  rw [schemePairing_units R A T y, schemePairing_units R B T]
  simp only [specPoints_apply, specHomEquiv_postcomp]
  exact pointCharacter_dualMap (C := sections T) φ _ _

end Spectra

section Schemes

variable {R : CommRingCat.{u}}

attribute [local instance] finiteScheme_isAffine finiteScheme_cocomm finiteScheme_finite
  finiteScheme_projective

variable (G : CommGroupScheme (Spec R)) [IsFinite G.X.hom] [Flat G.X.hom]
  [LocallyOfFinitePresentation G.X.hom]

/-- The actual evaluation pairing for a finite locally free group scheme and its dual spectrum. -/
def finiteSchemePairing (T : Over (Spec R)) (y : T ⟶ (schemeDual G).X) :
    (T ⟶ G.X) →* (T ⟶ (Gm (Spec R)).X) :=
  (schemePairing R (AffineCoordinates.hopfAlgebra G.toGrp) T y).comp
    (((yonedaGrp.mapIso (AffineCoordinates.hopfSpecIso G.toGrp).symm).app (op T)).groupIsoToMulEquiv.toMonoidHom)

@[simp]
theorem finiteSchemePairing_apply (T : Over (Spec R)) (y : T ⟶ (schemeDual G).X) (x : T ⟶ G.X) :
    finiteSchemePairing G T y x = schemePairing R (AffineCoordinates.hopfAlgebra G.toGrp) T y
      (x ≫ (AffineCoordinates.hopfSpecIso G.toGrp).inv.hom.hom) := rfl

/-- Evaluation is natural on arbitrary test schemes. -/
theorem finiteSchemePairing_naturality {T U : Over (Spec R)} (a : U ⟶ T)
    (x : T ⟶ G.X) (y : T ⟶ (schemeDual G).X) :
    finiteSchemePairing G U (a ≫ y) (a ≫ x) = a ≫ finiteSchemePairing G T y x := by
  let A := AffineCoordinates.hopfAlgebra G.toGrp
  let b := (AffineCoordinates.hopfSpecIso G.toGrp).inv.hom.hom
  calc
    finiteSchemePairing G U (a ≫ y) (a ≫ x) = schemePairing R A U (a ≫ y) (a ≫ (x ≫ b)) :=
      congrArg (schemePairing R A U (a ≫ y)) (Category.assoc a x b)
    _ = a ≫ finiteSchemePairing G T y x := schemePairing_naturality R A a y (x ≫ b)

/-- Evaluation is multiplicative in the dual point. -/
theorem finiteSchemePairing_mul (T : Over (Spec R)) (y z : T ⟶ (schemeDual G).X) (x : T ⟶ G.X) :
    finiteSchemePairing G T (y * z) x = finiteSchemePairing G T y x * finiteSchemePairing G T z x :=
  schemePairing_mul R (AffineCoordinates.hopfAlgebra G.toGrp) T y z
    (x ≫ (AffineCoordinates.hopfSpecIso G.toGrp).inv.hom.hom)

variable {G} {H : CommGroupScheme (Spec R)} [IsFinite H.X.hom] [Flat H.X.hom]
  [LocallyOfFinitePresentation H.X.hom]

/-- An actual finite group map and its dual are adjoint for the evaluation pairings. -/
theorem finiteSchemePairing_dualMap (f : G ⟶ H) (T : Over (Spec R))
    (x : T ⟶ G.X) (y : T ⟶ (schemeDual H).X) :
    finiteSchemePairing H T y (x ≫ f.toMul.hom.hom) =
      finiteSchemePairing G T (y ≫ (schemeDualMap f).toMul.hom.hom) x := by
  let a := AffineCoordinates.hopfSpecIso G.toGrp
  let b := AffineCoordinates.hopfSpecIso H.toGrp
  let φ := (Langlands.GroupScheme.AffineHopfMorphism.pullback f.toMul).hom
  have hp : (hopfSpec R).map (Langlands.GroupScheme.AffineHopfMorphism.pullback f.toMul).op = a.hom ≫ f.toMul ≫ b.inv :=
    hopfSpec.fullyFaithful.map_preimage _
  have he : specMap φ.toAlgHom = a.hom.hom.hom ≫ f.toMul.hom.hom ≫ b.inv.hom.hom :=
    congrArg (fun g => g.hom.hom) hp
  have hcancel : a.inv.hom.hom ≫ a.hom.hom.hom = 𝟙 G.X :=
    congrArg (fun g => g.hom.hom) a.inv_hom_id
  have he' : (x ≫ a.inv.hom.hom) ≫ specMap φ.toAlgHom = (x ≫ f.toMul.hom.hom) ≫ b.inv.hom.hom := by
    calc
      (x ≫ a.inv.hom.hom) ≫ specMap φ.toAlgHom =
          (x ≫ (a.inv.hom.hom ≫ a.hom.hom.hom)) ≫ f.toMul.hom.hom ≫ b.inv.hom.hom := by
        rw [he]
        simp only [Category.assoc]
      _ = _ := by rw [hcancel, Category.comp_id, Category.assoc]
  have hd : (schemeDualMap f).toMul.hom.hom = specMap (dualBialgHom φ).toAlgHom := rfl
  calc
    finiteSchemePairing H T y (x ≫ f.toMul.hom.hom) =
        schemePairing R (AffineCoordinates.hopfAlgebra H.toGrp) T y
          ((x ≫ a.inv.hom.hom) ≫ specMap φ.toAlgHom) :=
      congrArg (schemePairing R (AffineCoordinates.hopfAlgebra H.toGrp) T y) he'.symm
    _ = schemePairing R (AffineCoordinates.hopfAlgebra G.toGrp) T
          (y ≫ specMap (dualBialgHom φ).toAlgHom) (x ≫ a.inv.hom.hom) :=
      schemePairing_dualMap φ T (x ≫ a.inv.hom.hom) y
    _ = finiteSchemePairing G T (y ≫ (schemeDualMap f).toMul.hom.hom) x :=
      congrArg (fun z => schemePairing R (AffineCoordinates.hopfAlgebra G.toGrp) T
        (y ≫ z) (x ≫ a.inv.hom.hom)) hd.symm

end Schemes
end Langlands.GroupScheme.Cartier.FiniteDual
