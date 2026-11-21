import Langlands.GroupScheme.Cartier.FiniteDualProduct
import Langlands.GroupScheme.Cartier.FiniteDualAffineCharacters
import Langlands.GroupScheme.Torus.InducedProducts

/-! # Perfectness of the alternating pairing on a finite split product -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory AlgebraicGeometry Opposite Module
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cartier

section Product

variable {S : Scheme.{u}} (G H : CommGroupScheme S) (T : Over S)

/-- Actual relative characters of a binary product are the two relative characters
obtained by restriction along its factor inclusions. -/
def productCharactersEquiv : (characters (CommGroupScheme.prod G H)).obj (op T) ≃+
    (characters G).obj (op T) × (characters H).obj (op T) where
  toFun χ := ((CommGroupScheme.baseChange T.hom).map (CommGroupScheme.prodInl G H) ≫ χ,
    (CommGroupScheme.baseChange T.hom).map (CommGroupScheme.prodInr G H) ≫ χ)
  invFun χ := precompose (Gm S) (CommGroupScheme.prodFst G H) T χ.1 +
    precompose (Gm S) (CommGroupScheme.prodSnd G H) T χ.2
  left_inv χ := by
    change (CommGroupScheme.baseChange T.hom).map (CommGroupScheme.prodFst G H) ≫
        ((CommGroupScheme.baseChange T.hom).map (CommGroupScheme.prodInl G H) ≫ χ) +
      (CommGroupScheme.baseChange T.hom).map (CommGroupScheme.prodSnd G H) ≫
        ((CommGroupScheme.baseChange T.hom).map (CommGroupScheme.prodInr G H) ≫ χ) = χ
    simp only [← Category.assoc, ← Preadditive.add_comp, ← Functor.map_comp,
      ← Functor.map_add, CommGroupScheme.prod_decomposition]
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  right_inv χ := by
    apply Prod.ext <;> simp [Preadditive.comp_add, ← Category.assoc, ← Functor.map_comp]
  map_add' χ ψ := by
    exact Prod.ext (Preadditive.comp_add _ _ _ _ _ _) (Preadditive.comp_add _ _ _ _ _ _)

/-- Evaluation of the combined relative character multiplies the two factor evaluations. -/
theorem productCharactersEquiv_evaluation (χ : (characters G).obj (op T))
    (ψ : (characters H).obj (op T)) (x : T ⟶ (CommGroupScheme.prod G H).X) :
    characterEvaluation ((productCharactersEquiv G H T).symm (χ, ψ)) x =
      characterEvaluation χ (x ≫ (CommGroupScheme.prodFst G H).toMul.hom.hom) *
        characterEvaluation ψ (x ≫ (CommGroupScheme.prodSnd G H).toMul.hom.hom) := by
  change characterEvaluation (((charactersMap (CommGroupScheme.prodFst G H)).app (op T)) χ +
    ((charactersMap (CommGroupScheme.prodSnd G H)).app (op T)) ψ) x = _
  rw [characterEvaluation_add, characterEvaluation_precompose, characterEvaluation_precompose]

private theorem productCharactersEquiv_symm_restrict {V : Over S} (a : V ⟶ T)
    (χ : (characters G).obj (op T)) (ψ : (characters H).obj (op T)) :
    (characters (CommGroupScheme.prod G H)).map a.op ((productCharactersEquiv G H T).symm (χ, ψ)) =
      (productCharactersEquiv G H V).symm ((characters G).map a.op χ, (characters H).map a.op ψ) := by
  change restrict _ _ a (precompose (Gm S) (CommGroupScheme.prodFst G H) T χ +
    precompose (Gm S) (CommGroupScheme.prodSnd G H) T ψ) = _
  rw [map_add, restrict_precompose, restrict_precompose]
  rfl

end Product

namespace FiniteDual

attribute [local instance] finiteScheme_isAffine finiteScheme_cocomm finiteScheme_finite
  finiteScheme_projective

variable {R : CommRingCat.{u}} (G : CommGroupScheme (Spec R)) [IsFinite G.X.hom] [Flat G.X.hom]
  [LocallyOfFinitePresentation G.X.hom]

local notation "A" => AffineCoordinates.hopfAlgebra G.toGrp
local notation "D" => schemeDual G
local notation "P" => CommGroupScheme.prod G (schemeDual G)

private def specComparison : specGroup R A ≅ G :=
  CommGroupScheme.isoOfGroupIso (AffineCoordinates.hopfSpecIso G.toGrp)

private def dualPointCharacter (T : Over (Spec R)) (y : T ⟶ (D).X) : (characters G).obj (op T) :=
  precompose (Gm (Spec R)) (specComparison G).inv T (characterOfPoint R A y)

private def primalToBidual (T : Over (Spec R)) (x : T ⟶ G.X) :
    T ⟶ (specGroup R (Dual R (Dual R A))).X :=
  (x ≫ (specComparison G).inv.toMul.hom.hom) ≫ specMap (bidualEquiv R A).symm.toAlgEquiv.toAlgHom

private def primalPointCharacter (T : Over (Spec R)) (x : T ⟶ G.X) : (characters D).obj (op T) :=
  characterOfPoint R (Dual R A) (primalToBidual G T x)

private theorem dualPointCharacter_restrict {T V : Over (Spec R)} (a : V ⟶ T) (y : T ⟶ (D).X) :
    (characters G).map a.op (dualPointCharacter G T y) = dualPointCharacter G V (a ≫ y) := by
  change restrict G (Gm (Spec R)) a (precompose _ (specComparison G).inv T (characterOfPoint R A y)) = _
  rw [restrict_precompose, characterOfPoint_restrict]
  rfl

private theorem primalPointCharacter_restrict {T V : Over (Spec R)} (a : V ⟶ T) (x : T ⟶ G.X) :
    (characters D).map a.op (primalPointCharacter G T x) = primalPointCharacter G V (a ≫ x) := by
  change restrict _ _ a (characterOfPoint R (Dual R A) (primalToBidual G T x)) = _
  rw [characterOfPoint_restrict]
  simp only [primalPointCharacter, primalToBidual, Category.assoc]

private theorem dualPointCharacter_mul (T : Over (Spec R)) (y z : T ⟶ (D).X) :
    dualPointCharacter G T (y * z) = dualPointCharacter G T y + dualPointCharacter G T z := by
  let f := precompose (Gm (Spec R)) (specComparison G).inv T
  have h := characterOfPoint_mul R A y z
  exact (congrArg (fun χ => f χ) h).trans (map_add f _ _)

private theorem primalPointCharacter_mul (T : Over (Spec R)) (x z : T ⟶ G.X) :
    primalPointCharacter G T (x * z) = primalPointCharacter G T x + primalPointCharacter G T z := by
  have h : primalToBidual G T (x * z) = primalToBidual G T x * primalToBidual G T z := by
    let f : CommHopfAlgCat.of R (Dual R (Dual R A)) ⟶ CommHopfAlgCat.of R A :=
      ⟨(bidualEquiv R A).symm.toBialgHom⟩
    let b := (hopfSpec R).map f.op
    change (((x * z) ≫ (specComparison G).inv.toMul.hom.hom) ≫ b.hom.hom) = _
    rw [MonObj.mul_comp, MonObj.mul_comp]
    rfl
  exact (congrArg (characterOfPoint R (Dual R A)) h).trans (characterOfPoint_mul R (Dual R A) _ _)

private def splitPoints (T : Over (Spec R)) :
    (T ⟶ (P).X) ≃* (T ⟶ G.X) × (T ⟶ (D).X) :=
  productWithDualPoints G T

private def factorPairingCharacters (T : Over (Spec R)) (x : T ⟶ (P).X) :
    (characters G).obj (op T) × (characters D).obj (op T) :=
  let t := splitPoints G T x
  (-dualPointCharacter G T t.2, primalPointCharacter G T t.1)

private theorem factorPairingCharacters_mul (T : Over (Spec R)) (x y : T ⟶ (P).X) :
    factorPairingCharacters G T (x * y) =
      factorPairingCharacters G T x + factorPairingCharacters G T y := by
  let e := splitPoints G T
  have h := map_mul e x y
  change (-dualPointCharacter G T (e (x * y)).2, primalPointCharacter G T (e (x * y)).1) = _
  rw [h]
  exact Prod.ext ((congrArg Neg.neg (dualPointCharacter_mul G T (e x).2 (e y).2)).trans (neg_add _ _))
    (primalPointCharacter_mul G T (e x).1 (e y).1)

/-- The actual alternating pairing defines a natural character of the split product for each
point of the same product. -/
def splitPairingCharacters : additivePoints (P).toGrp ⟶ characters P where
  app T := AddCommGrpCat.ofHom (AddMonoidHom.mk' (fun x =>
    (productCharactersEquiv G D T.unop).symm (factorPairingCharacters G T.unop x.toMul)) (by
    intro x y
    let e := (productCharactersEquiv G D T.unop).symm
    exact (congrArg e (factorPairingCharacters_mul G T.unop x.toMul y.toMul)).trans (map_add e _ _)))
  naturality T V a := by
    ext x
    let t := splitPoints G T.unop (Additive.toMul x)
    change (productCharactersEquiv G D V.unop).symm (factorPairingCharacters G V.unop (a.unop ≫ x.toMul)) =
      (characters P).map a.unop.op ((productCharactersEquiv G D T.unop).symm
        (-dualPointCharacter G T.unop t.2, primalPointCharacter G T.unop t.1))
    have h : splitPoints G V.unop (a.unop ≫ x.toMul) =
        (a.unop ≫ t.1, a.unop ≫ t.2) := productPointsEquiv_naturality G.toGrp (D).toGrp a.unop x.toMul
    unfold factorPairingCharacters
    rw [h, productCharactersEquiv_symm_restrict G (D) T.unop a.unop]
    change _ = (productCharactersEquiv G D V.unop).symm
      ((characters G).map a.unop.op (-dualPointCharacter G T.unop t.2),
        (characters D).map a.unop.op (primalPointCharacter G T.unop t.1))
    exact congrArg (productCharactersEquiv G D V.unop).symm
      (Prod.ext ((congrArg Neg.neg (dualPointCharacter_restrict G a.unop t.2)).symm.trans
        (map_neg (restrict G (Gm (Spec R)) a.unop) _).symm)
        (primalPointCharacter_restrict G a.unop t.1).symm)

private theorem dualPointCharacter_evaluation (T : Over (Spec R)) (y : T ⟶ (D).X) (x : T ⟶ G.X) :
    @characterEvaluation _ G T (dualPointCharacter G T y) x = finiteSchemePairing G T y x := by
  let b : G ⟶ specGroup R A := (specComparison G).inv
  let c : RelativeHom (specGroup R A) (Gm (Spec R)) T := characterOfPoint R A y
  let z : T ⟶ (specGroup R A).X := x ≫ b.toMul.hom.hom
  exact (evaluation_precompose b c x).trans (characterOfPoint_evaluation R A (T := T) y z)

private theorem primalPointCharacter_evaluation (T : Over (Spec R)) (x : T ⟶ G.X) (y : T ⟶ (D).X) :
    @characterEvaluation _ (D) T (primalPointCharacter G T x) y = finiteSchemePairing G T y x := by
  change evaluation (characterOfPoint R (Dual R A) (primalToBidual G T x)) y = _
  rw [characterOfPoint_evaluation]
  exact schemePairing_bidual R A T (x ≫ (specComparison G).inv.toMul.hom.hom) y

/-- Evaluation of the induced character is the original alternating evaluation. -/
theorem splitPairingCharacters_evaluation (T : Over (Spec R)) (x y : T ⟶ (P).X) :
    @characterEvaluation _ (P) T ((splitPairingCharacters G).app (op T) (Additive.ofMul x)) y =
      productWithDualPairing G T x y := by
  let e := productWithDualPoints G T
  change characterEvaluation ((productCharactersEquiv G D T).symm
    (-dualPointCharacter G T (e x).2, primalPointCharacter G T (e x).1)) y = _
  rw [productCharactersEquiv_evaluation, characterEvaluation_neg, productWithDualPairing_apply]
  change (characterEvaluation (dualPointCharacter G T (e x).2) (e y).1)⁻¹ *
      @characterEvaluation _ (D) T (primalPointCharacter G T (e x).1) (e y).2 =
    finiteSchemePairing G T (e y).2 (e x).1 * (finiteSchemePairing G T (e x).2 (e y).1)⁻¹
  rw [dualPointCharacter_evaluation, primalPointCharacter_evaluation, mul_comm]

private theorem primalToBidual_bijective (T : Over (Spec R)) : Function.Bijective (primalToBidual G T) := by
  let e := (AffineCoordinates.hopfSpecIso G.toGrp).symm
  let e₁ : G.X ≅ specOver R A := (Grp.forget (Over (Spec R))).mapIso e
  let e₂ : specOver R A ≅ specOver R (Dual R (Dual R A)) :=
    (algSpec R).mapIso (CommAlgCat.isoMk (bidualEquiv R A).symm.toAlgEquiv).op
  have hh₁ : Function.Bijective (fun x : T ⟶ G.X => x ≫ e₁.hom) := by
    refine ⟨fun _ _ h => (cancel_mono e₁.hom).mp h, fun y => ⟨y ≫ e₁.inv, ?_⟩⟩
    change (y ≫ e₁.inv) ≫ e₁.hom = y
    rw [Category.assoc, e₁.inv_hom_id, Category.comp_id]
  have hh₂ : Function.Bijective (fun x : T ⟶ specOver R A => x ≫ e₂.hom) := by
    refine ⟨fun _ _ h => (cancel_mono e₂.hom).mp h, fun y => ⟨y ≫ e₂.inv, ?_⟩⟩
    change (y ≫ e₂.inv) ≫ e₂.hom = y
    rw [Category.assoc, e₂.inv_hom_id, Category.comp_id]
  exact hh₂.comp hh₁

private theorem dualPointCharacter_affine_bijective (C : Type u) [CommRing C] [Algebra R C] :
    Function.Bijective (dualPointCharacter G (specOver R C)) := by
  let T := specOver R C
  let e := (charactersIso (specComparison G).symm).app (op T)
  let f := affineCharacterEquiv R A C
  exact e.addCommGroupIsoToAddEquiv.bijective.comp f.bijective

private theorem primalPointCharacter_affine_bijective (C : Type u) [CommRing C] [Algebra R C] :
    Function.Bijective (primalPointCharacter G (specOver R C)) :=
  (affineCharacterEquiv R (Dual R A) C).bijective.comp (primalToBidual_bijective G (specOver R C))

private theorem swappedPair_bijective {W X Y U V : Type u} [AddGroup U]
    (e : W ≃ X × Y) (f : Y → U) (g : X → V) (hf : Function.Bijective f) (hg : Function.Bijective g) :
    Function.Bijective (fun w => (-f (e w).2, g (e w).1)) := by
  let a := (Equiv.ofBijective f hf).trans (Equiv.neg U)
  let b := Equiv.ofBijective g hg
  exact (Equiv.prodCongr a b).bijective.comp ((Equiv.prodComm X Y).bijective.comp e.bijective)

private theorem factorPairingCharacters_affine_bijective (C : Type u) [CommRing C] [Algebra R C] :
    Function.Bijective (factorPairingCharacters G (specOver R C)) := by
  let T := specOver R C
  let e := splitPoints G T
  let f := dualPointCharacter G T
  let g := primalPointCharacter G T
  have h : Function.Bijective (fun w => (-f (e w).2, g (e w).1)) :=
    swappedPair_bijective e.toEquiv f g (dualPointCharacter_affine_bijective G C)
      (primalPointCharacter_affine_bijective G C)
  exact h

private theorem splitPairingCharacters_affine_bijective (C : Type u) [CommRing C] [Algebra R C] :
    Function.Bijective ((splitPairingCharacters G).app (op (specOver R C))) := by
  let T := specOver R C
  change Function.Bijective (fun x : Additive (T ⟶ (P).X) =>
    (productCharactersEquiv G D T).symm (factorPairingCharacters G T x.toMul))
  exact (productCharactersEquiv G D T).symm.bijective.comp
    ((factorPairingCharacters_affine_bijective G C).comp Additive.toMul.bijective)

/-- The alternating evaluation is perfect on all relative tests. -/
def splitPairingPerfect : additivePoints (P).toGrp ≅ characters P := by
  let : IsIso (splitPairingCharacters G) :=
    isIso_additivePoints_characters_of_bijective (splitPairingCharacters G)
      (splitPairingCharacters_affine_bijective G)
  exact asIso (splitPairingCharacters G)

end FiniteDual
end Langlands.GroupScheme.Cartier
