import Langlands.Global.AdelicIntertwiningRadicalIntersection
import Langlands.Global.AdelicLogSection
import Langlands.Representation.Exponents.GeometricLemmaExponentTransfer

/-! # Weyl transport on actual adelic positive split components -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions PositiveRealTorus

variable {F : Type u} [Field F] [NumberField F]
  {G P M Q M' : GroupScheme (Spec (CommRingCat.of F))}
  {p : P ⟶ G} {q : Q ⟶ G} {l : M ⟶ P} {l' : M' ⟶ Q} {π' : Q ⟶ M'}
  {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X} {c : M' ⟶ M}
  {A A' : CommGroupScheme (Spec (CommRingCat.of F))}
  {a : A.toGrp ⟶ M} {a' : A'.toGrp ⟶ M'}

set_option maxHeartbeats 600000 in
/-- The parabolic map used to pull back Weyl parameters carries the actual target
positive image into the source positive image. -/
theorem weylMap_positive [IsAffineHom M.X.hom]
    (ha : IsSplitComponent a) (ha' : IsSplitComponent a') (hc : IsIso c)
    (hπ' : l' ≫ π' = 𝟙 M') (x : intrinsicSubgroup F A') :
    map F Q P (π' ≫ c ≫ l) (positivePointMap F Q A' (a' ≫ l') x) ∈
      imageSubgroup F A P (a ≫ l) := by
  let : IsIso c := hc
  have hcent := (ha'.comp_iso (asIso c)).1
  obtain ⟨f, hf⟩ := ha.exists_factor ha'.1.1.1 hcent.2
  change f ≫ a = a' ≫ c at hf
  have hmem : pointMap F A'.toGrp A.toGrp (Adeles F) f x.val ∈ intrinsicSubgroup F A := by
    exact map_intrinsicSubgroup_le F A' A (Additive.ofMul f) ⟨x.val, x.property, rfl⟩
  refine ⟨pointMap F A'.toGrp A.toGrp (Adeles F) f x.val, hmem, ?_⟩
  have heq : f ≫ a ≫ l = (a' ≫ l') ≫ π' ≫ c ≫ l := by
    rw [← Category.assoc f a, hf]
    simp only [Category.assoc, ← Category.assoc l' π', hπ', Category.id_comp]
  change map F A.toGrp P (a ≫ l) (map F A'.toGrp A.toGrp f x.val) =
    map F Q P (π' ≫ c ≫ l) (map F A'.toGrp Q (a' ≫ l') x.val)
  rw [← map_comp_apply_of_hom f, ← map_comp_apply_of_hom (a' ≫ l'), heq]

/-- In the ambient adelic group, the map on a target positive point is conjugation
by the inverse rational representative. -/
theorem weylMap_positive_conjugation
    (hw : IsWeylConjugation p l q l' w c) (hπ' : l' ≫ π' = 𝟙 M')
    (x : intrinsicSubgroup F A') :
    map F P G p (map F Q P (π' ≫ c ≫ l) (positivePointMap F Q A' (a' ≫ l') x)) =
      (innerAdelicPoint F G w)⁻¹ *
        map F Q G q (positivePointMap F Q A' (a' ≫ l') x) * innerAdelicPoint F G w := by
  have heq : (a' ≫ l') ≫ (π' ≫ c ≫ l) ≫ p =
      ((a' ≫ l') ≫ q) ≫ (G.innerIso w).inv := by
    simp only [Category.assoc, ← Category.assoc l' π', hπ', Category.id_comp, hw.comp_eq]
  rw [positivePointMap_apply, ← map_comp_apply_of_hom, ← map_comp_apply_of_hom, heq,
    map_comp_apply_of_hom ((a' ≫ l') ≫ q), map_comp_apply_of_hom (a' ≫ l')]
  exact comp_innerIso_inv_adelic w _

omit [NumberField F] in
/-- The Weyl pullback of a parameter pairs with the actual log by applying the
covariant log map in the opposite direction. -/
theorem weylParameter_pairing (l : M ⟶ P) (c : M' ⟶ M) (π' : Q ⟶ M')
    (lam : ComplexCharacterParameter F P) (H : RealCharacterDual F Q) :
    complexParameterPairing F Q (weylParameter l c π' lam) H =
      complexParameterPairing F P lam (realCharacterDualMap F Q P (π' ≫ c ≫ l) H) := by
  induction lam using TensorProduct.inductionOn with
  | tmul z χ => rfl
  | add lam nu hlam hnu => simp only [map_add, LinearMap.add_apply, hlam, hnu]

/-- At any actual target point the Weyl parameter power is the source power at
its image under the parabolic map. -/
theorem weylParameter_power (l : M ⟶ P) (c : M' ⟶ M) (π' : Q ⟶ M')
    (lam : ComplexCharacterParameter F P) (x : AdelicGroupPoints F Q) :
    parameterPower F Q (weylParameter l c π' lam) x =
      parameterPower F P lam (map F Q P (π' ≫ c ≫ l) x) := by
  rw [parameterPower, parameterPower, characterLog_map, weylParameter_pairing]

/-- The actual Weyl conjugacy identifies the target positive left translates
with source positive left translates and transports their parameter powers. -/
def WeylPositiveTransportStatement (_ha : IsSplitComponent a) (_ha' : IsSplitComponent a')
    (_hw : IsWeylConjugation p l q l' w c) (_hπ' : l' ≫ π' = 𝟙 M') : Prop :=
  ∀ x : intrinsicSubgroup F A',
    let xQ := positivePointMap F Q A' (a' ≫ l') x
    let xP := map F Q P (π' ≫ c ≫ l) xQ
    xP ∈ imageSubgroup F A P (a ≫ l) ∧
    map F P G p xP = (innerAdelicPoint F G w)⁻¹ * map F Q G q xQ * innerAdelicPoint F G w ∧
    characterLog F P xP = realCharacterDualMap F Q P (π' ≫ c ≫ l) (characterLog F Q xQ) ∧
    ∀ lam : ComplexCharacterParameter F P,
      parameterPower F Q (weylParameter l c π' lam) xQ = parameterPower F P lam xP

theorem weylPositiveTransport [IsAffineHom M.X.hom] (ha : IsSplitComponent a) (ha' : IsSplitComponent a')
    (hw : IsWeylConjugation p l q l' w c) (hπ' : l' ≫ π' = 𝟙 M') :
    WeylPositiveTransportStatement ha ha' hw hπ' :=
  fun x => ⟨weylMap_positive ha ha' hw.isIso hπ' x, weylMap_positive_conjugation hw hπ' x,
    characterLog_map F Q P _ _, fun lam => weylParameter_power l c π' lam _⟩

end Langlands.Global.AdelicGroupPoints
