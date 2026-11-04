import Langlands.GroupScheme.Absolute.SurjectiveCharacterPoint
import Langlands.GroupScheme.Absolute.RationalPointCommutativeSubgroup
import Langlands.GroupScheme.Commutative.NoTorus
import Langlands.GroupScheme.Torus.CocharacterSpecialization
import Langlands.GroupScheme.Rational.CharacterBaseChange

/-! # Characters vanish in the absence of cocharacters -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace rationalCharacters

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {A : Type u} [CommRing A] [Algebra k A] [Algebra K A] [IsScalarTower k K A]

/-- The unit obtained by evaluating a rational character is unchanged by actual base change. -/
theorem identity_characterValue_baseChange (χ : rationalCharacters G)
    (x : Lie.AffinePoints ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) A) :
    Lie.characterValue (𝟙 (Gm (Spec (CommRingCat.of K))))
      (x ≫ (baseChange (algebraBaseMap k K) χ).toMul.hom.hom) =
    Lie.characterValue (𝟙 (Gm (Spec (CommRingCat.of k))))
      (Lie.affineBaseChangeEquiv k K G A x ≫ χ.toMul.hom.hom) := by
  rw [CentralSurjectionImage.characterValue_id, CentralSurjectionImage.characterValue_id]
  let q := Units.mapEquiv
    (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.toMulEquiv
  change q (characterEval (baseChange (algebraBaseMap k K) χ) _ x) =
    q (characterEval χ _ (Lie.affineBaseChangeEquiv k K G A x))
  congr 1
  rw [characterEval_baseChange]
  change _ = characterEval χ _ ((Lie.affineBaseTestIso k K A).inv ≫
    GroupScheme.baseChangePointsEquiv (algebraBaseMap k K) G _ x)
  rw [characterEval_naturality]
  simp [Lie.affineBaseTestIso]
  rfl

end rationalCharacters

namespace AbsoluteNoCocharacter

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

/-- Over an algebraically closed field, a smooth connected affine group without
cocharacters has no nonzero rational characters. The source need not be commutative. -/
theorem character_eq_zero_of_gm_hom_eq_zero
    (hG : ∀ f : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G, f = 0)
    (χ : rationalCharacters G) : χ = 0 := by
  by_contra hχ
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨K, _, _, _, x, hx⟩ :=
    χ.exists_infiniteOrder_point_of_surjective (χ.surjective_of_ne_zero hχ)
  let b := algebraBaseMap k K
  let GK := (GroupScheme.baseChange b).obj G
  have : IsAffineHom GK.X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  have : IsAffine GK.X.left := isAffine_of_isAffineHom GK.X.hom
  have : LocallyOfFiniteType GK.X.hom := by
    change LocallyOfFiniteType (pullback.snd G.X.hom b)
    infer_instance
  let xK : Lie.AffinePoints GK K := (Lie.affineBaseChangeEquiv k K G K).symm x
  obtain ⟨C, z, y, hz, hy⟩ := rationalPointCommutativeSubgroup K GK xK
  let : IsClosedImmersion z.hom.hom.left := hz
  have : IsAffineHom C.toGrp.X.hom := by
    rw [← Over.w z.hom.hom]
    infer_instance
  have : LocallyOfFiniteType C.toGrp.X.hom := by
    rw [← Over.w z.hom.hom]
    infer_instance
  let χK := rationalCharacters.baseChange b χ
  let χC := characterRestrict z χK
  have hval : Lie.characterValue (rationalCharacters.equivCharacterLattice C χC) y =
      Lie.characterValue (𝟙 (Gm (Spec (CommRingCat.of k)))) (x ≫ χ.toMul.hom.hom) := by
    calc
      _ = Lie.characterValue (𝟙 (Gm (Spec (CommRingCat.of K))))
          ((y ≫ z.hom.hom) ≫ χK.toMul.hom.hom) := by
        rw [CentralSurjectionImage.characterValue_id]
        rw [Lie.characterValue, rationalCharacters.groupHom_equivCharacterLattice]
        rfl
      _ = Lie.characterValue (𝟙 (Gm (Spec (CommRingCat.of K))))
          (xK ≫ χK.toMul.hom.hom) := by rw [hy]
      _ = _ := by
        rw [rationalCharacters.identity_characterValue_baseChange]
        rw [show Lie.affineBaseChangeEquiv k K G K xK = x from
          (Lie.affineBaseChangeEquiv k K G K).apply_symm_apply x]
  have hynt : ∀ n : ℕ, n ≠ 0 →
      Lie.characterValue (rationalCharacters.equivCharacterLattice C χC) y ^ n ≠ 1 := by
    intro n hn
    rw [hval]
    exact hx n hn
  obtain ⟨nu, hnu⟩ := CentralSurjectionImage.exists_gm_characterRestrict_ne_zero_of_point y hynt
  apply hnu
  change nu ≫ χC.toMul = 0
  change nu ≫ (z ≫ χK.toMul) = 0
  rw [← Category.assoc, CocharacterSpecialization.gm_hom_eq_zero_of_baseField K hG (nu ≫ z),
    zero_comp]

/-- A smooth connected affine solvable group over an algebraically closed field is
unipotent when it has no nonzero cocharacters. -/
theorem isUnipotent_of_gm_hom_eq_zero (hsol : IsSolvableGroupScheme G)
    (hG : ∀ f : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G, f = 0) :
    IsUnipotent G :=
  hsol.isUnipotent_of_characters_eq_zero (character_eq_zero_of_gm_hom_eq_zero hG)

end AbsoluteNoCocharacter

/-- The algebraically closed solvable case of the no-cocharacter unipotence criterion. -/
def SolvableNoCocharacterUnipotentStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    IsSolvableGroupScheme G →
    (∀ f : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G, f = 0) → IsUnipotent G

/-- The cyclic commutative closure detects characters, and a triangular quotient
proves unipotence once all characters vanish. -/
theorem solvableNoCocharacterUnipotent : SolvableNoCocharacterUnipotentStatement.{u} := by
  intro k _ _ G _ _ _ hsol hG
  exact AbsoluteNoCocharacter.isUnipotent_of_gm_hom_eq_zero hsol hG

end Langlands.GroupScheme
