import Langlands.Global.AdelicGaloisTwistNormOne

/-! # Proof that Galois twisting preserves norm-one adelic points (Lemma C) -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.Global.AdelicGaloisUnit

open Langlands.GroupScheme AdelicGroupPoints AdelicSiegelFactors GaloisPointComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Generic

variable {S S' : Scheme.{u}} (a : S' ⟶ S) [IsIso a]

/-- Pullback along an isomorphism of schemes has an invertible counit. -/
instance isIso_mapPullbackAdj_counit : IsIso (Over.mapPullbackAdj a).counit := by
  have h : ∀ Z : Over S, IsIso ((Over.mapPullbackAdj a).counit.app Z) := by
    intro Z
    have : IsIso ((Over.forget S).map ((Over.mapPullbackAdj a).counit.app Z)) := by
      change IsIso (pullback.fst Z.hom a)
      infer_instance
    exact isIso_of_reflects_iso _ (Over.forget S)
  exact NatIso.isIso_of_isIso_app _

/-- Base change of group schemes along an isomorphism of schemes is fully faithful. -/
def baseChangeFullyFaithful : (GroupScheme.baseChange a).FullyFaithful :=
  (Over.mapPullbackAdj a).fullyFaithfulROfIsIsoCounit.mapGrp

/-- Every character of a base change along an isomorphism is the base change of a
character, followed by the canonical identification of the base-changed `𝔾_m`. -/
theorem exists_baseChange_character {G : GroupScheme S}
    (ψ : (GroupScheme.baseChange a).obj G ⟶ (GroupScheme.Gm S').toGrp) :
    ∃ χ : G ⟶ (GroupScheme.Gm S).toGrp,
      ψ = (GroupScheme.baseChange a).map χ ≫ (GroupScheme.Gm.baseChangeIso a).hom := by
  refine ⟨(baseChangeFullyFaithful a).preimage (ψ ≫ (GroupScheme.Gm.baseChangeIso a).inv), ?_⟩
  rw [Functor.FullyFaithful.map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Generic

variable {F L : Type u} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]

omit [NumberField F] [NumberField L] in
/-- `Spec σ` is an isomorphism. -/
theorem isIso_galoisBaseMap (σ : L ≃ₐ[F] L) : IsIso (galoisBaseMap F L σ) := by
  change IsIso (Spec.map (σ.toRingEquiv.toCommRingCatIso.hom))
  infer_instance

omit [NumberField L] in
/-- The value of an actual character evaluation, through the global sections of the
spectrum of the coefficient algebra. -/
theorem characterUnits_val (G : GroupScheme (Spec (CommRingCat.of L)))
    (χ : AlgebraicCharacter L G) (A : CommAlgCat.{u} (CommRingCat.of L))
    (x : G.affinePoints A) :
    (characterUnits L G χ A x : A) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom
        (GroupScheme.Gm.pointsEquiv (Spec (CommRingCat.of L))
          ((algSpec (CommRingCat.of L)).obj (op A)) (x ≫ χ.hom.hom)).val :=
  rfl

/-- Character values of a Galois-twisted point are the Galois conjugates of the character
values of the original point. -/
theorem character_twistPoint (σ : L ≃ₐ[F] L) (H : GroupScheme (Spec (CommRingCat.of L)))
    (p : adeleTest L ⟶ H.X) (χ : AlgebraicCharacter L H)
    (ψ : AlgebraicCharacter L ((GroupScheme.baseChange (galoisBaseMap F L σ)).obj H))
    (hψ : ψ = (GroupScheme.baseChange (galoisBaseMap F L σ)).map χ ≫
      (GroupScheme.Gm.baseChangeIso (galoisBaseMap F L σ)).hom) :
    character L _ ψ (twistPoint F L σ H p) =
      AdeleGalois.idelesMap σ (character L H χ (p : AdelicGroupPoints L H)) := by
  apply Units.ext
  rw [AdeleGalois.idelesMap_val]
  change (characterUnits L _ ψ _ (twistPoint F L σ H p) : Adeles L) =
    AdeleGalois.ringEquiv F L σ (characterUnits L H χ _ p : Adeles L)
  rw [characterUnits_val, characterUnits_val]
  have hpts : GroupScheme.Gm.pointsEquiv (Spec (CommRingCat.of L)) (adeleTest L)
      (twistPoint F L σ H p ≫ ψ.hom.hom) =
      Units.map (adeleTestIso F L σ).hom.left.appTop.hom.toMonoidHom
        (GroupScheme.Gm.pointsEquiv (Spec (CommRingCat.of L)) (adeleTest L)
          (p ≫ χ.hom.hom)) := by
    rw [hψ, Grp.comp_hom_hom, ← Category.assoc,
      GroupScheme.Gm.pointsEquiv_baseChangeIso_hom, GroupScheme.Gm.baseChangeUnitsEquiv_apply,
      baseChangePointsEquiv_comp, baseChangePointsEquiv_twistPoint, Category.assoc,
      GroupScheme.Gm.pointsEquiv_naturality]
  change (Scheme.ΓSpecIso (CommRingCat.of (Adeles L))).hom
      (GroupScheme.Gm.pointsEquiv (Spec (CommRingCat.of L)) (adeleTest L)
        (twistPoint F L σ H p ≫ ψ.hom.hom)).val = _
  rw [hpts, Units.coe_map, adeleTestIso_hom_left]
  change ((Spec.map (CommRingCat.ofHom (AdeleGalois.ringEquiv F L σ : Adeles L →+* Adeles L))).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of (Adeles L))).hom) _ = _
  rw [Scheme.ΓSpecIso_naturality]
  rfl

/-- Lemma C: Galois twisting preserves norm-one adelic points. -/
theorem twistPoint_mem_normOneSubgroup : TwistPointNormOneStatement.{u} := by
  intro F L _ _ _ _ _ _ _ σ H p hp
  have := isIso_galoisBaseMap σ
  rw [mem_normOneSubgroup] at hp ⊢
  intro ψ
  obtain ⟨χ, hχ⟩ := exists_baseChange_character (galoisBaseMap F L σ) ψ
  change IdeleAbsoluteValue.full L (character L _ ψ (twistPoint F L σ H p)) = 1
  rw [character_twistPoint σ H p χ ψ hχ, AdeleGalois.full_idelesMap]
  exact hp χ

end Langlands.Global.AdelicGaloisUnit
