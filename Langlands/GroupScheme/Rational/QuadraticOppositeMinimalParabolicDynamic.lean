import Langlands.GroupScheme.Rational.NumberFieldQuadraticOppositeMinimalParabolicLevi
import Langlands.GroupScheme.Rational.QuadraticOppositeTorusCell
import Langlands.GroupScheme.Rational.ParabolicLeviRealization
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalProof

/-! # A cocharacter for a quadratic opposite minimal parabolic and its Levi subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

private theorem centralizer_transportCocharacter' {B S : Scheme.{u}}
    (b : S ⟶ B) (a : S ⟶ S) (ha : a ≫ b = b) (G : GroupScheme B)
    (χ : (Gm S).toGrp ⟶ (GroupScheme.baseChange b).obj G) :
    Dynamic.centralizer (transportCocharacter b a ha G χ) =
      SubgroupFunctor.descentTransport b a ha G (Dynamic.centralizer χ) := by
  let e := descentBaseChangeIso b a ha G
  have he : transportCocharacter b a ha G χ ≫ e.inv =
      Dynamic.baseChangeCocharacter a χ := by
    simp only [transportCocharacter, Dynamic.baseChangeCocharacter, e, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [Dynamic.centralizer_eq_comap_of_iso _ e.symm, Iso.symm_hom, he, Dynamic.centralizer_baseChange]
  rfl

private theorem unipotent_transportCocharacter' {B S : Scheme.{u}}
    (b : S ⟶ B) (a : S ⟶ S) (ha : a ≫ b = b) (G : GroupScheme B)
    (χ : (Gm S).toGrp ⟶ (GroupScheme.baseChange b).obj G) :
    Dynamic.unipotent (transportCocharacter b a ha G χ) =
      SubgroupFunctor.descentTransport b a ha G (Dynamic.unipotent χ) := by
  let e := descentBaseChangeIso b a ha G
  have he : transportCocharacter b a ha G χ ≫ e.inv =
      Dynamic.baseChangeCocharacter a χ := by
    simp only [transportCocharacter, Dynamic.baseChangeCocharacter, e, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [Dynamic.unipotent_eq_comap_of_iso _ e.symm, Iso.symm_hom, he, Dynamic.unipotent_baseChange]
  rfl

/-- For a quadratic opposite minimal parabolic Levi subgroup `t : C ⟶ G`, there are a
cocharacter `χ` of `G_Q` whose dynamic centralizer is `C_Q` and the nonidentity automorphism `σ`
of `Q/F`, such that Galois conjugation by `σ` carries the positive unipotent subgroup `U(χ)` to
the negative one `U(-χ)`. -/
theorem IsQuadraticOppositeMinimalParabolicLevi.exists_dynamicData
    {F Q : Type u} [Field F] [Field Q] [Algebra F Q]
    {G C : GroupScheme (Spec (CommRingCat.of F))} {t : C ⟶ G}
    (hG : IsConnectedReductive G) (ht : IsQuadraticOppositeMinimalParabolicLevi Q t) :
    let b := algebraBaseMap F Q
    let GQ := (GroupScheme.baseChange b).obj G
    ∃ (σ : Q ≃ₐ[F] Q) (χ : (Gm (Spec (CommRingCat.of Q))).toGrp ⟶ GQ), σ ≠ 1 ∧
      Dynamic.centralizer χ = SubgroupFunctor.range ((GroupScheme.baseChange b).map t) ∧
      SubgroupFunctor.galoisTransport F Q G σ (Dynamic.unipotent χ) =
        Dynamic.unipotent (Dynamic.oppositeCocharacter χ) := by
  dsimp only
  let b := algebraBaseMap F Q
  let BC := GroupScheme.baseChange b
  let GQ := BC.obj G
  have hGQ : IsConnectedReductive GQ := connectedReductiveFieldExtensionStatement F Q G hG
  obtain ⟨_, _, σ, P, j, l, hσ, hj, hl, hlj, hinter⟩ := ht
  obtain ⟨χ, hP, hC⟩ := DynamicLeviConjugacy.exists_cocharacter_parabolic_levi parabolicDynamic
    dynamicGeometricUnipotentRadical hGQ hj.1 hl
  rw [hlj] at hC
  let a := galoisBaseMap F Q σ
  let ha := galoisBaseMap_over F Q σ
  let χσ := transportCocharacter b a ha G χ
  have hPσ : Dynamic.parabolic χσ = SubgroupFunctor.range (radicalGaloisHom j σ) := by
    rw [Dynamic.parabolic_transportCocharacter_eq_descentTransport, ← hP,
      SubgroupFunctor.descentTransport_range]
    rfl
  have hCσ : Dynamic.centralizer χσ = Dynamic.centralizer χ := by
    rw [centralizer_transportCocharacter', ← hC, SubgroupFunctor.range_baseChangeHom,
      SubgroupFunctor.descentTransport_baseChange]
  have hI : Dynamic.parabolic χ ⊓ Dynamic.parabolic χσ = Dynamic.centralizer χ := by
    rw [← hP, hPσ, ← hC]
    exact hinter
  have hI' := congrArg (fun A : SubgroupFunctor GQ => A.carrier
    (Over.mk (𝟙 (Spec (CommRingCat.of Q))))) hI
  have hU := (oppositeDynamicParabolicUniqueness Q GQ hGQ χ χσ hCσ hI').2
  exact ⟨σ, χ, hσ, hC.symm, (unipotent_transportCocharacter' b a ha G χ).symm.trans hU⟩

end Langlands.GroupScheme
