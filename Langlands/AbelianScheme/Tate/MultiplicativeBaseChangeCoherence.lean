import Langlands.AbelianScheme.Tate.MultiplicativeBaseChangeCoherenceStatement

noncomputable section
set_option maxHeartbeats 800000
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.Gm.TateComparison

universe u

private theorem levelEquiv_levelRestrict {S : Scheme.{u}} {T T' : Over S}
    (a : T' ⟶ T) (n : ℕ) (x : Tate.Level (Gm S).toGrp T n) :
    levelEquiv T' n (Tate.levelRestrict (Gm S).toGrp a n x) =
      TateTwist.levelMap a.left.appTop.hom n (levelEquiv T n x) :=
  levelEquiv_restrict a n x

/-- Identity coherence on finite multiplicative torsion sections. -/
theorem levelBaseChangeIdentity : LevelBaseChangeIdentity.{u} := by
  intro S T n x
  apply (levelEquiv ((Over.map (𝟙 S)).obj T) n).injective
  rw [levelEquiv_levelBaseChange]
  rw [levelEquiv_levelRestrict]
  simp only [Over.mapId_hom_app_left, Scheme.Hom.id_appTop]
  rfl

/-- Composition coherence on finite multiplicative torsion sections. -/
theorem levelBaseChangeComposition : LevelBaseChangeComposition.{u} := by
  intro S S' S'' b c T n x
  apply (levelEquiv ((Over.map (c ≫ b)).obj T) n).injective
  rw [levelEquiv_levelBaseChange]
  rw [levelEquiv_levelRestrict]
  simp only [Functor.comp_obj]
  rw [levelEquiv_levelBaseChange, levelEquiv_levelBaseChange]
  simp only [Over.mapComp_hom_app_left, Scheme.Hom.id_appTop]
  rfl

/-- Selected inverse-limit identity coherence follows coordinatewise. -/
theorem integralBaseChangeIdentity : IntegralBaseChangeIdentity.{u} := by
  intro S T P x
  apply Subtype.ext
  funext n
  exact levelBaseChangeIdentity S T n.val (x.val n)

/-- Selected inverse-limit composition coherence follows coordinatewise. -/
theorem integralBaseChangeComposition : IntegralBaseChangeComposition.{u} := by
  intro S S' S'' b c T P x
  apply Subtype.ext
  funext n
  exact levelBaseChangeComposition S S' S'' b c T n.val (x.val n)

/-- Prime-power inverse-limit identity coherence follows coordinatewise. -/
theorem primeIntegralBaseChangeIdentity : PrimeIntegralBaseChangeIdentity.{u} := by
  intro S T p hp x
  apply Subtype.ext
  funext n
  exact levelBaseChangeIdentity S T (p ^ n) (x.val n)

/-- Prime-power inverse-limit composition coherence follows coordinatewise. -/
theorem primeIntegralBaseChangeComposition : PrimeIntegralBaseChangeComposition.{u} := by
  intro S S' S'' b c T p hp x
  apply Subtype.ext
  funext n
  exact levelBaseChangeComposition S S' S'' b c T (p ^ n) (x.val n)

/-- Rationalization over the integers preserves identity coherence. -/
theorem rationalBaseChangeIdentity : RationalBaseChangeIdentity.{u} := by
  intro S T P x
  induction x using TensorProduct.inductionOn with
  | tmul q x =>
    simp only [rationalBaseChange_tmul, Tate.rationalTestRestrict_tmul]
    rw [integralBaseChangeIdentity S T P x]
  | add x y hx hy => simp_all

/-- Rationalization over the integers preserves composition coherence. -/
theorem rationalBaseChangeComposition : RationalBaseChangeComposition.{u} := by
  intro S S' S'' b c T P x
  induction x using TensorProduct.inductionOn with
  | tmul q x =>
    simp only [rationalBaseChange_tmul, Tate.rationalTestRestrict_tmul]
    rw [integralBaseChangeComposition S S' S'' b c T P x]
  | add x y hx hy => simp_all

/-- Extension from the p-adic integers preserves identity coherence. -/
theorem primeRationalBaseChangeIdentity : PrimeRationalBaseChangeIdentity.{u} := by
  intro S T p hp x
  have heq : (primeRationalBaseChange (𝟙 S) T p).toLinearMap =
      Tate.PrimeAdic.rationalTestRestrict (Gm S).toGrp p ((Over.mapId S).hom.app T) := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro q y
    change q ⊗ₜ[ℤ_[p]] primeIntegralBaseChange (𝟙 S) T p y =
      q ⊗ₜ[ℤ_[p]] Tate.PrimeAdic.testRestrict (Gm S).toGrp p
        ((Over.mapId S).hom.app T) y
    rw [primeIntegralBaseChangeIdentity]
  exact LinearMap.congr_fun heq x

/-- Extension from the p-adic integers preserves composition coherence. -/
theorem primeRationalBaseChangeComposition : PrimeRationalBaseChangeComposition.{u} := by
  intro S S' S'' b c T p hp x
  have heq : (primeRationalBaseChange (c ≫ b) T p).toLinearMap =
      (Tate.PrimeAdic.rationalTestRestrict (Gm S).toGrp p
        ((Over.mapComp c b).hom.app T)).comp
        ((primeRationalBaseChange b ((Over.map c).obj T) p).toLinearMap.comp
          (primeRationalBaseChange c T p).toLinearMap) := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro q y
    change q ⊗ₜ[ℤ_[p]] primeIntegralBaseChange (c ≫ b) T p y =
      q ⊗ₜ[ℤ_[p]] Tate.PrimeAdic.testRestrict (Gm S).toGrp p
        ((Over.mapComp c b).hom.app T)
        (primeIntegralBaseChange b ((Over.map c).obj T) p
          (primeIntegralBaseChange c T p y))
    rw [primeIntegralBaseChangeComposition]
  exact LinearMap.congr_fun heq x

/-- All five multiplicative Tate comparisons satisfy identity and composition coherence. -/
theorem multiplicativeBaseChangeCoherence : MultiplicativeBaseChangeCoherence.{u} :=
  ⟨levelBaseChangeIdentity, levelBaseChangeComposition,
    integralBaseChangeIdentity, integralBaseChangeComposition,
    primeIntegralBaseChangeIdentity, primeIntegralBaseChangeComposition,
    rationalBaseChangeIdentity, rationalBaseChangeComposition,
    primeRationalBaseChangeIdentity, primeRationalBaseChangeComposition⟩

end Langlands.GroupScheme.Gm.TateComparison
