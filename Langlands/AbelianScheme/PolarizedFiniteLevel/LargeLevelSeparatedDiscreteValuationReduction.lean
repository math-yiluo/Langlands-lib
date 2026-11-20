import Langlands.AlgebraicGeometry.Picard.DiscreteValuativeClosedIrreducibleImagesProof
import Langlands.AbelianScheme.PolarizedFiniteLevel.DiscreteValuationDatumUniquenessStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.LargeLevelSeparatedStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.LargeLevelFiniteTypeStatement
import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-! # Separatedness of the moduli scheme from discrete valuative uniqueness of data -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Noetherian valuative criterion for separatedness (Stacks Lemma 32.15.2, (3) ⇒ (1)): over
a locally noetherian base, a morphism locally of finite type is separated if valuative squares
with a discrete valuation ring have at most one lift. -/
theorem isSeparated_of_discreteValuativeUniqueness {X S : Scheme.{u}} [IsLocallyNoetherian S]
    (f : X ⟶ S) [LocallyOfFiniteType f]
    (hf : ∀ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R →
      Subsingleton sq.commSq.LiftStruct) :
    IsSeparated f where
  isClosedImmersion_diagonal := by
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    have hE : DiscreteValuativeCriterion.Existence (pullback.diagonal f) := by
      intro S hS
      have hc : CommSq S.i₁ (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)))
          f (S.i₂ ≫ pullback.fst f f ≫ f) := ⟨by simp [← S.commSq.w_assoc]⟩
      let S' : ValuativeCommSq f := ⟨S.R, S.K, S.i₁, S.i₂ ≫ pullback.fst f f ≫ f, hc⟩
      have : Subsingleton S'.commSq.LiftStruct := hf S' hS
      let S'l₁ : S'.commSq.LiftStruct := ⟨S.i₂ ≫ pullback.fst f f,
        by simp [S', ← S.commSq.w_assoc], by simp [S']⟩
      let S'l₂ : S'.commSq.LiftStruct := ⟨S.i₂ ≫ pullback.snd f f,
        by simp [S', ← S.commSq.w_assoc], by simp [S', pullback.condition]⟩
      have h₁₂ : S'l₁ = S'l₂ := Subsingleton.elim _ _
      constructor
      constructor
      refine ⟨S.i₂ ≫ pullback.fst _ _, ?_, ?_⟩
      · simp [← S.commSq.w_assoc]
      · simp only [Category.assoc]
        apply IsPullback.hom_ext (IsPullback.of_hasPullback _ _)
        · simp
        · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id]
          exact congrArg CommSq.LiftStruct.l h₁₂
    have hsp : SpecializingMap (pullback.diagonal f) :=
      DiscreteValuativeCriterion.Existence.specializingMap (pullback.diagonal f) hE
    have hcl : IsClosedMap (pullback.diagonal f) :=
      (isClosedMap_iff_specializingMap _).mpr hsp
    exact .of_isPreimmersion _ hcl.isClosed_range

end Langlands.AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

set_option linter.defProp false in
/-- Proved definition: eventual local finite type of representing level bases and uniqueness
of data over discrete valuation rings (in universe zero) imply `LargeLevelSeparatedStatement`.
Two lifts in a discrete valuative square give two data over `Spec R` whose pullbacks to the
fraction field agree; uniqueness identifies them, and the representing isomorphism identifies
the lifts. -/
def largeLevelSeparated_of_datumUniqueness (Hft : LargeLevelFiniteTypeStatement)
    (H : DiscreteValuationDatumUniquenessStatement.{0}) : LargeLevelSeparatedStatement := by
  intro P g d hg hd
  obtain ⟨N, hN⟩ := Hft P g d hg hd
  refine ⟨N, fun n hn' hn X ⟨e⟩ => ?_⟩
  have : LocallyOfFiniteType X.toLocalizationSpec := (hN n hn' hn X ⟨e⟩).1
  apply Langlands.AlgebraicGeometry.isSeparated_of_discreteValuativeUniqueness
  intro sq hR
  let R := sq.R
  let K := sq.K
  let ι : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R K))
  have hunit : IsUnit (n : Γ(Spec (CommRingCat.of R), ⊤)) := by
    rw [← map_natCast sq.i₂.appTop.hom n]
    exact (LevelBase.localizationSpec n).level_isUnit.map _
  have hunitK : IsUnit (n : Γ(Spec (CommRingCat.of K), ⊤)) := by
    rw [← map_natCast ι.appTop.hom n]
    exact hunit.map _
  have hunitR : IsUnit (n : R) := by
    rw [← map_natCast (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom n]
    exact hunit.map _
  let T : LevelBase n := LevelBase.ofScheme (Spec (CommRingCat.of R)) hunit
  let TK : LevelBase n := LevelBase.ofScheme (Spec (CommRingCat.of K)) hunitK
  let ιT : TK ⟶ T := LevelBase.homMk ι
  constructor
  intro l₁ l₂
  let φ : sq.commSq.LiftStruct → (uliftYoneda.{1}.obj X).obj (Opposite.op T) :=
    fun l => ULift.up (LevelBase.homMk (S := T) (T := X) l.l)
  have key : ∀ l : sq.commSq.LiftStruct,
      (moduliFunctor P g d n hd hn).map ιT.op (e.hom.app (Opposite.op T) (φ l)) =
        e.hom.app (Opposite.op TK)
          (ULift.up (LevelBase.homMk (S := TK) (T := X) sq.i₁)) := by
    intro l
    rw [← NatTrans.naturality_apply]
    congr 1
    apply ULift.ext
    apply (LevelBase.homEquiv TK X).injective
    exact l.fac_left
  obtain ⟨a₁, ha₁⟩ := Quotient.exists_rep
    (e.hom.app (Opposite.op T) (φ l₁) : Moduli P T.obj g d n)
  obtain ⟨a₂, ha₂⟩ := Quotient.exists_rep
    (e.hom.app (Opposite.op T) (φ l₂) : Moduli P T.obj g d n)
  have hK : (a₁.pullback ι).classOf = (a₂.pullback ι).classOf := by
    have h₁ := key l₁
    have h₂ := key l₂
    rw [← ha₁] at h₁
    rw [← ha₂] at h₂
    exact h₁.trans h₂.symm
  have hiso : Isomorphic a₁ a₂ :=
    H P g d n R K hunitR a₁ a₂ (Quotient.exact hK)
  have hx : e.hom.app (Opposite.op T) (φ l₁) = e.hom.app (Opposite.op T) (φ l₂) := by
    rw [← ha₁, ← ha₂]
    exact Quotient.sound hiso
  have hy : φ l₁ = φ l₂ :=
    (CategoryTheory.mono_iff_injective (e.hom.app (Opposite.op T))).1 inferInstance hx
  have hl : l₁.l = l₂.l := congrArg (fun z => z.down.hom) hy
  cases l₁
  cases l₂
  cases hl
  rfl

end Langlands.AbelianScheme.PolarizedFiniteLevel
