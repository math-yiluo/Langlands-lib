import Langlands.Representation.Derivative.MirabolicProductRestrictionStatement

/-!
# Rank-cast normal forms for the mirabolic restriction sequence

The three terms of `MirabolicProductRestrictionStatement` are rewritten so that
all of them end with the same rank cast `mirabolicRankCast` along
`(m + 1) + n = m + n + 1`, and exactness data are transported through that
cast.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative

open GeneralLinear

universe uF uV uW uD vD

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

namespace MirabolicProductRestriction

/-- The three exactness conditions of the statement at one pair of composable
morphisms of smooth representations. -/
def ExactAt {G : Type uF} [Group G] [TopologicalSpace G]
    {A B C : SmoothRep.{0, uF, uW} ℂ G} (f : A ⟶ B) (g : B ⟶ C) : Prop :=
  Function.Injective (SmoothRep.hom f) ∧
    LinearMap.range (SmoothRep.hom f).toLinearMap =
      LinearMap.ker (SmoothRep.hom g).toLinearMap ∧
    Function.Surjective (SmoothRep.hom g)

/-- Restriction after a rank cast is restriction followed by the mirabolic cast. -/
theorem generalLinearRankCast_comp_restriction (T : F.TopologicalData) {c d : ℕ}
    (h : c = d) (h' : c + 1 = d + 1) :
    letI := T.topology
    generalLinearRankCast.{uF, uW} T h' ⋙ generalLinearRestriction T d =
      generalLinearRestriction T c ⋙ mirabolicRankCast T h := by
  subst h
  rfl

/-- Two successive mirabolic rank casts are one cast. -/
theorem mirabolicRankCast_comp (T : F.TopologicalData) {a b c : ℕ} (h : a = b)
    (h' : b = c) :
    letI := T.topology
    mirabolicRankCast.{uF, uW} T h ⋙ mirabolicRankCast T h' =
      mirabolicRankCast T (h.trans h') := by
  subst h h'
  rfl

/-- Exactness data on functors to `P_(c+1)` give exactness data after a rank cast. -/
theorem exists_exact_comp_mirabolicRankCast (T : F.TopologicalData)
    {D : Type uD} [Category.{vD} D] {c d : ℕ} (h : c = d)
    {F₁ F₂ F₃ : letI := T.topology
      D ⥤ SmoothRep.{0, uF, uW} ℂ (mirabolic c F.Carrier)}
    (H : letI := T.topology
      ∃ (i : F₁ ⟶ F₂) (q : F₂ ⟶ F₃), ∀ X, ExactAt (i.app X) (q.app X)) :
    letI := T.topology
    ∃ (i : F₁ ⋙ mirabolicRankCast T h ⟶ F₂ ⋙ mirabolicRankCast T h)
      (q : F₂ ⋙ mirabolicRankCast T h ⟶ F₃ ⋙ mirabolicRankCast T h),
      ∀ X, ExactAt (i.app X) (q.app X) := by
  subst h
  exact H

/-- The identification `P_(c+1) ≅ P_(d+1)` along a rank equality, entrywise the
cast of indices. -/
def mirabolicCast {K : Type uF} [CommRing K] [TopologicalSpace K] {c d : ℕ} (h : c = d) :
    mirabolic c K ≃ₜ* mirabolic d K := by
  subst h
  exact ContinuousMulEquiv.refl _

theorem mirabolicCast_apply {K : Type uF} [CommRing K] [TopologicalSpace K] {c d : ℕ}
    (h : c = d) (g : mirabolic c K) (i j : Fin (d + 1)) :
    (mirabolicCast h g).val.val i j =
      g.val.val (Fin.cast (congrArg (· + 1) h).symm i) (Fin.cast (congrArg (· + 1) h).symm j) := by
  subst h
  rfl

/-- The mirabolic rank cast is pullback along `mirabolicCast`. -/
theorem mirabolicRankCast_eq_pullback (T : F.TopologicalData) {c d : ℕ} (h : c = d) :
    letI := T.topology
    mirabolicRankCast.{uF, uW} T h =
      MixedProductTensor.pullbackFunctor (mirabolicCast (K := F.Carrier) h.symm).toMonoidHom
        (mirabolicCast (K := F.Carrier) h.symm).continuous := by
  subst h
  rfl

variable (T : F.TopologicalData) (m n : ℕ)

theorem restrictedProduct_eq :
    letI := T.topology
    restrictedProduct.{uF, uV} T m n =
      T.binaryNormalizedProductFunctor (m + 1) (n + 1) ⋙
        generalLinearRestriction T ((m + 1) + n) ⋙
          mirabolicRankCast T (show (m + 1) + n = m + n + 1 by omega) := by
  let := T.topology
  change T.binaryNormalizedProductFunctor (m + 1) (n + 1) ⋙
      (generalLinearRankCast T (show (m + 1) + n + 1 = (m + n + 1) + 1 by omega) ⋙
        generalLinearRestriction T (m + n + 1)) = _
  rw [generalLinearRankCast_comp_restriction T (show (m + 1) + n = m + n + 1 by omega)]

theorem restrictionSubobject_eq :
    letI := T.topology
    restrictionSubobject.{uF, uV} T m n =
      ((generalLinearRestriction T m).prod
          (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier))) ⋙
        T.rightMixedProductFunctor (n + 1) m ⋙
          MixedProductTensor.pullbackFunctor
            (mirabolicCast (K := F.Carrier) (show (n + 1) + m = (m + 1) + n by omega).symm).toMonoidHom
            (mirabolicCast (K := F.Carrier) (show (n + 1) + m = (m + 1) + n by omega).symm).continuous) ⋙
        mirabolicRankCast T (show (m + 1) + n = m + n + 1 by omega) := by
  let := T.topology
  change _ ⋙ T.rightMixedProductFunctor (n + 1) m ⋙
      mirabolicRankCast T (show (n + 1) + m = m + n + 1 by omega) = _
  rw [← mirabolicRankCast_comp T (show (n + 1) + m = (m + 1) + n by omega)
    (show (m + 1) + n = m + n + 1 by omega),
    mirabolicRankCast_eq_pullback T (show (n + 1) + m = (m + 1) + n by omega)]
  rfl

theorem restrictionQuotient_eq :
    letI := T.topology
    restrictionQuotient.{uF, uV} T m n =
      ((𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier))).prod
          (generalLinearRestriction T n) ⋙
        T.leftMixedProductFunctor (m + 1) n) ⋙
        mirabolicRankCast T (show (m + 1) + n = m + n + 1 by omega) := rfl

end MirabolicProductRestriction

end Langlands.Derivative
