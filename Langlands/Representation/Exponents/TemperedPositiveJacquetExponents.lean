import Langlands.Representation.Exponents.BoundaryJacquetWitness
import Langlands.Representation.Exponents.PositiveExponentsUnitaryVanishing
import Langlands.Representation.Exponents.CasselmanSufficiencyAssembly

/-! # Strict exponent spectra of tempered representations -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local instance positiveTemperedAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]

section Spectrum

variable {P M U : GroupScheme (Spec (CommRingCat.of k))}
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
  (ha : IsSplitComponent a) (pres : ParabolicRootPresentation p l a)
  (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))

/-- The actual normalized Jacquet spectrum restricted to the strictly positive
cone of the specified compatible presentation. -/
def positiveJacquetExponents : Set (rationalPoints A.toGrp →* ℂˣ) :=
  {χ | IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ ∧
    Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ ∈
      pres.positiveCone}

@[simp]
theorem mem_positiveJacquetExponents (χ : rationalPoints A.toGrp →* ℂˣ) :
    χ ∈ positiveJacquetExponents p l r hp hl hr hmul ha pres π ↔
      IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ ∧
        Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ ∈
          pres.positiveCone :=
  Iff.rfl

/-- Every positive exponent is an exponent of the original normalized module. -/
theorem positiveJacquetExponents_subset_normalizedJacquetExponents :
    positiveJacquetExponents p l r hp hl hr hmul ha pres π ⊆
      normalizedJacquetExponents p l r hp hl hr hmul ha π :=
  fun _ hχ => hχ.1

end Spectrum

section UnitaryVanishing

variable (hG : IsConnectedReductive G)
  (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
  (hπ : IsNormalizedExponentTempered hG π)
  (hvan : ∀ (P M U : GroupScheme (Spec (CommRingCat.of k)))
    (A : CommGroupScheme (Spec (CommRingCat.of k)))
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (a : A.toGrp ⟶ M)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r)) (ha : IsSplitComponent a),
    ¬ IsIso p → unitaryJacquetPart p l r hp hl hr hmul ha π = ⊥)
  {P M U : GroupScheme (Spec (CommRingCat.of k))}
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
  (ha : IsSplitComponent a) (pres : ParabolicRootPresentation p l a)

include hG hπ hvan in
/-- If all proper unitary parts vanish, every tempered exponent is strictly
positive in every compatible presentation, including a full parabolic. -/
theorem normalizedRealPart_mem_positiveCone_of_unitaryJacquetParts_vanish
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ) :
    Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ ∈
      pres.positiveCone := by
  by_contra hstrict
  have hx := (hπ.parabolic p l a hp hl ha).2 pres U r hr hmul χ hχ
  let w := boundaryUnitaryJacquetWitness hG p l r hp hl hr hmul ha pres π hπ χ hχ
    hx hstrict
  exact w.unitaryJacquetPart_ne_bot
    (hvan w.Q w.L w.U w.A w.q w.l w.r w.a w.hq w.hl w.hr w.hmul w.ha w.proper)

/-- Under proper unitary vanishing, the original normalized spectrum is
canonically equivalent to its positive part, retaining each character. -/
def positiveJacquetExponentsEquivOfUnitaryVanishing :
    normalizedJacquetExponents p l r hp hl hr hmul ha π ≃
      positiveJacquetExponents p l r hp hl hr hmul ha pres π where
  toFun χ := ⟨χ.val, χ.property,
    normalizedRealPart_mem_positiveCone_of_unitaryJacquetParts_vanish
      hG π hπ hvan p l r hp hl hr hmul ha pres χ.val χ.property⟩
  invFun χ := ⟨χ.val, χ.property.1⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

@[simp]
theorem positiveJacquetExponentsEquivOfUnitaryVanishing_apply_val
    (χ : normalizedJacquetExponents p l r hp hl hr hmul ha π) :
    (positiveJacquetExponentsEquivOfUnitaryVanishing
      hG π hπ hvan p l r hp hl hr hmul ha pres χ).val = χ.val :=
  rfl

end UnitaryVanishing

/-- For a tempered representation, the exact all-parabolic positive-cone
condition is equivalent to vanishing of the unitary parts at all proper
actual parabolics. No analytic square-integrability criterion is used. -/
theorem hasPositiveRepresentedJacquetExponents_iff_unitaryJacquetParts_vanish
    (hG : IsConnectedReductive G)
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (hπ : IsNormalizedExponentTempered hG π) :
    HasPositiveRepresentedJacquetExponents π ↔
      ∀ (P M U : GroupScheme (Spec (CommRingCat.of k)))
        (A : CommGroupScheme (Spec (CommRingCat.of k)))
        (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (a : A.toGrp ⟶ M)
        (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
        (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
        (hmul : IsIso (subgroupMultiplication l r)) (ha : IsSplitComponent a),
        ¬ IsIso p → unitaryJacquetPart p l r hp hl hr hmul ha π = ⊥ := by
  constructor
  · intro hpos P M U A p l r a hp hl hr hmul ha hproper
    let pres := (hπ.nonempty_presentation p l a hp hl ha).some
    apply unitaryJacquetPart_eq_bot_of_positive_exponents
      hG p l r hp hl hr hmul ha pres π hproper
    intro χ hχ
    exact hpos P M U A p l r a hp hl hr hmul ha pres χ hχ
  · intro hvan P M U A p l r a hp hl hr hmul ha pres χ hχ
    exact normalizedRealPart_mem_positiveCone_of_unitaryJacquetParts_vanish
      hG π hπ hvan p l r hp hl hr hmul ha pres χ hχ

end Langlands.Aubert.General.RepresentedParabolic
