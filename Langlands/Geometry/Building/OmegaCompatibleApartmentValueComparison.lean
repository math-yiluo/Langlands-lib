import Langlands.Geometry.Building.ApartmentRootReflections

/-! # Valuation values from equivariant affine apartment comparisons -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.Plancherel

namespace Langlands.Geometry.Building

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G)
    {α : relativeRoots B.i} {g : rationalPoints G}
    {p : rationalPoints G × rationalPoints G}

/-- Applying the root to an actual reflection displacement recovers twice the
negative valuation value. -/
theorem rootForm_reflectionElement_vsub
    (hg : g ∈ B.rootGroup α) (hg1 : g ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) g p)
    (x : B.Apartment) :
    rootForm B.i α (B.reflectionElement hp • x -ᵥ x) =
      -2 * B.reflectionFunctional α g x := by
  have hact : B.reflectionElement hp • x =
      (-B.reflectionFunctional α g x) • B.reflectionCoroot hg hg1 hp +ᵥ x :=
    DFunLike.congr_fun (B.normalizerAffineEquiv_reflectionElement hg hg1 hp) x
  rw [hact, vadd_vsub, map_smul,
    B.rootForm_reflectionCoroot hg hg1 hp, smul_eq_mul]
  ring

end ValuationBuildingData

namespace KPApartmentData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))}
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    (D E : KPApartmentData i (localFieldOrder F))
    (C : CentralizerDatum i)
    (hD : D.IsOmegaCompatible C) (hE : E.IsOmegaCompatible C)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)

include C hD hE hG hi in
/-- An equivariant affine comparison with identity derivative preserves the
valuation value of every nonidentity root point admitting an actual opposite
factor pair. -/
theorem value_eq_of_equivariant_affineEquiv_of_oppositeFactorPair
    (f : D.Apartment ≃ᵃ[ℝ] E.Apartment)
    (hlinear : f.linear = LinearEquiv.refl ℝ (TranslationSpace i))
    (hequiv : ∀ (n : normalizerPoints i) (x : D.Apartment), f (n • x) = n • f x)
    (α : relativeRoots i) (g : rationalPoints G)
    (hg : g ∈ rootGroupPoints i α) (hg1 : g ≠ 1)
    (p : rationalPoints G × rationalPoints G)
    (hp : RelativeRoot.IsOppositeFactorPair i (α : characterLattice S) g p)
    (x : D.Apartment) :
    (f x).val α g = x.val α g := by
  let B : ValuationBuildingData G :=
    ⟨hG, S, i, hi, D, C, hD⟩
  let B' : ValuationBuildingData G :=
    ⟨hG, S, i, hi, E, C, hE⟩
  let m : normalizerPoints i := ⟨p.1 * g * p.2, hp.2.2⟩
  have hdisp : m • f x -ᵥ f x = m • x -ᵥ x := by
    rw [← hequiv]
    have hf := f.toAffineMap.linearMap_vsub (m • x) x
    change f.linear (m • x -ᵥ x) = f (m • x) -ᵥ f x at hf
    rw [hlinear, LinearEquiv.refl_apply] at hf
    exact hf.symm
  have hleft := B.rootForm_reflectionElement_vsub hg hg1 hp x
  have hright := B'.rootForm_reflectionElement_vsub hg hg1 hp (f x)
  change rootForm i α (m • x -ᵥ x) = -2 * B.reflectionFunctional α g x at hleft
  change rootForm i α (m • f x -ᵥ f x) =
    -2 * B'.reflectionFunctional α g (f x) at hright
  rw [hdisp, hleft] at hright
  have hvalue : B'.reflectionFunctional α g (f x) = B.reflectionFunctional α g x := by
    linarith
  rw [← B'.coe_reflectionFunctional_apply hg hg1 (f x),
    ← B.coe_reflectionFunctional_apply hg hg1 x, hvalue]

end KPApartmentData

/-- The rank-one value-identification assertion for a supplied actual opposite
factor pair; this does not assert existence of such pairs. -/
def OmegaCompatibleApartmentValueComparisonStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (S : CommGroupScheme (Spec (CommRingCat.of F)))
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (i : S.toGrp ⟶ G) [Mono i.hom.hom.left]
    (D E : KPApartmentData i (localFieldOrder F)) (C : CentralizerDatum i),
    D.IsOmegaCompatible C → E.IsOmegaCompatible C →
    IsConnectedReductive G → IsMaximalSplitTorus i →
    ∀ (f : D.Apartment ≃ᵃ[ℝ] E.Apartment),
      f.linear = LinearEquiv.refl ℝ (TranslationSpace i) →
      (∀ (n : normalizerPoints i) (x : D.Apartment), f (n • x) = n • f x) →
      ∀ (α : relativeRoots i) (g : rationalPoints G),
        g ∈ rootGroupPoints i α → g ≠ 1 →
        ∀ (p : rationalPoints G × rationalPoints G),
          RelativeRoot.IsOppositeFactorPair i (α : characterLattice S) g p →
          ∀ (x : D.Apartment), (f x).val α g = x.val α g

/-- The implemented root-displacement argument proves the full conditional
value-comparison assertion in every universe. -/
theorem omegaCompatibleApartmentValueComparison :
    OmegaCompatibleApartmentValueComparisonStatement.{u} := by
  intro F _ _ _ _ S G _ i _ D E C hD hE hG hi f hlinear hequiv α g hg hg1 p hp x
  exact D.value_eq_of_equivariant_affineEquiv_of_oppositeFactorPair E C hD hE hG hi
    f hlinear hequiv α g hg hg1 p hp x

end Langlands.Geometry.Building
