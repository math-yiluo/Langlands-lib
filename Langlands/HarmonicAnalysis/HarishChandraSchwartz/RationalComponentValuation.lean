import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitPositiveConstantTerm
import Langlands.BruhatTits.Cartan.RenardLeviCones
import Langlands.Representation.Jacquet.StandardCasselmanUniformAsymptotics
import Langlands.BruhatTits.SpecialCompact.JacquetStrictElement

/-! # Actual component valuations and a strict point for positive decay -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.GroupScheme Langlands.Plancherel
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) {q : A.toGrp ⟶ S.toGrp}

/-- The target's actual component valuation, packaged as a homomorphism to the
multiplicative copy of the real cocharacter space. -/
def rationalComponentValuation : rationalPoints A.toGrp →* Multiplicative (RealTorusSpace.V S) :=
  (BruhatTits.Cartan.centralizerValuation (Standard.leviTorusHom i ν ∅)
    (minimalLevi_restrictionEvaluation_bijective hG hi hν)).comp
      ((Standard.leviPointsEquiv i ν ∅).symm.toMonoidHom.comp
        ((rationalPoints.map (q ≫ i)).codRestrict (standardLeviPoints i ν ∅)
          (map_mem_standardLeviPoints_empty q)))

@[simp] theorem rationalComponentValuation_toAdd (x : rationalPoints A.toGrp) :
    (rationalComponentValuation hG hi hν (q := q) x).toAdd =
      rationalComponentH0 hG hi hν (qA := q) x := rfl

/-- Every integral character evaluates the actual component `H₀` to its
positive normalized character order after applying the specified torus map. -/
theorem eval_rationalComponentH0 (α : characterLattice S) (x : rationalPoints A.toGrp) :
    RealTorusSpace.eval S α (rationalComponentH0 hG hi hν (qA := q) x) =
      (BruhatTits.Cartan.RenardLeviCones.characterOrder S α (rationalPoints.map q x) : ℝ) := by
  have hpt :
      (Standard.leviPointsEquiv i ν ∅).symm
          ⟨rationalPoints.map (q ≫ i) x, map_mem_standardLeviPoints_empty q x⟩ =
        rationalPoints.map (Standard.leviTorusHom i ν ∅) (rationalPoints.map q x) := by
    apply (Standard.leviPointsEquiv i ν ∅).injective
    apply Subtype.ext
    rw [MulEquiv.apply_symm_apply, Standard.leviPointsEquiv_val]
    have h := congrArg (fun f : S.toGrp ⟶ G =>
      rationalPoints.map f (rationalPoints.map q x)) (Standard.leviTorusHom_comp i ν ∅)
    simpa only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc] using h.symm
  change RealTorusSpace.eval S α
    (BruhatTits.Cartan.centralizerValuation (Standard.leviTorusHom i ν ∅)
      (minimalLevi_restrictionEvaluation_bijective hG hi hν)
      ((Standard.leviPointsEquiv i ν ∅).symm
        ⟨rationalPoints.map (q ≫ i) x, map_mem_standardLeviPoints_empty q x⟩)).toAdd = _
  rw [hpt]
  exact BruhatTits.Cartan.RenardLeviCones.eval_centralizerValuation_map _ _ hi.1.1 α _

/-- On a uniformizer cocharacter value, the target's `H₀` has the source-positive sign. -/
theorem eval_rationalComponentH0_latticeSection (α : characterLattice S)
    (c : cocharacterLattice A) :
    RealTorusSpace.eval S α (rationalComponentH0 hG hi hν (qA := q)
      (CocharacterUniformizer.latticeSection F A (.ofAdd c))) =
      (latticePairing S α (RealTorusSpace.cocharacterMapInt (Additive.ofMul q : A ⟶ S) c) : ℝ) := by
  rw [eval_rationalComponentH0]
  change (BruhatTits.Cartan.RenardLeviCones.characterOrder S α
    (rationalPoints.map (CommGroupScheme.groupHom (Additive.ofMul q : A ⟶ S))
      (RenardCartan.uniformizerSection A (.ofAdd c))) : ℝ) = _
  rw [RenardCartan.uniformizerSection_naturality]
  exact congrArg (fun z : ℤ => (z : ℝ))
    (CocharacterUniformizer.rationalCharacterValuation_latticeSection F S α
      (RealTorusSpace.cocharacterMapInt (Additive.ofMul q : A ⟶ S) c))

variable {J : Set (characterLattice S)}
  (hA : IsCompatibleStandardSplitComponent i ν J A q)

include hA in
/-- An actual point of the specified component supplies exactly the vanishing and
strict inequalities on `H₀` used by the abstract positive-part recurrence. -/
theorem exists_rationalComponentH0_strict {ζ : cocharacterLattice S}
    (hζ : IsStandardCocharacter i ν J ζ) :
    ∃ x : rationalPoints A.toGrp,
      x ∈ CocharacterUniformizer.CA F A ∧
      (∀ β ∈ J, RealTorusSpace.eval S β
        (rationalComponentH0 hG hi hν (qA := q) x) = 0) ∧
      ∀ α ∈ simpleRelativeRoots i ν \ J, 0 < RealTorusSpace.eval S α
        (rationalComponentH0 hG hi hν (qA := q) x) := by
  obtain ⟨c, hc⟩ := hA.exists_cocharacter_lift i ν hi hζ
  have hcz : RealTorusSpace.cocharacterMapInt (Additive.ofMul q : A ⟶ S) c = ζ :=
    congrArg Additive.ofMul hc
  refine ⟨CocharacterUniformizer.latticeSection F A (.ofAdd c), ⟨.ofAdd c, rfl⟩, ?_, ?_⟩
  · intro β hβ
    rw [eval_rationalComponentH0_latticeSection, hcz, hζ.2.1 β hβ, Int.cast_zero]
  · rintro α ⟨hα, hαJ⟩
    rw [eval_rationalComponentH0_latticeSection, hcz]
    exact_mod_cast hζ.2.2 α hα hαJ

end Langlands.HarishChandraSchwartz
