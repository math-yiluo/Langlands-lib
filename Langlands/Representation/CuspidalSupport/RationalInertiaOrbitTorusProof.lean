import Langlands.Representation.CuspidalSupport.RationalInertiaOrbitTorusStatement
import Langlands.Representation.CuspidalSupport.RationalInertiaOrbitTorusAlgebra
import Langlands.Representation.CuspidalSupport.RationalTwistStabilizerFiniteProof

/-! # Unramified orbits of irreducible representations are tori (Renard V.2.7) -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

section Stabilizer

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance instRationalInertiaOrbitTorus1 :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

local instance instRationalInertiaOrbitTorus2 :
    IsTopologicalGroup (GroupScheme.rationalPoints G) :=
  rationalPoint_isTopologicalGroup F G

/-- The stabilizer `X(G)(π)` of `A` under unramified twisting, as a subgroup. -/
def rationalTwistStabilizer (A : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) :
    Subgroup (unramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul)) where
  carrier := {s | Nonempty (rationalUnramifiedTwist G s A ≅ A)}
  one_mem' := ⟨rationalUnramifiedTwistOneIso G A⟩
  mul_mem' := by
    rintro s s' ⟨e⟩ ⟨e'⟩
    exact ⟨(rationalUnramifiedTwistMulIso G s s' A).symm ≪≫
      SmoothRep.twistIso s.val.toMonoidHom (isOpen_rationalUnramifiedCharacter_ker G s) e' ≪≫ e⟩
  inv_mem' := by
    rintro s ⟨e⟩
    exact ⟨(SmoothRep.twistIso (s⁻¹).val.toMonoidHom
        (isOpen_rationalUnramifiedCharacter_ker G s⁻¹) e).symm ≪≫
      rationalUnramifiedTwistMulIso G s⁻¹ s A ≪≫
      eqToIso (congrArg (fun ψ => rationalUnramifiedTwist G ψ A) (inv_mul_cancel s)) ≪≫
      rationalUnramifiedTwistOneIso G A⟩

/-- Two unramified twists of `A` are isomorphic exactly when the characters are
congruent modulo the stabilizer. -/
theorem nonempty_rationalUnramifiedTwist_iso_iff
    (A : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
    (χ χ' : unramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul)) :
    Nonempty (rationalUnramifiedTwist G χ A ≅ rationalUnramifiedTwist G χ' A) ↔
      χ⁻¹ * χ' ∈ rationalTwistStabilizer G A := by
  constructor
  · rintro ⟨e⟩
    exact ⟨(rationalUnramifiedTwistMulIso G χ⁻¹ χ' A).symm ≪≫
      (SmoothRep.twistIso (χ⁻¹).val.toMonoidHom
        (isOpen_rationalUnramifiedCharacter_ker G χ⁻¹) e).symm ≪≫
      rationalUnramifiedTwistMulIso G χ⁻¹ χ A ≪≫
      eqToIso (congrArg (fun ψ => rationalUnramifiedTwist G ψ A) (inv_mul_cancel χ)) ≪≫
      rationalUnramifiedTwistOneIso G A⟩
  · rintro ⟨e⟩
    exact ⟨(SmoothRep.twistIso χ.val.toMonoidHom
        (isOpen_rationalUnramifiedCharacter_ker G χ) e).symm ≪≫
      rationalUnramifiedTwistMulIso G χ (χ⁻¹ * χ') A ≪≫
      eqToIso (congrArg (fun ψ => rationalUnramifiedTwist G ψ A) (mul_inv_cancel_left χ χ'))⟩

/-- Descent of unramified characters to the valuation image, as a group
homomorphism into the characters of that image. -/
def rationalUnramifiedDescendHom :
    unramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul) →*
      (rationalDiscreteValuationImage G →* ℂˣ) where
  toFun χ := (rationalImageUnramifiedDescend G χ).toMonoidHom
  map_one' := by
    refine MonoidHom.ext fun a => ?_
    obtain ⟨g, rfl⟩ := rationalValuationImageProjection_surjective G a
    exact rationalImageUnramifiedDescend_projection G 1 g
  map_mul' χ ψ := by
    refine MonoidHom.ext fun a => ?_
    obtain ⟨g, rfl⟩ := rationalValuationImageProjection_surjective G a
    change rationalImageUnramifiedDescend G (χ * ψ) (rationalValuationImageProjection G g) =
      rationalImageUnramifiedDescend G χ (rationalValuationImageProjection G g) *
        rationalImageUnramifiedDescend G ψ (rationalValuationImageProjection G g)
    rw [rationalImageUnramifiedDescend_projection, rationalImageUnramifiedDescend_projection,
      rationalImageUnramifiedDescend_projection]
    rfl

omit [LocallyOfFiniteType G.X.hom] in
theorem rationalUnramifiedDescendHom_projection
    (χ : unramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul))
    (g : GroupScheme.rationalPoints G) :
    rationalUnramifiedDescendHom G χ (rationalValuationImageProjection G g) = χ.val g :=
  rationalImageUnramifiedDescend_projection G χ g

/-- Every character of the valuation image comes from a unique unramified character. -/
theorem rationalUnramifiedDescendHom_bijective :
    Function.Bijective (rationalUnramifiedDescendHom G) := by
  constructor
  · intro χ ψ h
    apply Subtype.ext
    apply ContinuousMonoidHom.ext
    intro g
    have h1 := DFunLike.congr_fun h (rationalValuationImageProjection G g)
    rwa [rationalUnramifiedDescendHom_projection, rationalUnramifiedDescendHom_projection] at h1
  · intro f
    refine ⟨rationalImageUnramifiedPullback G (continuous_rationalValuationImageProjection G)
      { toMonoidHom := f, continuous_toFun := continuous_of_discreteTopology }, ?_⟩
    refine MonoidHom.ext fun a => ?_
    obtain ⟨g, rfl⟩ := rationalValuationImageProjection_surjective G a
    exact rationalUnramifiedDescendHom_projection G _ g

/-- The coordinate evaluation of a monomial is the descended character value. -/
theorem rationalUnramifiedCoordinateEvaluation_single_apply
    (a : Additive (rationalDiscreteValuationImage G)) (c : ℂ)
    (χ : unramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul)) :
    rationalUnramifiedCoordinateEvaluation G (continuous_rationalValuationImageProjection G)
        (AddMonoidAlgebra.single a c) χ =
      c * (rationalUnramifiedDescendHom G χ a.toMul : ℂ) := by
  change rationalImageCoordinateEvaluation G _ (rationalImageUnramifiedDescend G χ) = _
  rw [rationalImageCoordinateEvaluation_single]
  rfl

end Stabilizer

/-- Renard V.2.7, Corollary and the following Notations paragraph: the orbit of
an irreducible representation under unramified twisting is `X(G)/X(G)(π)`, and
its algebra of polynomial functions `F^{X(G)(π)}` is a Laurent polynomial
algebra in `rank Λ(G)` variables whose complex points are the points of the
orbit. -/
theorem rationalInertiaOrbitTorus : RationalInertiaOrbitTorusStatement.{uF, uV} := by
  intro F _ _ _ _ G hG
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  have : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
    rationalPoint_isTopologicalGroup F G
  intro A hA S invariant
  have hp := continuous_rationalValuationImageProjection G
  have hfin : Finite (rationalTwistStabilizer G A) :=
    (rationalTwistStabilizerFinite F G hG A hA).to_subtype
  obtain ⟨Φ, hinj, hrange, hpts, horb⟩ :=
    OrbitTorus.exists_invariant_laurent (S := rationalTwistStabilizer G A)
      (rationalReductiveValuationBasis G hG) (rationalUnramifiedDescendHom_bijective G)
      (rationalUnramifiedCoordinateEvaluation_single_apply G)
      (rationalUnramifiedCoordinateEvaluation_injective G hp)
  have hinv : {f | f ∈ (rationalUnramifiedCoordinateEvaluation G hp).range ∧
      ∀ s ∈ rationalTwistStabilizer G A, ∀ χ, f (χ * s) = f χ} = invariant := by
    rw [rationalUnramifiedCoordinateEvaluation_range G hp]
    rfl
  rw [hinv] at hrange horb
  refine ⟨nonempty_rationalUnramifiedTwist_iso_iff G A, Φ, hinj, hrange, hpts, ?_⟩
  intro χ χ'
  exact (nonempty_rationalUnramifiedTwist_iso_iff G A χ χ').trans (horb χ χ')

end Langlands.CuspidalSupport
