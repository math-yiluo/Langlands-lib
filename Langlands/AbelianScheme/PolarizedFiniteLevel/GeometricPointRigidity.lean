import Langlands.AbelianScheme.PolarizedFiniteLevel.PullbackCoherence
import Langlands.AbelianScheme.PolarizedFiniteLevel.TorsionConfigurationRigidity
import Langlands.AlgebraicGeometry.FactorizationOfGlobalFunctionsProof
import Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof
import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameLocusCoverReduction
import Langlands.AbelianScheme.PolarizedFiniteLevel.CanonicalCubicRigidity
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Polarized automorphisms that are trivial at every geometric point -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard
open Langlands.AlgebraicGeometry.Modules.DerivedSections

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

variable {S : Scheme.{u}}

/-- An endomorphism of an abelian scheme whose base change to every geometric point
with algebraically closed residue field is the identity is the identity. -/
theorem hom_eq_id_of_geometricPoints (A : AbelianScheme S) (f : A ⟶ A)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (b : Spec (CommRingCat.of K) ⟶ S),
      hom ((baseChange b).map f) = 𝟙 _) :
    hom f = 𝟙 A.X.left := by
  let X : Over S := A.X
  let φ : X ⟶ X := (groupHom f).hom.hom
  let δ : X ⟶ X := φ / 𝟙 X
  have hφ : η[X] ≫ φ = η[X] := IsMonHom.one_hom φ
  have hδe : η[X] ≫ δ = 1 := by
    simp only [δ, GrpObj.comp_div, hφ, Category.comp_id, div_self']
  have hδe' : η[X].left ≫ δ.left = η[X].left := by
    change (η[X] ≫ δ).left = η[X].left
    rw [hδe, ← MonObj.one_eq_one]
  have hfibre : ∀ (K : Type u) [Field K] [IsAlgClosed K] (b : Spec (CommRingCat.of K) ⟶ S),
      (Over.pullback b).map δ = (Over.pullback b).map (1 : X ⟶ X) := by
    intro K _ _ b
    have hb : (Over.pullback b).map φ = 𝟙 _ := Over.OverMorphism.ext (h K b)
    simp only [δ, div_eq_mul_inv, Functor.map_mul, Functor.map_inv',
      Functor.map_one, hb, CategoryTheory.Functor.map_id, mul_inv_cancel]
  have hpoint : ∀ x : X.left, δ.left x = (1 : X ⟶ X).left x := by
    intro x
    let s := X.hom x
    let K := AlgebraicClosure (S.residueField s)
    let b : Spec (CommRingCat.of K) ⟶ S :=
      Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) K)) ≫
        S.fromSpecResidueField s
    let z : Spec (CommRingCat.of K) := default
    have hz : b z = X.hom x := by
      rw [Scheme.Hom.comp_apply]
      exact Scheme.fromSpecResidueField_apply s _
    obtain ⟨y, hy, -⟩ := Scheme.Pullback.exists_preimage_pullback x z hz.symm
    have hh := congrArg (fun k => k.left ≫ Limits.pullback.fst X.hom b) (hfibre K b)
    simp only [Over.pullback_map_left, Limits.pullback.lift_fst] at hh
    have hh' := congrArg (fun k : _ ⟶ X.left => k y) hh
    simp only [Scheme.Hom.comp_apply, hy] at hh'
    exact hh'
  have hglob := Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions
    X.left S X.hom A.smooth A.proper A.geometricallyConnected
  have hfactor := Langlands.AlgebraicGeometry.factorizationOfGlobalFunctions
    X.left S X.left X.hom η[X].left δ.left η[X].w hglob (fun x => by
      rw [hδe', hpoint x]
      rfl)
  have hδ : δ = 1 := by
    apply Over.OverMorphism.ext
    rw [hfactor, hδe']
    rfl
  have hφ1 : φ = 𝟙 X := div_eq_one.mp hδ
  exact congrArg CommaMorphism.left hφ1

variable {P : Prerequisites.{u}} {g d n : ℕ} {a : Datum P S g d n}

/-- A polarized automorphism whose pullback to every algebraically closed geometric
point is the identity is itself the identity. -/
theorem PolarizedIso.eq_refl_of_geometricPoints (α : PolarizedIso a a)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (b : Spec (CommRingCat.of K) ⟶ S),
      α.pullback b = PolarizedIso.refl (a.pullback b)) :
    α = PolarizedIso.refl a := by
  apply α.eq_refl_of_hom_eq_id
  apply hom_eq_id_of_geometricPoints
  intro K _ _ b
  exact congrArg (fun e : PolarizedIso (a.pullback b) (a.pullback b) =>
    hom e.abelianIso.hom) (h K b)

set_option backward.isDefEq.respectTransparency false in
/-- **Rigidity over an algebraically closed field at large level.** Assume Lefschetz's
theorem `CubicFieldEmbeddingStatement`. Over an algebraically closed field in which `n` is
nonzero, with `n > (6^g d) * (6^g d g!)`, every polarized automorphism of an ordinary
polarized full-level datum is the identity. -/
theorem PolarizedIso.eq_refl_of_field_of_cubicFieldEmbedding
    (hL : CubicFieldEmbeddingStatement.{u}) (hg : 0 < g) (hd : 0 < d)
    (hN : (cubicProjectiveDimension g d + 1) * (6 ^ g * d * Nat.factorial g) < n)
    {K : Type u} [Field K] [IsAlgClosed K] {a : Datum P (Spec (CommRingCat.of K)) g d n}
    (hnK : (n : K) ≠ 0) (α : PolarizedIso a a) :
    α = PolarizedIso.refl a := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hN
  have hFP := Langlands.AlgebraicGeometry.Modules.isFinitePresentation_of_hasFiniteLocalBasis _
    (hasFiniteLocalBasis_of_isLocallyFreeOfRank
      (cubicDirectImage P (Spec (CommRingCat.of K)) g d n hd a).1)
  have : Epi a.cubicEvaluationAdjoint := (hL P K g d n hd a).1
  let V := (relativeGlobalSections a.abelian.X.hom).obj a.cubicBundle.obj
  have hV : Module.finrank K V = cubicProjectiveDimension g d + 1 := a.finrank_cubicSections hd
  have : FiniteDimensional K V := Module.finite_of_finrank_eq_succ hV
  let β : Module.Basis (Fin (cubicProjectiveDimension g d + 1)) K V :=
    Module.finBasisOfFinrankEq K V hV
  have hs := a.basis_generates β
  have hclosed := a.isClosedImmersion_cubicSectionMap hL hd β hs
  exact α.eq_refl_of_canonicalCubicSectionBasis_count cubicTorsionHyperplaneBound hg hd hn hnK
    β hs hclosed (frameSize_lt hg hN)

/-- **Rigidity over a base on which the level is invertible, at large level.** Assume
Lefschetz's theorem `CubicFieldEmbeddingStatement`. If `n` is a unit on `S` and
`n > (6^g d) * (6^g d g!)`, then every polarized automorphism of an ordinary polarized
full-level datum over `S` is the identity. -/
theorem PolarizedIso.eq_refl_of_cubicFieldEmbedding
    (hL : CubicFieldEmbeddingStatement.{u}) (hg : 0 < g) (hd : 0 < d)
    (hN : (cubicProjectiveDimension g d + 1) * (6 ^ g * d * Nat.factorial g) < n)
    (hunit : IsUnit (n : Γ(S, ⊤))) (α : PolarizedIso a a) :
    α = PolarizedIso.refl a := by
  apply α.eq_refl_of_geometricPoints
  intro K _ _ b
  have hnK : (n : K) ≠ 0 := by
    have h1 : IsUnit (n : Γ(Spec (CommRingCat.of K), ⊤)) := by
      have := hunit.map b.appTop.hom
      simpa only [map_natCast] using this
    have h2 : IsUnit (n : K) := by
      have := h1.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
      simpa only [map_natCast] using this
    exact h2.ne_zero
  exact (α.pullback b).eq_refl_of_field_of_cubicFieldEmbedding hL hg hd hN hnK

end Langlands.AbelianScheme.PolarizedFiniteLevel
