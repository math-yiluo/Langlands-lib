import Langlands.AbelianScheme.Tate.Integral
import Langlands.AbelianScheme.Basic
import Langlands.AlgebraicGeometry.SmoothReducedProof
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Density of actual geometric two-power torsion -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.Tate

universe u

variable {Ω : Type u} [Field Ω]

/-- The underlying points of the actual sections killed by a power of two. -/
def twoPowerTorsionLocus (A : AbelianScheme (Spec (CommRingCat.of Ω))) :
    Set A.X.left :=
  {x | ∃ (n : ℕ) (s : Over.mk (𝟙 (Spec (CommRingCat.of Ω))) ⟶ A.X),
    s ^ (2 ^ n) = 1 ∧ s.left (default : Spec (CommRingCat.of Ω)) = x}

/-- Two-power torsion is Zariski dense in every abelian variety over an
algebraically closed characteristic-zero field. -/
def FieldTwoPowerTorsionDensityStatement : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    (A : AbelianScheme (Spec (CommRingCat.of Ω))),
    Dense (twoPowerTorsionLocus A)

/-- Density of the actual two-power torsion detects vanishing of an actual
homomorphism through its existing torsion-level maps. -/
theorem hom_eq_zero_of_dense_twoPowerTorsion
    {A B : AbelianScheme (Spec (CommRingCat.of Ω))}
    (hA : Dense (twoPowerTorsionLocus A)) (f : A ⟶ B)
    (hf : ∀ n : ℕ, GroupScheme.Tate.levelMap
      (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))) (AbelianScheme.groupHom f) (2 ^ n) = 0) :
    f = 0 := by
  let T : Over (Spec (CommRingCat.of Ω)) := Over.mk (𝟙 _)
  let f' : A.X ⟶ B.X := (AbelianScheme.groupHom f).hom.hom
  let z' : A.X ⟶ B.X := (AbelianScheme.groupHom (0 : A ⟶ B)).hom.hom
  have hsection (n : ℕ) (s : T ⟶ A.X) (hs : s ^ (2 ^ n) = 1) :
      s ≫ f' = s ≫ z' := by
    let t : GroupScheme.Tate.Level A.toGrp T (2 ^ n) :=
      Additive.ofMul ⟨s, (GroupScheme.Tate.mem_levelGroup A.toGrp T (2 ^ n) s).mpr hs⟩
    have h := congrArg (fun F =>
      (GroupScheme.Tate.toSection B.toGrp T (2 ^ n) (F t)).toMul) (hf n)
    change s ≫ f' = 1 at h
    simpa [z', MonObj.comp_one] using h
  have : IsReduced A.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      Ω A.X.left A.X.hom
  have : IsDominant (equalizer.ι f' z').left := by
    constructor
    apply hA.mono
    rintro x ⟨n, s, hs, rfl⟩
    refine ⟨(equalizer.lift s (hsection n s hs)).left
      (default : Spec (CommRingCat.of Ω)), ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, equalizer.lift_ι]
  have hhom : AbelianScheme.hom f = AbelianScheme.hom (0 : A ⟶ B) := by
    apply ext_of_isDominant_of_isSeparated B.X.hom
      (by exact f'.w.trans z'.w.symm) (equalizer.ι f' z').left
    exact congrArg (fun k => k.left) (equalizer.condition f' z')
  apply (Additive.toMul.injective)
  apply Grp.hom_ext
  exact Over.OverMorphism.ext hhom

end Langlands.AbelianScheme.Tate
