import Langlands.Automorphic.TransposeAutomorphic
import Langlands.Automorphic.OperatorCore

/-! # Inverse-transpose pullback on the actual stable automorphic operator core -/

noncomputable section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global Langlands.GeneralLinear NumberField IsDedekindDomain
open ContinuousRationalFunctions

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

local instance transposeCoreRationalGroup :
    AddCommGroup (RationalInvariantFunctions K n) := Submodule.addCommGroup _
local instance transposeCoreContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions K n) := Submodule.addCommGroup _
local instance transposeCoreFiniteSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions K n) := Submodule.addCommGroup _
local instance transposeCoreFormGroup :
    AddCommGroup (AutomorphicForms K n) := Submodule.addCommGroup _
local instance transposeCoreStableGroup :
    AddCommGroup (StableAutomorphicFunctions K n) := Submodule.addCommGroup _

/-- The compact subgroup translation is twisted by the actual compact involution. -/
theorem finiteSmoothTranspose_compactRightAction (k : standardInfiniteCompact K n)
    (f : FiniteSmoothRationalFunctions K n) :
    finiteSmoothTranspose K n
        (finiteSmoothCompactRightAction K n (ArchimedeanGL.compactTranspose K n k) f) =
      finiteSmoothCompactRightAction K n k (finiteSmoothTranspose K n f) := by
  change finiteSmoothTranspose K n
      (finiteSmoothRightAction K n
        (AdelicGL.ofInfinite K n
          (inverseTranspose n (InfiniteAdeleRing K) k.val)) f) = _
  rw [finiteSmoothTranspose_rightAction, Langlands.Global.RankinSelbergGlobal.Unfolding.inverseTranspose_ofInfinite,
    inverseTranspose_involutive]
  rfl

/-- Conjugate an actual ambient operator by the involutive inverse-transpose argument pullback. -/
def finiteSmoothTransposeConjugation : FiniteSmoothEnd K n ≃ₐ[ℂ] FiniteSmoothEnd K n :=
  (finiteSmoothTranspose K n).symm.conjAlgEquiv ℂ

@[simp] theorem finiteSmoothTransposeConjugation_apply (a : FiniteSmoothEnd K n)
    (f : FiniteSmoothRationalFunctions K n) :
    finiteSmoothTransposeConjugation K n a f =
      (finiteSmoothTranspose K n).symm (a (finiteSmoothTranspose K n f)) := rfl

@[simp] theorem finiteSmoothTransposeConjugation_finite (d : FiniteAdelicGL K n) :
    finiteSmoothTransposeConjugation K n (finiteSmoothFiniteRightAction K n d) =
      finiteSmoothFiniteRightAction K n (inverseTranspose n (FiniteAdeleRing (𝓞 K) K) d) := by
  apply LinearMap.ext
  intro f
  apply (finiteSmoothTranspose K n).injective
  rw [finiteSmoothTransposeConjugation_apply, LinearEquiv.apply_symm_apply]
  exact (finiteSmoothTranspose_finiteRightAction K n d f).symm

@[simp] theorem finiteSmoothTransposeConjugation_compact (k : standardInfiniteCompact K n) :
    finiteSmoothTransposeConjugation K n (finiteSmoothCompactRightAction K n k) =
      finiteSmoothCompactRightAction K n (ArchimedeanGL.compactTranspose K n k) := by
  apply LinearMap.ext
  intro f
  apply (finiteSmoothTranspose K n).injective
  rw [finiteSmoothTransposeConjugation_apply, LinearEquiv.apply_symm_apply]
  exact (finiteSmoothTranspose_compactRightAction K n k f).symm

@[simp] theorem finiteSmoothTransposeConjugation_differential
    (a : ArchimedeanGL.EnvelopingAlgebra K n) :
    finiteSmoothTransposeConjugation K n (finiteSmoothEnvelopingAction K n a) =
      finiteSmoothEnvelopingAction K n
        (ArchimedeanGL.envelopingIota K n a) := by
  apply LinearMap.ext
  intro f
  apply (finiteSmoothTranspose K n).injective
  rw [finiteSmoothTransposeConjugation_apply, LinearEquiv.apply_symm_apply]
  exact (finiteSmoothTranspose_envelopingAction K n a f).symm

@[simp] theorem finiteSmoothTransposeConjugation_involutive (a : FiniteSmoothEnd K n) :
    finiteSmoothTransposeConjugation K n (finiteSmoothTransposeConjugation K n a) = a := by
  apply LinearMap.ext
  intro f
  simp only [finiteSmoothTransposeConjugation_apply, finiteSmoothTranspose_symm,
    finiteSmoothTranspose_involutive]

private theorem finiteSmoothTransposeConjugation_mem (a : FiniteSmoothEnd K n)
    (ha : a ∈ automorphicOperatorAlgebra K n) :
    finiteSmoothTransposeConjugation K n a ∈ automorphicOperatorAlgebra K n := by
  refine Algebra.adjoin_induction
    (p := fun a _ => finiteSmoothTransposeConjugation K n a ∈ automorphicOperatorAlgebra K n)
    ?_ ?_ ?_ ?_ ha
  · rintro a ((⟨d, rfl⟩ | ⟨k, rfl⟩) | ⟨u, rfl⟩)
    · rw [finiteSmoothTransposeConjugation_finite]
      exact Algebra.subset_adjoin (Or.inl (Or.inl ⟨_, rfl⟩))
    · rw [finiteSmoothTransposeConjugation_compact]
      exact Algebra.subset_adjoin (Or.inl (Or.inr ⟨_, rfl⟩))
    · rw [finiteSmoothTransposeConjugation_differential]
      exact Algebra.subset_adjoin (Or.inr ⟨_, rfl⟩)
  · intro c
    rw [AlgEquiv.commutes]
    exact (automorphicOperatorAlgebra K n).algebraMap_mem c
  · intro _ _ _ _ hca hcb
    rw [map_add]
    exact (automorphicOperatorAlgebra K n).add_mem hca hcb
  · intro _ _ _ _ hca hcb
    rw [map_mul]
    exact (automorphicOperatorAlgebra K n).mul_mem hca hcb

/-- The actual concrete operator algebra is preserved, with the same involution as inverse. -/
def transposeOperatorConjugation :
    automorphicOperatorAlgebra K n ≃ₐ[ℂ] automorphicOperatorAlgebra K n where
  toFun a := ⟨finiteSmoothTransposeConjugation K n a.val, finiteSmoothTransposeConjugation_mem K n _ a.property⟩
  invFun a := ⟨finiteSmoothTransposeConjugation K n a.val, finiteSmoothTransposeConjugation_mem K n _ a.property⟩
  left_inv a := Subtype.ext (finiteSmoothTransposeConjugation_involutive K n a.val)
  right_inv a := Subtype.ext (finiteSmoothTransposeConjugation_involutive K n a.val)
  map_mul' a b := Subtype.ext (map_mul _ a.val b.val)
  map_add' a b := Subtype.ext (map_add _ a.val b.val)
  commutes' c := Subtype.ext (AlgEquiv.commutes _ c)

@[simp] theorem transposeOperatorConjugation_val (a : automorphicOperatorAlgebra K n) :
    (transposeOperatorConjugation K n a).val = finiteSmoothTransposeConjugation K n a.val := rfl

@[simp] theorem transposeOperatorConjugation_finite (d : FiniteAdelicGL K n) :
    transposeOperatorConjugation K n (finiteOperator K n d) =
      finiteOperator K n (inverseTranspose n (FiniteAdeleRing (𝓞 K) K) d) :=
  Subtype.ext (finiteSmoothTransposeConjugation_finite K n d)

@[simp] theorem transposeOperatorConjugation_compact (k : standardInfiniteCompact K n) :
    transposeOperatorConjugation K n (compactOperator K n k) =
      compactOperator K n (ArchimedeanGL.compactTranspose K n k) :=
  Subtype.ext (finiteSmoothTransposeConjugation_compact K n k)

@[simp] theorem transposeOperatorConjugation_differential
    (a : ArchimedeanGL.EnvelopingAlgebra K n) :
    transposeOperatorConjugation K n (differentialOperator K n a) =
      differentialOperator K n
        (ArchimedeanGL.envelopingIota K n a) :=
  Subtype.ext (finiteSmoothTransposeConjugation_differential K n a)

@[simp] theorem transposeOperatorConjugation_involutive (a : automorphicOperatorAlgebra K n) :
    transposeOperatorConjugation K n (transposeOperatorConjugation K n a) = a :=
  Subtype.ext (finiteSmoothTransposeConjugation_involutive K n a.val)

@[simp] theorem transposeOperatorConjugation_symm :
    (transposeOperatorConjugation K n).symm = transposeOperatorConjugation K n := rfl

/-- Whole-algebra covariance on actual finite-smooth functions. -/
theorem operatorAction_transpose (a : automorphicOperatorAlgebra K n)
    (f : FiniteSmoothRationalFunctions K n) :
    a.val (finiteSmoothTranspose K n f) =
      finiteSmoothTranspose K n ((transposeOperatorConjugation K n a).val f) := by
  change a.val (finiteSmoothTranspose K n f) =
    finiteSmoothTranspose K n
      ((finiteSmoothTranspose K n).symm (a.val (finiteSmoothTranspose K n f)))
  rw [LinearEquiv.apply_symm_apply]


/-- Whole-algebra covariance and actual form preservation imply core preservation. -/
theorem mem_automorphicOperatorCore_transpose
    {f : FiniteSmoothRationalFunctions K n} (hf : f ∈ automorphicOperatorCore K n) :
    finiteSmoothTranspose K n f ∈ automorphicOperatorCore K n := by
  intro a
  rw [operatorAction_transpose]
  exact (finiteSmoothTranspose_mem_automorphic_iff K n _).mpr
    (hf (transposeOperatorConjugation K n a))

@[simp] theorem finiteSmoothTranspose_mem_automorphicOperatorCore_iff
    (f : FiniteSmoothRationalFunctions K n) :
    finiteSmoothTranspose K n f ∈ automorphicOperatorCore K n ↔
      f ∈ automorphicOperatorCore K n := by
  constructor
  · intro hf
    have h := mem_automorphicOperatorCore_transpose K n hf
    rwa [finiteSmoothTranspose_involutive] at h
  · exact mem_automorphicOperatorCore_transpose K n

private theorem automorphicOperatorCore_map_transpose :
    (automorphicOperatorCore K n).toSubmodule.map
        (finiteSmoothTranspose K n).toLinearMap =
      (automorphicOperatorCore K n).toSubmodule := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact mem_automorphicOperatorCore_transpose K n hg
  · intro hf
    obtain ⟨g, rfl⟩ := (finiteSmoothTranspose K n).surjective f
    exact ⟨g, (finiteSmoothTranspose_mem_automorphicOperatorCore_iff K n g).mp hf, rfl⟩

namespace StableAutomorphicFunctions

/-- Restrict the existing continuous inverse-transpose argument pullback to the actual stable core. -/
def transpose : StableAutomorphicFunctions K n ≃ₗ[ℂ] StableAutomorphicFunctions K n :=
  (finiteSmoothTranspose K n).ofSubmodules _ _
    (automorphicOperatorCore_map_transpose K n)

@[simp] theorem transpose_val (f : StableAutomorphicFunctions K n) :
    (transpose K n f).val = finiteSmoothTranspose K n f.val := rfl

@[simp] theorem transpose_involutive (f : StableAutomorphicFunctions K n) :
    transpose K n (transpose K n f) = f := by
  apply Subtype.ext
  exact finiteSmoothTranspose_involutive K n f.val

@[simp] theorem transpose_symm :
    (transpose K n).symm = transpose K n := by
  apply LinearEquiv.ext
  intro f
  apply (transpose K n).injective
  rw [LinearEquiv.apply_symm_apply, transpose_involutive]

/-- Every actual operator satisfies the inverse-transpose covariance on the constructed core. -/
theorem operatorAction_transpose (a : automorphicOperatorAlgebra K n)
    (f : StableAutomorphicFunctions K n) :
    stableAutomorphicAction K n a (transpose K n f) =
      transpose K n (stableAutomorphicAction K n (transposeOperatorConjugation K n a) f) := by
  apply Subtype.ext
  exact Langlands.Automorphic.operatorAction_transpose K n a f.val

theorem finiteAction_transpose (d : FiniteAdelicGL K n)
    (f : StableAutomorphicFunctions K n) :
    stableAutomorphicFiniteAction K n d (transpose K n f) =
      transpose K n
        (stableAutomorphicFiniteAction K n (inverseTranspose n (FiniteAdeleRing (𝓞 K) K) d) f) := by
  apply Subtype.ext
  exact (finiteSmoothTranspose_finiteRightAction K n d f.val).symm

theorem compactAction_transpose (k : standardInfiniteCompact K n)
    (f : StableAutomorphicFunctions K n) :
    stableAutomorphicCompactAction K n k (transpose K n f) =
      transpose K n
        (stableAutomorphicCompactAction K n (ArchimedeanGL.compactTranspose K n k) f) := by
  apply Subtype.ext
  exact (finiteSmoothTranspose_compactRightAction K n k f.val).symm

theorem envelopingAction_transpose (a : ArchimedeanGL.EnvelopingAlgebra K n)
    (f : StableAutomorphicFunctions K n) :
    stableAutomorphicEnvelopingAction K n a (transpose K n f) =
      transpose K n
        (stableAutomorphicEnvelopingAction K n
          (ArchimedeanGL.envelopingIota K n a) f) := by
  apply Subtype.ext
  exact (finiteSmoothTranspose_envelopingAction K n a f.val).symm

@[simp] theorem inclusion_transpose (f : StableAutomorphicFunctions K n) :
    stableAutomorphicInclusion K n (transpose K n f) =
      AutomorphicForms.transpose K n (stableAutomorphicInclusion K n f) := rfl

@[simp] theorem evaluate_transpose (f : StableAutomorphicFunctions K n)
    (g : AdelicGL K n) :
    evaluate K n (transpose K n f).val.val g =
      evaluate K n f.val.val (inverseTranspose n (AdeleRing (𝓞 K) K) g) :=
  evaluate_continuousTranspose K n _ g

@[simp] theorem evaluate_transpose_symm (f : StableAutomorphicFunctions K n)
    (g : AdelicGL K n) :
    evaluate K n ((transpose K n).symm f).val.val g =
      evaluate K n f.val.val (inverseTranspose n (AdeleRing (𝓞 K) K) g) := by
  rw [transpose_symm]
  exact evaluate_transpose K n f g

end StableAutomorphicFunctions
end Langlands.Automorphic
