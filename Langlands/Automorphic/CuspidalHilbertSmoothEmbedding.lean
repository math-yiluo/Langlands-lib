import Langlands.Automorphic.CuspidalHilbertContinuity
import Langlands.Automorphic.CuspidalHilbertActionCompatibility
import Langlands.Representation.Archimedean.HilbertSmoothKernelStatement
import Langlands.Representation.Archimedean.SmoothVectors
import Langlands.Global.ArchimedeanDifferentialGeometry
import Mathlib.Analysis.InnerProductSpace.Dual

/-! # Genuine smooth Hilbert orbits from the retained scalar coefficient premises -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open scoped Classical Manifold ContDiff

namespace Langlands.Archimedean
universe uA uG uE
variable {A : Type uA} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] {G : Type uG} [Group G] [TopologicalSpace G]
  [ChartedSpace A G] [LieGroup 𝓘(ℝ, A) ∞ G]
  {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [TopologicalSpace G] [CompleteSpace E] in
/-- The original unitary inner product reduces orbit kernels to a scalar
coefficient at the relative group element. -/
theorem inner_orbit_relative (π : G →* (E →L[ℂ] E))
    (hπ : ∀ g x y, Inner.inner ℂ (π g x) (π g y) = Inner.inner ℂ x y)
    (v : E) (g h : G) :
    Inner.inner ℂ (π g v) (π h v) = Inner.inner ℂ v (π (g⁻¹ * h) v) := by
  have hr : π g (π (g⁻¹ * h) v) = π h v := by
    change (π g * π (g⁻¹ * h)) v = _
    rw [← map_mul, mul_inv_cancel_left]
  exact (congrArg (Inner.inner ℂ (π g v)) hr).symm.trans (hπ g v _)

/-- The explicit smooth-kernel criterion upgrades a smooth scalar diagonal
coefficient to a genuine Hilbert-norm smooth orbit. -/
theorem isSmoothVector_of_smooth_diagonal
    (hkernel : HilbertSmoothKernelStatement.{uA, uG, uE})
    (π : G →* (E →L[ℂ] E))
    (hπ : ∀ g x y, Inner.inner ℂ (π g x) (π g y) = Inner.inner ℂ x y)
    (v : E) (hc : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, ℂ) ∞
      (fun g => Inner.inner ℂ v (π g v))) :
    IsSmoothVector 𝓘(ℝ, A) π v := by
  apply (hkernel A G E (fun g => π g v)).mpr
  have hs : ContMDiff (𝓘(ℝ, A).prod 𝓘(ℝ, A)) 𝓘(ℝ, ℂ) ∞
      (fun p : G × G => Inner.inner ℂ v (π (p.1⁻¹ * p.2) v)) :=
    hc.comp (contMDiff_fst.inv.mul contMDiff_snd)
  exact hs.congr (fun p => inner_orbit_relative π hπ v p.1 p.2)

end Langlands.Archimedean

namespace Langlands.UnitaryEmbeddingFamily
universe sG sV sE sH
variable {Γ : Type sG} [Group Γ] {V : Type sV}
  {E : Type sE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {H : Type sH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The actual target pairing computes the dense carrier's source coefficient. -/
theorem inner_dense_orbit (J : Γ → E →ₗᵢ[ℂ] H) (U : Γ →* (E →L[ℂ] E))
    (hU : RealizesEmbeddings J U) (j : V → E) (k : Γ → V → H)
    (hvalue : ∀ a v, J a (j v) = k a v) (w : E) (v : V) (a : Γ) :
    Inner.inner ℂ w (U a (j v)) = Inner.inner ℂ (J 1 w) (k a v) :=
  ((J 1).inner_map_map w (U a (j v))).symm.trans
    (congrArg (Inner.inner ℂ (J 1 w)) ((hU.1 a (j v)).trans (hvalue a v)))

end Langlands.UnitaryEmbeddingFamily

namespace Langlands.Archimedean
universe tA tG tE tΓ tV tH
variable {A : Type tA} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] {G : Type tG} [Group G] [TopologicalSpace G]
  [ChartedSpace A G] [LieGroup 𝓘(ℝ, A) ∞ G]
  {E : Type tE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {Γ : Type tΓ} [Group Γ] {V : Type tV}
  {H : Type tH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Actual scalar target values and the retained smooth-kernel criterion give
a genuine smooth source vector, under the same supplied representation. -/
theorem isSmoothVector_of_target_diagonal
    (hkernel : HilbertSmoothKernelStatement.{tA, tG, tE})
    (J : Γ → E →ₗᵢ[ℂ] H) (U : Γ →* (E →L[ℂ] E))
    (hU : Langlands.UnitaryEmbeddingFamily.RealizesEmbeddings J U)
    (φ : G →* Γ) (j : V → E) (k : Γ → V → H)
    (hvalue : ∀ a v, J a (j v) = k a v) (v : V)
    (hc : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, ℂ) ∞
      (fun g => Inner.inner ℂ (J 1 (j v)) (k (φ g) v))) :
    IsSmoothVector 𝓘(ℝ, A) (U.comp φ) (j v) :=
  isSmoothVector_of_smooth_diagonal hkernel (U.comp φ)
    (fun g => hU.2 (φ g)) (j v)
    (hc.congr fun g => Langlands.UnitaryEmbeddingFamily.inner_dense_orbit
      J U hU j k hvalue (j v) v (φ g))

end Langlands.Archimedean

namespace Langlands.Archimedean
universe gA gG gE
variable {A : Type gA} [NormedAddCommGroup A] [NormedSpace ℝ A]
  {G : Type gG} [Group G] [TopologicalSpace G] [ChartedSpace A G]
  {E : Type gE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A bounded scalar inner functional commutes with the genuine orbit derivative. -/
theorem inner_lieDerivative (π : G →* (E →L[ℂ] E))
    {v : E} (hv : IsSmoothVector 𝓘(ℝ, A) π v) (w : E) (X : A) :
    Inner.inner ℂ w (lieDerivative 𝓘(ℝ, A) π X v) =
      mfderiv 𝓘(ℝ, A) 𝓘(ℝ, ℂ)
        (fun g => Inner.inner ℂ w (π g v)) 1 X := by
  let L := (innerSL ℂ w).restrictScalars ℝ
  have hf : MDifferentiableAt 𝓘(ℝ, A) 𝓘(ℝ, E) (orbitMap π v) 1 :=
    hv.mdifferentiableAt (by simp)
  have hL : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℂ) L (orbitMap π v 1) :=
    L.differentiableAt.mdifferentiableAt
  change L (mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) (orbitMap π v) 1 X) =
    mfderiv 𝓘(ℝ, A) 𝓘(ℝ, ℂ) (L ∘ orbitMap π v) 1 X
  rw [mfderiv_comp 1 hL hf, ContinuousLinearMap.mfderiv_eq]
  rfl

end Langlands.Archimedean

namespace Langlands.Archimedean
universe qR qG

/-- Normalization of the identity point and matrix direction is independent
of the particular scalar function or the original group coordinates. -/
theorem scalar_mfderiv_unit_one
    {R : Type qR} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]
    {Γ : Type qG} [Group Γ] (e : Γ →* Rˣ) (s : Rˣ → ℂ) (X : R) :
    NormedSpace.fromTangentSpace _
      (mfderiv 𝓘(ℝ, R) 𝓘(ℝ, ℂ) s (e 1) ((e 1 : R) * X)) =
      mfderiv 𝓘(ℝ, R) 𝓘(ℝ, ℂ) s 1 X := by
  change mfderiv 𝓘(ℝ, R) 𝓘(ℝ, ℂ) s (e 1) ((e 1 : R) * X) = _
  have hm : (e 1 : R) * X = X := by rw [map_one, Units.val_one, one_mul]
  exact (congrArg (mfderiv 𝓘(ℝ, R) 𝓘(ℝ, ℂ) s (e 1)) hm).trans
    (congrArg (fun a : Rˣ => mfderiv 𝓘(ℝ, R) 𝓘(ℝ, ℂ) s a X) e.map_one)

end Langlands.Archimedean

namespace Langlands.Archimedean
universe cA cG cE cH cV cX
variable {A : Type cA} [NormedAddCommGroup A] [NormedSpace ℝ A]
  {G : Type cG} [Group G] [TopologicalSpace G] [ChartedSpace A G]
  {E : Type cE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {H : Type cH} {V : Type cV} {X : Type cX}

/-- Exact scalar values of source orbits through a prescribed target map. -/
def ScalarCoefficientValues (π : G →* (E →L[ℂ] E)) (j : V → E) (J : E → H)
    (c : H → V → G → ℂ) : Prop :=
  ∀ w v g, Inner.inner ℂ w (π g (j v)) = c (J w) v g

/-- Actual scalar lifts retain their original values and first directional
operator identity at the identity, rather than assuming a vector derivative. -/
def ScalarGeneratorLifts (c : H → V → G → ℂ) (D : X → V → V) (ζ : X → A) : Prop :=
  ∀ w, ∃ C : V → G → ℂ, (∀ v g, C v g = c w v g) ∧
    ∀ x v, C (D x v) 1 = mfderiv 𝓘(ℝ, A) 𝓘(ℝ, ℂ) (C v) 1 (ζ x)

/-- Agreement of the prescribed source generators with genuine orbit derivatives. -/
def RealGeneratorCompatibility (π : G →* (E →L[ℂ] E)) (j : V → E)
    (D : X → V → V) (ζ : X → A) : Prop :=
  ∀ x v, j (D x v) = lieDerivative 𝓘(ℝ, A) π (ζ x) (j v)

/-- Scalar differential identities imply the original vector generator identity. -/
theorem realGeneratorCompatibility_of_scalar
    (π : G →* (E →L[ℂ] E)) (j : V → E) (J : E → H) (c : H → V → G → ℂ)
    (D : X → V → V) (ζ : X → A) (hvalue : ScalarCoefficientValues π j J c)
    (hs : ∀ v, IsSmoothVector 𝓘(ℝ, A) π (j v))
    (hlift : ScalarGeneratorLifts c D ζ) : RealGeneratorCompatibility π j D ζ := by
  intro x v
  apply ext_inner_left ℂ
  intro w
  obtain ⟨C, hC, hD⟩ := hlift (J w)
  have he (z : V) : (fun g => Inner.inner ℂ w (π g (j z))) = C z := by
    funext g
    exact (hvalue w z g).trans (hC z g).symm
  have he1 : Inner.inner ℂ w (j (D x v)) = C (D x v) 1 := by
    have h := congrFun (he (D x v)) 1
    simpa only [map_one, one_apply_eq_self] using h
  have hd := inner_lieDerivative π (hs v) w (ζ x)
  exact he1.trans ((hD x v).trans
    ((congrArg (fun t => mfderiv 𝓘(ℝ, A) 𝓘(ℝ, ℂ) t 1 (ζ x)) (he v)).symm.trans hd.symm))

end Langlands.Archimedean

namespace Langlands.UnitaryEmbeddingFamily
universe vA vG vΓ vE vH vV
variable {A : Type vA} [NormedAddCommGroup A] [NormedSpace ℝ A]
  {G : Type vG} [Group G] [TopologicalSpace G] [ChartedSpace A G]
  {Γ : Type vΓ} [Group Γ] {V : Type vV}
  {E : Type vE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {H : Type vH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

omit [TopologicalSpace G] in
/-- The actual target scalar pairings give the source coefficient predicate. -/
theorem scalarCoefficientValues_of_target
    (J : Γ → E →ₗᵢ[ℂ] H) (U : Γ →* (E →L[ℂ] E)) (hU : RealizesEmbeddings J U)
    (φ : G →* Γ) (j : V → E) (k : Γ → V → H) (c : H → V → G → ℂ)
    (hvalue : ∀ a v, J a (j v) = k a v)
    (hpair : ∀ w v g, Inner.inner ℂ w (k (φ g) v) = c w v g) :
    Langlands.Archimedean.ScalarCoefficientValues (U.comp φ) j (J 1) c :=
  fun w v g => (inner_dense_orbit J U hU j k hvalue w v (φ g)).trans (hpair _ v g)

end Langlands.UnitaryEmbeddingFamily

namespace Langlands.Archimedean
universe eA eG eV eE
variable {A : Type eA} [NormedAddCommGroup A] [NormedSpace ℝ A]
  {G : Type eG} [Group G] [TopologicalSpace G] [ChartedSpace A G]
  {V : Type eV} [AddCommGroup V] [Module ℂ V]
  {E : Type eE} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Restrict a given linear embedding with genuine smooth values. -/
def linearSmoothEmbedding (π : G →* (E →L[ℂ] E)) (j : V →ₗ[ℂ] E)
    (hs : ∀ v, IsSmoothVector 𝓘(ℝ, A) π (j v)) :
    V →ₗ[ℂ] smoothVectors 𝓘(ℝ, A) π :=
  j.codRestrict _ hs

/-- Injectivity of the prescribed restriction to genuine smooth vectors. -/
def SmoothEmbeddingInjectivity (π : G →* (E →L[ℂ] E)) (j : V →ₗ[ℂ] E)
    (hs : ∀ v, IsSmoothVector 𝓘(ℝ, A) π (j v)) : Prop :=
  Function.Injective (linearSmoothEmbedding π j hs)

theorem linearSmoothEmbedding_injective (π : G →* (E →L[ℂ] E)) (j : V →ₗ[ℂ] E)
    (hs : ∀ v, IsSmoothVector 𝓘(ℝ, A) π (j v)) (hj : Function.Injective j) :
    Function.Injective (linearSmoothEmbedding π j hs) := by
  intro v w h
  exact hj (congrArg Subtype.val h)

end Langlands.Archimedean

namespace Langlands.Automorphic
open Langlands.Global MeasureTheory
open scoped NumberField Matrix.Norms.Operator
universe u
variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local instance hilbertSmoothRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance hilbertSmoothContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance hilbertSmoothFiniteGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance hilbertSmoothFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance hilbertSmoothStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance hilbertSmoothSpaceGroup (S : OperatorRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

namespace OperatorDeterminantSlice

/-- The actual infinite inclusion written in the published real manifold coordinates. -/
def infiniteCoordinateInclusion (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    ArchimedeanGL F n →* AdelicGL F n :=
  (AdelicGL.ofInfinite F n).toMonoidHom.comp (archimedeanGLCoordinates F n).symm.toMonoidHom

/-- At the identity, the genuine enveloping generator is the actual manifold
derivative in its original real matrix direction. -/
theorem smoothCoefficient_generator_one
    (X : ArchimedeanGL.RealLieAlgebra F n) (s : ArchimedeanGL.SmoothFunctions F n) :
    (ArchimedeanGL.envelopingAction F n
      (ArchimedeanGL.envelopingGenerator F n (ArchimedeanGL.complexify F n X)) s).val 1 =
    mfderiv 𝓘(ℝ, ArchimedeanMatrix F n) 𝓘(ℝ, ℂ)
      (fun g => s.val ((archimedeanGLCoordinates F n).symm g)) 1
      (ArchimedeanGL.realLieAlgebraToMatrix F n X) := by
  exact (congrArg (fun L => (L s).val 1)
    (ArchimedeanGL.envelopingAction_real_generator F n X)).trans
      ((ArchimedeanGL.smoothDifferential_eq_mfderiv F n X s 1).trans
        (Langlands.Archimedean.scalar_mfderiv_unit_one
          (archimedeanGLCoordinates F n).toMonoidHom
          (fun g => s.val ((archimedeanGLCoordinates F n).symm g))
          (ArchimedeanGL.realLieAlgebraToMatrix F n X)))

variable [CompactSpace (AdeleQuotient F)] {r : ℕ} (T : CuspidalOperatorRealization F r)
  (hcoeff : CuspidalHilbertOrbitCoefficientStatement.{u})
  (χ : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
  (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1) (hTχ : T.realization.HasCentralCharacter χ)
  (b : T.realization.UnitaryForm)
  (hb : ∀ f g : T.Space, b.inner f g =
    ∫ q, Inner.inner ℂ (toQuotient F (r + 1) T.realization f q)
      (toQuotient F (r + 1) T.realization g q)
      ∂(quotientHaarMeasure F (r + 1)).restrict (band F (r + 1)))

/-- The already constructed source action in actual real manifold coordinates. -/
def coordinateHilbertRepresentation :
    ArchimedeanGL F (r + 1) →*
      (b.finiteForm.HilbertCompletion →L[ℂ] b.finiteForm.HilbertCompletion) :=
  (adelicHilbertRepresentation T hcoeff χ hχ hTχ b hb).comp
    (infiniteCoordinateInclusion F (r + 1))


/-- The original source vectors are genuine norm-smooth Hilbert vectors under
the two explicitly retained analytic premises. -/
theorem toHilbert_isSmoothVector
    (hkernel : Langlands.Archimedean.HilbertSmoothKernelStatement.{u, u, u}) (f : T.Space) :
    Langlands.Archimedean.IsSmoothVector 𝓘(ℝ, ArchimedeanMatrix F (r + 1))
      (coordinateHilbertRepresentation T hcoeff χ hχ hTχ b hb) (b.finiteForm.toHilbert f) := by
  let w := translatedHilbertEmbedding T.realization T.cuspidal (Nat.succ_ne_zero r)
    χ hχ hTχ b hb 1 (b.finiteForm.toHilbert f)
  refine Exists.elim (hcoeff F r T ⟨χ, hχ, hTχ⟩ w).2 fun C hC => ?_
  have hc : ContMDiff 𝓘(ℝ, ArchimedeanMatrix F (r + 1)) 𝓘(ℝ, ℂ) ∞
      (fun g : ArchimedeanGL F (r + 1) => Inner.inner ℂ w
        (translatedToL2 T.realization T.cuspidal (infiniteCoordinateInclusion F (r + 1) g) f)) :=
    (C f).property.congr fun g =>
      (inner_translatedToL2_left T w
        (AdelicGL.ofInfinite F (r + 1) ((archimedeanGLCoordinates F (r + 1)).symm g)) f).trans
          (hC.1 f ((archimedeanGLCoordinates F (r + 1)).symm g)).symm
  exact Langlands.Archimedean.isSmoothVector_of_target_diagonal hkernel
    (translatedHilbertEmbedding T.realization T.cuspidal (Nat.succ_ne_zero r) χ hχ hTχ b hb)
    (adelicHilbertRepresentation T hcoeff χ hχ hTχ b hb)
    (adelicHilbertRepresentation_realizes T hcoeff χ hχ hTχ b hb)
    (infiniteCoordinateInclusion F (r + 1)) b.finiteForm.toHilbert
    (fun a v => translatedToL2 T.realization T.cuspidal a v)
    (translatedHilbertEmbedding_toHilbert T.realization T.cuspidal (Nat.succ_ne_zero r)
      χ hχ hTχ b hb) f hc

/-- The canonical source embedding takes its values in the genuine smooth
vectors of the already constructed infinite representation. -/
def toHilbertSmooth
    (hkernel : Langlands.Archimedean.HilbertSmoothKernelStatement.{u, u, u}) :=
  Langlands.Archimedean.linearSmoothEmbedding
    (coordinateHilbertRepresentation T hcoeff χ hχ hTχ b hb) b.finiteForm.toHilbert
    (toHilbert_isSmoothVector T hcoeff χ hχ hTχ b hb hkernel)



end OperatorDeterminantSlice
end Langlands.Automorphic
