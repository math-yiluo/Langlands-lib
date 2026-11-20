import Langlands.Analysis.AnalyticUnitComponentVanishing
import Langlands.Automorphic.CuspidalBandOrbitClosure
import Langlands.Automorphic.CuspidalHilbertCoefficientComparison
import Langlands.Global.ArchimedeanCompactComponentCoverageProof

/-! # Invariant Hilbert closures from coefficient restrictions -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open scoped Classical Matrix.Norms.Operator

namespace Langlands.Automorphic.HilbertCoefficientComparison

open Langlands.Global ArchimedeanGL
universe u uA uV uE uG

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The restriction of an adelic representation along an inclusion into the
mixed archimedean coordinates. -/
def placeAction {G : Type uG} [Monoid G] (U : AdelicGL F n →* (E →L[ℂ] E))
    (ι : G →* ArchimedeanGL F n) : G →* (E →L[ℂ] E) :=
  U.comp ((AdelicGL.ofInfinite F n).toMonoidHom.comp
    ((archimedeanGLCoordinates F n).symm.toMonoidHom.comp ι))

/-- Every action operator takes the Hilbert closure of the indicated algebraic
image into itself. -/
def PreservesImageClosure {G : Type uG} [Monoid G] (π : G →* (E →L[ℂ] E))
    (j : V →ₗ[ℂ] E) (W : Submodule ℂ V) : Prop :=
  ∀ g x, x ∈ (W.map j).topologicalClosure → π g x ∈ (W.map j).topologicalClosure

variable [CompleteSpace E] {A : Type uA} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- The standard compact inclusion provides a representative in each component
of a real or complex general linear group. -/
theorem exists_unitary_point_mem_connectedComponent
    {𝕜 : Type*} [RCLike 𝕜] {m : Type*} [Fintype m] [DecidableEq m]
    (g : Matrix.GeneralLinearGroup m 𝕜) :
    ∃ k : Matrix.unitaryGroup m 𝕜, g ∈ connectedComponent (Unitary.toUnits k) := by
  obtain ⟨p, hp, hg⟩ := exists_unitary_mem_connectedComponent (𝕜 := 𝕜) (m := m) g
  let k : Matrix.unitaryGroup m 𝕜 := ⟨(p : Matrix m m 𝕜), hp⟩
  have hk : Unitary.toUnits k = p := Units.ext rfl
  exact ⟨k, hk.symm ▸ hg⟩

/-- A joint-finite coefficient family forces local closure invariance when
the local derivatives and the action at the supplied component representatives
preserve the original subspace. -/
theorem preservesImageClosure_of_coefficients
    (U : AdelicGL F n →* (E →L[ℂ] E)) (j : V →ₗ[ℂ] E) (W : Submodule ℂ V)
    (D : EnvelopingAlgebra F n → V → V)
    (hcoeff : JointFiniteCoefficientLifts U (AdelicGL.ofInfinite F n) j D)
    (ι : Aˣ →* ArchimedeanGL F n) (a : A → ArchimedeanMatrix F n)
    (L : A → RealLieAlgebra F n)
    (ha : ∀ g : Aˣ, a (g : A) = (ι g : ArchimedeanMatrix F n))
    (han : ∀ (f : SmoothFunctions F n) (g : Aˣ),
      AnalyticAt ℝ (coordinateExtension F n f) (ι g : ArchimedeanMatrix F n) →
        AnalyticAt ℝ (coordinateExtension F n f ∘ a) (g : A))
    (hder : ∀ (f : SmoothFunctions F n) (g : Aˣ) (X : A),
      fderiv ℝ (coordinateExtension F n f ∘ a) (g : A) ((g : A) * X) =
        (smoothDifferential F n (L X) f).val ((archimedeanGLCoordinates F n).symm (ι g)))
    (hW : ∀ X v, v ∈ W → D (envelopingGenerator F n (complexify F n (L X))) v ∈ W)
    {K : Type*} (includeCompact : K → Aˣ)
    (hcomponent : ∀ g : Aˣ, ∃ k : K, g ∈ connectedComponent (includeCompact k))
    (hcompact : ∀ (k : K) (v : W), ∃ v' : W, placeAction U ι (includeCompact k) (j v) = j v') :
    PreservesImageClosure (placeAction U ι) j W := by
  intro g x hx
  have hr : LinearMap.range (j.comp W.subtype) = W.map j := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hclosed : IsClosed ((placeAction U ι g) ⁻¹' ((W.map j).topologicalClosure : Set E)) :=
    (W.map j).isClosed_topologicalClosure.preimage (placeAction U ι g).continuous
  apply closure_minimal (t := (placeAction U ι g) ⁻¹' ((W.map j).topologicalClosure : Set E))
    _ hclosed hx
  rintro _ ⟨v, hv, rfl⟩
  change placeAction U ι g (j v) ∈ (W.map j).topologicalClosure
  rw [← hr]
  apply Langlands.mem_closure_range_of_inner_annihilators
  intro w hw
  obtain ⟨C, hC, hD, hfinite⟩ := hcoeff w
  let c (y : W) := coordinateExtension F n (C y) ∘ a
  let d (X : A) (y : W) : W :=
    ⟨D (envelopingGenerator F n (complexify F n (L X))) y, hW X y y.property⟩
  have hc (y : W) (q : Aˣ) :
      c y (q : A) = (C y).val ((archimedeanGLCoordinates F n).symm (ι q)) := by
    change coordinateExtension F n (C y) (a q) = _
    rw [ha q, coordinateExtension_apply]
  have hcval (y : W) (q : Aˣ) : c y (q : A) = Inner.inner ℂ w (placeAction U ι q (j y)) :=
    (hc y q).trans (hC y _)
  have hcan (y : W) (q : Aˣ) : AnalyticAt ℝ (c y) (q : A) :=
    han (C y) q (jointFiniteAnalyticity F n (C y) (hfinite y) (ι q))
  have hcder (X : A) (y : W) (q : Aˣ) :
      fderiv ℝ (c y) (q : A) ((q : A) * X) = c (d X y) (q : A) := by
    change fderiv ℝ (coordinateExtension F n (C y) ∘ a) (q : A) ((q : A) * X) = _
    rw [hder, hc]
    have h := hD (envelopingGenerator F n (complexify F n (L X))) y
    rw [envelopingAction_real_generator] at h
    rw [show C (d X y) = smoothDifferential F n (L X) (C y) from h]
  obtain ⟨k, hk⟩ := hcomponent g
  have hzero (y : W) : c y (includeCompact k : A) = 0 := by
    obtain ⟨y', hy'⟩ := hcompact k y
    exact (hcval y (includeCompact k)).trans ((congrArg (Inner.inner ℂ w) hy').trans (hw y'))
  have hg := Langlands.Analysis.analyticUnitComponentVanishing c d hcan hcder
    (includeCompact k) hzero g hk ⟨v, hv⟩
  exact (hcval ⟨v, hv⟩ g).symm.trans hg

end Langlands.Automorphic.HilbertCoefficientComparison
