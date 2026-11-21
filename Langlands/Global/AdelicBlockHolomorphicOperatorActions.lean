import Langlands.Global.AdelicEisensteinDifferentialParameters
import Langlands.Global.AdelicEisensteinFiniteParameters
import Langlands.Automorphic.OperatorSubquotientPullback

/-! # Holomorphic families of block-section operators -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option autoImplicit false

namespace Langlands.Global.EisensteinJet

open Langlands.Automorphic Langlands.GeneralLinear

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}
  {E : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {V : Type w} [AddCommGroup V] [Module ℂ V]

/-- The free operator action on a fixed section carrier with parameter-dependent
finite and enveloping actions and a fixed infinite compact action. -/
def sectionOperatorAction (R : E → Representation ℂ (FiniteAdelicGL F n) V)
    (C : Representation ℂ (standardInfiniteCompact F n) V)
    (D : E → ArchimedeanGL.EnvelopingAlgebra F n →ₐ[ℂ] Module.End ℂ V)
    (t : E) : FreeOperatorAlgebra F n →ₐ[ℂ] Module.End ℂ V :=
  FreeAlgebra.lift ℂ (Sum.elim (Sum.elim (R t) C) (D t))

set_option backward.isDefEq.respectTransparency false in
omit [NumberField F] in
private theorem enveloping_mem
    (D : E → ArchimedeanGL.EnvelopingAlgebra F n →ₐ[ℂ] Module.End ℂ V)
    (hD : ∀ (X : ArchimedeanGL.RealLieAlgebra F n) (v : V),
      (fun t => D t (ArchimedeanGL.envelopingGenerator F n (ArchimedeanGL.complexify F n X)) v) ∈
        finiteHolomorphicSections E V)
    (a : ArchimedeanGL.EnvelopingAlgebra F n) (v : V) :
    (fun t => D t a v) ∈ finiteHolomorphicSections E V := by
  obtain ⟨b, rfl⟩ := RingCon.mkₐ_surjective (α := ℂ)
    (UniversalEnvelopingAlgebra.ringCon ℂ (ArchimedeanGL.ComplexLieAlgebra F n)) a
  change (fun t => D t
    (UniversalEnvelopingAlgebra.mkAlgHom ℂ (ArchimedeanGL.ComplexLieAlgebra F n) b) v) ∈
      finiteHolomorphicSections E V
  induction b using TensorAlgebra.induction generalizing v with
  | algebraMap z =>
    simpa only [AlgHom.commutes, Module.algebraMap_end_apply] using
      FiniteHolomorphicSections.const_mem (E := E) (z • v)
  | «ι» Z =>
    change (fun t => D t (ArchimedeanGL.envelopingGenerator F n Z) v) ∈
      finiteHolomorphicSections E V
    induction Z using TensorProduct.inductionOn with
    | tmul z X =>
      have hz : z ⊗ₜ[ℝ] X = z • ArchimedeanGL.complexify F n X := by
        rw [ArchimedeanGL.complexify_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      simp only [hz, map_smul, LinearMap.smul_apply]
      exact (finiteHolomorphicSections E V).smul_mem z (hD X v)
    | add X Y hX hY =>
      simp only [map_add, LinearMap.add_apply]
      exact (finiteHolomorphicSections E V).add_mem hX hY
  | mul a b ha hb =>
    simp only [map_mul, Module.End.mul_apply]
    exact FiniteHolomorphicSections.apply_mem
      (fun t => D t (UniversalEnvelopingAlgebra.mkAlgHom ℂ
        (ArchimedeanGL.ComplexLieAlgebra F n) a)) ha (hb v)
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply]
    exact (finiteHolomorphicSections E V).add_mem (ha v) (hb v)

/-- Finite holomorphic expansions for finite translations and real Lie
directions give expansions for every generator of the free operator algebra. -/
theorem sectionOperatorAction_generator_mem
    (R : E → Representation ℂ (FiniteAdelicGL F n) V)
    (C : Representation ℂ (standardInfiniteCompact F n) V)
    (D : E → ArchimedeanGL.EnvelopingAlgebra F n →ₐ[ℂ] Module.End ℂ V)
    (hR : ∀ (g : FiniteAdelicGL F n) (v : V),
      (fun t => R t g v) ∈ finiteHolomorphicSections E V)
    (hD : ∀ (X : ArchimedeanGL.RealLieAlgebra F n) (v : V),
      (fun t => D t (ArchimedeanGL.envelopingGenerator F n (ArchimedeanGL.complexify F n X)) v) ∈
        finiteHolomorphicSections E V)
    (i : OperatorIndex F n) (v : V) :
    (fun t => sectionOperatorAction R C D t (FreeAlgebra.ι ℂ i) v) ∈ finiteHolomorphicSections E V := by
  simp only [sectionOperatorAction, FreeAlgebra.lift_ι_apply]
  rcases i with ((g | k) | a)
  · exact hR g v
  · exact FiniteHolomorphicSections.const_mem (C k v)
  · exact enveloping_mem D hD a v

end Langlands.Global.EisensteinJet

namespace Langlands.Global.AdelicGroupPoints.IsIwasawaCompact

open InfiniteAdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  {p : P ⟶ G} {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)
  {E : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  (e : E →ₗ[ℂ] ComplexCharacterParameter F P)
  {V : Type w} [AddCommGroup V] [Module ℂ V]
  (j : V →ₗ[ℂ] (AdelicGroupPoints F G → ℂ))

/-- A family realized by deformed finite translation has a finite holomorphic
expansion on the section carrier. -/
theorem mem_finiteHolomorphicSections_of_parameterRightAction
    [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left]
    (hj : Function.Injective j)
    (L : Subgroup (FiniteAdelicGroupPoints F G))
    (hLo : IsOpen (L : Set (FiniteAdelicGroupPoints F G)))
    (hLc : IsCompact (L : Set (FiniteAdelicGroupPoints F G)))
    (hL : ∀ l : L, ofFinite F G l.val ∈ K)
    (hFin : ∀ k ∈ K, finite F G k ∈ L)
    (hInf : ∀ k ∈ K, ofInfinite F G (infinite F G k) ∈ K)
    (b : FiniteAdelicGroupPoints F G) (v : V) (f : E → V)
    (hf : ∀ t, j (f t) = hK.parameterRightAction (e t) (ofFinite F G b) (j v)) :
    f ∈ finiteHolomorphicSections E V := by
  apply FiniteHolomorphicSections.mem_of_injective j hj
  simp only [hf]
  exact FiniteHolomorphicSections.mem_iff.mpr
    (hK.finiteExpansion_parameterRightAction L hLo hLc hL hFin hInf e b (j v))

/-- A family realized by the deformed derivative in one real direction has a
finite holomorphic expansion on the section carrier. -/
theorem mem_finiteHolomorphicSections_of_parameterDirectionalSection
    {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hH : hK.HasSmoothHeightPairings hsmooth)
    (hj : Function.Injective j)
    (X : smoothModel F d) (v : V)
    (hv : letI := fun q : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F q
      letI := smoothChartedSpace F G hsmooth
      ∀ b : FiniteAdelicGroupPoints F G,
        ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞ (fun a => j v (pair F G a b)))
    (f : E → V)
    (hf : ∀ t, j (f t) = hK.parameterDirectionalSection hsmooth (e t) X (j v)) :
    f ∈ finiteHolomorphicSections E V := by
  apply FiniteHolomorphicSections.mem_of_injective j hj
  simp only [hf]
  exact hK.parameterDirectionalSection_mem_finiteHolomorphicSections hsmooth e hH X (j v) hv

end Langlands.Global.AdelicGroupPoints.IsIwasawaCompact
