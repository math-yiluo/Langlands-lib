import Langlands.BaseChange.TwistedInductionSpans
import Langlands.Representation.Category.ClassInvariants
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-! # Disjoint spans of twisted irreducible character lines -/

noncomputable section

namespace Langlands.BaseChange

open CategoryTheory MeasureTheory HarmonicAnalysis

universe uG z

variable {G : Type uG} [Group G] [TopologicalSpace G]

private abbrev ComplexIrreducible (G : Type uG) [Group G] [TopologicalSpace G] :=
  IrreducibleAdmissibleRep.{0,uG,z} (k := ℂ) (G := G)

private abbrev StableClass (θ : G ≃* G) :=
  {c : SmoothDualClass.{0,uG,z} (k := ℂ) (G := G) //
    ∃ A : ComplexIrreducible.{uG,z} G, SmoothDualClass.ofRep A = c ∧
    Nonempty (A.obj.representation.Equiv (A.obj.representation.comp θ.toMonoidHom))}

private theorem smoothDualClass_eq_iff_equiv {A B : ComplexIrreducible.{uG,z} G} :
    SmoothDualClass.ofRep A = SmoothDualClass.ofRep B ↔
      Nonempty (A.obj.representation.Equiv B.obj.representation) := by
  constructor
  · intro h
    obtain ⟨e⟩ : Nonempty (A ≅ B) := Quotient.exact h
    exact ⟨SmoothRep.equivOfIso
      ((irreducibleAdmissibleProperty (k := ℂ) (G := G)).ι.mapIso e)⟩
  · rintro ⟨e⟩
    apply Quotient.sound
    exact ⟨ObjectProperty.isoMk (irreducibleAdmissibleProperty (k := ℂ) (G := G))
      (SmoothRep.mkIso e)⟩

variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure] (θ : G ≃* G)

private def stableRepresentative (c : StableClass.{uG,z} θ) : ComplexIrreducible.{uG,z} G :=
  c.property.choose

private def stableIntertwiner (c : StableClass.{uG,z} θ) :
    let A := stableRepresentative θ c
    A.obj.representation.Equiv (A.obj.representation.comp θ.toMonoidHom) :=
  c.property.choose_spec.2.some

private def stableDistribution (c : StableClass.{uG,z} θ) : Distribution G :=
  twistedDistribution μ (stableRepresentative θ c).obj.representation
    (stableRepresentative θ c).property.2 (stableIntertwiner θ c).toLinearMap

private theorem linearIndependent_stableDistribution
    (hθ : ∀ U : OpenSubgroup G,
      ∃ K : OpenSubgroup G, K ≤ U ∧ IsCompact (K : Set G) ∧ ∀ k ∈ K, θ.symm k ∈ K) :
    LinearIndependent ℂ (stableDistribution μ θ : StableClass.{uG,z} θ → Distribution G) := by
  classical
  apply linearIndependent_iff_finset_linearIndependent.mpr
  intro s
  let A (i : s) : ComplexIrreducible.{uG,z} G := stableRepresentative θ i.val
  let V (i : s) : Type z := (A i).obj
  let ρ (i : s) : Representation ℂ G (V i) := (A i).obj.representation
  let T (i : s) : (ρ i).Equiv ((ρ i).comp θ.toMonoidHom) := stableIntertwiner θ i.val
  exact twistedDistribution_linearIndependent μ θ hθ ρ (fun i => (A i).property.2)
    (fun i => (A i).property.1) (fun i j hij h => hij (Subtype.ext (Subtype.ext
      (i.val.property.choose_spec.1.symm.trans (smoothDualClass_eq_iff_equiv.mpr h) |>.trans
        j.val.property.choose_spec.1)))) (fun i => (T i).toLinearMap)
    (fun i g => (T i).isIntertwining' g) (fun i => (T i).injective)

variable (P Q : ∀ (W : Type z) [AddCommGroup W] [Module ℂ W], Representation ℂ G W → Prop)

private def stableClassSet : Set (StableClass.{uG,z} θ) :=
  {c | ∃ A : ComplexIrreducible.{uG,z} G,
    SmoothDualClass.ofRep A = c.val ∧ P A.obj A.obj.representation}

private theorem twistedSpectrumSpan_le_span_stableDistribution :
    twistedSpectrumSpan μ θ P ≤
      Submodule.span ℂ (stableDistribution μ θ '' stableClassSet θ P) := by
  apply Submodule.span_le.mpr
  rintro d ⟨W, iAdd, iMod, π, hπ, T, hirr, hP, rfl⟩
  let := iAdd
  let := iMod
  let A : ComplexIrreducible.{uG,z} G := ⟨SmoothRep.of π hπ.1, hirr, hπ⟩
  let c : StableClass.{uG,z} θ := ⟨SmoothDualClass.ofRep A, A, rfl, ⟨T⟩⟩
  have hc : c ∈ stableClassSet θ P := ⟨A, rfl, hP⟩
  have he : SmoothDualClass.ofRep (stableRepresentative θ c) = SmoothDualClass.ofRep A :=
    c.property.choose_spec.1
  obtain ⟨e⟩ := smoothDualClass_eq_iff_equiv.mp he
  obtain ⟨a, ha⟩ := exists_twistedDistribution_eq_smul_of_equiv μ θ
    (stableRepresentative θ c).property.2 (stableRepresentative θ c).property.1 hπ e
    (stableIntertwiner θ c) T
  exact ha.symm ▸ Submodule.smul_mem _ a (Submodule.subset_span ⟨c, hc, rfl⟩)

/-- The twisted-character spans of two classes are disjoint when no member of one class
is equivalent to a member of the other. -/
theorem disjoint_twistedSpectrumSpan
    (hθ : ∀ U : OpenSubgroup G,
      ∃ K : OpenSubgroup G, K ≤ U ∧ IsCompact (K : Set G) ∧ ∀ k ∈ K, θ.symm k ∈ K)
    (hPQ : ∀ {V W : Type z} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
      {ρ : Representation ℂ G V} {π : Representation ℂ G W},
      P V ρ → Q W π → ¬ Nonempty (ρ.Equiv π)) :
    Disjoint (twistedSpectrumSpan μ θ P) (twistedSpectrumSpan μ θ Q) := by
  apply Disjoint.mono (twistedSpectrumSpan_le_span_stableDistribution μ θ P)
    (twistedSpectrumSpan_le_span_stableDistribution μ θ Q)
  apply (linearIndependent_stableDistribution.{uG,z} μ θ hθ).disjoint_span_image
  refine Set.disjoint_left.mpr ?_
  rintro c ⟨A, hA, hP⟩ ⟨B, hB, hQ⟩
  exact hPQ hP hQ (smoothDualClass_eq_iff_equiv.mp (hA.trans hB.symm))

/-- There is a projection fixing the twisted-character span of the first class
and killing the span of an inequivalent class. -/
theorem exists_twistedSpectrum_projection
    (hθ : ∀ U : OpenSubgroup G,
      ∃ K : OpenSubgroup G, K ≤ U ∧ IsCompact (K : Set G) ∧ ∀ k ∈ K, θ.symm k ∈ K)
    (hPQ : ∀ {V W : Type z} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
      {ρ : Representation ℂ G V} {π : Representation ℂ G W},
      P V ρ → Q W π → ¬ Nonempty (ρ.Equiv π)) :
    ∃ p : Distribution G →ₗ[ℂ] Distribution G,
      (∀ d, p d ∈ twistedSpectrumSpan μ θ P) ∧
      (∀ d ∈ twistedSpectrumSpan μ θ P, p d = d) ∧
      ∀ d ∈ twistedSpectrumSpan μ θ Q, p d = 0 := by
  let A := twistedSpectrumSpan μ θ P
  let B := twistedSpectrumSpan μ θ Q
  let f := B.mkQ.domRestrict A
  have hf : Function.Injective f := by
    rw [LinearMap.injective_domRestrict_iff, Submodule.ker_mkQ]
    exact disjoint_twistedSpectrumSpan μ θ P Q hθ hPQ
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf)
  let p := A.subtype.comp (g.comp B.mkQ)
  refine ⟨p, fun d => (g (B.mkQ d)).property, fun d hd => ?_, fun d hd => ?_⟩
  · exact congrArg Subtype.val (LinearMap.congr_fun hg (⟨d, hd⟩ : A))
  · have hzero : B.mkQ d = 0 := (Submodule.Quotient.mk_eq_zero (p := B)).mpr hd
    change (g (B.mkQ d) : Distribution G) = 0
    rw [hzero, map_zero]
    rfl

end Langlands.BaseChange
