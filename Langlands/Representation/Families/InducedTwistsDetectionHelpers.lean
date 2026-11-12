import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Aubert.General.DynamicParabolic
import Langlands.Representation.Aubert.General.InductionCarrierTransport
import Langlands.Representation.Smooth.FixedVectors.NormalizedJacquetBridgeProof
import Langlands.BruhatTits.Iwasawa.PointProducts
import Langlands.GroupScheme.Rational.StandardCocharacterProof

/-! # Auxiliary facts for the uniform induced-twist detector

A normal subgroup of a fixed compact subgroup is normalized by it; the Iwasawa
products of the minimal standard parabolic split into Levi and radical factors;
and generation by fixed vectors passes between an induced representation and the
induction of the universe-lifted inducing representation.
-/

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Renard.AlgebraicFamily.InducedTwistsDetection

open Langlands.GroupScheme Langlands.Aubert.General Langlands.Aubert.General.RepresentedParabolic

/-- If `K ≤ K₀` and `K` is normal in `K₀`, then `K₀` normalizes `K`. -/
theorem le_normalizer_of_subgroupOf_normal {H : Type*} [Group H] {K K₀ : Subgroup H}
    (hle : K ≤ K₀) (hn : (K.subgroupOf K₀).Normal) : K₀ ≤ Subgroup.normalizer K := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have hmem : (⟨h, hle hh⟩ : K₀) ∈ K.subgroupOf K₀ := hh
    have := hn.conj_mem _ hmem ⟨a, ha⟩
    exact this
  · intro hh
    have ha' : a⁻¹ ∈ K₀ := K₀.inv_mem ha
    have hK₀ : a * h * a⁻¹ ∈ K₀ := hle hh
    have hh₀ : h ∈ K₀ := by
      have : h = a⁻¹ * (a * h * a⁻¹) * a := by group
      rw [this]
      exact K₀.mul_mem (K₀.mul_mem ha' hK₀) ha
    have hmem : (⟨a * h * a⁻¹, hK₀⟩ : K₀) ∈ K.subgroupOf K₀ := hh
    have := hn.conj_mem _ hmem ⟨a⁻¹, ha'⟩
    have heq : a⁻¹ * (a * h * a⁻¹) * a⁻¹⁻¹ = h := by group
    change a⁻¹ * (a * h * a⁻¹) * a⁻¹⁻¹ ∈ K at this
    rwa [heq] at this

/-- Iwasawa products for the minimal standard parabolic give `g = m n k` with `m` in
the minimal standard Levi and `n` in its radical. -/
theorem exists_standard_minimal_factorization {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T) :
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    IsGenericCocharacter i ν →
    ∀ K₀ : Subgroup (rationalPoints G), BruhatTits.Iwasawa.StandardParabolicProducts i ν K₀ →
      ∀ g : rationalPoints G, ∃ m ∈ standardLeviPoints i ν ∅,
        ∃ n ∈ standardUnipotentPoints i ν ∅, ∃ k ∈ K₀, g = m * n * k := by
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  have := hG.isSeparated
  intro hν K₀ hprod g
  obtain ⟨⟨ζ, hζ⟩, hall⟩ := standardCocharacter k G hG T i hi ν hν ∅ (Set.empty_subset _)
  obtain ⟨hP, hM, hU⟩ := hall ζ hζ
  have hsd := dynamic_isSemidirectDecomposition (CommGroupScheme.groupHom ζ ≫ i)
    (Over.mk (𝟙 (Spec (CommRingCat.of k))))
  have hg : g ∈ (Set.univ : Set (rationalPoints G)) := Set.mem_univ g
  rw [(hprod ∅ (Set.empty_subset _)).1] at hg
  obtain ⟨x, hx, c, hc, rfl⟩ := Set.mem_mul.mp hg
  have hx' : x ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i)).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
    change x ∈ (standardParabolic i ν ∅).carrier (Over.mk (𝟙 _)) at hx
    rwa [hP] at hx
  let m := hsd.projection ⟨x, hx'⟩
  refine ⟨(m : rationalPoints G), ?_, (m : rationalPoints G)⁻¹ * x, ?_, c, hc, ?_⟩
  · change (m : rationalPoints G) ∈ (standardLevi i ν ∅).carrier (Over.mk (𝟙 _))
    rw [hM]
    exact m.property
  · change (m : rationalPoints G)⁻¹ * x ∈ (standardUnipotent i ν ∅).carrier (Over.mk (𝟙 _))
    rw [hU]
    exact hsd.projection_inv_mul_mem ⟨x, hx'⟩
  · group

section Universe

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance inducedTwistsHelpersPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- Generation by fixed vectors passes from the induction of the universe-lifted
inducing representation to the induction of the original one. -/
theorem leviInduction_generate_of_universeLift
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) (hp : IsParabolicSubgroup p)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r) (hl : IsRationalLeviSubgroup l)
    (hmul : IsIso (subgroupMultiplication l r)) :
    letI := leviPointTopology l hl
    ∀ (τ : SmoothRep.{0, u, v} ℂ (rationalPoints M)) (K : Subgroup (rationalPoints G)),
      (∀ S : Subrepresentation ((leviInductionFunctor.{u, max u v} p l r hp hr hl hmul).obj
          (SmoothRep.universeLift.{u} τ)).representation,
        fixedVectors ((leviInductionFunctor.{u, max u v} p l r hp hr hl hmul).obj
          (SmoothRep.universeLift.{u} τ)).representation K ≤ S.toSubmodule → S = ⊤) →
      ∀ S : Subrepresentation ((leviInductionFunctor.{u, v} p l r hp hr hl hmul).obj τ).representation,
        fixedVectors ((leviInductionFunctor.{u, v} p l r hp hr hl hmul).obj τ).representation K ≤
          S.toSubmodule → S = ⊤ := by
  let := leviPointTopology l hl
  intro τ K hgen
  let e := leviPointsEquiv p l hp hl
  let E : (SmoothRep.pullback e.symm τ).representation.Equiv
      (SmoothRep.pullback e.symm (SmoothRep.universeLift.{u} τ)).representation :=
    Representation.Equiv.mk (SmoothRep.universeLiftEquiv.{u} τ).toLinearEquiv
      (fun x => (SmoothRep.universeLiftEquiv.{u} τ).isIntertwining' (e.symm x))
  let F := normalizedInductionEquivOfEquiv
    (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup) E
  exact NormalizedJacquetBridge.generation_of_equiv F.symm K hgen

end Universe

end Langlands.Renard.AlgebraicFamily.InducedTwistsDetection
