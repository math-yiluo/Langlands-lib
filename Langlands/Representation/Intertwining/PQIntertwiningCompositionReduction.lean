import Langlands.Representation.Intertwining.PQIntegralIntertwiningStatements
import Langlands.Representation.Intertwining.PQIntertwiningOperatorProof
import Langlands.Representation.Jacquet.OppositeIwahoriBasisAbstract

/-! # Reduction of Renard VII.3.5 (i) to geometric inputs -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry MeasureTheory Topology Filter Pointwise
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

section Topology

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

/-- A function on a topological group that is invariant under right translation by an open
subgroup is continuous. -/
theorem continuous_of_forall_mul_openSubgroup {X : Type*} [TopologicalSpace X] {φ : Γ → X}
    (K : OpenSubgroup Γ) (h : ∀ (x : Γ) (k : K), φ (x * k) = φ x) : Continuous φ := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  apply Filter.EventuallyEq.continuousAt (y := φ x)
  have hmem : (fun y => x⁻¹ * y) ⁻¹' (K : Set Γ) ∈ 𝓝 x := by
    apply (K.isOpen.preimage (continuous_const.mul continuous_id)).mem_nhds
    simp
  filter_upwards [hmem] with y hy
  have := h x ⟨x⁻¹ * y, hy⟩
  simpa using this

omit [IsTopologicalGroup Γ] in
/-- In a locally compact nonarchimedean group every compact set lies in a compact clopen
set. -/
theorem exists_isCompact_isClopen_superset [NonarchimedeanGroup Γ] [LocallyCompactSpace Γ]
    {S : Set Γ} (hS : IsCompact S) : ∃ C : Set Γ, S ⊆ C ∧ IsCompact C ∧ IsClopen C := by
  obtain ⟨U₀, hU₀c, -⟩ := Jacquet.exists_isCompact_openSubgroup_subset
    (Filter.univ_mem (f := 𝓝 (1 : Γ)))
  refine ⟨S * (U₀ : Set Γ), Set.subset_mul_left S U₀.one_mem, hS.mul hU₀c, ?_, ?_⟩
  · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    have hxU : (fun y => x⁻¹ * y) ⁻¹' (U₀ : Set Γ) ∈ 𝓝 x := by
      apply (U₀.isOpen.preimage (continuous_const.mul continuous_id)).mem_nhds
      simp
    refine Filter.mem_of_superset hxU fun y hy hyC => hx ?_
    obtain ⟨s, hs, w, hw, hsw⟩ := Set.mem_mul.mp hyC
    refine Set.mem_mul.mpr ⟨s, hs, w * (x⁻¹ * y)⁻¹, U₀.mul_mem hw (U₀.inv_mem hy), ?_⟩
    rw [← mul_assoc, hsw]
    group
  · exact U₀.isOpen.mul_left

end Topology

open GroupScheme

/-- Uniqueness behind Renard VII.3.4: for a `PQ`-regular `σ`, two intertwining operators
`i_P^G(σ) → i_Q^G(σ)` that agree at `1` on every `f ∈ F̃^{<1̄}_{PQ}(σ)` are equal. -/
theorem pqIntertwiner_eq_of_eval_one :
    ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
      [IsNonarchimedeanLocalField k] [T2Space k]
      (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
      haveI := hG.isAffineHom
      letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
      ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
        (P M N Q U : GroupScheme (Spec (CommRingCat.of k)))
        (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
        (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
        (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
        (hmul : IsIso (subgroupMultiplication l r))
        (q : Q ⟶ G) (lQ : M ⟶ Q) (rQ : U ⟶ Q)
        (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
        (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
        (hmulQ : IsIso (subgroupMultiplication lQ rQ))
        (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ M),
        IsSplitComponent a →
        haveI := hl.isConnectedReductive.isAffineHom
        letI := leviPointTopology l hl
        ∀ (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M)),
          IsPQRegular p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ a σ →
          ∀ J J' : ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation.IntertwiningMap
              ((leviInductionFunctor q lQ rQ hq hrQ hlQ hmulQ).obj σ).representation,
            (∀ f : (leviInductionFunctor p l r hp hr hl hmul).obj σ,
              f ∈ (boundaryVanishingSubfunctor p l r hp hr hl hmul q
                (identityParabolicDoubleCoset p q)).obj σ →
              Induction.eval (pointImage q)
                  (inducingRepresentation
                    (isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ hmulQ)
                    (isClosed_pointImage_comp q rQ hq.isClosedSubgroup hrQ.1.isClosedSubgroup)
                    (SmoothRep.pullback (leviPointsEquiv q lQ hq hlQ).symm σ)) (J f) 1 =
                Induction.eval (pointImage q)
                  (inducingRepresentation
                    (isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ hmulQ)
                    (isClosed_pointImage_comp q rQ hq.isClosedSubgroup hrQ.1.isClosedSubgroup)
                    (SmoothRep.pullback (leviPointsEquiv q lQ hq hlQ).symm σ)) (J' f) 1) →
            J = J' := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M N Q U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ A a ha
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  intro σ hregular J J' hJJ'
  let I := (leviInductionFunctor p l r hp hr hl hmul).obj σ
  let R := (leviJacquetInductionFunctor.{u, v} p l r hp hr hl hmul
    q lQ rQ hq hrQ hlQ hmulQ).obj σ
  let T := boundarySupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
    (identityParabolicDoubleCoset p q)
  obtain ⟨F, hF⟩ := leviFrobeniusReciprocity k G hG Q M U q lQ rQ hq hlQ hrQ hmulQ I σ
  change _ ≃ₗ[ℂ] R.ρ.IntertwiningMap σ.representation at F
  let incl : (T.obj σ).toRepresentation.IntertwiningMap R.ρ :=
    { toLinearMap := (T.obj σ).toSubmodule.subtype
      isIntertwining' _ := rfl }
  obtain ⟨K, -, hunique⟩ := existsUnique_intertwining_extension
    (ρ := R.ρ) (rationalPoints.map a)
    ha.isCentralSplitTorus.isCentral.map_mem_center (T.obj σ) ((F J).comp incl) hregular
  apply F.injective
  have h1 : F J = K := hunique _ fun _ => rfl
  have h2 : F J' = K := by
    apply hunique
    intro x
    obtain ⟨f, hf, hfx⟩ := x.property
    calc F J' (x : R) = F J' (Jacquet.Localization.mk I.representation
          (pointImage (rQ ≫ q)) 1 f) := congrArg (F J') hfx.symm
      _ = F J (Jacquet.Localization.mk I.representation (pointImage (rQ ≫ q)) 1 f) :=
          (hF J' f).trans ((hJJ' f hf).symm.trans (hF J f).symm)
      _ = F J (x : R) := congrArg (F J) hfx
  rw [h1, h2]


set_option linter.unusedVariables false in
/-- Renard's description of `F̃^{<1̄}_{PQ}` (VII.3.5, proof of (i), printed p.239 / PDF p.245):
for parabolics `P = MN`, `Q = MU` with the same Levi and an opposite `P̄ = MN̄`, a function
`f ∈ i_P^G(σ)` vanishes on `closure(PQ) \ PQ` exactly when its restriction to
`V = N̄(F) ∩ U(F)` vanishes outside a compact subset of `V`. -/
def PQBoundaryVanishingCompactSupportStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M N Q U Pb Nb : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r))
      (q : Q ⟶ G) (lQ : M ⟶ Q) (rQ : U ⟶ Q)
      (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
      (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
      (hmulQ : IsIso (subgroupMultiplication lQ rQ))
      (pb : Pb ⟶ G) (lb : M ⟶ Pb) (rb : Nb ⟶ Pb)
      (_hpb : IsParabolicSubgroup pb) (_hlb : IsRationalLeviSubgroup lb)
      (_hrb : LeviSubgroup.IsGeometricUnipotentRadical rb)
      (_hmulb : IsIso (subgroupMultiplication lb rb)),
      l ≫ p = lQ ≫ q →
      lb ≫ pb = l ≫ p →
      pointImage p ⊓ pointImage pb = pointImage (l ≫ p) →
      let V : Subgroup (rationalPoints G) := pointImage (rb ≫ pb) ⊓ pointImage (rQ ≫ q)
      haveI := hl.isConnectedReductive.isAffineHom
      letI := leviPointTopology l hl
      ∀ (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
        (f : (leviInductionFunctor p l r hp hr hl hmul).obj σ),
        f ∈ (boundaryVanishingSubfunctor p l r hp hr hl hmul q
            (identityParabolicDoubleCoset p q)).obj σ ↔
          ∃ K : Set V, IsCompact K ∧ ∀ x : V, x ∉ K →
            Induction.eval (pointImage p)
              (inducingRepresentation
                (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
                (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
                (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm σ)) f x = 0

set_option linter.unusedVariables false in
/-- The product decomposition used in Renard VII.3.5 (proof of (i), printed p.239 / PDF p.245):
under `d(P₁, P₂) + d(P₂, P₃) = d(P₁, P₃)` and `d(P₁, P₂) = 1` (the setting of
`PQIntertwiningCompositionStatement`), multiplication `V₁₂ × V₂₃ → V₁₃`, `(w, u) ↦ w u`, is a
homeomorphism, where `V₁₂ = N̄₁(F) ∩ N₂(F)`, `V₂₃ = N̄₂(F) ∩ N₃(F)`, `V₁₃ = N̄₁(F) ∩ N₃(F)`. -/
def PQCompositionProductStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (M P₁ N₁ P₂ N₂ P₃ N₃ Pb₁ Nb₁ Pb₂ Nb₂ Pb₃ Nb₃ : GroupScheme (Spec (CommRingCat.of k)))
      (p₁ : P₁ ⟶ G) (l₁ : M ⟶ P₁) (r₁ : N₁ ⟶ P₁)
      (hp₁ : IsParabolicSubgroup p₁) (hl₁ : IsRationalLeviSubgroup l₁)
      (hr₁ : LeviSubgroup.IsGeometricUnipotentRadical r₁)
      (hmul₁ : IsIso (subgroupMultiplication l₁ r₁))
      (p₂ : P₂ ⟶ G) (l₂ : M ⟶ P₂) (r₂ : N₂ ⟶ P₂)
      (hp₂ : IsParabolicSubgroup p₂) (hl₂ : IsRationalLeviSubgroup l₂)
      (hr₂ : LeviSubgroup.IsGeometricUnipotentRadical r₂)
      (hmul₂ : IsIso (subgroupMultiplication l₂ r₂))
      (p₃ : P₃ ⟶ G) (l₃ : M ⟶ P₃) (r₃ : N₃ ⟶ P₃)
      (hp₃ : IsParabolicSubgroup p₃) (hl₃ : IsRationalLeviSubgroup l₃)
      (hr₃ : LeviSubgroup.IsGeometricUnipotentRadical r₃)
      (hmul₃ : IsIso (subgroupMultiplication l₃ r₃))
      (pb₁ : Pb₁ ⟶ G) (lb₁ : M ⟶ Pb₁) (rb₁ : Nb₁ ⟶ Pb₁)
      (_hpb₁ : IsParabolicSubgroup pb₁) (_hlb₁ : IsRationalLeviSubgroup lb₁)
      (_hrb₁ : LeviSubgroup.IsGeometricUnipotentRadical rb₁)
      (_hmulb₁ : IsIso (subgroupMultiplication lb₁ rb₁))
      (pb₂ : Pb₂ ⟶ G) (lb₂ : M ⟶ Pb₂) (rb₂ : Nb₂ ⟶ Pb₂)
      (_hpb₂ : IsParabolicSubgroup pb₂) (_hlb₂ : IsRationalLeviSubgroup lb₂)
      (_hrb₂ : LeviSubgroup.IsGeometricUnipotentRadical rb₂)
      (_hmulb₂ : IsIso (subgroupMultiplication lb₂ rb₂))
      (pb₃ : Pb₃ ⟶ G) (lb₃ : M ⟶ Pb₃) (rb₃ : Nb₃ ⟶ Pb₃)
      (_hpb₃ : IsParabolicSubgroup pb₃) (_hlb₃ : IsRationalLeviSubgroup lb₃)
      (_hrb₃ : LeviSubgroup.IsGeometricUnipotentRadical rb₃)
      (_hmulb₃ : IsIso (subgroupMultiplication lb₃ rb₃)),
      l₂ ≫ p₂ = l₁ ≫ p₁ → l₃ ≫ p₃ = l₁ ≫ p₁ →
      lb₁ ≫ pb₁ = l₁ ≫ p₁ → lb₂ ≫ pb₂ = l₁ ≫ p₁ → lb₃ ≫ pb₃ = l₁ ≫ p₁ →
      pointImage p₁ ⊓ pointImage pb₁ = pointImage (l₁ ≫ p₁) →
      pointImage p₂ ⊓ pointImage pb₂ = pointImage (l₁ ≫ p₁) →
      pointImage p₃ ⊓ pointImage pb₃ = pointImage (l₁ ≫ p₁) →
      ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ M),
        IsSplitComponent a →
        let rootsIn : SubgroupFunctor G → Set (characterLattice A) := fun F =>
          RelativeRoot.subgroupRelativeRoots (a ≫ l₁ ≫ p₁) F ∩
            RelativeRoot.indivisibleRoots (a ≫ l₁ ≫ p₁)
        let d : SubgroupFunctor G → SubgroupFunctor G → ℕ := fun F F' =>
          (rootsIn F ∩ rootsIn F').ncard
        d (SubgroupFunctor.range (r₁ ≫ p₁)) (SubgroupFunctor.range (rb₂ ≫ pb₂)) +
            d (SubgroupFunctor.range (r₂ ≫ p₂)) (SubgroupFunctor.range (rb₃ ≫ pb₃)) =
          d (SubgroupFunctor.range (r₁ ≫ p₁)) (SubgroupFunctor.range (rb₃ ≫ pb₃)) →
        d (SubgroupFunctor.range (r₁ ≫ p₁)) (SubgroupFunctor.range (rb₂ ≫ pb₂)) = 1 →
        let V₁₂ : Subgroup (rationalPoints G) := pointImage (rb₁ ≫ pb₁) ⊓ pointImage (r₂ ≫ p₂)
        let V₂₃ : Subgroup (rationalPoints G) := pointImage (rb₂ ≫ pb₂) ⊓ pointImage (r₃ ≫ p₃)
        let V₁₃ : Subgroup (rationalPoints G) := pointImage (rb₁ ≫ pb₁) ⊓ pointImage (r₃ ≫ p₃)
        ∃ e : V₁₂ × V₂₃ ≃ₜ V₁₃, ∀ x : V₁₂ × V₂₃,
          ((e x : V₁₃) : rationalPoints G) = (x.1 : rationalPoints G) * (x.2 : rationalPoints G)

set_option linter.unusedVariables false in
/-- Clause 1 of `PQIntertwiningCompositionStatement` (Renard VII.3.5 (i)), stated on its own:
compatible Haar measures on `V₁₃` exist for all Haar measures on `V₁₂` and `V₂₃`. -/
def PQCompositionHaarStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (M P₁ N₁ P₂ N₂ P₃ N₃ Pb₁ Nb₁ Pb₂ Nb₂ Pb₃ Nb₃ : GroupScheme (Spec (CommRingCat.of k)))
      (p₁ : P₁ ⟶ G) (l₁ : M ⟶ P₁) (r₁ : N₁ ⟶ P₁)
      (hp₁ : IsParabolicSubgroup p₁) (hl₁ : IsRationalLeviSubgroup l₁)
      (hr₁ : LeviSubgroup.IsGeometricUnipotentRadical r₁)
      (hmul₁ : IsIso (subgroupMultiplication l₁ r₁))
      (p₂ : P₂ ⟶ G) (l₂ : M ⟶ P₂) (r₂ : N₂ ⟶ P₂)
      (hp₂ : IsParabolicSubgroup p₂) (hl₂ : IsRationalLeviSubgroup l₂)
      (hr₂ : LeviSubgroup.IsGeometricUnipotentRadical r₂)
      (hmul₂ : IsIso (subgroupMultiplication l₂ r₂))
      (p₃ : P₃ ⟶ G) (l₃ : M ⟶ P₃) (r₃ : N₃ ⟶ P₃)
      (hp₃ : IsParabolicSubgroup p₃) (hl₃ : IsRationalLeviSubgroup l₃)
      (hr₃ : LeviSubgroup.IsGeometricUnipotentRadical r₃)
      (hmul₃ : IsIso (subgroupMultiplication l₃ r₃))
      (pb₁ : Pb₁ ⟶ G) (lb₁ : M ⟶ Pb₁) (rb₁ : Nb₁ ⟶ Pb₁)
      (_hpb₁ : IsParabolicSubgroup pb₁) (_hlb₁ : IsRationalLeviSubgroup lb₁)
      (_hrb₁ : LeviSubgroup.IsGeometricUnipotentRadical rb₁)
      (_hmulb₁ : IsIso (subgroupMultiplication lb₁ rb₁))
      (pb₂ : Pb₂ ⟶ G) (lb₂ : M ⟶ Pb₂) (rb₂ : Nb₂ ⟶ Pb₂)
      (_hpb₂ : IsParabolicSubgroup pb₂) (_hlb₂ : IsRationalLeviSubgroup lb₂)
      (_hrb₂ : LeviSubgroup.IsGeometricUnipotentRadical rb₂)
      (_hmulb₂ : IsIso (subgroupMultiplication lb₂ rb₂))
      (pb₃ : Pb₃ ⟶ G) (lb₃ : M ⟶ Pb₃) (rb₃ : Nb₃ ⟶ Pb₃)
      (_hpb₃ : IsParabolicSubgroup pb₃) (_hlb₃ : IsRationalLeviSubgroup lb₃)
      (_hrb₃ : LeviSubgroup.IsGeometricUnipotentRadical rb₃)
      (_hmulb₃ : IsIso (subgroupMultiplication lb₃ rb₃)),
      l₂ ≫ p₂ = l₁ ≫ p₁ → l₃ ≫ p₃ = l₁ ≫ p₁ →
      lb₁ ≫ pb₁ = l₁ ≫ p₁ → lb₂ ≫ pb₂ = l₁ ≫ p₁ → lb₃ ≫ pb₃ = l₁ ≫ p₁ →
      pointImage p₁ ⊓ pointImage pb₁ = pointImage (l₁ ≫ p₁) →
      pointImage p₂ ⊓ pointImage pb₂ = pointImage (l₁ ≫ p₁) →
      pointImage p₃ ⊓ pointImage pb₃ = pointImage (l₁ ≫ p₁) →
      ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ M),
        IsSplitComponent a →
        let rootsIn : SubgroupFunctor G → Set (characterLattice A) := fun F =>
          RelativeRoot.subgroupRelativeRoots (a ≫ l₁ ≫ p₁) F ∩
            RelativeRoot.indivisibleRoots (a ≫ l₁ ≫ p₁)
        let d : SubgroupFunctor G → SubgroupFunctor G → ℕ := fun F F' =>
          (rootsIn F ∩ rootsIn F').ncard
        d (SubgroupFunctor.range (r₁ ≫ p₁)) (SubgroupFunctor.range (rb₂ ≫ pb₂)) +
            d (SubgroupFunctor.range (r₂ ≫ p₂)) (SubgroupFunctor.range (rb₃ ≫ pb₃)) =
          d (SubgroupFunctor.range (r₁ ≫ p₁)) (SubgroupFunctor.range (rb₃ ≫ pb₃)) →
        d (SubgroupFunctor.range (r₁ ≫ p₁)) (SubgroupFunctor.range (rb₂ ≫ pb₂)) = 1 →
        let V₁₂ : Subgroup (rationalPoints G) := pointImage (rb₁ ≫ pb₁) ⊓ pointImage (r₂ ≫ p₂)
        let V₂₃ : Subgroup (rationalPoints G) := pointImage (rb₂ ≫ pb₂) ⊓ pointImage (r₃ ≫ p₃)
        let V₁₃ : Subgroup (rationalPoints G) := pointImage (rb₁ ≫ pb₁) ⊓ pointImage (r₃ ≫ p₃)
        ∀ [MeasurableSpace V₁₂] [BorelSpace V₁₂] [MeasurableSpace V₂₃] [BorelSpace V₂₃]
          [MeasurableSpace V₁₃] [BorelSpace V₁₃],
          let Compatible : Measure V₁₂ → Measure V₂₃ → Measure V₁₃ → Prop :=
            fun haar₁₂ haar₂₃ haar₁₃ =>
              ∀ φ : rationalPoints G → ℂ, Continuous φ → HasCompactSupport φ →
                ∫ x : V₁₃, φ x ∂haar₁₃ =
                  ∫ u : V₂₃, ∫ w : V₁₂, φ ((w : rationalPoints G) * u) ∂haar₁₂ ∂haar₂₃
          ∀ (haar₁₂ : Measure V₁₂) (haar₂₃ : Measure V₂₃),
            haar₁₂.IsHaarMeasure → haar₂₃.IsHaarMeasure →
            ∃ haar₁₃ : Measure V₁₃, haar₁₃.IsHaarMeasure ∧ Compatible haar₁₂ haar₂₃ haar₁₃

set_option linter.unusedVariables false in
/-- The regularity part of clause 2 of `PQIntertwiningCompositionStatement` (Renard VII.3.5 (i),
printed pp.237–239), stated on its own: every `P₁P₃`-regular `σ` is `P₂P₃`- and
`P₁P₂`-regular. -/
def PQCompositionRegularityStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (M P₁ N₁ P₂ N₂ P₃ N₃ Pb₁ Nb₁ Pb₂ Nb₂ Pb₃ Nb₃ : GroupScheme (Spec (CommRingCat.of k)))
      (p₁ : P₁ ⟶ G) (l₁ : M ⟶ P₁) (r₁ : N₁ ⟶ P₁)
      (hp₁ : IsParabolicSubgroup p₁) (hl₁ : IsRationalLeviSubgroup l₁)
      (hr₁ : LeviSubgroup.IsGeometricUnipotentRadical r₁)
      (hmul₁ : IsIso (subgroupMultiplication l₁ r₁))
      (p₂ : P₂ ⟶ G) (l₂ : M ⟶ P₂) (r₂ : N₂ ⟶ P₂)
      (hp₂ : IsParabolicSubgroup p₂) (hl₂ : IsRationalLeviSubgroup l₂)
      (hr₂ : LeviSubgroup.IsGeometricUnipotentRadical r₂)
      (hmul₂ : IsIso (subgroupMultiplication l₂ r₂))
      (p₃ : P₃ ⟶ G) (l₃ : M ⟶ P₃) (r₃ : N₃ ⟶ P₃)
      (hp₃ : IsParabolicSubgroup p₃) (hl₃ : IsRationalLeviSubgroup l₃)
      (hr₃ : LeviSubgroup.IsGeometricUnipotentRadical r₃)
      (hmul₃ : IsIso (subgroupMultiplication l₃ r₃))
      (pb₁ : Pb₁ ⟶ G) (lb₁ : M ⟶ Pb₁) (rb₁ : Nb₁ ⟶ Pb₁)
      (_hpb₁ : IsParabolicSubgroup pb₁) (_hlb₁ : IsRationalLeviSubgroup lb₁)
      (_hrb₁ : LeviSubgroup.IsGeometricUnipotentRadical rb₁)
      (_hmulb₁ : IsIso (subgroupMultiplication lb₁ rb₁))
      (pb₂ : Pb₂ ⟶ G) (lb₂ : M ⟶ Pb₂) (rb₂ : Nb₂ ⟶ Pb₂)
      (_hpb₂ : IsParabolicSubgroup pb₂) (_hlb₂ : IsRationalLeviSubgroup lb₂)
      (_hrb₂ : LeviSubgroup.IsGeometricUnipotentRadical rb₂)
      (_hmulb₂ : IsIso (subgroupMultiplication lb₂ rb₂))
      (pb₃ : Pb₃ ⟶ G) (lb₃ : M ⟶ Pb₃) (rb₃ : Nb₃ ⟶ Pb₃)
      (_hpb₃ : IsParabolicSubgroup pb₃) (_hlb₃ : IsRationalLeviSubgroup lb₃)
      (_hrb₃ : LeviSubgroup.IsGeometricUnipotentRadical rb₃)
      (_hmulb₃ : IsIso (subgroupMultiplication lb₃ rb₃)),
      l₂ ≫ p₂ = l₁ ≫ p₁ → l₃ ≫ p₃ = l₁ ≫ p₁ →
      lb₁ ≫ pb₁ = l₁ ≫ p₁ → lb₂ ≫ pb₂ = l₁ ≫ p₁ → lb₃ ≫ pb₃ = l₁ ≫ p₁ →
      pointImage p₁ ⊓ pointImage pb₁ = pointImage (l₁ ≫ p₁) →
      pointImage p₂ ⊓ pointImage pb₂ = pointImage (l₁ ≫ p₁) →
      pointImage p₃ ⊓ pointImage pb₃ = pointImage (l₁ ≫ p₁) →
      ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ M),
        IsSplitComponent a →
        let rootsIn : SubgroupFunctor G → Set (characterLattice A) := fun F =>
          RelativeRoot.subgroupRelativeRoots (a ≫ l₁ ≫ p₁) F ∩
            RelativeRoot.indivisibleRoots (a ≫ l₁ ≫ p₁)
        let d : SubgroupFunctor G → SubgroupFunctor G → ℕ := fun F F' =>
          (rootsIn F ∩ rootsIn F').ncard
        d (SubgroupFunctor.range (r₁ ≫ p₁)) (SubgroupFunctor.range (rb₂ ≫ pb₂)) +
            d (SubgroupFunctor.range (r₂ ≫ p₂)) (SubgroupFunctor.range (rb₃ ≫ pb₃)) =
          d (SubgroupFunctor.range (r₁ ≫ p₁)) (SubgroupFunctor.range (rb₃ ≫ pb₃)) →
        d (SubgroupFunctor.range (r₁ ≫ p₁)) (SubgroupFunctor.range (rb₂ ≫ pb₂)) = 1 →
        haveI := hl₁.isConnectedReductive.isAffineHom
        letI := leviPointTopology l₁ hl₁
        ∀ σ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
          IsPQRegular p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁ p₃ l₃ r₃ hp₃ hr₃ hl₃ hmul₃ a σ →
          IsPQRegular p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂ p₃ l₃ r₃ hp₃ hr₃ hl₃ hmul₃ a σ ∧
          IsPQRegular p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁ p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂ a σ


section Abstract

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [NonarchimedeanGroup Γ]
  [LocallyCompactSpace Γ]

/-- The operator computation in Renard's proof of VII.3.5 (i), for abstract data. Three
representations `ρ₁, ρ₂, ρ₃` of `Γ` come with evaluation maps `Eᵢ` intertwining right translation,
and `ρ₁` is smooth. The sets `F₁₂`, `F₂₃`, `F₁₃` are characterized by compact support on
`V₁₂`, `V₂₃`, `V₁₃`; multiplication `V₁₂ × V₂₃ → V₁₃` is a homeomorphism; the measures are
compatible; `J₁₂, J₂₃, J₁₃` satisfy the integral formulas against linear forms. Then
`J₂₃ (J₁₂ f)` and `J₁₃ f` agree at `1` for every `f ∈ F₁₃`. -/
theorem eval_one_comp_eq_of_integral_formulas
    {S W₁ W₂ W₃ : Type*} [AddCommGroup S] [Module ℂ S]
    [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂]
    [AddCommGroup W₃] [Module ℂ W₃]
    (ρ₁ : Representation ℂ Γ W₁) (ρ₂ : Representation ℂ Γ W₂) (ρ₃ : Representation ℂ Γ W₃)
    (E₁ : W₁ → Γ → S) (E₂ : W₂ → Γ → S) (E₃ : W₃ → Γ → S)
    (hE₁ : ∀ (g : Γ) (f : W₁) (x : Γ), E₁ (ρ₁ g f) x = E₁ f (x * g))
    (hE₂ : ∀ (g : Γ) (f : W₂) (x : Γ), E₂ (ρ₂ g f) x = E₂ f (x * g))
    (hsmooth : IsSmooth ρ₁)
    (V₁₂ V₂₃ V₁₃ : Subgroup Γ) [MeasurableSpace V₁₂] [MeasurableSpace V₂₃]
    [MeasurableSpace V₁₃] (haar₁₂ : Measure V₁₂) (haar₂₃ : Measure V₂₃) (haar₁₃ : Measure V₁₃)
    (F₁₂ F₁₃ : Set W₁) (F₂₃ : Set W₂)
    (char₁₂ : ∀ f : W₁, (∃ K : Set V₁₂, IsCompact K ∧ ∀ x : V₁₂, x ∉ K → E₁ f x = 0) →
      f ∈ F₁₂)
    (char₂₃ : ∀ f : W₂, (∃ K : Set V₂₃, IsCompact K ∧ ∀ x : V₂₃, x ∉ K → E₂ f x = 0) →
      f ∈ F₂₃)
    (char₁₃ : ∀ f ∈ F₁₃, ∃ K : Set V₁₃, IsCompact K ∧ ∀ x : V₁₃, x ∉ K → E₁ f x = 0)
    (e : V₁₂ × V₂₃ ≃ₜ V₁₃) (he : ∀ x : V₁₂ × V₂₃, ((e x : V₁₃) : Γ) = (x.1 : Γ) * (x.2 : Γ))
    (hcompat : ∀ φ : Γ → ℂ, Continuous φ → HasCompactSupport φ →
      ∫ x : V₁₃, φ x ∂haar₁₃ = ∫ u : V₂₃, ∫ w : V₁₂, φ ((w : Γ) * u) ∂haar₁₂ ∂haar₂₃)
    (J₁₂ : ρ₁.IntertwiningMap ρ₂) (J₂₃ : ρ₂.IntertwiningMap ρ₃) (J₁₃ : ρ₁.IntertwiningMap ρ₃)
    (hJ₁₂ : ∀ f ∈ F₁₂, ∀ ℓ : Module.Dual ℂ S,
      ℓ (E₂ (J₁₂ f) 1) = ∫ x : V₁₂, ℓ (E₁ f x) ∂haar₁₂)
    (hJ₂₃ : ∀ f ∈ F₂₃, ∀ ℓ : Module.Dual ℂ S,
      ℓ (E₃ (J₂₃ f) 1) = ∫ x : V₂₃, ℓ (E₂ f x) ∂haar₂₃)
    (hJ₁₃ : ∀ f ∈ F₁₃, ∀ ℓ : Module.Dual ℂ S,
      ℓ (E₃ (J₁₃ f) 1) = ∫ x : V₁₃, ℓ (E₁ f x) ∂haar₁₃) :
    ∀ f ∈ F₁₃, E₃ (J₂₃ (J₁₂ f)) 1 = E₃ (J₁₃ f) 1 := by
  intro f hf
  have sep : ∀ x y : S, (∀ ℓ : Module.Dual ℂ S, ℓ x = ℓ y) → x = y := fun x y hxy =>
    sub_eq_zero.mp ((Module.forall_dual_apply_eq_zero_iff ℂ (x - y)).mp fun ℓ => by
      rw [map_sub, hxy ℓ, sub_self])
  have he' : ∀ (w : V₁₂) (u : V₂₃), ((e (w, u) : V₁₃) : Γ) = (w : Γ) * (u : Γ) :=
    fun w u => he (w, u)
  obtain ⟨K, hK, hKf⟩ := char₁₃ f hf
  have hT : IsCompact (e ⁻¹' K) := e.isCompact_preimage.mpr hK
  have hvan : ∀ (w : V₁₂) (u : V₂₃), E₁ f ((w : Γ) * u) ≠ 0 → e (w, u) ∈ K := by
    intro w u h
    by_contra hn
    apply h
    rw [← he' w u]
    exact hKf _ hn
  have h12 : ∀ u : V₂₃, ρ₁ u f ∈ F₁₂ := by
    intro u
    apply char₁₂
    refine ⟨Prod.fst '' (e ⁻¹' K), hT.image continuous_fst, fun w hw => ?_⟩
    rw [hE₁]
    by_contra h
    exact hw ⟨(w, u), hvan w u h, rfl⟩
  have hJu : ∀ (u : V₂₃) (ℓ : Module.Dual ℂ S),
      ℓ (E₂ (J₁₂ f) u) = ∫ w : V₁₂, ℓ (E₁ f ((w : Γ) * u)) ∂haar₁₂ := by
    intro u ℓ
    have h1 : E₂ (J₁₂ f) u = E₂ (J₁₂ (ρ₁ u f)) 1 := by
      rw [J₁₂.isIntertwining, hE₂, one_mul]
    rw [h1, hJ₁₂ _ (h12 u) ℓ]
    simp only [hE₁]
  have h23 : J₁₂ f ∈ F₂₃ := by
    apply char₂₃
    refine ⟨Prod.snd '' (e ⁻¹' K), hT.image continuous_snd, fun u hu => ?_⟩
    refine sep _ _ fun ℓ => ?_
    rw [hJu u ℓ, map_zero]
    have hzero : ∀ w : V₁₂, ℓ (E₁ f ((w : Γ) * u)) = 0 := by
      intro w
      by_contra h
      have h' : E₁ f ((w : Γ) * u) ≠ 0 := fun h0 => h (by rw [h0, map_zero])
      exact hu ⟨(w, u), hvan w u h', rfl⟩
    simp [hzero]
  obtain ⟨K₀, hK₀⟩ := hsmooth f
  have hfix : ∀ k : K₀, ρ₁ (k : Γ) f = f := fun k => hK₀ ⟨k, k.2⟩
  refine sep _ _ fun ℓ => ?_
  have hcont : Continuous fun x : Γ => ℓ (E₁ f x) :=
    continuous_of_forall_mul_openSubgroup K₀ fun x k => by rw [← hE₁, hfix k]
  obtain ⟨C, hSC, hCc, hCo⟩ :=
    exists_isCompact_isClopen_superset (hK.image (continuous_subtype_val (p := (· ∈ V₁₃))))
  let φ : Γ → ℂ := C.indicator fun x => ℓ (E₁ f x)
  have hφc : Continuous φ := hCo.continuous_indicator hcont
  have hφs : HasCompactSupport φ :=
    HasCompactSupport.intro' hCc hCo.isClosed fun x hx => Set.indicator_of_notMem hx _
  have hφV : ∀ x : V₁₃, φ x = ℓ (E₁ f x) := by
    intro x
    by_cases hx : (x : Γ) ∈ C
    · exact Set.indicator_of_mem hx _
    · show C.indicator (fun x => ℓ (E₁ f x)) x = _
      rw [Set.indicator_of_notMem hx, hKf x fun hxK => hx (hSC ⟨x, hxK, rfl⟩), map_zero]
  calc ℓ (E₃ (J₂₃ (J₁₂ f)) 1) = ∫ u : V₂₃, ℓ (E₂ (J₁₂ f) u) ∂haar₂₃ := hJ₂₃ _ h23 ℓ
    _ = ∫ u : V₂₃, ∫ w : V₁₂, φ ((w : Γ) * u) ∂haar₁₂ ∂haar₂₃ := by
        congr 1
        ext u
        rw [hJu u ℓ]
        congr 1
        ext w
        rw [← he' w u, hφV]
    _ = ∫ x : V₁₃, φ x ∂haar₁₃ := (hcompat φ hφc hφs).symm
    _ = ∫ x : V₁₃, ℓ (E₁ f x) ∂haar₁₃ := by
        congr 1
        ext x
        exact hφV x
    _ = ℓ (E₃ (J₁₃ f) 1) := (hJ₁₃ f hf ℓ).symm

end Abstract

/-- Renard VII.3.5 (i) from the four inputs isolated above: compact-support description of
`F̃^{<1̄}` (`PQBoundaryVanishingCompactSupportStatement`), the product decomposition
`V₁₃ = V₁₂ V₂₃` (`PQCompositionProductStatement`), existence of compatible Haar measures
(`PQCompositionHaarStatement`) and inheritance of regularity
(`PQCompositionRegularityStatement`). -/
theorem pqIntertwiningComposition_of_reductions
    (hChar : PQBoundaryVanishingCompactSupportStatement.{u, v})
    (hProd : PQCompositionProductStatement.{u})
    (hHaar : PQCompositionHaarStatement.{u})
    (hReg : PQCompositionRegularityStatement.{u, v}) :
    PQIntertwiningCompositionStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ M P₁ N₁ P₂ N₂ P₃ N₃ Pb₁ Nb₁ Pb₂ Nb₂ Pb₃ Nb₃ p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
      p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂ p₃ l₃ r₃ hp₃ hl₃ hr₃ hmul₃
      pb₁ lb₁ rb₁ hpb₁ hlb₁ hrb₁ hmulb₁ pb₂ lb₂ rb₂ hpb₂ hlb₂ hrb₂ hmulb₂
      pb₃ lb₃ rb₃ hpb₃ hlb₃ hrb₃ hmulb₃ h21 h31 hb1 hb2 hb3 ho1 ho2 ho3 A a ha rootsIn d hd hd1
    V₁₂ V₂₃ V₁₃ _ _ _ _ _ _ Compatible
  refine ⟨fun haar₁₂ haar₂₃ h₁₂ h₂₃ => hHaar k G hG M P₁ N₁ P₂ N₂ P₃ N₃ Pb₁ Nb₁ Pb₂ Nb₂ Pb₃ Nb₃ p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
      p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂ p₃ l₃ r₃ hp₃ hl₃ hr₃ hmul₃
      pb₁ lb₁ rb₁ hpb₁ hlb₁ hrb₁ hmulb₁ pb₂ lb₂ rb₂ hpb₂ hlb₂ hrb₂ hmulb₂
      pb₃ lb₃ rb₃ hpb₃ hlb₃ hrb₃ hmulb₃ h21 h31 hb1 hb2 hb3 ho1 ho2 ho3 A a ha hd hd1 haar₁₂ haar₂₃ h₁₂ h₂₃, ?_⟩
  have := hl₁.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l₁ hl₁
  intro σ hreg
  obtain ⟨hreg23, hreg12⟩ := hReg k G hG M P₁ N₁ P₂ N₂ P₃ N₃ Pb₁ Nb₁ Pb₂ Nb₂ Pb₃ Nb₃ p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
      p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂ p₃ l₃ r₃ hp₃ hl₃ hr₃ hmul₃
      pb₁ lb₁ rb₁ hpb₁ hlb₁ hrb₁ hmulb₁ pb₂ lb₂ rb₂ hpb₂ hlb₂ hrb₂ hmulb₂
      pb₃ lb₃ rb₃ hpb₃ hlb₃ hrb₃ hmulb₃ h21 h31 hb1 hb2 hb3 ho1 ho2 ho3 A a ha hd hd1 σ hreg
  refine ⟨hreg23, hreg12, ?_⟩
  intro haar₁₂ haar₂₃ haar₁₃ _ _ _ hcompat J₁₂ J₂₃ J₁₃ hJ₁₂ hJ₂₃ hJ₁₃
  obtain ⟨e, he⟩ := hProd k G hG M P₁ N₁ P₂ N₂ P₃ N₃ Pb₁ Nb₁ Pb₂ Nb₂ Pb₃ Nb₃ p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
      p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂ p₃ l₃ r₃ hp₃ hl₃ hr₃ hmul₃
      pb₁ lb₁ rb₁ hpb₁ hlb₁ hrb₁ hmulb₁ pb₂ lb₂ rb₂ hpb₂ hlb₂ hrb₂ hmulb₂
      pb₃ lb₃ rb₃ hpb₃ hlb₃ hrb₃ hmulb₃ h21 h31 hb1 hb2 hb3 ho1 ho2 ho3 A a ha hd hd1
  have char₁₃ := hChar k G hG P₁ M N₁ P₃ N₃ Pb₁ Nb₁ p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
    p₃ l₃ r₃ hp₃ hl₃ hr₃ hmul₃ pb₁ lb₁ rb₁ hpb₁ hlb₁ hrb₁ hmulb₁ h31.symm hb1 ho1 σ
  have char₁₂ := hChar k G hG P₁ M N₁ P₂ N₂ Pb₁ Nb₁ p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
    p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂ pb₁ lb₁ rb₁ hpb₁ hlb₁ hrb₁ hmulb₁ h21.symm hb1 ho1 σ
  have ho2' : pointImage p₂ ⊓ pointImage pb₂ = pointImage (l₂ ≫ p₂) := by
    rw [h21]
    exact ho2
  have char₂₃ := hChar k G hG P₂ M N₂ P₃ N₃ Pb₂ Nb₂ p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂
    p₃ l₃ r₃ hp₃ hl₃ hr₃ hmul₃ pb₂ lb₂ rb₂ hpb₂ hlb₂ hrb₂ hmulb₂ (h21.trans h31.symm)
    (hb2.trans h21.symm) ho2' σ
  let I₁ := (leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj σ
  let I₂ := (leviInductionFunctor p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂).obj σ
  let I₃ := (leviInductionFunctor p₃ l₃ r₃ hp₃ hr₃ hl₃ hmul₃).obj σ
  let E₁ : I₁ → rationalPoints G → σ := fun f x =>
    Induction.eval (pointImage p₁)
      (inducingRepresentation
        (isSemidirectDecomposition_pointImage p₁ l₁ r₁ hp₁.isClosedSubgroup hr₁ hmul₁)
        (isClosed_pointImage_comp p₁ r₁ hp₁.isClosedSubgroup hr₁.1.isClosedSubgroup)
        (SmoothRep.pullback (leviPointsEquiv p₁ l₁ hp₁ hl₁).symm σ)) f x
  let E₂ : I₂ → rationalPoints G → σ := fun f x =>
    Induction.eval (pointImage p₂)
      (inducingRepresentation
        (isSemidirectDecomposition_pointImage p₂ l₂ r₂ hp₂.isClosedSubgroup hr₂ hmul₂)
        (isClosed_pointImage_comp p₂ r₂ hp₂.isClosedSubgroup hr₂.1.isClosedSubgroup)
        (SmoothRep.pullback (leviPointsEquiv p₂ l₂ hp₂ hl₂).symm σ)) f x
  let E₃ : I₃ → rationalPoints G → σ := fun f x =>
    Induction.eval (pointImage p₃)
      (inducingRepresentation
        (isSemidirectDecomposition_pointImage p₃ l₃ r₃ hp₃.isClosedSubgroup hr₃ hmul₃)
        (isClosed_pointImage_comp p₃ r₃ hp₃.isClosedSubgroup hr₃.1.isClosedSubgroup)
        (SmoothRep.pullback (leviPointsEquiv p₃ l₃ hp₃ hl₃).symm σ)) f x
  let F₁₂ : Set I₁ := {f | f ∈ (boundaryVanishingSubfunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁ p₂
    (identityParabolicDoubleCoset p₁ p₂)).obj σ}
  let F₁₃ : Set I₁ := {f | f ∈ (boundaryVanishingSubfunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁ p₃
    (identityParabolicDoubleCoset p₁ p₃)).obj σ}
  let F₂₃ : Set I₂ := {f | f ∈ (boundaryVanishingSubfunctor p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂ p₃
    (identityParabolicDoubleCoset p₂ p₃)).obj σ}
  refine pqIntertwiner_eq_of_eval_one k G hG P₁ M N₁ P₃ N₃ p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
    p₃ l₃ r₃ hp₃ hl₃ hr₃ hmul₃ A a ha σ hreg _ _
    (eval_one_comp_eq_of_integral_formulas (S := σ) I₁.representation I₂.representation
      I₃.representation E₁ E₂ E₃ (fun _ _ _ => rfl) (fun _ _ _ => rfl) I₁.property
      V₁₂ V₂₃ V₁₃ haar₁₂ haar₂₃ haar₁₃ F₁₂ F₁₃ F₂₃ ?c₁₂ ?c₂₃ ?c₁₃ e he hcompat J₁₂ J₂₃ J₁₃
      ?j₁₂ ?j₂₃ ?j₁₃)
  case c₁₂ => exact fun f h => (char₁₂ f).mpr h
  case c₂₃ => exact fun f h => (char₂₃ f).mpr h
  case c₁₃ => exact fun f h => (char₁₃ f).mp h
  case j₁₂ => exact fun f hf ℓ => (hJ₁₂ f hf ℓ).2
  case j₂₃ => exact fun f hf ℓ => (hJ₂₃ f hf ℓ).2
  case j₁₃ => exact fun f hf ℓ => (hJ₁₃ f hf ℓ).2

set_option linter.defProp false in
/-- The implication of `pqIntertwiningComposition_of_reductions`, recorded as a definition:
the four inputs together imply `PQIntertwiningCompositionStatement`. -/
def pqIntertwiningCompositionOfReductions :
    PQBoundaryVanishingCompactSupportStatement.{u, v} → PQCompositionProductStatement.{u} →
      PQCompositionHaarStatement.{u} → PQCompositionRegularityStatement.{u, v} →
      PQIntertwiningCompositionStatement.{u, v} :=
  pqIntertwiningComposition_of_reductions

end Langlands.Aubert.General.RepresentedParabolic
