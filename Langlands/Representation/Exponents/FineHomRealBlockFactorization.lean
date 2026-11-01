import Langlands.Representation.Exponents.InnerInducedCoarseScalar
import Langlands.Representation.Parabolic.SecondAdjointnessProof

/-! Factorization of every fine Hom through a coarse real block. -/

noncomputable section

namespace Langlands.FineHomRealBlockFactorization

open GeneralLinear Geometric RelativeJacquetMultiplicity RelativeRegularComparison

universe uF uV uW uX uY

/-- A coarse endomorphism acting identically on the selected real block acts
identically on every fine Hom whose actual inner induction lies in that block. -/
theorem fineMapFixedByProjector
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    {n : ℕ} (hn : 0 < n) (B : BlockShape n) (S : BlockRefinement B)
    (τ : Rep.{uV} ℂ (refinedLevi F.Carrier B S))
    (π : Rep.{uW} ℂ (B.Levi F.Carrier))
    (x : Fin B.length → ℝ)
    (a : π.ρ.IntertwiningMap π.ρ)
    (ha : ∀ v : π, v ∈ T.realCentralBlock B π.ρ x → a v = v)
    (hsource : T.realCentralBlock B (innerInduced T B S τ).ρ x = ⊤) :
    letI := T.topology
    IsAdmissible τ.ρ → IsAdmissible π.ρ →
    ∀ f : τ.ρ.IntertwiningMap (T.normalizedRefinedOppositeJacquet B S π.ρ),
      (T.normalizedRefinedOppositeJacquetMap B S a).comp f = f := by
  let := T.topology
  intro hτ hπ f
  obtain ⟨E, _, htarget⟩ :=
    Parabolic.normalizedSecondAdjointness.{uF,uV,uW}.2 p F T n hn B S
  let g := (E τ π hτ hπ).symm f
  have hag : a.comp g = g := by
    ext v
    apply ha
    apply map_mem_groupedCentralCharacterSpace g _
    change v ∈ T.realCentralBlock B (innerInduced T B S τ).ρ x
    rw [hsource]
    trivial
  ext v
  have hnat := htarget τ π π hτ hπ hπ a g v
  rw [hag] at hnat
  change T.normalizedRefinedOppositeJacquetMap B S a (f v) = f v
  simpa only [g, LinearEquiv.apply_symm_apply] using hnat.symm

/-- Composition of the actual normalized refined opposite Jacquet maps,
proved on actual quotient representatives. -/
theorem jacquetMapComp
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
    (A : Rep.{uV} ℂ (B.Levi F.Carrier))
    (C : Rep.{uW} ℂ (B.Levi F.Carrier))
    (D : Rep.{uX} ℂ (B.Levi F.Carrier))
    (f : A.ρ.IntertwiningMap C.ρ) (g : C.ρ.IntertwiningMap D.ρ) :
    (T.normalizedRefinedOppositeJacquetMap B S g).comp
      (T.normalizedRefinedOppositeJacquetMap B S f) =
        T.normalizedRefinedOppositeJacquetMap B S (g.comp f) := by
  ext v
  rfl

/-- Postcomposing fine Hom maps by an actual coarse map is injective if a
map back makes a projector equal to the identity on the selected real block. -/
theorem fineHomPostcomposeInjective
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    {n : ℕ} (hn : 0 < n) (B : BlockShape n) (S : BlockRefinement B)
    (τ : Rep.{uV} ℂ (refinedLevi F.Carrier B S))
    (π : Rep.{uW} ℂ (B.Levi F.Carrier))
    (C : Rep.{uX} ℂ (B.Levi F.Carrier))
    (x : Fin B.length → ℝ)
    (r : π.ρ.IntertwiningMap C.ρ) (i : C.ρ.IntertwiningMap π.ρ)
    (hri : ∀ v : π, v ∈ T.realCentralBlock B π.ρ x → i (r v) = v)
    (hsource : T.realCentralBlock B (innerInduced T B S τ).ρ x = ⊤) :
    letI := T.topology
    IsAdmissible τ.ρ → IsAdmissible π.ρ →
    Function.Injective
      (fun f : τ.ρ.IntertwiningMap (T.normalizedRefinedOppositeJacquet B S π.ρ) =>
        (T.normalizedRefinedOppositeJacquetMap B S r).comp f) := by
  let := T.topology
  intro hτ hπ f g hfg
  have hf := fineMapFixedByProjector T hn B S τ π x (i.comp r) hri
    hsource hτ hπ f
  have hg := fineMapFixedByProjector T hn B S τ π x (i.comp r) hri
    hsource hτ hπ g
  rw [← hf, ← hg]
  ext v
  have h := congrArg (fun k => T.normalizedRefinedOppositeJacquetMap B S i (k v)) hfg
  have hcomp := jacquetMapComp T B S π C π r i
  exact (congrArg (fun k => k (f v)) hcomp).symm.trans
    (h.trans (congrArg (fun k => k (g v)) hcomp))

/-- The injection gives the corresponding finrank bound whenever its target
Hom space is finite dimensional. -/
theorem fineHomPostcomposeFinrankLe
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    {n : ℕ} (hn : 0 < n) (B : BlockShape n) (S : BlockRefinement B)
    (τ : Rep.{uV} ℂ (refinedLevi F.Carrier B S))
    (π : Rep.{uW} ℂ (B.Levi F.Carrier))
    (C : Rep.{uX} ℂ (B.Levi F.Carrier))
    (x : Fin B.length → ℝ)
    (r : π.ρ.IntertwiningMap C.ρ) (i : C.ρ.IntertwiningMap π.ρ)
    (hri : ∀ v : π, v ∈ T.realCentralBlock B π.ρ x → i (r v) = v)
    (hsource : T.realCentralBlock B (innerInduced T B S τ).ρ x = ⊤) :
    letI := T.topology
    IsAdmissible τ.ρ → IsAdmissible π.ρ →
    FiniteDimensional ℂ
      (τ.ρ.IntertwiningMap (T.normalizedRefinedOppositeJacquet B S C.ρ)) →
    Module.finrank ℂ
        (τ.ρ.IntertwiningMap (T.normalizedRefinedOppositeJacquet B S π.ρ)) ≤
      Module.finrank ℂ
        (τ.ρ.IntertwiningMap (T.normalizedRefinedOppositeJacquet B S C.ρ)) := by
  let := T.topology
  intro hτ hπ hfin
  let := hfin
  let L := Representation.IntertwiningMap.llcomp τ.ρ
    (T.normalizedRefinedOppositeJacquet B S π.ρ)
    (T.normalizedRefinedOppositeJacquet B S C.ρ)
    (T.normalizedRefinedOppositeJacquetMap B S r)
  have hL : Function.Injective L :=
    fineHomPostcomposeInjective T hn B S τ π C x r i hri hsource hτ hπ
  exact LinearMap.finrank_le_finrank_of_injective hL

/-- The actual nested scalar calculation supplies the source-block
hypothesis in the preceding injection for every coarse vector. -/
theorem nestedFineHomPostcomposeInjective
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    {n : ℕ} (hn : 0 < n) (B : BlockShape n) (Q : BlockRefinement B)
    (R : BlockRefinement (B.flatten Q)) (S : BlockRefinement B)
    (h : (B.flatten Q).flatten R = B.flatten S)
    (ω : Rep.{uV} ℂ (((B.flatten Q).flatten R).Levi F.Carrier))
    (π : Rep.{uW} ℂ (B.Levi F.Carrier))
    (C : Rep.{uX} ℂ (B.Levi F.Carrier)) :
    letI := T.topology
    Representation.IsIrreducible ω.ρ → IsAdmissible ω.ρ → IsUnitarizable ω.ρ →
    ∀ (v₀ : Fin ((B.flatten Q).flatten R).length → ℝ),
      IsPositiveRootParameter (B.flatten Q) R v₀ →
      let ωB : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier) := h ▸ ω
      let vB : Fin (B.flatten S).length → ℝ := h ▸ v₀
      ∀ (t : Fin B.length → ℝ)
        (r : π.ρ.IntertwiningMap C.ρ) (i : C.ρ.IntertwiningMap π.ρ),
        (∀ v : π,
          v ∈ T.realCentralBlock B π.ρ (fun k => (B.size k : ℝ) * t k) →
            i (r v) = v) →
        IsAdmissible (fineTwist T B S ωB vB t).ρ → IsAdmissible π.ρ →
        Function.Injective
          (fun f : (fineTwist T B S ωB vB t).ρ.IntertwiningMap
              (T.normalizedRefinedOppositeJacquet B S π.ρ) =>
            (T.normalizedRefinedOppositeJacquetMap B S r).comp f) := by
  let := T.topology
  dsimp only
  intro hi ha hu v₀ hv t r i hri hτ hπ
  exact fineHomPostcomposeInjective T hn B S _ π C _ r i hri
    (InnerInducedCoarseScalar.nestedRealBlockEqTop
      T B Q R S h ω hi ha hu v₀ hv t) hτ hπ

end Langlands.FineHomRealBlockFactorization
