import Langlands.Global.CompletionPadic
import Langlands.JacquetLanglands.AwayTransfer
import Langlands.JacquetLanglands.HarrisAwaySplitting
import Langlands.JacquetLanglands.Relation

/-!
# Harris's transfer `JL(π_f)` from `GJ` to `GG`

Harris (1999), §5, printed p.312: for an irreducible admissible representation `π_f` of
`GJ(A_f)` whose constituent `π_v` at the distinguished place `v` (a representation of
`GL_n(𝒦_v)`) is supercuspidal, `JL(π_f)` is the irreducible admissible representation of
`GG(A_f)` with the same local constituents as `π_f` away from `v`, and the local
Jacquet–Langlands transfer of `π_v` at `v`.

Here `GG`, whose algebra `ℬ` is a division algebra at `v`, is split at `w₀ = v` onto `Δˣ` for a
`K_{w₀}`-algebra isomorphism `t : K_{w₀} ⊗[K] ℬ ≃ Δ` onto a division algebra `Δ`, and
`IsHarrisJacquetLanglandsTransfer` is the published away-transfer relation `IsAwayTransfer`
for the splittings of `GJ` and `GG` at `w₀`, with the local Jacquet–Langlands relation
`IsJacquetLanglandsPair` at `w₀`. See `HarrisTransfer.md`.
-/

noncomputable section

open scoped TensorProduct NumberField
open NumberField IsDedekindDomain

set_option autoImplicit false

universe u v w z z' uS uΔ uV

namespace Langlands.JacquetLanglands

open Langlands.Shimura Langlands.Global Langlands.Global.AdelicFunctoriality

section FactorUnitsAlg

variable {K : Type v} [Field K] {B : Type z} [Ring B] [Algebra K B]
  {S : Type uS} [CommRing S] [Algebra K S] [TopologicalSpace S] [IsTopologicalRing S]
  {Δ : Type uΔ} [Ring Δ] [Algebra S Δ] [TopologicalSpace Δ] [IsModuleTopology S Δ]

/-- An `S`-algebra isomorphism `t : S ⊗[K] B ≃ₐ[S] Δ` onto an `S`-algebra `Δ` carrying its
`S`-module topology induces an isomorphism of `(S ⊗[K] B)ˣ`, with the units topology of the
`S`-module topology, onto `Δˣ` with its units topology. -/
def factorUnitsAlgEquiv (t : S ⊗[K] B ≃ₐ[S] Δ) :
    ImaginaryQuadraticSplit.FactorUnits K B S ≃ₜ* Δˣ where
  toMulEquiv := Units.mapEquiv t.toRingEquiv.toMulEquiv
  continuous_toFun := by
    let : TopologicalSpace (S ⊗[K] B) := moduleTopology S _
    have := IsModuleTopology.toContinuousAdd S Δ
    exact (IsModuleTopology.continuous_of_linearMap t.toLinearMap).units_map
      t.toRingHom.toMonoidHom
  continuous_invFun := by
    let : TopologicalSpace (S ⊗[K] B) := moduleTopology S _
    have := ModuleTopology.continuousAdd S (S ⊗[K] B)
    have := ModuleTopology.continuousSMul S (S ⊗[K] B)
    exact (IsModuleTopology.continuous_of_linearMap t.symm.toLinearMap).units_map
      t.symm.toRingHom.toMonoidHom

omit [IsTopologicalRing S] in
@[simp] theorem factorUnitsAlgEquiv_apply_val (t : S ⊗[K] B ≃ₐ[S] Δ)
    (x : ImaginaryQuadraticSplit.FactorUnits K B S) :
    ((factorUnitsAlgEquiv t x : Δˣ) : Δ) = t (Units.val (α := S ⊗[K] B) x) :=
  rfl

end FactorUnitsAlg

section LocalRelation

variable {K : Type v} [Field K] [NumberField K]

/-- The local Jacquet–Langlands relation at a finite place `w` of `K`, between representations
of `GL_n(K_w)` and of `Δˣ` for a central division algebra `Δ` over the completion `K_w`:
`IsJacquetLanglandsPair K_w Δ n`, where `K_w` carries the nonarchimedean local field structure
of the published `CompletionPadic.topologicalData w` (whose topology is the completion
topology). The spaces are objects of `ModuleCat ℂ`, as `IsAwayTransfer` requires. -/
def completionJacquetLanglandsPair (w : HeightOneSpectrum (𝓞 K)) (n : ℕ) (Δ : Type v)
    [DivisionRing Δ] [Algebra (w.adicCompletion K) Δ] [FiniteDimensional (w.adicCompletion K) Δ]
    [Algebra.IsCentral (w.adicCompletion K) Δ] [TopologicalSpace Δ]
    [IsModuleTopology (w.adicCompletion K) Δ] (X X' : ModuleCat.{uV} ℂ)
    (π : Representation ℂ (GeneralLinear n (w.adicCompletion K)) X)
    (π' : Representation ℂ Δˣ X') : Prop :=
  letI : ValuativeRel (w.adicCompletion K) := (CompletionPadic.topologicalData w).valuativeRel
  haveI : IsNonarchimedeanLocalField (w.adicCompletion K) :=
    (CompletionPadic.topologicalData w).localField
  IsJacquetLanglandsPair (w.adicCompletion K) Δ n π π'

end LocalRelation

section TrivialSplit

universe uG uL uH

/-- The trivial representation of a topological group on `ℂ` is admissible: every vector is
fixed by the open subgroup `⊤`, and every subspace of `ℂ` is finite-dimensional. -/
theorem isAdmissible_trivial (G : Type uG) [Group G] [TopologicalSpace G] :
    IsAdmissible (Representation.trivial ℂ G ℂ) :=
  ⟨fun _ => ⟨⊤, fun _ => rfl⟩, fun _ => inferInstance⟩

variable {G : Type uG} {L : Type uL} {H : Type uH} [Group G] [Group L] [Group H]
  [TopologicalSpace G] [TopologicalSpace L] [TopologicalSpace H]

/-- For a splitting `Φ : G ≃ₜ* L × H` and representations `π`, `σ` of `L`, `H` on `ℂ` acting
trivially, the trivial representation of `G` on `ℂ` is isomorphic to `splitTensor Φ π σ`
through `ℂ ≃ ℂ ⊗[ℂ] ℂ`, `z ↦ 1 ⊗ z`. -/
def trivialEquivSplitTensor (Φ : G ≃ₜ* L × H) (π : Representation ℂ L ℂ)
    (σ : Representation ℂ H ℂ) (hπ : ∀ l, π l = 1) (hσ : ∀ h, σ h = 1) :
    (Representation.trivial ℂ G ℂ).Equiv (splitTensor Φ π σ) :=
  Representation.Equiv.mk (TensorProduct.lid ℂ ℂ).symm fun g => by
    refine LinearMap.ext_ring ?_
    simp [splitTensor_apply_tmul, hπ, hσ]

end TrivialSplit

section Harris

variable {E : Type u} {K : Type v}
variable [Field E] [NumberField E] [IsTotallyReal E]
variable [Field K] [NumberField K] [IsTotallyComplex K]
variable [Algebra E K] [Algebra.IsQuadraticExtension E K]
variable {F : Type w} [Field F] [NumberField F] [IsCMField F] [Algebra.IsQuadraticExtension ℚ F]
variable {D : Type z} [Ring D] [Algebra K D] [Algebra E D]
  [Algebra ℚ D] [IsScalarTower ℚ E D] [IsScalarTower ℚ K D] [Module.Finite ℚ D]
variable {B : Type z'} [Ring B] [Algebra K B] [Algebra E B]
  [Algebra ℚ B] [IsScalarTower ℚ E B] [IsScalarTower ℚ K B] [Module.Finite ℚ B]
variable (σD : SecondKindInvolution E K D) (σB : SecondKindInvolution E K B) (ι : F →+* K)
  (p : ℕ) (hp : p.Prime) (v : {v : Global.FinitePlace ℚ // (p : 𝓞 ℚ) ∈ v.asIdeal})
  (𝔭 : FinitePlacesAbove F v.1)
  (h𝔭 : Function.Bijective (FiniteExtension.completionMap v.1 𝔭.1))
  (w₀ : letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1)

/-- For `GG`: an isomorphism `t : K_{w₀} ⊗[K] ℬ ≃ₐ Δ` onto a `K_{w₀}`-algebra `Δ` with its
module topology turns the factor at `w₀` of `harrisAwaySplit` into `Δˣ`:
`GG(A_f) ≃ₜ* Δˣ × HarrisAwayComplement`. -/
def harrisAwaySplitAlg {Δ : Type uΔ} [Ring Δ] [Algebra (w₀.1.adicCompletion K) Δ]
    [TopologicalSpace Δ] [IsModuleTopology (w₀.1.adicCompletion K) Δ]
    (t : w₀.1.adicCompletion K ⊗[K] B ≃ₐ[w₀.1.adicCompletion K] Δ) :
    σB.rationalInvolution.FiniteAdelicPoints ≃ₜ* Δˣ × HarrisAwayComplement σB ι p v 𝔭 w₀ :=
  (harrisAwaySplit σB ι p hp v 𝔭 h𝔭 w₀).trans
    (continuousMulEquivProdCongr (factorUnitsAlgEquiv t) (ContinuousMulEquiv.refl _))

theorem harrisAwaySplitAlg_apply_fst {Δ : Type uΔ} [Ring Δ] [Algebra (w₀.1.adicCompletion K) Δ]
    [TopologicalSpace Δ] [IsModuleTopology (w₀.1.adicCompletion K) Δ]
    (t : w₀.1.adicCompletion K ⊗[K] B ≃ₐ[w₀.1.adicCompletion K] Δ)
    (g : σB.rationalInvolution.FiniteAdelicPoints) :
    ((harrisAwaySplitAlg σB ι p hp v 𝔭 h𝔭 w₀ t g).1 : Δ) =
      t (Units.val (α := w₀.1.adicCompletion K ⊗[K] B)
        ((σB.splitPlacePoints ι v.1 𝔭 h𝔭 (σB.rationalInvolution.finiteLocalMap v.1 g)).1 w₀)) := by
  change t (Units.val (α := w₀.1.adicCompletion K ⊗[K] B)
    (harrisAwaySplit σB ι p hp v 𝔭 h𝔭 w₀ g).1) = _
  rw [harrisAwaySplit_apply_fst]

theorem harrisAwaySplitAlg_apply_snd {Δ : Type uΔ} [Ring Δ]
    [Algebra (w₀.1.adicCompletion K) Δ] [TopologicalSpace Δ]
    [IsModuleTopology (w₀.1.adicCompletion K) Δ]
    (t : w₀.1.adicCompletion K ⊗[K] B ≃ₐ[w₀.1.adicCompletion K] Δ)
    (g : σB.rationalInvolution.FiniteAdelicPoints) :
    (harrisAwaySplitAlg σB ι p hp v 𝔭 h𝔭 w₀ t g).2 = (harrisAwaySplit σB ι p hp v 𝔭 h𝔭 w₀ g).2 :=
  rfl

section Transfer

variable (n : ℕ)
  (s : w₀.1.adicCompletion K ⊗[K] D ≃ₐ[w₀.1.adicCompletion K]
    Matrix (Fin n) (Fin n) (w₀.1.adicCompletion K))
  (Δ : Type v) [DivisionRing Δ] [Algebra (w₀.1.adicCompletion K) Δ]
  [FiniteDimensional (w₀.1.adicCompletion K) Δ] [Algebra.IsCentral (w₀.1.adicCompletion K) Δ]
  [TopologicalSpace Δ] [IsModuleTopology (w₀.1.adicCompletion K) Δ]
  (t : w₀.1.adicCompletion K ⊗[K] B ≃ₐ[w₀.1.adicCompletion K] Δ)
  (f : ∀ w : {w : (letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1) // w ≠ w₀},
    w.1.1.adicCompletion K ⊗[K] D ≃ₐ[w.1.1.adicCompletion K] w.1.1.adicCompletion K ⊗[K] B)
  (e : PrimeToFiniteAdeles p ⊗[ℚ] D ≃ₐ[PrimeToFiniteAdeles p] PrimeToFiniteAdeles p ⊗[ℚ] B)
  (he : ∀ x, e (σD.rationalInvolution.baseChange _ x) =
    σB.rationalInvolution.baseChange _ (e x))

/-- Harris's transfer relation `ρ' = JL(ρ)` (Harris 1999, §5, printed p.312) between a
representation `ρ` of `GJ(A_f)` (algebra `D`, split at `w₀` by `s`) and a representation `ρ'`
of `GG(A_f)` (algebra `B`, identified at `w₀` with the central division algebra `Δ` by `t`):
both are irreducible and admissible, and `IsAwayTransfer` holds for the splittings
`harrisAwaySplitGL σD … s` and `harrisAwaySplitAlg σB … t`, the identification of the
complements `harrisComplementEquiv σB σD … f e he`, and the local Jacquet–Langlands relation
`completionJacquetLanglandsPair w₀ n Δ` at `w₀`. -/
def IsHarrisJacquetLanglandsTransfer
    {V V' : Type uV} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (ρ : Representation ℂ σD.rationalInvolution.FiniteAdelicPoints V)
    (ρ' : Representation ℂ σB.rationalInvolution.FiniteAdelicPoints V') : Prop :=
  ρ.IsIrreducible ∧ IsAdmissible ρ ∧ ρ'.IsIrreducible ∧ IsAdmissible ρ' ∧
    IsAwayTransfer (harrisAwaySplitGL σD ι p hp v 𝔭 h𝔭 w₀ s)
      (harrisAwaySplitAlg σB ι p hp v 𝔭 h𝔭 w₀ t) (harrisComplementEquiv σB σD ι p v 𝔭 w₀ f e he)
      (completionJacquetLanglandsPair w₀.1 n Δ) ρ ρ'

variable {σD σB ι p hp v 𝔭 h𝔭 w₀ n s Δ t f e he}
variable {V V' V₂ : Type uV} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  [AddCommGroup V₂] [Module ℂ V₂]
  {ρ : Representation ℂ σD.rationalInvolution.FiniteAdelicPoints V}
  {ρ' : Representation ℂ σB.rationalInvolution.FiniteAdelicPoints V'}

namespace IsHarrisJacquetLanglandsTransfer

theorem isIrreducible_left
    (h : IsHarrisJacquetLanglandsTransfer σD σB ι p hp v 𝔭 h𝔭 w₀ n s Δ t f e he ρ ρ') :
    ρ.IsIrreducible :=
  h.1

theorem isAdmissible_left
    (h : IsHarrisJacquetLanglandsTransfer σD σB ι p hp v 𝔭 h𝔭 w₀ n s Δ t f e he ρ ρ') :
    IsAdmissible ρ :=
  h.2.1

theorem isIrreducible_right
    (h : IsHarrisJacquetLanglandsTransfer σD σB ι p hp v 𝔭 h𝔭 w₀ n s Δ t f e he ρ ρ') :
    ρ'.IsIrreducible :=
  h.2.2.1

theorem isAdmissible_right
    (h : IsHarrisJacquetLanglandsTransfer σD σB ι p hp v 𝔭 h𝔭 w₀ n s Δ t f e he ρ ρ') :
    IsAdmissible ρ' :=
  h.2.2.2.1

theorem isAwayTransfer
    (h : IsHarrisJacquetLanglandsTransfer σD σB ι p hp v 𝔭 h𝔭 w₀ n s Δ t f e he ρ ρ') :
    IsAwayTransfer (harrisAwaySplitGL σD ι p hp v 𝔭 h𝔭 w₀ s)
      (harrisAwaySplitAlg σB ι p hp v 𝔭 h𝔭 w₀ t) (harrisComplementEquiv σB σD ι p v 𝔭 w₀ f e he)
      (completionJacquetLanglandsPair w₀.1 n Δ) ρ ρ' :=
  h.2.2.2.2

/-- The relation depends only on the isomorphism class of the representation of `GJ(A_f)`. -/
theorem of_equiv_left {ρ₂ : Representation ℂ σD.rationalInvolution.FiniteAdelicPoints V₂}
    (eρ : ρ.Equiv ρ₂)
    (h : IsHarrisJacquetLanglandsTransfer σD σB ι p hp v 𝔭 h𝔭 w₀ n s Δ t f e he ρ₂ ρ') :
    IsHarrisJacquetLanglandsTransfer σD σB ι p hp v 𝔭 h𝔭 w₀ n s Δ t f e he ρ ρ' :=
  ⟨isIrreducible_of_equiv eρ.symm h.1, isAdmissible_of_equiv eρ.symm h.2.1, h.2.2.1, h.2.2.2.1,
    h.2.2.2.2.of_equiv_left eρ⟩

/-- The relation depends only on the isomorphism class of the representation of `GG(A_f)`. -/
theorem of_equiv_right {ρ'₂ : Representation ℂ σB.rationalInvolution.FiniteAdelicPoints V₂}
    (eρ' : ρ'.Equiv ρ'₂)
    (h : IsHarrisJacquetLanglandsTransfer σD σB ι p hp v 𝔭 h𝔭 w₀ n s Δ t f e he ρ ρ'₂) :
    IsHarrisJacquetLanglandsTransfer σD σB ι p hp v 𝔭 h𝔭 w₀ n s Δ t f e he ρ ρ' :=
  ⟨h.1, h.2.1, isIrreducible_of_equiv eρ'.symm h.2.2.1, isAdmissible_of_equiv eρ'.symm h.2.2.2.1,
    h.2.2.2.2.of_equiv_right eρ'⟩

end IsHarrisJacquetLanglandsTransfer

/-- Constructor: local Jacquet–Langlands constituents `π`, `π'` at `w₀` and a common
complement constituent `σ` give related external tensor products, as soon as these are
irreducible and admissible. -/
theorem isHarrisJacquetLanglandsTransfer_splitTensor {X X' Y : ModuleCat.{uV} ℂ}
    (π : Representation ℂ (GeneralLinear n (w₀.1.adicCompletion K)) X)
    (π' : Representation ℂ Δˣ X') (σ : Representation ℂ (HarrisAwayComplement σD ι p v 𝔭 w₀) Y)
    (hR : completionJacquetLanglandsPair w₀.1 n Δ X X' π π')
    (h₁ : (splitTensor (harrisAwaySplitGL σD ι p hp v 𝔭 h𝔭 w₀ s) π σ).IsIrreducible)
    (h₂ : IsAdmissible (splitTensor (harrisAwaySplitGL σD ι p hp v 𝔭 h𝔭 w₀ s) π σ))
    (h₃ : (splitTensor (harrisAwaySplitAlg σB ι p hp v 𝔭 h𝔭 w₀ t) π'
      (σ.comp (harrisComplementEquiv σB σD ι p v 𝔭 w₀ f e he).symm.toMulEquiv.toMonoidHom)).IsIrreducible)
    (h₄ : IsAdmissible (splitTensor (harrisAwaySplitAlg σB ι p hp v 𝔭 h𝔭 w₀ t) π'
      (σ.comp (harrisComplementEquiv σB σD ι p v 𝔭 w₀ f e he).symm.toMulEquiv.toMonoidHom))) :
    IsHarrisJacquetLanglandsTransfer σD σB ι p hp v 𝔭 h𝔭 w₀ n s Δ t f e he
      (splitTensor (harrisAwaySplitGL σD ι p hp v 𝔭 h𝔭 w₀ s) π σ)
      (splitTensor (harrisAwaySplitAlg σB ι p hp v 𝔭 h𝔭 w₀ t) π'
        (σ.comp (harrisComplementEquiv σB σD ι p v 𝔭 w₀ f e he).symm.toMulEquiv.toMonoidHom)) :=
  ⟨h₁, h₂, h₃, h₄, isAwayTransfer_splitTensor π π' σ hR⟩

end Transfer

section Trivial

variable
  (f : ∀ w : {w : (letI := ι.toAlgebra; FinitePlacesAbove K 𝔭.1) // w ≠ w₀},
    w.1.1.adicCompletion K ⊗[K] D ≃ₐ[w.1.1.adicCompletion K] w.1.1.adicCompletion K ⊗[K] B)
  (e : PrimeToFiniteAdeles p ⊗[ℚ] D ≃ₐ[PrimeToFiniteAdeles p] PrimeToFiniteAdeles p ⊗[ℚ] B)
  (he : ∀ x, e (σD.rationalInvolution.baseChange _ x) =
    σB.rationalInvolution.baseChange _ (e x))

/-- Nonvacuity for `n = 1`: when `K_{w₀} ⊗[K] D ≃ M_1(K_{w₀})` and `K_{w₀} ⊗[K] B ≃ K_{w₀}`
(so `Δ = K_{w₀}`), the trivial representations of `GJ(A_f)` and `GG(A_f)` on `ℂ` are related.
All four conditions and the local relation (`isJacquetLanglandsPair_trivial_one`) hold. -/
theorem isHarrisJacquetLanglandsTransfer_trivial
    (s : w₀.1.adicCompletion K ⊗[K] D ≃ₐ[w₀.1.adicCompletion K]
      Matrix (Fin 1) (Fin 1) (w₀.1.adicCompletion K))
    (t : w₀.1.adicCompletion K ⊗[K] B ≃ₐ[w₀.1.adicCompletion K] w₀.1.adicCompletion K) :
    IsHarrisJacquetLanglandsTransfer σD σB ι p hp v 𝔭 h𝔭 w₀ 1 s (w₀.1.adicCompletion K) t f e he
      (Representation.trivial ℂ σD.rationalInvolution.FiniteAdelicPoints ℂ)
      (Representation.trivial ℂ σB.rationalInvolution.FiniteAdelicPoints ℂ) := by
  refine ⟨isIrreducible_trivial _, isAdmissible_trivial _, isIrreducible_trivial _,
    isAdmissible_trivial _, ?_⟩
  refine ⟨ModuleCat.of ℂ ℂ, ModuleCat.of ℂ ℂ, ModuleCat.of ℂ ℂ,
    Representation.trivial ℂ _ ℂ, Representation.trivial ℂ _ ℂ, Representation.trivial ℂ _ ℂ,
    ?_, ⟨trivialEquivSplitTensor _ _ _ (fun _ => rfl) (fun _ => rfl)⟩,
    ⟨trivialEquivSplitTensor _ _ _ (fun _ => rfl) (fun _ => rfl)⟩⟩
  let : ValuativeRel (w₀.1.adicCompletion K) :=
    (CompletionPadic.topologicalData w₀.1).valuativeRel
  have : IsNonarchimedeanLocalField (w₀.1.adicCompletion K) :=
    (CompletionPadic.topologicalData w₀.1).localField
  exact isJacquetLanglandsPair_trivial_one _

end Trivial

end Harris

end Langlands.JacquetLanglands
