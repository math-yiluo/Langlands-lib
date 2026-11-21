import Langlands.Global.Factors.CuspidalInducedFiniteTensor
import Langlands.Global.Factors.CuspidalPairFiniteLayer
import Langlands.Global.FiniteAdelicGL.LocalBlockCompactEvaluation
import Langlands.Global.FiniteAdelicGL.TensorEquiv
import Langlands.Group.GL.CompactOpen
import Langlands.Representation.CuspidalSupport.GroupTransport
import Langlands.Representation.Parabolic.NormalizedAdmissibilityProof
import Langlands.Representation.Smooth.Factorization.RestrictedTensorAdmissibilityProof
import Langlands.Representation.Unramified.SphericalFixedLineProof
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

/-! # Admissibility of the finite cuspidal induction tensor -/

noncomputable section

open scoped Classical TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

universe u uQ uV

namespace Langlands.Global.FiniteAdelicGL

open RestrictedTensor

/-- Admissibility of the actual finite adelic tensor follows from the local
admissibility and the eventual integral fixed line. -/
theorem isAdmissible_tensorRepresentation
    (F : Type u) [Field F] [NumberField F] (n : ℕ)
    {V : FinitePlace F → Type uV} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
    (ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v))
    (E : Finset (FinitePlace F)) (e : ∀ v, V v)
    (he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v)
    (hne : ∀ v ∉ E, e v ≠ 0) (hadm : ∀ v, IsAdmissible (ρ v))
    (hline : ∀ᶠ v in Filter.cofinite,
      Module.finrank ℂ (fixedVectors (ρ v) (localIntegral F n v).toSubgroup) = 1) :
    IsAdmissible (tensorRepresentation F n ρ E e he) := by
  let : ∀ v, LocallyCompactSpace (FiniteLocalGL F n v) := fun v =>
    (congrArg (fun t => @LocallyCompactSpace (FiniteLocalGL F n v) t)
      (localGL_topology_eq F v n)).mpr
      ((CompletionPadic.padicField v).canonicalGeneralLinearLocallyCompactSpace n)
  let : ∀ v, NonarchimedeanGroup (FiniteLocalGL F n v) := fun v =>
    (congrArg (fun t => @NonarchimedeanGroup (FiniteLocalGL F n v) _ t)
      (localGL_topology_eq F v n)).mpr
      ((CompletionPadic.padicField v).canonicalGeneralLinearNonarchimedean n)
  let : ∀ v, TotallyDisconnectedSpace (FiniteLocalGL F n v) := fun v => inferInstance
  let H (v : FinitePlace F) := (localIntegral F n v).toSubgroup
  let r₀ : ReferenceVectors V E := ⟨fun v _ => e v, hne⟩
  have hr₀ (v : FinitePlace F) (hv : v ∉ E) (g : FiniteLocalGL F n v) (hg : g ∈ H v) :
      ρ v g (r₀.vector v hv) = r₀.vector v hv := he v hv g hg
  have ha := restrictedTensorAdmissibility (FinitePlace F) (FiniteLocalGL F n) H V ρ E r₀ hr₀
    (fun v => ⟨(localIntegral F n v).isOpen, isCompact_localIntegral F n v⟩) hadm hline
  have ha' : IsAdmissible (restrictedTensorRepresentation F n ρ E r₀ hr₀) :=
    isAdmissible_comp_continuousMulEquiv _ (restrictedProductEquiv F n) ha
  have hFamily (v : FinitePlace F) (hv : v ∉ E) (g : FiniteLocalGL F n v)
      (hg : g ∈ localIntegral F n v) : ρ v g (r₀.family v) = r₀.family v := by
    simpa only [r₀.family_of_not_mem hv] using he v hv g hg
  let f := tensorEquivOver F n ρ ρ E E r₀.family e hFamily he
    (fun v => (Representation.Equiv.refl (ρ v)))
    (E.eventually_cofinite_notMem.mono fun v hv => r₀.family_of_not_mem hv)
  exact isAdmissible_of_equiv f ha'

set_option maxHeartbeats 1800000 in
private theorem localBlockInduced_fixedLine
    (F : Type u) [Field F] [NumberField F] {n : ℕ}
    (B : GeneralLinear.BlockShape n) (v : FinitePlace F)
    {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (σ : ∀ i, Representation ℂ (FiniteLocalGL F (B.size i) v) (V i))
    (hline : ∀ i, Module.finrank ℂ (fixedVectors (σ i) (localIntegralSubgroup F v (B.size i))) = 1) :
    Module.finrank ℂ (fixedVectors
      ((CompletionPadic.padicField v).canonicalNormalizedProductInduced B σ)
      (localIntegral F n v).toSubgroup) = 1 := by
  let J (i : Fin B.length) := localIntegralSubgroup F v (B.size i)
  have hfixed (i : Fin B.length) : fixedVectors (σ i) (J i) ≠ ⊥ := by
    intro hz
    have h := hline i
    rw [show localIntegralSubgroup F v (B.size i) = J i from rfl, hz, finrank_bot] at h
    exact Nat.zero_ne_one h
  choose e he he₀ using fun i => Submodule.exists_mem_ne_zero_of_ne_bot (hfixed i)
  let x (i : Fin B.length) : fixedVectors (σ i) (J i) := ⟨e i, he i⟩
  obtain ⟨f₀, hf₀, hfix₀⟩ := exists_localBlockReference F B v σ e (fun i g => he i g)
  let W := fixedVectors ((CompletionPadic.padicField v).canonicalNormalizedProductInduced B σ)
    (localIntegral F n v).toSubgroup
  let s : W := ⟨f₀, hfix₀⟩
  have htensor : PiTensorProduct.tprod ℂ e ≠ 0 := by
    choose φ hφ using fun i => Module.Projective.exists_dual_eq_one ℂ (he₀ i)
    let f : PiTensorProduct ℂ V →ₗ[ℂ] ℂ :=
      PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ (Fin B.length) ℂ).compLinearMap φ)
    intro hz
    have hval : f (PiTensorProduct.tprod ℂ e) = 1 := by simp [f, hφ]
    rw [hz, map_zero] at hval
    exact zero_ne_one hval
  have hs : s ≠ 0 := by
    intro hz
    have h₀ : f₀ = 0 := congrArg Subtype.val hz
    have hx := hf₀ 1
    rw [h₀, map_zero] at hx
    exact htensor hx.symm
  apply (finrank_eq_one_iff_of_nonzero' s hs).mpr
  intro f
  obtain ⟨c, hc⟩ := exists_smul_localBlockReference_eq F B v σ x
    (fun i hz => he₀ i (congrArg Subtype.val hz)) hline f₀ f.val hf₀ f.property
  exact ⟨c, Subtype.ext hc⟩

end Langlands.Global.FiniteAdelicGL

namespace Langlands.Global.CuspidalInducedFiniteTensor

open Langlands.Automorphic FiniteAdelicGL
open CompletionPadic (padicField)
open Correspondence (AutomorphicObject sphericalSubgroup)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents hasSphericalSpectrum_padicObject)

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r k : ℕ} {m : Fin k → ℕ} {T : ∀ i, CuspidalOperatorRealization F (m i)}

local instance finiteAdmissibilityTopology (v : FinitePlace F) (n : ℕ) :
    TopologicalSpace (GeneralLinear n (padicField v).Carrier) :=
  (padicField v).canonicalGeneralLinearTopology n

variable (hm : ∑ i, (m i + 1) = r + 1)
  (P : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T i))
  (h : ∀ i, HasIrreducibleAdmissibleComponents (P i))

private abbrev shape : GeneralLinear.BlockShape (r + 1) :=
  ⟨k, fun i => m i + 1, fun i => Nat.succ_pos (m i), hm⟩

private abbrev factor (v : FinitePlace F) (i : Fin k) :=
  ((P i).localComponent v).padicObject (h i v).1 (h i v).2

private abbrev sourceSpace (v : FinitePlace F) :=
  LocalBlockInduced F (shape hm) v (fun i => (factor P h v i).obj.representation)

local instance sourceAddCommGroup (v : FinitePlace F) : AddCommGroup (sourceSpace hm P h v) :=
  Submodule.addCommGroup _

private abbrev sourceRep (v : FinitePlace F) :
    Representation ℂ (FiniteLocalGL F (r + 1) v) (sourceSpace hm P h v) :=
  source hm P h v

set_option maxHeartbeats 1500000 in
private theorem source_isAdmissible (v : FinitePlace F) :
    @IsAdmissible ℂ (FiniteLocalGL F (r + 1) v) _ _ _ _ _
      Units.instTopologicalSpaceUnits (sourceRep hm P h v) := by
  let L := (padicField v).canonicalTopologicalData
  let B := shape hm
  let := L.topology
  let := L.generalLinearTopologicalGroup (r + 1)
  let := L.leviTopologicalGroup B
  have ha := Parabolic.normalizedInductionAdmissibility (padicField v) L B _
    (B.blockTensor (fun i => (factor P h v i).obj.representation))
    (FiniteTensor.isAdmissible_external _ (fun i => (factor P h v i).property.2))
  refine Eq.mpr (congrArg (fun t =>
    @IsAdmissible ℂ (FiniteLocalGL F (r + 1) v) _ _ _ _ _ t (sourceRep hm P h v))
    (localGL_topology_eq F v (r + 1))) ?_
  exact ha

set_option maxHeartbeats 1800000 in
private theorem source_fixedLine (v : FinitePlace F) (hv : ∀ i, v ∉ (P i).exceptional) :
    Module.finrank ℂ (fixedVectors (sourceRep hm P h v) (localIntegralSubgroup F v (r + 1))) = 1 := by
  let B := shape hm
  let σ (i : Fin k) := (factor P h v i).obj.representation
  let J (i : Fin k) := localIntegralSubgroup F v (m i + 1)
  have hfixed (i : Fin k) : fixedVectors (σ i) (J i) ≠ ⊥ := by
    obtain ⟨_, _, hspec⟩ := hasSphericalSpectrum_padicObject (P i) (h i) v (hv i)
    simpa only [σ, J, localIntegralSubgroup, localIntegral_eq_sphericalSubgroup] using hspec.1
  refine localBlockInduced_fixedLine F B v σ (fun i => ?_)
  change Module.finrank ℂ (fixedVectors (σ i) (J i)) = 1
  have hfix := hfixed i
  have hJ : J i = sphericalSubgroup (padicField v) (m i) :=
    localIntegral_eq_sphericalSubgroup F v (m i)
  rw [hJ] at hfix ⊢
  exact Unramified.sphericalFixedLine _ (padicField v) (m i) (factor P h v i) hfix

/-- The finite adelic action on the restricted tensor of normalized local
inductions in the original cuspidal block order. -/
abbrev sourceFiniteAction
    (E : Finset (FinitePlace F)) (e : ∀ v, sourceSpace hm P h v)
    (he : ∀ v ∉ E, ∀ g ∈ localIntegral F (r + 1) v, sourceRep hm P h v g (e v) = e v) :=
  tensorRepresentation F (r + 1) (sourceRep hm P h) E e he

set_option maxHeartbeats 1800000 in
/-- The finite induction tensor is admissible for any compatible nonzero
reference family. -/
theorem sourceTensor_isAdmissible
    (E : Finset (FinitePlace F)) (e : ∀ v, sourceSpace hm P h v)
    (he : ∀ v ∉ E, ∀ g ∈ localIntegral F (r + 1) v, sourceRep hm P h v g (e v) = e v)
    (hne : ∀ v ∉ E, e v ≠ 0) :
    IsAdmissible (sourceFiniteAction hm P h E e he) := by
  refine isAdmissible_tensorRepresentation F (r + 1) (sourceRep hm P h) E e he hne
    (source_isAdmissible hm P h) ?_
  let S := Finset.univ.biUnion fun i : Fin k => (P i).exceptional
  exact S.eventually_cofinite_notMem.mono fun v hv => source_fixedLine hm P h v
    (fun i hi => hv (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hi⟩))

end Langlands.Global.CuspidalInducedFiniteTensor
