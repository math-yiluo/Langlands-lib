import Langlands.Global.AdelicCompactProfileProjection
import Langlands.Global.AdelicLocalizedFiniteConvolutionModel
import Langlands.Global.AdelicMaximalCompactFactors
import Langlands.Global.AdelicNestedCuspidalConvolution

/-! # The convolution equation from stable spaces of cuspidal representatives -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory Set
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Langlands.Global.AdelicGroupPoints

open Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local notation "A" => AdelicGroupPoints F G

/-- Continuous functions whose right compact coefficient functions lie in `E`. -/
def compactProfileSubmodule (J : Subgroup (InfiniteAdelicGroupPoints F G))
    (E : Submodule ℂ (J → ℂ)) : Submodule ℂ C(A, ℂ) where
  carrier := {f | HasAdelicCompactProfiles J E f}
  zero_mem' := fun _ => E.zero_mem
  add_mem' hf hg := fun x => E.add_mem (hf x) (hg x)
  smul_mem' c _ hf := fun x => E.smul_mem c (hf x)

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global.StandardParabolicFamily

open AdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions Langlands.GroupScheme

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

local notation "A" => AdelicGroupPoints F G
local notation "Idx" => StandardIndex F G fam.i fam.ν

local notation "Inf(" k ")" => Subgroup.comap (ContinuousMonoidHom.toMonoidHom (ofInfinite F G)) k
local notation "Below(" p ")" => {Q : Idx // Q ≤ p}

/-- The finite-dimensional representatives on the smaller parabolics yield
the uniform equation once they are stable under localized transported kernels
with the specified output compact coefficients and the nested tests are injective. -/
theorem hasConvolutionEquationAt_of_cuspidalRepresentativeSpaces
    (outer : StandardIndex F G fam.i fam.ν) [IsClosedImmersion (fam.p outer).hom.hom.left]
    {K : Subgroup A} (hK : IsIwasawaCompact (fam.p outer) K)
    (hmax : IsMaximalCompactSubgroup F G K)
    {N d n : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (hρ : IsClosedSubgroup rho)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (e : (Fin n → ℂ) →ₗ[ℂ] ComplexCharacterParameter F (fam.P outer)) (s₀ : Fin n → ℂ)
    (f : C(A, ℂ)) (hf : fam.IsModerateContinuousOnParabolic rho outer f)
    (hinj : Function.Injective (fam.nestedCuspidalQuotientMap rho hN outer Inf(K)))
    (hLevi : ∀ Q : Below(outer), Langlands.CompactIwasawa.IsMaximalCompact
      (fam.leviInfiniteCompact Inf(K) Q.val))
    (L : Subgroup (FiniteAdelicGroupPoints F G)) (hL : IsOpen (L : Set (FiniteAdelicGroupPoints F G)))
    (E : Submodule ℂ (Inf(K) → ℂ)) [FiniteDimensional ℂ E] (hE : ∀ u : E, Continuous u.val)
    (hleft : ∀ (s : Inf(K)) (v : E), (fun k => v.val (s⁻¹ * k)) ∈ E)
    (hfE : HasAdelicCompactProfiles (F := F) (G := G) Inf(K) E f)
    (W : Below(outer) → Submodule ℂ C(A, ℂ)) (hW : ∀ Q : Below(outer), FiniteDimensional ℂ (W Q))
    (hWmoderate : ∀ (Q : Below(outer)) (w : C(A, ℂ)), w ∈ W Q →
      fam.IsModerateContinuousOnParabolic rho Q.val w)
    (hrepresent : ∀ Q : Below(outer), ∃ w : C(A, ℂ), w ∈ W Q ∧
      (fam.cuspidalAnnihilator Inf(K) rho Q.val).mkQ w =
        (fam.cuspidalAnnihilator Inf(K) rho Q.val).mkQ (fam.constantTerm Q.val f))
    (hStable : ∀ (h : A → ℂ) (hh : IsAdelicTestFunction F G h), HasFiniteProjectionSupport L h →
      ∀ lam : ComplexCharacterParameter F (fam.P outer),
      (∀ v : C(A, ℂ), HasAdelicCompactProfiles (F := F) (G := G) Inf(K) E
        (hK.twistedConvolutionEnd hsmooth hh lam v)) →
      ∀ (Q : Below(outer)) (v : C(A, ℂ)), v ∈ W Q → hK.twistedConvolutionEnd hsmooth hh lam v ∈ W Q) :
    HasConvolutionEquationAt Inf(K) (fun s => hK.parameterTwist f (e s)) s₀ := by
  let : CompactSpace Inf(K) := isCompact_iff_compactSpace.mp hmax.isMaximalCompact_comap_ofInfinite.1
  let : MeasurableSpace Inf(K) := borel Inf(K)
  let : BorelSpace Inf(K) := ⟨rfl⟩
  let measure : Measure Inf(K) := Measure.haar
  have hKi (k : Inf(K)) : ofInfinite F G k.val ∈ K := k.property
  let R (Q : Below(outer)) := (fam.cuspidalAnnihilator Inf(K) rho Q.val).mkQ.comp
    (ContinuousMap.coeFnLinearMap ℂ : C(A, ℂ) →ₗ[ℂ] (A → ℂ))
  let V (Q : Below(outer)) := (W Q).map (R Q)
  let S₀ := fam.cuspidalConstraintSpace rho hN outer Inf(K) V
  let S := S₀ ⊓ compactProfileSubmodule Inf(K) E
  have hV (Q : Below(outer)) : FiniteDimensional ℂ (V Q) := by
    let : FiniteDimensional ℂ (W Q) := hW Q
    exact Module.Finite.map (W Q) (R Q)
  let : FiniteDimensional ℂ S₀ := fam.finiteDimensional_cuspidalConstraintSpace rho hN outer Inf(K) V hinj hV
  let : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le (show S ≤ S₀ from inf_le_left)
  have hfS : f ∈ S := ⟨(fam.mem_cuspidalConstraintSpace_iff rho hN outer Inf(K) V f).2
      ⟨hf, fun Q => hrepresent Q⟩, hfE⟩
  obtain ⟨a, b, haFinite, hbFinite, ha, hb, hproject⟩ :=
    exists_reproducing_adelicCompactProfileWeights (F := F) (G := G) Inf(K) measure E hE hleft
  have htwist (v : S) : HasAdelicCompactProfiles (F := F) (G := G) Inf(K) E
      (hK.parameterTwist (v : C(A, ℂ)) (e s₀)) :=
    (hK.hasAdelicCompactProfiles_parameterTwist_iff Inf(K) hKi E (e s₀) v).2 v.property.2
  apply hK.hasConvolutionEquationAt_of_localized_averaged_stability hsmooth measure e s₀
    f S hfS a b haFinite hbFinite
    (fun v => ha _ (htwist v)) (fun v => hb _ (htwist v)) L hL
  intro h hh hsup s v hv
  let r := rightCompactKernelAverage measure b h
  let hr := isAdelicTestFunction_rightCompactKernelAverage measure hsmooth b hh
  let hh' := isAdelicTestFunction_leftCompactKernelAverage measure hsmooth a hr
  let D := hK.twistedConvolutionEnd hsmooth hh' (e s)
  have hD (w : C(A, ℂ)) : HasAdelicCompactProfiles (F := F) (G := G) Inf(K) E (D w) :=
    hK.hasAdelicCompactProfiles_twistedConvolutionEnd_leftCompactKernelAverage Inf(K) measure
      hKi hsmooth E a hproject hr (e s) w
  refine ⟨?_, hD v⟩
  obtain ⟨hvmod, hvV⟩ := (fam.mem_cuspidalConstraintSpace_iff rho hN outer Inf(K) V v).1 hv.1
  obtain ⟨hDmod, hDct⟩ := parabolicTwistedConvolution F G fam outer K hK rho hN hsmooth
    (leftCompactKernelAverage measure a r) hh' (e s) v hvmod
  refine (fam.mem_cuspidalConstraintSpace_iff rho hN outer Inf(K) V (D v)).2 ⟨hDmod, fun Q => ?_⟩
  obtain ⟨w, hw, heq⟩ := hvV Q
  have hctmod := fam.adelicParabolicConstantTermGrowth rho hN Q.property hvmod
  let ct : C(A, ℂ) := ⟨fam.constantTerm Q.val v, hctmod.2.1⟩
  have hDpair := fam.cuspidalQuotient_twistedConvolutionEnd_eq_of_eq hK Q.property rho hN hρ
    hsmooth (hLevi Q) hh' (e s) (f := w) (g := ct) (hWmoderate Q w hw) hctmod heq
  refine ⟨D w, hStable _ hh' (hasFiniteProjectionSupport_averaged measure hsup a b)
    (e s) hD Q w hw, ?_⟩
  have hcomm : fam.constantTerm Q.val (D v) = (D ct : A → ℂ) := by
    rw [show fam.constantTerm Q.val (D v) = _ from hDct Q.val Q.property]
    funext x
    simp only [D, IsIwasawaCompact.twistedConvolutionEnd_apply, IsIwasawaCompact.parameterTwist,
      IsIwasawaCompact.heightPower, map_neg, LinearMap.neg_apply, Complex.exp_neg, div_eq_mul_inv,
      r, ct, ContinuousMap.coe_mk]
  rw [hcomm]
  exact hDpair

end Langlands.Global.StandardParabolicFamily
