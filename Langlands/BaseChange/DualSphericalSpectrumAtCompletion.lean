import Langlands.Automorphic.AssociatedGammaPrincipalSeries
import Langlands.Automorphic.CuspidalContragredientLocalCompatibilityProof
import Langlands.Global.Factors.CuspidalPairFactorData
import Langlands.Representation.Smooth.Contragredient.FixedExtension
import Langlands.Representation.Smooth.Contragredient.LawsProof
import Langlands.Representation.Unramified.PairedHeckeScalars
import Langlands.Representation.Unramified.SphericalHeckeSpectrumExistenceProof

/-! # Spherical spectra of dual components at actual completions -/

noncomputable section

set_option autoImplicit false

universe u uQ uD

namespace Langlands.BaseChange

open Automorphic Correspondence Global Global.CompletionPadic
open Global.CuspidalPairFunctionalEquation Unramified

attribute [local instance] heckeFieldTopology heckeGeneralLinearTopology
  heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2 heckeGeneralLinearMeasurable
  heckeGeneralLinearBorel

/-- A spherical object transfers its spectrum to the smooth dual by inversion. -/
theorem hasSphericalHeckeSpectrum_of_smoothContragredient {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) {r : ℕ} (A : AutomorphicObject.{u, uQ} F r.succPNat)
    (D : AutomorphicObject.{u, uD} F r.succPNat)
    (e : (smoothContragredient A.obj.representation).Equiv D.obj.representation)
    (s : Eigenvalues (r + 1)) (hs : HasSphericalHeckeSpectrum F A s) :
    HasSphericalHeckeSpectrum F D (s.map fun z => z⁻¹) := by
  let K := sphericalOpenSubgroup F r
  let ρ := A.obj.representation
  let σ := D.obj.representation
  let dual := smoothDualCompactFixedEquiv ρ A.obj.isSmooth K (sphericalOpenSubgroup_isCompact F r)
  let fixed := fixedVectorsEquiv e K.toSubgroup
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hs.1
  let a₀ : fixedVectors ρ K.toSubgroup := ⟨a, ha⟩
  have ha₀ : a₀ ≠ 0 := fun h => ha0 (congrArg Subtype.val h)
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_eq_one ℂ ha₀
  let b := dual.symm ℓ
  let b₀ := fixed b
  have hb₀ : b₀ ≠ 0 := by
    intro he
    have h := congrArg (fun v => dual (fixed.symm v) a₀) he
    change dual (fixed.symm (fixed (dual.symm ℓ))) a₀ = dual (fixed.symm 0) a₀ at h
    rw [fixed.symm_apply_apply, dual.apply_symm_apply, hℓ,
      fixed.symm.map_zero, dual.map_zero, LinearMap.zero_apply] at h
    exact one_ne_zero h
  have hD : fixedVectors σ (sphericalSubgroup F r) ≠ ⊥ := by
    apply (Submodule.ne_bot_iff _).mpr
    exact ⟨b₀, b₀.property, fun h => hb₀ (Subtype.ext h)⟩
  obtain ⟨d, hd⟩ := sphericalHeckeSpectrumExistence p F r D hD
  let B := ((smoothDualPairing ρ).comp e.symm.toLinearEquiv.toLinearMap).flip
  have hB (g : GeneralLinear (r.succPNat : ℕ) F.Carrier) (x : A.obj) (y : D.obj) :
      B (ρ g x) (σ g y) = B x y := by
    have hg : e.symm (σ g y) = smoothContragredient ρ g (e.symm y) :=
      Representation.IntertwiningMap.isIntertwining σ (smoothContragredient ρ)
        e.symm.toIntertwiningMap g y
    exact (congrArg (fun a => smoothDualPairing ρ a (ρ g x)) hg).trans
      (smoothDualPairing_invariant g (e.symm y) x)
  have hab : B a₀ b₀ ≠ 0 := by
    have he : e.symm (b₀ : D.obj) = (b : SmoothDual ρ) := e.symm_apply_apply (b : SmoothDual ρ)
    change smoothDualPairing ρ (e.symm (b₀ : D.obj)) (a₀ : A.obj) ≠ 0
    rw [he]
    change dual b a₀ ≠ 0
    rw [dual.apply_symm_apply, hℓ]
    exact one_ne_zero
  have he := PairedHecke.eq_map_inv_of_pairing F ρ A.obj.isSmooth σ D.obj.isSmooth B hB
    a₀ b₀ s d (fun i => hs.2 i a₀) (fun i => hd.2 i b₀) hab
  exact he ▸ hd

/-- At every place where the given presentation is spherical, its actual
contragredient component has the inverse spectrum. -/
def DualSphericalSpectrumAtCompletionStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]
    (r : ℕ) (T Td : CuspidalOperatorRealization K r), Td.realization.IsContragredientOf T.realization →
    ∀ (P : CuspidalSpectralPresentation.{u, uQ} T) (Pd : CuspidalSpectralPresentation.{u, uD} Td)
      (_h : HasIrreducibleAdmissibleComponents P) (hd : HasIrreducibleAdmissibleComponents Pd)
      (v : FinitePlace K) (hv : v ∉ P.exceptional),
      HasSphericalSpectrum (padicField v) ((Pd.localComponent v).padicObject (hd v).1 (hd v).2)
        ((P.spectralSystem.eigenvalues v hv).map fun z => z⁻¹)

set_option maxHeartbeats 1000000 in
/-- Use compatibility with the local smooth contragredient at the supplied completion. -/
theorem dualSphericalSpectrumAtCompletion : DualSphericalSpectrumAtCompletionStatement.{u, uQ, uD} := by
  intro K _ _ _ r T Td hTd P Pd h hd v hv
  let F := padicField v
  let A := (P.localComponent v).padicObject (h v).1 (h v).2
  let D := (Pd.localComponent v).padicObject (hd v).1 (hd v).2
  let s := P.spectralSystem.eigenvalues v hv
  have hA : HasSphericalHeckeSpectrum F A s :=
    (hasSphericalHeckeSpectrumClass_classOf F A s).mp
      (((P.localComponent v).hasSphericalHeckeSpectrumClass_iff (h v).1 (h v).2 s).mpr
        (P.hasSpectrum v hv))
  obtain ⟨e⟩ := cuspidalContragredientLocalCompatibility K r T Td hTd P Pd v
    (h v).1 (h v).2 (hd v).1 (hd v).2
  exact hasSphericalSpectrum_of_hasSphericalHeckeSpectrum F D _
    (hasSphericalHeckeSpectrum_of_smoothContragredient F A D e.symm s hA)

end Langlands.BaseChange
