import Langlands.BaseChange.RegularElementaryTests
import Langlands.BaseChange.SphericalCosetDescent
import Langlands.BaseChange.SphericalDistributionTrace
import Langlands.BaseChange.WeylSphericalTraceReplacement

/-! # Replacing regular elementary tests by spherical tests in finite local trace sums -/

noncomputable section

namespace Langlands.BaseChange

open Correspondence HarmonicAnalysis Unramified

universe u v uV uW uI uJ

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

local instance {p : ℕ} [Fact p.Prime] (F : PadicField p) (n : ℕ) :
    LocallyCompactSpace (GeneralLinear n F.Carrier) :=
  LocalFieldTopology.generalLinear_locallyCompactSpace F.Carrier n

local instance {p : ℕ} [Fact p.Prime] (F : PadicField p) (n : ℕ) :
    TotallyDisconnectedSpace (GeneralLinear n F.Carrier) :=
  LocalFieldTopology.generalLinear_totallyDisconnectedSpace F.Carrier n

set_option backward.isDefEq.respectTransparency false in
/-- The actual finite local trace sums admit spherical replacement given their
regular elementary Jacquet expansions and Weyl support. -/
def SphericalTraceReplacementOfJacquetDataStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    (σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier) (l r : ℕ) (hcyc : IsCyclicAlgebra σ l)
    (he : E.canonicalTopologicalData.ramificationIndex =
      F.canonicalTopologicalData.ramificationIndex)
    (b : SphericalHeckeAlgebra E r →ₐ[ℂ] SphericalHeckeAlgebra F r),
    IsUnramifiedBaseChangeHom F E l r b →
    ∀ (I : Type uI) (J : Type uJ) [Fintype I] [Fintype J]
      (upper : I → AutomorphicObject.{v,uV} E r.succPNat)
      (lower : J → AutomorphicObject.{u,uW} F r.succPNat)
      (A : ∀ i, SigmaIntertwiner σ (r + 1) (upper i).obj.representation)
      (inducingE : I → Fin (r + 1) → ℂˣ) (inducingF : J → Fin (r + 1) → ℂˣ)
      (exponentsE : I → Multiset (Fin (r + 1) → ℂˣ))
      (exponentsF : J → Multiset (Fin (r + 1) → ℂˣ))
      (factor : StrictWeight (r + 1) → ℂ),
    let fixedE i := fixedVectors (upper i).obj.representation (sphericalSubgroup E r)
    let fixedF j := fixedVectors (lower j).obj.representation (sphericalSubgroup F r)
    let sphericalE i := fixedE i ≠ ⊥
    let sphericalF j := fixedF j ≠ ⊥
    let distE i := twistedDistribution (sphericalHaar E r) (upper i).obj.representation
      (upper i).property.2 (A i).toLinearMap
    let distF j := Character.distribution (sphericalHaar F r) (lower j).obj.representation
      (lower j).property.2
    let tests (w : StrictWeight (r + 1)) :=
      regularElementaryBaseChangeTests F E σ l hcyc he w.val w.property
    (∀ (i : I) (x : fixedE i), A i x.val = x.val) →
    (∀ i, sphericalE i → HasSphericalHeckeSpectrum E (upper i) (Eigenvalues.ofTuple (inducingE i))) →
    (∀ j, sphericalF j → HasSphericalHeckeSpectrum F (lower j) (Eigenvalues.ofTuple (inducingF j))) →
    HasWeylJacquetSupport inducingE sphericalE exponentsE →
    HasWeylJacquetSupport inducingF sphericalF exponentsF →
    (∀ w, factor w ≠ 0) →
    HasJacquetElementaryTraceExpansion 1 exponentsE factor (fun i w => distE i (tests w).1) →
    HasJacquetElementaryTraceExpansion l exponentsF factor (fun j w => distF j (tests w).2) →
    ∀ (a : I → ℂ) (c : J → ℂ),
      (∀ w, ∑ i, a i * distE i (tests w).1 = ∑ j, c j * distF j (tests w).2) →
      ∀ φ : SphericalHeckeAlgebra E r,
        ∑ i, a i * distE i φ.val = ∑ j, c j * distF j (b φ).val

set_option backward.isDefEq.respectTransparency false in
theorem sphericalTraceReplacementOfJacquetData :
    SphericalTraceReplacementOfJacquetDataStatement.{u,v,uV,uW,uI,uJ} := by
  classical
  intro p _ F E _ _ σ l r hcyc he b hb I J _ _ upper lower A inducingE inducingF exponentsE exponentsF
    factor fixedE fixedF sphericalE sphericalF distE distF tests hA hsE hsF hWeylE hWeylF
    hfactor htraceE htraceF a c heq φ
  let spectrumE i := Eigenvalues.ofTuple (inducingE i)
  let spectrumF j := Eigenvalues.power (Eigenvalues.ofTuple (inducingF j)) l
  let labels := Finset.univ.image spectrumE ∪ Finset.univ.image spectrumF
  let labelE (i : I) : labels :=
    ⟨spectrumE i, Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))⟩
  let labelF (j : J) : labels :=
    ⟨spectrumF j, Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))⟩
  let χE (s : Eigenvalues (r + 1)) := ((satakeCharacter p E r).1 s).choose
  let χF (s : Eigenvalues (r + 1)) := ((satakeCharacter p F r).1 s).choose
  have hχE (s : Eigenvalues (r + 1)) : IsSatakeCharacter E r s (χE s) :=
    ((satakeCharacter p E r).1 s).choose_spec
  have hχF (s : Eigenvalues (r + 1)) : IsSatakeCharacter F r s (χF s) :=
    ((satakeCharacter p F r).1 s).choose_spec
  let value (s : labels) (φ : SphericalHeckeAlgebra E r) := χE s.val φ
  let θ := entrywiseAut σ (r + 1)
  have hK (g : GeneralLinear (r + 1) E.Carrier) :
      θ g ∈ sphericalOpenSubgroup E r ↔ g ∈ sphericalOpenSubgroup E r := by
    change θ g ∈ sphericalSubgroup E r ↔ g ∈ sphericalSubgroup E r
    constructor
    · intro hg
      have hh := entrywiseAut_mem_sphericalSubgroup F E σ.symm hg
      change θ.symm (θ g) ∈ sphericalSubgroup E r at hh
      simpa only [MulEquiv.symm_apply_apply] using hh
    · exact entrywiseAut_mem_sphericalSubgroup F E σ
  have hSphE : HasSphericalTraceValues labelE sphericalE value (fun i f => distE i f.val) := by
    intro i f
    by_cases hi : sphericalE i
    · rw [ite_eq_left hi]
      exact twistedDistribution_spherical_eq_satake E (upper i) (hsE i hi)
        (χE (spectrumE i)) (hχE _) θ (A i) hK (hA i) f
    · rw [ite_eq_right hi]
      exact twistedDistribution_spherical_eq_zero E (upper i) (not_ne_iff.mp hi) (A i).toLinearMap f
  have hSphF : HasSphericalTraceValues labelF sphericalF value (fun j f => distF j (b f).val) := by
    intro j f
    by_cases hj : sphericalF j
    · rw [ite_eq_left hj]
      let s := Eigenvalues.ofTuple (inducingF j)
      exact (distribution_spherical_eq_satake F (lower j) (hsF j hj) (χF s) (hχF s) (b f)).trans
        (DFunLike.congr_fun (hb s (χF s) (χE (spectrumF j)) (hχF s) (hχE _)) f)
    · rw [ite_eq_right hj]
      exact distribution_spherical_eq_zero F (lower j) (not_ne_iff.mp hj) (b f)
  exact weylSphericalTraceReplacement (r + 1) l hcyc.pos.ne' I J labels (SphericalHeckeAlgebra E r)
    inducingE inducingF exponentsE exponentsF labelE labelF Subtype.val sphericalE sphericalF
    factor value (fun i w => distE i (tests w).1) (fun j w => distF j (tests w).2)
    (fun i f => distE i f.val) (fun j f => distF j (b f).val) a c
    Subtype.val_injective (fun _ => rfl) (fun _ => rfl) hfactor hWeylE hWeylF
    htraceE htraceF hSphE hSphF heq φ

end Langlands.BaseChange
