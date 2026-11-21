import Langlands.Analysis.Meromorphic.ScalarSumIdentityProof
import Langlands.Global.AdelicWeylParameterEquivalence

/-! # Propagation of an Eisenstein functional equation from an open patch -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.Analysis.Meromorphic Langlands.GroupScheme AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G P M Q M' : GroupScheme (Spec (CommRingCat.of F))}
  {p : P ⟶ G} {q : Q ⟶ G} {l : M ⟶ P} {l' : M' ⟶ Q}
  {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X} {c : M' ⟶ M} {π' : Q ⟶ M'}

/-- For the exact Weyl parameter map, equality on a nonempty open patch at
each adelic point implies the pointwise functional equation on the common
holomorphy domain. -/
theorem eisensteinFunctionalEquation_of_openAgreement
    (hl : IsRationalLeviSubgroup l) (hl' : IsRationalLeviSubgroup l')
    (hπ' : l' ≫ π' = 𝟙 M') (hw : IsWeylConjugation p l q l' w c)
    {EP : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ}
    {DP D : Set (ComplexCharacterParameter F P)} {DQ : Set (ComplexCharacterParameter F Q)}
    {k : ℕ} {coeff : Fin k → ComplexCharacterParameter F P → ℂ}
    {EQ : Fin k → ComplexCharacterParameter F Q → AdelicGroupPoints F G → ℂ}
    (hEP : ∀ g, IsMeromorphicInCoordinatesOn (fun lam => EP lam g) DP)
    (hcoeff : ∀ i, IsMeromorphicInCoordinatesOn (coeff i) D)
    (hEQ : ∀ i g, IsMeromorphicInCoordinatesOn (fun mu => EQ i mu g) DQ)
    (hopen : ∀ g : AdelicGroupPoints F G,
      ∃ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P) (O : Set (Fin n → ℂ)),
        IsOpen O ∧ O.Nonempty ∧ ∀ x ∈ O,
          EP (e x) g = ∑ i, coeff i (e x) * EQ i (weylParameter l c π' (e x)) g) :
    ∀ lam ∈ DP ∩ D, weylParameter l c π' lam ∈ DQ → ∀ g : AdelicGroupPoints F G,
      EP lam g = ∑ i, coeff i lam * EQ i (weylParameter l c π' lam) g := by
  let : IsIso c := hw.isIso
  obtain ⟨e, he⟩ := exists_weylParameter_linearEquiv l l' hl hl' c π' hπ'
  have hparam (lam : ComplexCharacterParameter F P) : e lam = weylParameter l c π' lam :=
    LinearMap.congr_fun he lam
  intro lam hlam hlamQ g
  obtain ⟨n, a, O, hO, hne, hagree⟩ := hopen g
  have hseed : ∀ x ∈ O, EP (a x) g = ∑ i, coeff i (a x) * EQ i (e (a x)) g := by
    simpa only [hparam] using hagree
  have htarget : e lam ∈ DQ := hparam lam ▸ hlamQ
  simpa only [hparam] using
    scalarMeromorphicSumIdentity (ComplexCharacterParameter F P) (ComplexCharacterParameter F Q)
      e (fun t => EP t g) DP D DQ k coeff (fun i mu => EQ i mu g) (hEP g) hcoeff
      (fun i => hEQ i g) n a O hO hne hseed lam hlam htarget

end Langlands.Global
