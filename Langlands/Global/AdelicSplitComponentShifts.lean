import Langlands.Global.AdelicCuspidalProductVanishing
import Langlands.Global.AdelicStandardConstantTerm
import Langlands.Global.AdelicExponentPolynomials
import Langlands.Automorphic.GroupSchemeAutomorphicLeftTranslation

/-! # Polynomials in the left action of a positive split component

For a standard parabolic `R`, the left action `φ ↦ φ(a ·)` of the positive split component
`𝔄_R` on functions on `G(𝔸)` extends to an algebra homomorphism from the complex group algebra
of `𝔄_R`. Its values preserve automorphy, cuspidality and generalized exponents along every
standard `Q ⊆ R`, commute with the constant terms along `Q`, and preserve the relation
"cuspidal projection". A power of a difference `a - z` kills a function with a generalized
exponent `λ` along `Q` when `z` is the value of `λ` at `a`, and is injective on such functions
otherwise. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Polynomial
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.HarmonicAnalysis

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G 𝓕.i 𝓕.ν
local notation "Fun" => (AdelicGroupPoints F G → ℂ)

attribute [local instance] positiveSplitComponentCommGroup

section Algebra

/-- The left action of `𝔄_R` on functions on `G(𝔸)`, extended to the complex group algebra. -/
def shiftAlgHom (R : Idx) :
    MonoidAlgebra ℂ (𝓕.positiveSplitComponent R) →ₐ[ℂ] Module.End ℂ Fun :=
  (𝓕.splitComponentRepresentation R).asAlgebraHom

theorem shiftAlgHom_of (R : Idx) (a : 𝓕.positiveSplitComponent R) (φ : Fun) :
    𝓕.shiftAlgHom R (MonoidAlgebra.of ℂ _ a) φ = 𝓕.unnormalizedAction R a φ := by
  rw [shiftAlgHom, Representation.asAlgebraHom_of]
  rfl

/-- A submodule stable under the action of `𝔄_R` is stable under its group algebra. -/
theorem shiftAlgHom_mem {R : Idx} (S : Submodule ℂ Fun)
    (hS : ∀ a : 𝓕.positiveSplitComponent R, ∀ v ∈ S, 𝓕.unnormalizedAction R a v ∈ S)
    (d : MonoidAlgebra ℂ (𝓕.positiveSplitComponent R)) :
    ∀ v ∈ S, 𝓕.shiftAlgHom R d v ∈ S := by
  induction d using MonoidAlgebra.induction_on with
  | of a =>
    intro v hv
    rw [shiftAlgHom_of]
    exact hS a v hv
  | add x y hx hy =>
    intro v hv
    rw [map_add, LinearMap.add_apply]
    exact S.add_mem (hx v hv) (hy v hv)
  | smul c x hx =>
    intro v hv
    rw [map_smul, LinearMap.smul_apply]
    exact S.smul_mem c (hx v hv)

/-- A map that is additive and homogeneous on a stable submodule and commutes there with the
action of `𝔄_R` commutes with its group algebra. -/
theorem shiftAlgHom_intertwine {R : Idx} (S : Submodule ℂ Fun)
    (hS : ∀ a : 𝓕.positiveSplitComponent R, ∀ v ∈ S, 𝓕.unnormalizedAction R a v ∈ S)
    (T : Fun → Fun) (hadd : ∀ v ∈ S, ∀ w ∈ S, T (v + w) = T v + T w)
    (hsmul : ∀ (c : ℂ), ∀ v ∈ S, T (c • v) = c • T v)
    (hT : ∀ a : 𝓕.positiveSplitComponent R, ∀ v ∈ S,
      T (𝓕.unnormalizedAction R a v) = 𝓕.unnormalizedAction R a (T v))
    (d : MonoidAlgebra ℂ (𝓕.positiveSplitComponent R)) :
    ∀ v ∈ S, T (𝓕.shiftAlgHom R d v) = 𝓕.shiftAlgHom R d (T v) := by
  induction d using MonoidAlgebra.induction_on with
  | of a =>
    intro v hv
    rw [shiftAlgHom_of, shiftAlgHom_of]
    exact hT a v hv
  | add x y hx hy =>
    intro v hv
    rw [map_add, LinearMap.add_apply, LinearMap.add_apply,
      hadd _ (𝓕.shiftAlgHom_mem S hS x v hv) _ (𝓕.shiftAlgHom_mem S hS y v hv), hx v hv, hy v hv]
  | smul c x hx =>
    intro v hv
    rw [map_smul, LinearMap.smul_apply, LinearMap.smul_apply,
      hsmul c _ (𝓕.shiftAlgHom_mem S hS x v hv), hx v hv]

end Algebra

section Lift

/-- A point of `𝔄_R` is, in `G(𝔸)`, a point of `𝔄_Q` for every `Q ⊆ R`. -/
theorem exists_splitLift {Q R : Idx} (hQR : Q ≤ R) (a : 𝓕.positiveSplitComponent R) :
    ∃ b : 𝓕.positiveSplitComponent Q,
      map F (𝓕.P Q) G (𝓕.p Q) b = map F (𝓕.P R) G (𝓕.p R) a := by
  obtain ⟨b, hb, -⟩ := 𝓕.exists_positiveSplitComponent_lift_with_values hQR a
  exact ⟨b, hb⟩

/-- A chosen point of `𝔄_Q` with the same image in `G(𝔸)` as a point of `𝔄_R`. -/
def splitLift {Q R : Idx} (hQR : Q ≤ R) (a : 𝓕.positiveSplitComponent R) :
    𝓕.positiveSplitComponent Q :=
  (𝓕.exists_splitLift hQR a).choose

theorem map_splitLift {Q R : Idx} (hQR : Q ≤ R) (a : 𝓕.positiveSplitComponent R) :
    map F (𝓕.P Q) G (𝓕.p Q) (𝓕.splitLift hQR a) = map F (𝓕.P R) G (𝓕.p R) a :=
  (𝓕.exists_splitLift hQR a).choose_spec

theorem unnormalizedAction_splitLift {Q R : Idx} (hQR : Q ≤ R)
    (a : 𝓕.positiveSplitComponent R) (φ : Fun) :
    𝓕.unnormalizedAction Q (𝓕.splitLift hQR a) φ = 𝓕.unnormalizedAction R a φ := by
  funext g
  simp only [unnormalizedAction, map_splitLift]

end Lift

section Stability

variable {d N : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) (rho : MatrixRepresentation G (Fin N))

/-- Left invariance under `U_J(𝔸) M_J(F)` gives invariance under its two generators. -/
theorem isParabolicGeneratorInvariant_of_isLeftInvariantUnder (J : Idx) {h : Fun}
    (hh : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F (𝓕.p J) (𝓕.iU J) (𝓕.l J)) h) :
    𝓕.IsParabolicGeneratorInvariant J h := by
  refine ⟨fun n g => ?_, fun m g => hh _ (Subgroup.mem_sup_right ⟨m, rfl⟩) g⟩
  obtain ⟨v, hv⟩ := SubgroupFunctor.mem_range.mp n.2
  refine hh _ (Subgroup.mem_sup_left ⟨v, ?_⟩) g
  rw [← hv]
  rfl

/-- The automorphic functions on `U_J(𝔸) M_J(F) \ G(𝔸)`, as a submodule. -/
abbrev automorphicSubmodule (J : Idx) : Submodule ℂ Fun :=
  automorphicFunctionsOn (parabolicQuotientSubgroup F (𝓕.p J) (𝓕.iU J) (𝓕.l J)) Kinf rho
    hsmooth (adelicDifferentialCommutator_of_smooth F G hsmooth)

theorem mem_automorphicSubmodule {J : Idx} {h : Fun} :
    h ∈ 𝓕.automorphicSubmodule hsmooth Kinf rho J ↔ 𝓕.IsAutomorphicOn hsmooth Kinf rho J h :=
  Iff.rfl

/-- Translation by a point of `𝔄_J` preserves automorphy on `U_J(𝔸) M_J(F) \ G(𝔸)`. -/
theorem IsAutomorphicOn.unnormalizedAction {J : Idx} {h : Fun}
    (hh : 𝓕.IsAutomorphicOn hsmooth Kinf rho J h) (b : 𝓕.positiveSplitComponent J) :
    𝓕.IsAutomorphicOn hsmooth Kinf rho J (𝓕.unnormalizedAction J b h) := by
  have ht := IsAutomorphicFunctionOn.leftTranslate
    (adelicDifferentialCommutator_of_smooth F G hsmooth) hh (map F (𝓕.P J) G (𝓕.p J) b)
  have hgen := IsParabolicGeneratorInvariant.adelicLeftShift 𝓕
    (𝓕.isParabolicGeneratorInvariant_of_isLeftInvariantUnder J hh.1) b
  exact ⟨IsParabolicGeneratorInvariant.isLeftInvariantUnder 𝓕 hgen, ht.2⟩

/-- For `Q ⊆ R`, translation by a point of `𝔄_R` preserves automorphy along `Q`. -/
theorem IsAutomorphicOn.unnormalizedAction_of_le {Q R : Idx} (hQR : Q ≤ R) {h : Fun}
    (hh : 𝓕.IsAutomorphicOn hsmooth Kinf rho Q h) (a : 𝓕.positiveSplitComponent R) :
    𝓕.IsAutomorphicOn hsmooth Kinf rho Q (𝓕.unnormalizedAction R a h) := by
  rw [← 𝓕.unnormalizedAction_splitLift hQR a]
  exact IsAutomorphicOn.unnormalizedAction 𝓕 hsmooth Kinf rho hh _

/-- For `Q ⊆ R`, the group algebra of `𝔄_R` preserves automorphy along `Q`. -/
theorem IsAutomorphicOn.shiftAlgHom {Q R : Idx} (hQR : Q ≤ R) {h : Fun}
    (hh : 𝓕.IsAutomorphicOn hsmooth Kinf rho Q h)
    (D : MonoidAlgebra ℂ (𝓕.positiveSplitComponent R)) :
    𝓕.IsAutomorphicOn hsmooth Kinf rho Q (𝓕.shiftAlgHom R D h) :=
  𝓕.shiftAlgHom_mem (𝓕.automorphicSubmodule hsmooth Kinf rho Q)
    (fun a _ hv => IsAutomorphicOn.unnormalizedAction_of_le 𝓕 hsmooth Kinf rho hQR hv a) D h hh

/-- Functions with polynomial orbits of degree at most `k` for the exponent `λ` along `J`. -/
def polynomialOrbitSubmodule (J : Idx) (lam : ComplexCharacterParameter F (𝓕.P J)) (k : ℕ) :
    Submodule ℂ Fun where
  carrier := {φ | 𝓕.HasPolynomialOrbit J lam k φ}
  zero_mem' := fun _ => ⟨0, Submodule.zero_mem _, fun x _ => by
    simp [unnormalizedAction]⟩
  add_mem' {φ ψ} hφ hψ := fun g => by
    obtain ⟨p, hp, hpe⟩ := hφ g
    obtain ⟨q, hq, hqe⟩ := hψ g
    refine ⟨p + q, Submodule.add_mem _ hp hq, fun x hx => ?_⟩
    simp only [unnormalizedAction, Pi.add_apply, add_mul] at hpe hqe ⊢
    rw [hpe x hx, hqe x hx]
  smul_mem' c φ hφ := fun g => by
    obtain ⟨p, hp, hpe⟩ := hφ g
    refine ⟨c • p, Submodule.smul_mem _ c hp, fun x hx => ?_⟩
    simp only [unnormalizedAction, Pi.smul_apply, smul_eq_mul, mul_assoc] at hpe ⊢
    rw [hpe x hx]

theorem mem_polynomialOrbitSubmodule {J : Idx} {lam : ComplexCharacterParameter F (𝓕.P J)}
    {k : ℕ} {φ : Fun} : φ ∈ 𝓕.polynomialOrbitSubmodule J lam k ↔ 𝓕.HasPolynomialOrbit J lam k φ :=
  Iff.rfl

/-- Translation by a point of `𝔄_J` preserves polynomial orbits along `J`. -/
theorem HasPolynomialOrbit.unnormalizedAction {J : Idx}
    {lam : ComplexCharacterParameter F (𝓕.P J)} {k : ℕ} {φ : Fun}
    (hφ : 𝓕.HasPolynomialOrbit J lam k φ) (b : 𝓕.positiveSplitComponent J) :
    𝓕.HasPolynomialOrbit J lam k (𝓕.unnormalizedAction J b φ) := by
  intro g
  obtain ⟨p, hp, hpe⟩ := hφ (map F (𝓕.P J) G (𝓕.p J) b * g)
  refine ⟨p, hp, fun x hx => ?_⟩
  rw [← hpe x hx]
  change φ (map F (𝓕.P J) G (𝓕.p J) b * (map F (𝓕.P J) G (𝓕.p J) x * g)) * _ =
    φ (map F (𝓕.P J) G (𝓕.p J) x * (map F (𝓕.P J) G (𝓕.p J) b * g)) * _
  rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, 𝓕.positiveSplitComponent_mul_comm J b.2 hx]

/-- For `Q ⊆ R`, the group algebra of `𝔄_R` preserves polynomial orbits along `Q`. -/
theorem HasPolynomialOrbit.shiftAlgHom {Q R : Idx} (hQR : Q ≤ R)
    {lam : ComplexCharacterParameter F (𝓕.P Q)} {k : ℕ} {φ : Fun}
    (hφ : 𝓕.HasPolynomialOrbit Q lam k φ) (D : MonoidAlgebra ℂ (𝓕.positiveSplitComponent R)) :
    𝓕.HasPolynomialOrbit Q lam k (𝓕.shiftAlgHom R D φ) :=
  𝓕.shiftAlgHom_mem (𝓕.polynomialOrbitSubmodule Q lam k)
    (fun a v hv => by
      rw [← 𝓕.unnormalizedAction_splitLift hQR a]
      exact HasPolynomialOrbit.unnormalizedAction 𝓕 hv _) D φ hφ

/-- For `Q ⊆ R`, the group algebra of `𝔄_R` preserves generalized exponents along `Q`. -/
theorem HasUnnormalizedExponent.shiftAlgHom {Q R : Idx} (hQR : Q ≤ R)
    {lam : ComplexCharacterParameter F (𝓕.P Q)} {φ : Fun}
    (hφ : 𝓕.HasUnnormalizedExponent Q lam φ) (D : MonoidAlgebra ℂ (𝓕.positiveSplitComponent R)) :
    𝓕.HasUnnormalizedExponent Q lam (𝓕.shiftAlgHom R D φ) := by
  obtain ⟨k, hk⟩ := hφ
  exact ⟨k, HasPolynomialOrbit.shiftAlgHom 𝓕 hQR hk D⟩

/-- For `Q ⊆ R`, the group algebra of `𝔄_R` preserves the cuspidal annihilator along `Q`. -/
theorem shiftAlgHom_mem_cuspidalAnnihilator {Q R : Idx} (hQR : Q ≤ R) {φ : Fun}
    (hφ : φ ∈ 𝓕.cuspidalAnnihilator Kinf rho Q)
    (D : MonoidAlgebra ℂ (𝓕.positiveSplitComponent R)) :
    𝓕.shiftAlgHom R D φ ∈ 𝓕.cuspidalAnnihilator Kinf rho Q :=
  𝓕.shiftAlgHom_mem (𝓕.cuspidalAnnihilator Kinf rho Q)
    (fun a v hv => by
      rw [← 𝓕.unnormalizedAction_splitLift hQR a]
      exact InCuspidalAnnihilator.adelicLeftShift 𝓕 Kinf rho _ hv) D φ hφ

/-- Functions whose pairings with all Levi cusp forms along `J` converge absolutely at every
point. -/
def leviIntegrableSubmodule (J : Idx) : Submodule ℂ Fun where
  carrier := {φ | ∀ ψ : AdelicGroupPoints F (𝓕.M J) → ℂ, 𝓕.IsLeviCuspForm Kinf rho J ψ →
    ∀ g : AdelicGroupPoints F G,
      Integrable (𝓕.leviPairingIntegrand J φ g ψ) (normOneRationalQuotientHaarMeasure F (𝓕.M J))}
  zero_mem' := fun ψ _ g => by
    have h0 : 𝓕.leviPairingIntegrand J 0 g ψ = 0 := by
      funext x
      simp [leviPairingIntegrand]
    rw [h0]
    exact integrable_zero _ _ _
  add_mem' {φ φ'} hφ hφ' := fun ψ hψ g => by
    have h : 𝓕.leviPairingIntegrand J (φ + φ') g ψ =
        𝓕.leviPairingIntegrand J φ g ψ + 𝓕.leviPairingIntegrand J φ' g ψ := by
      funext x
      simp only [leviPairingIntegrand, Pi.add_apply, add_mul]
    rw [h]
    exact (hφ ψ hψ g).add (hφ' ψ hψ g)
  smul_mem' c φ hφ := fun ψ hψ g => by
    have h : 𝓕.leviPairingIntegrand J (c • φ) g ψ = c • 𝓕.leviPairingIntegrand J φ g ψ := by
      funext x
      simp only [leviPairingIntegrand, Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [h]
    exact (hφ ψ hψ g).smul c

/-- Translation by a point of `𝔄_J` is a right translation on the Levi pairing integrand. -/
theorem leviPairingIntegrand_unnormalizedAction (J : Idx) (b : 𝓕.positiveSplitComponent J)
    (φ : Fun) (g : AdelicGroupPoints F G) (ψ : AdelicGroupPoints F (𝓕.M J) → ℂ) :
    𝓕.leviPairingIntegrand J (𝓕.unnormalizedAction J b φ) g ψ =
      𝓕.leviPairingIntegrand J φ (map F (𝓕.P J) G (𝓕.p J) b * g) ψ := by
  funext q
  simp only [leviPairingIntegrand, unnormalizedAction]
  rw [← mul_assoc, (𝓕.commute_positiveSplitComponent_levi J b _).eq, mul_assoc]

/-- For `Q ⊆ R`, the group algebra of `𝔄_R` preserves absolute convergence of the Levi
pairings along `Q`. -/
theorem shiftAlgHom_mem_leviIntegrableSubmodule {Q R : Idx} (hQR : Q ≤ R) {φ : Fun}
    (hφ : φ ∈ 𝓕.leviIntegrableSubmodule Kinf rho Q)
    (D : MonoidAlgebra ℂ (𝓕.positiveSplitComponent R)) :
    𝓕.shiftAlgHom R D φ ∈ 𝓕.leviIntegrableSubmodule Kinf rho Q :=
  𝓕.shiftAlgHom_mem (𝓕.leviIntegrableSubmodule Kinf rho Q)
    (fun a v hv => by
      rw [← 𝓕.unnormalizedAction_splitLift hQR a]
      intro ψ hψ g
      rw [𝓕.leviPairingIntegrand_unnormalizedAction]
      exact hv ψ hψ _) D φ hφ

/-- For `Q ⊆ R`, the constant term along `Q` commutes with the group algebra of `𝔄_R` on
functions invariant under `U_R(𝔸)` with absolutely convergent constant terms along `Q`. -/
theorem constantTerm_shiftAlgHom {Q R : Idx} (hQR : Q ≤ R) {φ : Fun}
    (hφ : φ ∈ 𝓕.radicalIntegrableSubmodule Q R)
    (D : MonoidAlgebra ℂ (𝓕.positiveSplitComponent R)) :
    𝓕.constantTerm Q (𝓕.shiftAlgHom R D φ) = 𝓕.shiftAlgHom R D (𝓕.constantTerm Q φ) :=
  𝓕.shiftAlgHom_intertwine (𝓕.radicalIntegrableSubmodule Q R)
    (fun a _ hv => 𝓕.adelicLeftShift_mem_radicalIntegrableSubmodule hQR a hv)
    (𝓕.constantTerm Q)
    (fun _ hv _ hw => 𝓕.constantTerm_add_of_hasIntegrableConstantTerm hv.2 hw.2)
    (fun c v _ => 𝓕.constantTerm_const_smul Q c v)
    (fun a _ hv => 𝓕.constantTerm_unnormalizedAction_of_radicalInvariant hQR a hv.1)
    D φ hφ

theorem shiftAlgHom_mem_radicalIntegrableSubmodule {Q R : Idx} (hQR : Q ≤ R) {φ : Fun}
    (hφ : φ ∈ 𝓕.radicalIntegrableSubmodule Q R)
    (D : MonoidAlgebra ℂ (𝓕.positiveSplitComponent R)) :
    𝓕.shiftAlgHom R D φ ∈ 𝓕.radicalIntegrableSubmodule Q R :=
  𝓕.shiftAlgHom_mem (𝓕.radicalIntegrableSubmodule Q R)
    (fun a _ hv => 𝓕.adelicLeftShift_mem_radicalIntegrableSubmodule hQR a hv) D φ hφ

/-- An automorphic function along `Q ⊆ R` is invariant under `U_R(𝔸)` and has absolutely
convergent constant terms along every `Q' ⊆ Q`. -/
theorem mem_radicalIntegrableSubmodule_of_automorphicOn {Q' Q R : Idx} (hQ'Q : Q' ≤ Q)
    (hQR : Q ≤ R) {h : Fun} (hh : 𝓕.IsAutomorphicOn hsmooth Kinf rho Q h) :
    h ∈ 𝓕.radicalIntegrableSubmodule Q' R := by
  have hgen := 𝓕.isParabolicGeneratorInvariant_of_isLeftInvariantUnder Q hh.1
  refine ⟨fun n g => hgen.1 ⟨n.1, 𝓕.radical_le_of_le hQR _ n.2⟩ g, fun g => ?_⟩
  exact 𝓕.integrable_constantTermIntegrand_of_le Q Q' hQ'Q hh.2.1.1 hh.1 g

/-- For `Q ⊆ R`, the group algebra of `𝔄_R` preserves cuspidality along `Q` of automorphic
functions along `Q`. -/
theorem IsCuspidalAlong.shiftAlgHom {Q R : Idx} (hQR : Q ≤ R) {h : Fun}
    (hh : 𝓕.IsAutomorphicOn hsmooth Kinf rho Q h) (hc : 𝓕.IsCuspidalAlong Q h)
    (D : MonoidAlgebra ℂ (𝓕.positiveSplitComponent R)) :
    𝓕.IsCuspidalAlong Q (𝓕.shiftAlgHom R D h) := by
  intro Q' hQ'
  rw [𝓕.constantTerm_shiftAlgHom (hQ'.le.trans hQR)
    (𝓕.mem_radicalIntegrableSubmodule_of_automorphicOn hsmooth Kinf rho hQ'.le hQR hh) D,
    hc Q' hQ', map_zero]

/-- For `Q ⊆ R`, the group algebra of `𝔄_R` preserves the relation "cuspidal projection along
`Q`". -/
theorem IsCuspidalProjection.shiftAlgHom {Q R : Idx} (hQR : Q ≤ R) {h hc : Fun}
    (hp : 𝓕.IsCuspidalProjection hsmooth Kinf rho Q h hc)
    (D : MonoidAlgebra ℂ (𝓕.positiveSplitComponent R)) :
    𝓕.IsCuspidalProjection hsmooth Kinf rho Q (𝓕.shiftAlgHom R D h) (𝓕.shiftAlgHom R D hc) := by
  refine ⟨IsAutomorphicOn.shiftAlgHom 𝓕 hsmooth Kinf rho hQR hp.1 D,
    IsCuspidalAlong.shiftAlgHom 𝓕 hsmooth Kinf rho hQR hp.1 hp.2.1 D, ?_⟩
  have hdiff : h - hc ∈ 𝓕.cuspidalAnnihilator Kinf rho Q := by
    intro ψ hψ g
    obtain ⟨i₁, i₂, he⟩ := hp.2.2 ψ hψ g
    let L := 𝓕.leviPairingIntegrandLinearMap Q g ψ
    change Integrable (L (h - hc)) _ ∧ (∫ x, L (h - hc) x ∂_) = 0
    rw [map_sub]
    refine ⟨i₁.sub i₂, ?_⟩
    exact (integral_sub i₁ i₂).trans (sub_eq_zero.mpr he)
  have hint : hc ∈ 𝓕.leviIntegrableSubmodule Kinf rho Q := fun ψ hψ g => (hp.2.2 ψ hψ g).2.1
  have hdiff' := 𝓕.shiftAlgHom_mem_cuspidalAnnihilator Kinf rho hQR hdiff D
  have hint' := 𝓕.shiftAlgHom_mem_leviIntegrableSubmodule Kinf rho hQR hint D
  rw [map_sub] at hdiff'
  intro ψ hψ g
  obtain ⟨j₁, e₁⟩ := hdiff' ψ hψ g
  have j₂ := hint' ψ hψ g
  let L := 𝓕.leviPairingIntegrandLinearMap Q g ψ
  have hsplit : 𝓕.shiftAlgHom R D h =
      (𝓕.shiftAlgHom R D h - 𝓕.shiftAlgHom R D hc) + 𝓕.shiftAlgHom R D hc := by abel
  change Integrable (L _) _ ∧ Integrable (L _) _ ∧ (∫ x, L _ x ∂_) = (∫ x, L _ x ∂_)
  change Integrable (L _) _ at j₁ j₂
  change (∫ x, L _ x ∂_) = 0 at e₁
  rw [hsplit, map_add]
  refine ⟨j₁.add j₂, j₂, ?_⟩
  change (∫ x, L _ x + L _ x ∂_) = _
  rw [integral_add j₁ j₂, e₁, zero_add]

/-- For `Q ⊆ R`, the group algebra of `𝔄_R` maps an exponent decomposition along `Q` to an
exponent decomposition with the same labels. -/
theorem IsExponentDecomposition.shiftAlgHom {Q R : Idx} (hQR : Q ≤ R) {ψ : Fun}
    {s : Finset (ComplexCharacterParameter F (𝓕.P Q))}
    {c : ComplexCharacterParameter F (𝓕.P Q) → Fun}
    (hd : 𝓕.IsExponentDecomposition hsmooth Kinf rho Q ψ s c)
    (D : MonoidAlgebra ℂ (𝓕.positiveSplitComponent R)) :
    𝓕.IsExponentDecomposition hsmooth Kinf rho Q (𝓕.shiftAlgHom R D ψ) s
      (fun lam => 𝓕.shiftAlgHom R D (c lam)) where
  sum_eq := by rw [hd.sum_eq, map_sum]
  automorphic lam hlam := IsAutomorphicOn.shiftAlgHom 𝓕 hsmooth Kinf rho hQR (hd.automorphic lam hlam) D
  cuspidal lam hlam := IsCuspidalAlong.shiftAlgHom 𝓕 hsmooth Kinf rho hQR (hd.automorphic lam hlam)
    (hd.cuspidal lam hlam) D
  exponent lam hlam := HasUnnormalizedExponent.shiftAlgHom 𝓕 hQR (hd.exponent lam hlam) D

end Stability

section Factors

/-- The value of the shift operator of a point of `𝔄_R`, as a left translation along `Q`. -/
theorem shiftAlgHom_of_eq_leftFunctions {Q R : Idx} (hQR : Q ≤ R)
    (a : 𝓕.positiveSplitComponent R) :
    𝓕.shiftAlgHom R (MonoidAlgebra.of ℂ _ a) =
      GroupAction.leftFunctions (map F (𝓕.P Q) G (𝓕.p Q) (𝓕.splitLift hQR a))⁻¹ := by
  apply LinearMap.ext
  intro φ
  funext g
  rw [shiftAlgHom_of, GroupAction.leftFunctions_apply, inv_inv,
    ← 𝓕.unnormalizedAction_splitLift hQR a]
  rfl

/-- The operator of a power of a difference `a - z` is the corresponding polynomial in the shift
by `a`. -/
theorem shiftAlgHom_factor {R : Idx} (a : 𝓕.positiveSplitComponent R) (z : ℂ) (m : ℕ) :
    𝓕.shiftAlgHom R ((MonoidAlgebra.of ℂ _ a - algebraMap ℂ _ z) ^ m) =
      aeval (𝓕.shiftAlgHom R (MonoidAlgebra.of ℂ _ a)) ((X - C z) ^ m) := by
  rw [map_pow, map_sub, AlgHom.commutes, map_pow, map_sub, aeval_X, aeval_C]

/-- A power of `a - a^λ` of exponent `k + 1` kills every function with polynomial orbits of
degree at most `k` for the exponent `λ` along `Q ⊆ R`. -/
theorem shiftAlgHom_factor_eq_zero {Q R : Idx} (hQR : Q ≤ R)
    {lam : ComplexCharacterParameter F (𝓕.P Q)} {k : ℕ} {φ : Fun}
    (hφ : 𝓕.HasPolynomialOrbit Q lam k φ) (a : 𝓕.positiveSplitComponent R) :
    𝓕.shiftAlgHom R ((MonoidAlgebra.of ℂ _ a -
      algebraMap ℂ _ (parameterPower F (𝓕.P Q) lam (𝓕.splitLift hQR a))) ^ (k + 1)) φ = 0 := by
  have h := 𝓕.isTranslationPolynomialSolution_pow_of_polynomialOrbit Q hφ (𝓕.splitLift hQR a)
  rw [isTranslationPolynomialSolution_iff_aeval] at h
  rw [shiftAlgHom_factor, 𝓕.shiftAlgHom_of_eq_leftFunctions hQR a]
  exact h

/-- A power of `a - z` is injective on functions with polynomial orbits for an exponent `λ`
along `Q ⊆ R` when `z` differs from `a^λ`. -/
theorem eq_zero_of_shiftAlgHom_factor_eq_zero {Q R : Idx} (hQR : Q ≤ R)
    {lam : ComplexCharacterParameter F (𝓕.P Q)} {k : ℕ} {φ : Fun}
    (hφ : 𝓕.HasPolynomialOrbit Q lam k φ) (a : 𝓕.positiveSplitComponent R) (z : ℂ) (m : ℕ)
    (hz : z ≠ parameterPower F (𝓕.P Q) lam (𝓕.splitLift hQR a))
    (h0 : 𝓕.shiftAlgHom R ((MonoidAlgebra.of ℂ _ a - algebraMap ℂ _ z) ^ m) φ = 0) :
    φ = 0 := by
  set T := 𝓕.shiftAlgHom R (MonoidAlgebra.of ℂ _ a)
  set w := parameterPower F (𝓕.P Q) lam (𝓕.splitLift hQR a)
  have h1 : aeval T ((X - C z) ^ m) φ = 0 := by
    rw [← shiftAlgHom_factor]
    exact h0
  have h2 : aeval T ((X - C w) ^ (k + 1)) φ = 0 := by
    rw [← shiftAlgHom_factor]
    exact 𝓕.shiftAlgHom_factor_eq_zero hQR hφ a
  obtain ⟨u, v, huv⟩ :=
    (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hz).isUnit).pow (m := m) (n := k + 1)
  calc φ = aeval T (u * (X - C z) ^ m + v * (X - C w) ^ (k + 1)) φ := by
        rw [huv, map_one, Module.End.one_apply]
    _ = aeval T u (aeval T ((X - C z) ^ m) φ) + aeval T v (aeval T ((X - C w) ^ (k + 1)) φ) := by
        rw [map_add, map_mul, map_mul, LinearMap.add_apply, Module.End.mul_apply,
          Module.End.mul_apply]
    _ = 0 := by rw [h1, h2, map_zero, map_zero, add_zero]

/-- A product of powers of differences, one of which kills a function, kills it. -/
theorem shiftAlgHom_prod_eq_zero {R : Idx} {Ix : Type*} [DecidableEq Ix] (S : Finset Ix)
    (A : Ix → 𝓕.positiveSplitComponent R) (Z : Ix → ℂ) (M : Ix → ℕ) {j : Ix} (hj : j ∈ S)
    {φ : Fun}
    (h0 : 𝓕.shiftAlgHom R ((MonoidAlgebra.of ℂ _ (A j) - algebraMap ℂ _ (Z j)) ^ M j) φ = 0) :
    𝓕.shiftAlgHom R (∏ i ∈ S, (MonoidAlgebra.of ℂ _ (A i) - algebraMap ℂ _ (Z i)) ^ M i) φ = 0 := by
  rw [← Finset.prod_erase_mul S _ hj, map_mul, Module.End.mul_apply, h0, map_zero]

/-- A product of powers of differences `A i - Z i`, with every `Z i` different from
`(A i)^λ`, is injective on functions with polynomial orbits for `λ` along `Q ⊆ R`. -/
theorem eq_zero_of_shiftAlgHom_prod_eq_zero {Q R : Idx} (hQR : Q ≤ R) {Ix : Type*}
    [DecidableEq Ix] (S : Finset Ix) (A : Ix → 𝓕.positiveSplitComponent R) (Z : Ix → ℂ)
    (M : Ix → ℕ) {lam : ComplexCharacterParameter F (𝓕.P Q)} {k : ℕ} {φ : Fun}
    (hφ : 𝓕.HasPolynomialOrbit Q lam k φ)
    (hZ : ∀ i ∈ S, Z i ≠ parameterPower F (𝓕.P Q) lam (𝓕.splitLift hQR (A i)))
    (h0 : 𝓕.shiftAlgHom R (∏ i ∈ S, (MonoidAlgebra.of ℂ _ (A i) - algebraMap ℂ _ (Z i)) ^ M i)
      φ = 0) :
    φ = 0 := by
  induction S using Finset.induction_on generalizing φ with
  | empty =>
    rw [Finset.prod_empty, map_one, Module.End.one_apply] at h0
    exact h0
  | insert j S hjS ih =>
    rw [Finset.prod_insert hjS, map_mul, Module.End.mul_apply] at h0
    have hin := HasPolynomialOrbit.shiftAlgHom 𝓕 hQR hφ
      (∏ i ∈ S, (MonoidAlgebra.of ℂ _ (A i) - algebraMap ℂ _ (Z i)) ^ M i)
    have hz := 𝓕.eq_zero_of_shiftAlgHom_factor_eq_zero hQR hin (A j) (Z j) (M j)
      (hZ j (Finset.mem_insert_self j S)) h0
    exact ih hφ (fun i hi => hZ i (Finset.mem_insert_of_mem hi)) hz

end Factors


end Langlands.Global.StandardParabolicFamily
