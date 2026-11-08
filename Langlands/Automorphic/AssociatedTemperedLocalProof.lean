import Langlands.Automorphic.AssociatedFactorStatement
import Langlands.Global.Factors.CertifiedFactorSeparationProof
import Langlands.LocalFactor.UnitaryArithmeticPair
import Langlands.LocalFactor.UnitaryWeilDeligne
import Langlands.WeilDeligne.TensorDual
import Langlands.Correspondence.SupercuspidalOperationRealization

/-! # Local assembly of the tempered associated factor equalities -/

noncomputable section

universe uG uV uF uE u

namespace Langlands.Global.FactorSeparation

open LocalFactor

/-- The original and reflected dual Euler polynomials of a unitary Weil action
have no common nonzero zero. -/
theorem noReflectedCommonZero_of_isUnitary
    {G : Type uG} [Group G] {ν : G →* ℂˣ}
    (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    (I : Subgroup G) [I.Normal] (g : G)
    (hA : A.toFiniteRepresentation.IsUnitary) {q : ℕ} (hq : 1 < q) :
    GLPoleRegion.HasNoReflectedCommonZero q
      (WeilDeligne.eulerPolynomial A I g)
      (WeilDeligne.eulerPolynomial (WeilDeligneRepresentation.dual A) I g) := by
  intro z _ h
  have hz : ‖z‖ = 1 := by
    by_contra hn
    exact WeilDeligne.eulerPolynomial_eval_ne_zero_of_isUnitary A I hA g hn h.1
  have hq' : 1 < (q : ℝ) := by exact_mod_cast hq
  have hr : ‖(q : ℂ)⁻¹ * z⁻¹‖ ≠ 1 := by
    rw [norm_mul, norm_inv, norm_inv, hz, inv_one, mul_one, Complex.norm_natCast]
    exact ne_of_lt (inv_lt_one_of_one_lt₀ hq')
  exact WeilDeligne.eulerPolynomial_eval_ne_zero_of_isUnitary
    (WeilDeligneRepresentation.dual A) I
    (FiniteRepresentation.isUnitary_dual A.toFiniteRepresentation hA) g hr h.2

end Langlands.Global.FactorSeparation

namespace Langlands.ClassField.Global.RelativeWeilGroup

open LocalFactor LocalFactor.CommonClosure Correspondence Weil.Local

section Local

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uF} p)

/-- Gamma equality for every supplied system yields all factor equalities when
one system exists, the Weil actions are unitary, and automorphic pole regions
are certified. -/
theorem isPairFactorMatch_of_unitary_gamma
    (ψ : NontrivialAdditiveCharacter K)
    (A B : LocalWeilDeligneRepresentation.{uF, uV} K)
    {r t : ℕ} (π : AutomorphicClass.{uF, uF} K r.succPNat)
    (π' : AutomorphicClass.{uF, uF} K t.succPNat)
    (hA : A.toFiniteRepresentation.IsUnitary)
    (hB : B.toFiniteRepresentation.IsUnitary)
    (hGL : Global.FactorSeparation.CertifiedAutomorphicPoleRegions K ψ π π')
    (eC₀ : ReciprocityFamily K) (ε₀ : NonabelianSystem.Assignment.{uF, uE} K)
    (hε₀ : NonabelianSystem.IsSystem K eC₀ ε₀)
    (hgamma : ∀ (eC : ReciprocityFamily K)
      (ε : NonabelianSystem.Assignment.{uF, uE} K)
      (hε : NonabelianSystem.IsSystem K eC ε),
      IsPairGammaMatch K eC ε hε ψ π π'
        (WeilDeligneRepresentation.classOf A) (WeilDeligneRepresentation.classOf B)) :
    IsPairFactorMatch.{uF, uV, uE} K ψ π π'
      (WeilDeligneRepresentation.classOf A) (WeilDeligneRepresentation.classOf B)
      (WeilDeligneRepresentation.dualClass (WeilDeligneRepresentation.classOf A))
      (WeilDeligneRepresentation.dualClass (WeilDeligneRepresentation.classOf B)) := by
  have hW := Global.FactorSeparation.noReflectedCommonZero_of_isUnitary
    (WeilDeligneRepresentation.tensor A B) (localInertia K) (localGeometricFrobenius K)
    (WeilDeligneRepresentation.tensor_isUnitary hA hB)
    K.canonicalTopologicalData.residueCardinality_gt_one
  have hs (eC : ReciprocityFamily K) (ε : NonabelianSystem.Assignment.{uF, uE} K)
      (hε : NonabelianSystem.IsSystem K eC ε) :=
    Global.FactorSeparation.certifiedFactorSeparation K eC ε hε ψ
      (WeilDeligneRepresentation.classOf A) (WeilDeligneRepresentation.classOf B)
      (WeilDeligneRepresentation.tensor A B) rfl r t π π' hW hGL (hgamma eC ε hε)
  have h₀ := hs eC₀ ε₀ hε₀
  refine ⟨⟨h₀.1, ?_⟩, ?_, ?_⟩
  · intro ν hν
    obtain ⟨_, _, P, _, _, _, _, hP, _, _, _, _, _, hL, _⟩ := h₀.2 ν hν
    exact ⟨P, hP, hL⟩
  · intro πd πd' hπd hπd'
    refine ⟨h₀.1, ?_⟩
    intro ν hν
    obtain ⟨δ, δ', _, Pd, _, hδ, hδ', _, hPd, _, _, _, _, _, hLd⟩ := h₀.2 ν hν
    have hd : πd = δ :=
      ((isSmoothDual_iff_eq_contragredient K π πd).mp hπd).trans
        ((isSmoothDual_iff_eq_contragredient K π δ).mp hδ).symm
    have hd' : πd' = δ' :=
      ((isSmoothDual_iff_eq_contragredient K π' πd').mp hπd').trans
        ((isSmoothDual_iff_eq_contragredient K π' δ').mp hδ').symm
    subst πd
    subst πd'
    refine ⟨Pd, hPd, ?_⟩
    change WeilDeligne.rationalLFactor
      (WeilDeligneRepresentation.tensor
        (WeilDeligneRepresentation.dual A) (WeilDeligneRepresentation.dual B))
      (localInertia K) (localGeometricFrobenius K) = _
    rw [WeilDeligne.rationalLFactor_eq_of_equiv (localInertia K)
      (WeilDeligneRepresentation.tensorDualEquiv A B) (localGeometricFrobenius K)]
    exact hLd
  · intro eC ε hε
    refine ⟨(hs eC ε hε).1, ?_⟩
    intro ν hν
    obtain ⟨_, _, _, _, e, _, _, _, _, he, hear, _⟩ := (hs eC ε hε).2 ν hν
    exact ⟨e, he, hear⟩

end Local

section RelativeLocal

open Langlands.Global Langlands.Global.CompletionPadic

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E] {c : FundamentalClass.ClassFamily.{u}}
  {v : FinitePlace F}

/-- Restriction of the algebraic dual is canonically the algebraic dual of
restriction, on the same space of linear functionals. -/
def localComponentDualEquiv
    (S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (ι : localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E) :
    FiniteRepresentation.Equiv (localComponent S.dual ι) (localComponent S ι).dual :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ _) (fun g => by
    change (S.representation ((ι g)⁻¹)).dualMap =
      (S.representation (ι (g⁻¹))).dualMap
    rw [map_inv ι g])

/-- The dual local pair class in the global statement is the dual of the
original local pair class. -/
theorem localPairClass_dual
    (S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (ι : localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E) :
    localPairClass S.dual ι = WeilDeligneRepresentation.dualClass (localPairClass S ι) := by
  apply Quotient.sound
  refine ⟨WeilDeligneRepresentation.Equiv.trans
    (WeilDeligneRepresentation.Equiv.ofIso
      ((WeilDeligneRepresentation.zeroMonodromyFunctor _).mapIso
        (FiniteRepresentation.isoOfEquiv (localComponentDualEquiv S ι))))
    (WeilDeligneRepresentation.dualZeroMonodromyEquiv (localComponent S ι)).symm⟩

/-- The local assembly with exactly the original and dual Weil classes occurring
in the global associated tempered factor statement. -/
theorem isPairFactorMatch_localPairClass_of_unitary_gamma
    (S S' : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (ι : localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E)
    (ψ : NontrivialAdditiveCharacter (padicField v))
    {r t : ℕ} (π : AutomorphicClass.{u, u} (padicField v) r.succPNat)
    (π' : AutomorphicClass.{u, u} (padicField v) t.succPNat)
    (hS : (localComponent S ι).IsUnitary)
    (hS' : (localComponent S' ι).IsUnitary)
    (hGL : Global.FactorSeparation.CertifiedAutomorphicPoleRegions
      (padicField v) ψ π π')
    (eC₀ : ReciprocityFamily (padicField v))
    (ε₀ : NonabelianSystem.Assignment.{u, uE} (padicField v))
    (hε₀ : NonabelianSystem.IsSystem (padicField v) eC₀ ε₀)
    (hgamma : ∀ (eC : ReciprocityFamily (padicField v))
      (ε : NonabelianSystem.Assignment.{u, uE} (padicField v))
      (hε : NonabelianSystem.IsSystem (padicField v) eC ε),
      IsPairGammaMatch (padicField v) eC ε hε ψ π π'
        (localPairClass S ι) (localPairClass S' ι)) :
    IsPairFactorMatch.{u, uV, uE} (padicField v) ψ π π'
      (localPairClass S ι) (localPairClass S' ι)
      (localPairClass S.dual ι) (localPairClass S'.dual ι) := by
  rw [localPairClass_dual S ι, localPairClass_dual S' ι]
  exact isPairFactorMatch_of_unitary_gamma (padicField v) ψ
    (WeilDeligneRepresentation.zeroMonodromy _ (localComponent S ι))
    (WeilDeligneRepresentation.zeroMonodromy _ (localComponent S' ι))
    π π' hS hS' hGL eC₀ ε₀ hε₀ hgamma

end RelativeLocal

end Langlands.ClassField.Global.RelativeWeilGroup
