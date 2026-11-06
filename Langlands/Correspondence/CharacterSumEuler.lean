import Langlands.Correspondence.UnramifiedReciprocityBridge
import Langlands.LocalFactor.UnramifiedDegree
import Langlands.LocalFactor.WeilDeligne

/-!
# Euler polynomials of character-sum parameters

For a pair with zero monodromy on which a normal subgroup `I` acts trivially, the
Weil–Deligne Euler polynomial `det(1 - X g | (ker N)^I)` is the Euler polynomial of
`g` on the whole carrier. For the character sum `⊕_i (ψ_i, 0)` of characters trivial
on inertia it is `∏_i (1 - ψ_i(g) X)`. The same holds for every pair representing a
character-sum parameter class. At the geometric Frobenius lift, for a geometric
candidate and unramified quasi-characters, it is `∏_i (1 - χ_i(ϖ) X)`.
-/

noncomputable section

universe u v w uK uG uV uF uP

open Polynomial

namespace Langlands.LocalFactor

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
  [Module.Free R V] [Module.Finite R V]

/-- If an operator is diagonal in a finite basis, with diagonal entries `c i`, its
Euler polynomial is `∏_i (1 - c_i X)`. -/
theorem eulerPolynomial_eq_prod_of_repr {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R V) (f : Module.End R V) (c : ι → R)
    (h : ∀ v i, b.repr (f v) i = c i * b.repr v i) :
    eulerPolynomial f = ∏ i, (1 - C (c i) * X) := by
  have hm : LinearMap.toMatrix b b f = Matrix.diagonal c := by
    ext i j
    rw [LinearMap.toMatrix_apply, h, Module.Basis.repr_self, Matrix.diagonal_apply,
      Finsupp.single_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  rw [eulerPolynomial_eq_det f b, hm, Matrix.diagonal_map (map_zero C),
    ← Matrix.diagonal_one, ← Matrix.diagonal_smul, Matrix.diagonal_sub,
    Matrix.det_diagonal]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

end Langlands.LocalFactor

namespace Langlands.WeilDeligneRepresentation

variable {K : Type uK} [Field K] {G : Type uG} [Group G] {ν : G →* Kˣ}
  (I : Subgroup G) [I.Normal] (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)

/-- With zero monodromy and trivial action of `I`, the inclusion of the
`I`-fixed monodromy kernel is surjective. -/
theorem inertiaKernelInclusion_surjective (hN : A.monodromy = 0)
    (hI : ∀ i : I, A.representation i = 1) :
    Function.Surjective (inertiaKernelInclusion I A) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    ((inertiaKernel_rank_eq_iff I A).mpr ⟨hN, hI⟩)).mp (inertiaKernelInclusion_injective I A)

/-- With zero monodromy and trivial action of `I`, the inclusion of the
`I`-fixed monodromy kernel is a linear equivalence onto the carrier. -/
def inertiaKernelEquivOfMonodromyEqZero (hN : A.monodromy = 0)
    (hI : ∀ i : I, A.representation i = 1) :
    inertiaKernelRepresentation I A ≃ₗ[K] A :=
  LinearEquiv.ofBijective (inertiaKernelInclusion I A)
    ⟨inertiaKernelInclusion_injective I A, inertiaKernelInclusion_surjective I A hN hI⟩

end Langlands.WeilDeligneRepresentation

namespace Langlands.LocalFactor.WeilDeligne

variable {K : Type uK} [Field K] {G : Type uG} [Group G] {ν : G →* Kˣ}
  (I : Subgroup G) [I.Normal] (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)

/-- With zero monodromy and trivial action of `I`, the Weil–Deligne Euler
polynomial at `g` is the Euler polynomial of `g` on the whole carrier. -/
theorem eulerPolynomial_eq_of_monodromy_eq_zero (hN : A.monodromy = 0)
    (hI : ∀ i : I, A.representation i = 1) (g : G) :
    eulerPolynomial A I g = LocalFactor.eulerPolynomial (A.representation g) := by
  let E := WeilDeligneRepresentation.inertiaKernelEquivOfMonodromyEqZero I A hN hI
  rw [eulerPolynomial, ← LocalFactor.eulerPolynomial_conj E]
  congr 1
  apply LinearMap.ext
  intro v
  rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  change A.representation g (E (E.symm v)) = A.representation g v
  rw [LinearEquiv.apply_symm_apply]

end Langlands.LocalFactor.WeilDeligne

namespace Langlands.Correspondence

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance characterSumEulerFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

variable {F}

/-- On the character sum, `g` acts with Euler polynomial `∏_i (1 - ψ_i(g) X)`. -/
theorem eulerPolynomial_characterSumPair_representation {ι : Type} [Fintype ι]
    (ψ : ι → Weil.Local.localWeilGroup F →* ℂˣ) (g : Weil.Local.localWeilGroup F) :
    LocalFactor.eulerPolynomial ((characterSumPair.{uF, uP} F ψ).representation g) =
      ∏ i, (1 - C (ψ i g : ℂ) * X) := by
  classical
  let E : (DirectSum ι fun _ => ULift.{uP} ℂ) ≃ₗ[ℂ] (ι →₀ ℂ) :=
    (DFinsupp.mapRange.linearEquiv fun _ => ULift.moduleEquiv).trans
      (finsuppLequivDFinsupp ℂ).symm
  let b : Module.Basis ι ℂ (characterSumPair.{uF, uP} F ψ) := Module.Basis.ofRepr E
  apply LocalFactor.eulerPolynomial_eq_prod_of_repr b
  intro v i
  rfl

/-- The Weil–Deligne Euler polynomial of the character sum of characters trivial on
inertia is `∏_i (1 - ψ_i(g) X)`. -/
theorem eulerPolynomial_characterSumPair {ι : Type} [Fintype ι]
    {ψ : ι → Weil.Local.localWeilGroup F →* ℂˣ}
    (hψ : ∀ i, ∀ w ∈ Weil.Local.localInertia F, ψ i w = 1) (g : Weil.Local.localWeilGroup F) :
    LocalFactor.WeilDeligne.eulerPolynomial (characterSumPair.{uF, uP} F ψ)
        (Weil.Local.localInertia F) g =
      ∏ i, (1 - C (ψ i g : ℂ) * X) := by
  rw [LocalFactor.WeilDeligne.eulerPolynomial_eq_of_monodromy_eq_zero _ _
    (characterSumPair_monodromy ψ) (characterSumPair_isUnramified hψ),
    eulerPolynomial_characterSumPair_representation]

/-- Every pair representing a character-sum parameter class, for characters whose
pullbacks are trivial on inertia, has Weil–Deligne Euler polynomial
`∏_i (1 - (χ_i ∘ e)(g) X)`. -/
theorem eulerPolynomial_of_isCharacterSumParameter (e : ReciprocityCandidate F) {r : ℕ}
    {χ : Fin (r + 1) → QuasiCharacter F}
    (hχ : ∀ i, ∀ w ∈ Weil.Local.localInertia F, weilCharacter F e (χ i) w = 1)
    {D : WeilDeligneClass.{uF, uP} F r.succPNat} (hD : IsCharacterSumParameter F e χ D)
    {A : Weil.Local.LocalWeilDeligneRepresentation.{uF, uP} F}
    (hA : WeilDeligneRepresentation.classOf A = parameterForget F D)
    (g : Weil.Local.localWeilGroup F) :
    LocalFactor.WeilDeligne.eulerPolynomial A (Weil.Local.localInertia F) g =
      ∏ i, (1 - C (weilCharacter F e (χ i) g : ℂ) * X) := by
  obtain ⟨B, hB, ⟨f⟩⟩ := hD
  obtain ⟨fAB⟩ := (WeilDeligneRepresentation.classOf_eq_iff A B).mp (hA.trans hB.symm)
  have fSB := (WeilDeligneRepresentation.directSumCongr fun i =>
    WeilDeligneRepresentation.zeroMonodromyCongr
      (Weil.Local.localNormCharacter F).toMonoidHom
      (FiniteRepresentation.characterLineEquiv.{uF, uP} (weilCharacter F e (χ i)))).trans f
  rw [LocalFactor.WeilDeligne.eulerPolynomial_eq_of_equiv _ fAB,
    ← LocalFactor.WeilDeligne.eulerPolynomial_eq_of_equiv _ fSB]
  exact eulerPolynomial_characterSumPair hχ g

/-- Under a geometric candidate, the pullback of an unramified quasi-character takes
the value `χ(ϖ)` at the geometric Frobenius lift. -/
theorem weilCharacter_localGeometricFrobenius {e : ReciprocityCandidate F}
    (he : IsGeometricReciprocity F e) {χ : QuasiCharacter F}
    (hχ : F.canonicalTopologicalData.IsUnramifiedCharacter χ.toMonoidHom) :
    weilCharacter F e χ (Weil.Local.localGeometricFrobenius F) =
      χ F.canonicalTopologicalData.uniformizerUnit := by
  rw [weilCharacter_apply_of_isUnramified F he hχ, Weil.Local.localDegreeInt,
    Weil.Local.localGeometricFrobenius_degree, toAdd_ofAdd, zpow_one]

/-- For a geometric candidate and unramified quasi-characters, every pair
representing the character-sum parameter class has Weil–Deligne Euler polynomial
`∏_i (1 - χ_i(ϖ) X)` at the geometric Frobenius lift. -/
theorem eulerPolynomial_of_isCharacterSumParameter_of_isGeometricReciprocity
    {e : ReciprocityCandidate F} (he : IsGeometricReciprocity F e) {r : ℕ}
    {χ : Fin (r + 1) → QuasiCharacter F}
    (hχ : ∀ i, F.canonicalTopologicalData.IsUnramifiedCharacter (χ i).toMonoidHom)
    {D : WeilDeligneClass.{uF, uP} F r.succPNat} (hD : IsCharacterSumParameter F e χ D)
    {A : Weil.Local.LocalWeilDeligneRepresentation.{uF, uP} F}
    (hA : WeilDeligneRepresentation.classOf A = parameterForget F D) :
    LocalFactor.WeilDeligne.eulerPolynomial A (Weil.Local.localInertia F)
        (Weil.Local.localGeometricFrobenius F) =
      ∏ i, (1 - C (χ i F.canonicalTopologicalData.uniformizerUnit : ℂ) * X) := by
  rw [eulerPolynomial_of_isCharacterSumParameter e
    (fun i _ hw => weilCharacter_eq_one_of_mem_localInertia F he (hχ i) hw) hD hA]
  simp only [weilCharacter_localGeometricFrobenius he (hχ _)]

end Langlands.Correspondence
