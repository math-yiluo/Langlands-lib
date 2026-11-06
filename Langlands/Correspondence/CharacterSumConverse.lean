import Langlands.Correspondence.CharacterSumEuler
import Langlands.Correspondence.UnramifiedEuler
import Langlands.Weil.Local.AssemblyProof
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Semisimple

/-!
# Unramified parameters with a given Euler polynomial are character sums

A Frobenius-semisimple parameter class with zero monodromy and trivial inertia action
is determined by the Euler polynomial of the geometric Frobenius lift. If that
polynomial is `∏_i (1 - c_i X)`, the class is `unramifiedCharacterSumClass F c`, the
character sum of the unramified characters `w ↦ c_i ^ deg(w)`. For a geometric
candidate and unramified quasi-characters, this characterizes the character-sum
parameter. In terms of the standard Euler polynomial `parameterEulerPolynomial F D`, a
class of rank `r + 1` has standard Euler polynomial `∏_i (1 - c_i X)` exactly when it is
`unramifiedCharacterSumClass F c`; no unramifiedness hypothesis is needed.
-/

noncomputable section

universe u v w uF uP

open Polynomial

namespace Langlands.LocalFactor

/-- If a finite basis consists of eigenvectors, with eigenvalues `c i`, the Euler
polynomial is `∏_i (1 - c_i X)`. -/
theorem eulerPolynomial_eq_prod_of_apply_basis {R : Type u} [CommRing R] {V : Type v}
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    {ι : Type w} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R V) (f : Module.End R V) (c : ι → R)
    (h : ∀ i, f (b i) = c i • b i) :
    eulerPolynomial f = ∏ i, (1 - C (c i) * X) := by
  refine eulerPolynomial_eq_prod_of_repr b f c fun v i => ?_
  have hc : (b.coord i).comp f = c i • b.coord i := b.ext fun j => by
    by_cases hij : j = i
    · subst hij
      simp [h]
    · simp [h, hij]
  simpa using LinearMap.congr_fun hc v

/-- The roots of `∏_i (1 - a_i X)`, for nonzero `a_i`, are the inverses `a_i⁻¹`. -/
theorem roots_prod_one_sub_C_mul_X {K : Type u} [Field K] {ι : Type w} [Fintype ι]
    (a : ι → K) (ha : ∀ i, a i ≠ 0) :
    (∏ i, (1 - C (a i) * X)).roots = Finset.univ.val.map fun i => (a i)⁻¹ := by
  have hfac : ∀ i, (1 - C (a i) * X : K[X]) = C (-a i) * (X - C (a i)⁻¹) := by
    intro i
    rw [mul_sub, ← C_mul, neg_mul, mul_inv_cancel₀ (ha i), C_neg, C_neg, C_1]
    ring
  have hne : ∀ i ∈ Finset.univ, (1 - C (a i) * X : K[X]) ≠ 0 := fun i _ h0 => by
    have := congrArg (eval 0) h0
    simp at this
  rw [roots_prod _ _ (Finset.prod_ne_zero_iff.mpr hne)]
  simp_rw [hfac, roots_C_mul _ (neg_ne_zero.mpr (ha _)), roots_X_sub_C]
  exact Multiset.bind_singleton _ _

/-- Two finite families with the same multiset of values differ by a bijection of
their index types. -/
theorem exists_equiv_of_map_univ_eq {α : Type u} {β : Type v} {γ : Type w} [Fintype α]
    [Fintype β] [DecidableEq γ] {f : α → γ} {g : β → γ}
    (h : Finset.univ.val.map f = Finset.univ.val.map g) :
    ∃ e : α ≃ β, ∀ a, g (e a) = f a := by
  classical
  have hcard : ∀ c, Fintype.card {a // f a = c} = Fintype.card {b // g b = c} := by
    intro c
    have hc := congrArg (Multiset.count c) h
    rw [Multiset.count_map, Multiset.count_map] at hc
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simpa [Finset.card, Finset.filter_val, eq_comm] using hc
  exact ⟨Equiv.ofFiberEquiv fun c => Fintype.equivOfCardEq (hcard c),
    Equiv.ofFiberEquiv_map _⟩

/-- Over an algebraically closed field, a semisimple endomorphism of a finite-dimensional
space has a basis of eigenvectors. -/
theorem exists_basis_apply_eq_smul_of_isSemisimple {K : Type u} {V : Type v} [Field K]
    [IsAlgClosed K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {f : Module.End K V} (hf : Module.End.IsSemisimple f) :
    ∃ (b : Module.Basis (Fin (Module.finrank K V)) K V) (μ : Fin (Module.finrank K V) → K),
      ∀ j, f (b j) = μ j • b j := by
  classical
  have hint : DirectSum.IsInternal fun μ : K => Module.End.eigenspace f μ :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (Module.End.eigenspaces_iSupIndep f) (Module.End.IsSemisimple.iSup_eigenspace_eq_top hf)
  let B := hint.collectedBasis fun μ => Module.Basis.ofVectorSpace K (Module.End.eigenspace f μ)
  have : Finite (Σ μ : K, Module.Basis.ofVectorSpaceIndex K (Module.End.eigenspace f μ)) :=
    Module.Finite.finite_basis B
  let := Fintype.ofFinite (Σ μ : K, Module.Basis.ofVectorSpaceIndex K (Module.End.eigenspace f μ))
  let e := Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis B).symm
  refine ⟨B.reindex e, fun j => (e.symm j).1, fun j => ?_⟩
  rw [Module.Basis.reindex_apply]
  exact Module.End.mem_eigenspace_iff.mp (hint.collectedBasis_mem _ (e.symm j))

/-- `∏_i (1 - c_i X)`, with every `c_i` nonzero, has degree the number of factors. -/
theorem natDegree_prod_one_sub_C_mul_X {K : Type u} [Field K] {ι : Type w} [Fintype ι]
    (c : ι → K) (hc : ∀ i, c i ≠ 0) :
    (∏ i, (1 - C (c i) * X)).natDegree = Fintype.card ι := by
  have hlin : ∀ i, (1 - C (c i) * X : K[X]) = C (-c i) * X + C 1 := fun i => by
    rw [C_neg, C_1]
    ring
  have hdeg : ∀ i, (1 - C (c i) * X : K[X]).natDegree = 1 := fun i => by
    rw [hlin]
    exact natDegree_linear (neg_ne_zero.mpr (hc i))
  rw [natDegree_prod _ _ fun i _ h0 => by simpa [h0] using hdeg i]
  simp [hdeg]

end Langlands.LocalFactor

namespace Langlands.Correspondence

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance characterSumConverseFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

variable {F}

/-- The unramified character `w ↦ z ^ deg(w)` is trivial on inertia. -/
theorem localUnramifiedCharacter_eq_one_of_mem_localInertia (z : ℂˣ)
    {w : Weil.Local.localWeilGroup F} (hw : w ∈ Weil.Local.localInertia F) :
    (Weil.Local.localUnramifiedCharacter F z).toMonoidHom w = 1 :=
  Weil.Local.localUnramifiedCharacter_on_inertia F z ⟨w, hw⟩

/-- If inertia acts trivially and `v` is an eigenvector of the geometric Frobenius lift
with eigenvalue `z`, every Weil element `w` acts on `v` by `z ^ deg(w)`. -/
theorem representation_apply_of_isUnramified
    {A : Weil.Local.LocalWeilDeligneRepresentation.{uF, uP} F}
    (hI : ∀ i : Weil.Local.localInertia F, A.representation i = 1) {z : ℂˣ} {v : A}
    (hv : A.representation (Weil.Local.localGeometricFrobenius F) v = (z : ℂ) • v)
    (w : Weil.Local.localWeilGroup F) :
    A.representation w v = (Weil.Local.localUnramifiedCharacter F z w : ℂ) • v := by
  set Φ := Weil.Local.localGeometricFrobenius F
  have hinv : A.representation Φ⁻¹ v = ((z⁻¹ : ℂˣ) : ℂ) • v := by
    have h1 : A.representation Φ⁻¹ (A.representation Φ v) = v :=
      Representation.inv_self_apply _ _ _
    rw [hv, map_smul] at h1
    calc A.representation Φ⁻¹ v
        = ((z⁻¹ : ℂˣ) : ℂ) • ((z : ℂ) • A.representation Φ⁻¹ v) := by
          rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
      _ = ((z⁻¹ : ℂˣ) : ℂ) • v := by rw [h1]
  have hpow : ∀ k : ℤ, A.representation (Φ ^ k) v = ((z ^ k : ℂˣ) : ℂ) • v := by
    intro k
    induction k using Int.induction_on with
    | zero => simp
    | succ k ih =>
      rw [zpow_add_one, map_mul, Module.End.mul_apply, hv, map_smul, ih, smul_smul,
        zpow_add_one z, Units.val_mul, mul_comm]
    | pred k ih =>
      rw [zpow_sub_one, map_mul, Module.End.mul_apply, hinv, map_smul, ih, smul_smul,
        zpow_sub_one z, Units.val_mul, mul_comm]
  set k := Weil.Local.localDegreeInt F w
  have hmem : w * Φ ^ (-k) ∈ Weil.Local.localInertia F := by
    change Weil.Local.localDegree F (w * Φ ^ (-k)) = 1
    rw [map_mul, map_zpow, Weil.Local.localGeometricFrobenius_degree, ← ofAdd_zsmul,
      smul_eq_mul, mul_one, ofAdd_neg]
    change Weil.Local.localDegree F w * (Multiplicative.ofAdd (Weil.Local.localDegree F w).toAdd)⁻¹ = 1
    rw [ofAdd_toAdd, mul_inv_cancel]
  have h1 : A.representation (w * Φ ^ (-k)) = 1 := hI ⟨_, hmem⟩
  have hw : w = w * Φ ^ (-k) * Φ ^ k := by group
  calc A.representation w v = A.representation (w * Φ ^ (-k) * Φ ^ k) v := by rw [← hw]
    _ = ((z ^ k : ℂˣ) : ℂ) • v := by
      rw [map_mul, Module.End.mul_apply, hpow, map_smul, h1, Module.End.one_apply]
    _ = (Weil.Local.localUnramifiedCharacter F z w : ℂ) • v := rfl

/-- A pair with zero monodromy and trivial inertia action, with a basis of eigenvectors
of the geometric Frobenius lift with eigenvalues `c i`, is equivalent to the character
sum of the unramified characters `w ↦ c_i ^ deg(w)`. -/
theorem nonempty_equiv_characterSumPair
    {A : Weil.Local.LocalWeilDeligneRepresentation.{uF, uP} F} (hN : A.monodromy = 0)
    (hI : ∀ i : Weil.Local.localInertia F, A.representation i = 1) {n : ℕ} (c : Fin n → ℂˣ)
    (b : Module.Basis (Fin n) ℂ A)
    (hb : ∀ i, A.representation (Weil.Local.localGeometricFrobenius F) (b i) = (c i : ℂ) • b i) :
    Nonempty (WeilDeligneRepresentation.Equiv
      (characterSumPair.{uF, uP} F fun i =>
        (Weil.Local.localUnramifiedCharacter F (c i)).toMonoidHom) A) := by
  classical
  let ψ : Fin n → Weil.Local.localWeilGroup F →* ℂˣ := fun i =>
    (Weil.Local.localUnramifiedCharacter F (c i)).toMonoidHom
  let E : (DirectSum (Fin n) fun _ => ULift.{uP} ℂ) ≃ₗ[ℂ] (Fin n →₀ ℂ) :=
    (DFinsupp.mapRange.linearEquiv fun _ => ULift.moduleEquiv).trans
      (finsuppLequivDFinsupp ℂ).symm
  let b₀ : Module.Basis (Fin n) ℂ (characterSumPair.{uF, uP} F ψ) := Module.Basis.ofRepr E
  have hrepr : ∀ g v j, b₀.repr ((characterSumPair.{uF, uP} F ψ).representation g v) j =
      (ψ j g : ℂ) * b₀.repr v j := fun _ _ _ => rfl
  have hb₀ : ∀ g i, (characterSumPair.{uF, uP} F ψ).representation g (b₀ i) =
      (ψ i g : ℂ) • b₀ i := by
    intro g i
    apply b₀.repr.injective
    ext j
    rw [hrepr, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, smul_eq_mul,
      Finsupp.single_apply]
    split_ifs with hij
    · subst hij
      rfl
    · simp
  let L := b₀.equiv b (Equiv.refl _)
  refine ⟨⟨Representation.Equiv.mk L fun g => b₀.ext fun i => ?_, ?_⟩⟩
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, hb₀, map_smul]
    change (ψ i g : ℂ) • L (b₀ i) = A.representation g (L (b₀ i))
    rw [Module.Basis.equiv_apply, Equiv.refl_apply,
      representation_apply_of_isUnramified hI (hb i)]
    rfl
  · apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, characterSumPair_monodromy, hN, LinearMap.zero_apply,
      map_zero]

/-- The character-sum class does not depend on the proof that its characters are trivial
on inertia. -/
theorem characterSumClass_congr {r : ℕ}
    {ψ ψ' : Fin (r + 1) → Weil.Local.localWeilGroup F →* ℂˣ} (h : ψ = ψ')
    (hψ : ∀ i, ∀ w ∈ Weil.Local.localInertia F, ψ i w = 1)
    (hψ' : ∀ i, ∀ w ∈ Weil.Local.localInertia F, ψ' i w = 1) :
    characterSumClass.{uF, uP} ψ hψ = characterSumClass.{uF, uP} ψ' hψ' := by
  subst h
  rfl

variable (F) in
/-- The unramified parameter class with geometric Frobenius eigenvalues `c_i`: the
character-sum class of the unramified characters `w ↦ c_i ^ deg(w)`. -/
def unramifiedCharacterSumClass {r : ℕ} (c : Fin (r + 1) → ℂˣ) :
    WeilDeligneClass.{uF, uP} F r.succPNat :=
  characterSumClass.{uF, uP}
    (fun i => (Weil.Local.localUnramifiedCharacter F (c i)).toMonoidHom)
    (fun i _ hw => localUnramifiedCharacter_eq_one_of_mem_localInertia (c i) hw)

/-- An unramified parameter class whose Weil–Deligne Euler polynomial at the geometric
Frobenius lift is `∏_i (1 - c_i X)` is the character-sum class of the unramified
characters `w ↦ c_i ^ deg(w)`. -/
theorem eq_unramifiedCharacterSumClass_of_eulerPolynomial {r : ℕ}
    {D : WeilDeligneClass.{uF, uP} F r.succPNat} (hD : IsUnramifiedParameterClass F D)
    (c : Fin (r + 1) → ℂˣ) {A : Weil.Local.LocalWeilDeligneRepresentation.{uF, uP} F}
    (hA : WeilDeligneRepresentation.classOf A = parameterForget F D)
    (hE : LocalFactor.WeilDeligne.eulerPolynomial A (Weil.Local.localInertia F)
        (Weil.Local.localGeometricFrobenius F) = ∏ i, (1 - C (c i : ℂ) * X)) :
    D = unramifiedCharacterSumClass.{uF, uP} F c := by
  classical
  set Φ := Weil.Local.localGeometricFrobenius F
  obtain ⟨d, hd⟩ := D
  obtain ⟨a, rfl⟩ := Quotient.exists_rep d
  have hfa : parameterForget F ⟨Quotient.mk _ a, hd⟩ =
      WeilDeligneRepresentation.classOf a.val := rfl
  obtain ⟨B, hB, hBc⟩ := hD
  rw [hfa] at hBc hA
  obtain ⟨fB⟩ := (WeilDeligneRepresentation.classOf_eq_iff _ _).mp hBc
  obtain ⟨fA⟩ := (WeilDeligneRepresentation.classOf_eq_iff _ _).mp hA
  have hN : a.val.monodromy = 0 :=
    WeilDeligneRepresentation.monodromy_eq_zero_of_equiv fB rfl
  have hI : ∀ i : Weil.Local.localInertia F, a.val.representation i = 1 :=
    FiniteRepresentation.isUnramified_of_equiv fB.representationEquiv hB
  have hS : Module.End.IsSemisimple (a.val.representation Φ) := by
    refine a.property.2 Φ ?_
    change Multiplicative.toAdd (Weil.Local.localDegree F Φ) ≠ 0
    rw [Weil.Local.localGeometricFrobenius_degree]
    simp
  obtain ⟨b, μ, hb⟩ := LocalFactor.exists_basis_apply_eq_smul_of_isSemisimple hS
  have hE' : LocalFactor.eulerPolynomial (a.val.representation Φ) =
      ∏ i, (1 - C (c i : ℂ) * X) := by
    rw [← LocalFactor.WeilDeligne.eulerPolynomial_eq_of_monodromy_eq_zero _ _ hN hI,
      ← LocalFactor.WeilDeligne.eulerPolynomial_eq_of_equiv _ fA, hE]
  have hμ := LocalFactor.eulerPolynomial_eq_prod_of_apply_basis b _ μ hb
  have hμ0 : ∀ j, μ j ≠ 0 := by
    intro j h0
    have hj := hb j
    rw [h0, zero_smul] at hj
    apply b.ne_zero j
    have := congrArg (a.val.representation Φ⁻¹) hj
    rwa [Representation.inv_self_apply, map_zero] at this
  have hroots := congrArg Polynomial.roots (hμ.symm.trans hE')
  rw [LocalFactor.roots_prod_one_sub_C_mul_X _ hμ0,
    LocalFactor.roots_prod_one_sub_C_mul_X _ fun i => (c i).ne_zero] at hroots
  obtain ⟨e, he⟩ := LocalFactor.exists_equiv_of_map_univ_eq hroots
  have hb' : ∀ i, a.val.representation Φ (b.reindex e i) = (c i : ℂ) • b.reindex e i := by
    intro i
    have hi := he (e.symm i)
    rw [e.apply_symm_apply, inv_inj] at hi
    rw [Module.Basis.reindex_apply, hb, hi]
  obtain ⟨f⟩ := nonempty_equiv_characterSumPair hN hI c (b.reindex e) hb'
  apply parameterForget_injective
  rw [hfa, unramifiedCharacterSumClass, parameterForget_characterSumClass]
  exact ((WeilDeligneRepresentation.classOf_eq_iff _ _).mpr ⟨f⟩).symm

/-- For a geometric candidate and unramified quasi-characters `χ_i`, a parameter class
is the character-sum parameter of `χ` exactly when it is unramified and the
Weil–Deligne Euler polynomial at the geometric Frobenius lift is `∏_i (1 - χ_i(ϖ) X)`. -/
theorem isCharacterSumParameter_iff_eulerPolynomial {e : ReciprocityCandidate F}
    (he : IsGeometricReciprocity F e) {r : ℕ} {χ : Fin (r + 1) → QuasiCharacter F}
    (hχ : ∀ i, F.canonicalTopologicalData.IsUnramifiedCharacter (χ i).toMonoidHom)
    {D : WeilDeligneClass.{uF, uP} F r.succPNat}
    {A : Weil.Local.LocalWeilDeligneRepresentation.{uF, uP} F}
    (hA : WeilDeligneRepresentation.classOf A = parameterForget F D) :
    IsCharacterSumParameter F e χ D ↔
      IsUnramifiedParameterClass F D ∧
        LocalFactor.WeilDeligne.eulerPolynomial A (Weil.Local.localInertia F)
            (Weil.Local.localGeometricFrobenius F) =
          ∏ i, (1 - C (χ i F.canonicalTopologicalData.uniformizerUnit : ℂ) * X) := by
  constructor
  · intro hD
    exact ⟨isUnramifiedParameterClass_of_isCharacterSumParameter_of_isGeometricReciprocity
      he hχ hD, eulerPolynomial_of_isCharacterSumParameter_of_isGeometricReciprocity he hχ hD hA⟩
  · rintro ⟨hD, hE⟩
    have hψ : (fun i => weilCharacter F e (χ i)) = fun i =>
        (Weil.Local.localUnramifiedCharacter F
          (χ i F.canonicalTopologicalData.uniformizerUnit)).toMonoidHom :=
      funext fun i => weilCharacter_eq_localUnramifiedCharacter F he (hχ i)
    rw [eq_unramifiedCharacterSumClass_of_eulerPolynomial hD
        (fun i => χ i F.canonicalTopologicalData.uniformizerUnit) hA hE,
      unramifiedCharacterSumClass, ← characterSumClass_congr hψ
        (fun i _ hw => weilCharacter_eq_one_of_mem_localInertia F he (hχ i) hw)]
    exact isCharacterSumParameter_characterSumClass e χ _

/-! ### The standard Euler polynomial -/

/-- The standard Euler polynomial of a parameter class is the Weil–Deligne Euler
polynomial, at the geometric Frobenius lift, of any representative of its underlying
pair class. -/
theorem parameterEulerPolynomial_eq_of_classOf {n : ℕ+} {D : WeilDeligneClass.{uF, uP} F n}
    {A : Weil.Local.LocalWeilDeligneRepresentation.{uF, uP} F}
    (hA : WeilDeligneRepresentation.classOf A = parameterForget F D) :
    parameterEulerPolynomial F D =
      LocalFactor.WeilDeligne.eulerPolynomial A (Weil.Local.localInertia F)
        (Weil.Local.localGeometricFrobenius F) := by
  rw [parameterEulerPolynomial, ← hA, LocalFactor.WeilDeligne.eulerPolynomialClass_classOf]

/-- The standard Euler polynomial of the unramified class with geometric Frobenius
eigenvalues `c_i` is `∏_i (1 - c_i X)`. -/
theorem parameterEulerPolynomial_unramifiedCharacterSumClass {r : ℕ} (c : Fin (r + 1) → ℂˣ) :
    parameterEulerPolynomial F (unramifiedCharacterSumClass.{uF, uP} F c) =
      ∏ i, (1 - C (c i : ℂ) * X) := by
  rw [unramifiedCharacterSumClass,
    parameterEulerPolynomial_eq_of_classOf (parameterForget_characterSumClass _ _).symm,
    eulerPolynomial_characterSumPair
      (fun i _ hw => localUnramifiedCharacter_eq_one_of_mem_localInertia (c i) hw)]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h : (Weil.Local.localUnramifiedCharacter F (c i)).toMonoidHom
      (Weil.Local.localGeometricFrobenius F) = c i :=
    Weil.Local.localUnramifiedCharacter_geometricFrobenius F (c i)
  rw [h]

/-- A parameter class of rank `r + 1` whose standard Euler polynomial is
`∏_i (1 - c_i X)`, with `r + 1` units `c_i`, is unramified. -/
theorem isUnramifiedParameterClass_of_parameterEulerPolynomial_eq {r : ℕ}
    {D : WeilDeligneClass.{uF, uP} F r.succPNat} (c : Fin (r + 1) → ℂˣ)
    (hE : parameterEulerPolynomial F D = ∏ i, (1 - C (c i : ℂ) * X)) :
    IsUnramifiedParameterClass F D := by
  refine (parameterEulerPolynomial_natDegree_eq_rank_iff F D).mp ?_
  rw [hE, LocalFactor.natDegree_prod_one_sub_C_mul_X _ fun i => (c i).ne_zero,
    Fintype.card_fin, Nat.succPNat_coe, Nat.succ_eq_add_one]

/-- The unramified class with geometric Frobenius eigenvalues `c_i` is an unramified
parameter class. -/
theorem isUnramifiedParameterClass_unramifiedCharacterSumClass {r : ℕ}
    (c : Fin (r + 1) → ℂˣ) :
    IsUnramifiedParameterClass F (unramifiedCharacterSumClass.{uF, uP} F c) :=
  isUnramifiedParameterClass_of_parameterEulerPolynomial_eq c
    (parameterEulerPolynomial_unramifiedCharacterSumClass c)

/-- A parameter class of rank `r + 1` has standard Euler polynomial `∏_i (1 - c_i X)`
exactly when it is the unramified class with geometric Frobenius eigenvalues `c_i`. -/
theorem parameterEulerPolynomial_eq_prod_iff {r : ℕ}
    {D : WeilDeligneClass.{uF, uP} F r.succPNat} (c : Fin (r + 1) → ℂˣ) :
    parameterEulerPolynomial F D = ∏ i, (1 - C (c i : ℂ) * X) ↔
      D = unramifiedCharacterSumClass.{uF, uP} F c := by
  refine ⟨fun hE => ?_, fun hD => hD ▸ parameterEulerPolynomial_unramifiedCharacterSumClass c⟩
  have hA : WeilDeligneRepresentation.classOf (Quotient.out (parameterForget F D)) =
      parameterForget F D := Quotient.out_eq _
  exact eq_unramifiedCharacterSumClass_of_eulerPolynomial
    (isUnramifiedParameterClass_of_parameterEulerPolynomial_eq c hE) c hA
    ((parameterEulerPolynomial_eq_of_classOf hA).symm.trans hE)

/-- For a geometric candidate and unramified quasi-characters `χ_i`, the standard Euler
polynomial of the character-sum parameter of `χ` is `∏_i (1 - χ_i(ϖ) X)`. -/
theorem parameterEulerPolynomial_of_isCharacterSumParameter {e : ReciprocityCandidate F}
    (he : IsGeometricReciprocity F e) {r : ℕ} {χ : Fin (r + 1) → QuasiCharacter F}
    (hχ : ∀ i, F.canonicalTopologicalData.IsUnramifiedCharacter (χ i).toMonoidHom)
    {D : WeilDeligneClass.{uF, uP} F r.succPNat} (hD : IsCharacterSumParameter F e χ D) :
    parameterEulerPolynomial F D =
      ∏ i, (1 - C (χ i F.canonicalTopologicalData.uniformizerUnit : ℂ) * X) := by
  have hA : WeilDeligneRepresentation.classOf (Quotient.out (parameterForget F D)) =
      parameterForget F D := Quotient.out_eq _
  rw [parameterEulerPolynomial_eq_of_classOf hA]
  exact eulerPolynomial_of_isCharacterSumParameter_of_isGeometricReciprocity he hχ hD hA

/-- For a geometric candidate and unramified quasi-characters `χ_i`, a parameter class
is the character-sum parameter of `χ` exactly when its standard Euler polynomial is
`∏_i (1 - χ_i(ϖ) X)`. -/
theorem isCharacterSumParameter_iff_parameterEulerPolynomial {e : ReciprocityCandidate F}
    (he : IsGeometricReciprocity F e) {r : ℕ} {χ : Fin (r + 1) → QuasiCharacter F}
    (hχ : ∀ i, F.canonicalTopologicalData.IsUnramifiedCharacter (χ i).toMonoidHom)
    {D : WeilDeligneClass.{uF, uP} F r.succPNat} :
    IsCharacterSumParameter F e χ D ↔
      parameterEulerPolynomial F D =
        ∏ i, (1 - C (χ i F.canonicalTopologicalData.uniformizerUnit : ℂ) * X) := by
  refine ⟨parameterEulerPolynomial_of_isCharacterSumParameter he hχ, fun hE => ?_⟩
  have hA : WeilDeligneRepresentation.classOf (Quotient.out (parameterForget F D)) =
      parameterForget F D := Quotient.out_eq _
  refine (isCharacterSumParameter_iff_eulerPolynomial he hχ hA).mpr
    ⟨isUnramifiedParameterClass_of_parameterEulerPolynomial_eq
      (fun i => χ i F.canonicalTopologicalData.uniformizerUnit) hE, ?_⟩
  rw [← parameterEulerPolynomial_eq_of_classOf hA, hE]

end Langlands.Correspondence
