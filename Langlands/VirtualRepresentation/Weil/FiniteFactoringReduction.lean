import Langlands.VirtualRepresentation.Weil.Twist
import Langlands.VirtualRepresentation.Weil.Local
import Langlands.Weil.Local.IrreducibleReductionProof
import Langlands.Weil.Local.GaloisCorrectionProof
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Unramified twists of finite-factoring unitary Weil classes

Every continuous irreducible class of the local Weil group of a p-adic field
`K` is an unramified twist of a unitary class factoring through a finite
quotient of the absolute Galois group of `K`. When the class is itself unitary,
the twisting parameter has modulus one.
-/

noncomputable section

namespace Langlands.FiniteRepresentation

universe uG uV

open scoped ComplexConjugate

variable {G : Type uG} [Group G]

/-- The coordinate inner product of a finite basis, averaged over a finite set
of endomorphisms. -/
private def averagedInner (A : FiniteRepresentation.{0, uG, uV} ℂ G)
    (S : Finset (Module.End ℂ A)) (v w : A) : ℂ :=
  ∑ T ∈ S, ∑ i, conj ((Module.finBasis ℂ A).equivFun (T v) i) *
    (Module.finBasis ℂ A).equivFun (T w) i

/-- A representation with finite image preserves a positive definite Hermitian
form: average a coordinate inner product over the image. -/
theorem isUnitary_of_hasFiniteImage (A : FiniteRepresentation.{0, uG, uV} ℂ G)
    (h : A.HasFiniteImage) : A.IsUnitary := by
  classical
  have h' : (Set.range A.representation).Finite := h
  set S := h'.toFinset with hS
  set b := Module.finBasis ℂ A
  have hmemS : ∀ T, T ∈ S ↔ ∃ g, A.representation g = T := by
    intro T
    rw [hS, Set.Finite.mem_toFinset]
    rfl
  have hone : (1 : Module.End ℂ A) ∈ S := (hmemS 1).mpr ⟨1, map_one _⟩
  let core : InnerProductSpace.Core ℂ A :=
    { inner := averagedInner A S
      conj_inner_symm := by
        intro v w
        simp only [averagedInner, map_sum, map_mul, Complex.conj_conj]
        refine Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun i _ => ?_
        ring
      re_inner_nonneg := by
        intro v
        simp only [averagedInner, map_sum]
        refine Finset.sum_nonneg fun T _ => Finset.sum_nonneg fun i _ => ?_
        rw [mul_comm, Complex.mul_conj]
        exact_mod_cast Complex.normSq_nonneg _
      add_left := by
        intro v w u
        simp only [averagedInner, map_add, Pi.add_apply, map_add, add_mul,
          Finset.sum_add_distrib]
      smul_left := by
        intro v w r
        simp only [averagedInner, map_smul, Pi.smul_apply, smul_eq_mul, map_mul,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun i _ => ?_
        ring
      definite := by
        intro v hv
        have hre : ∀ T ∈ S, 0 ≤ (∑ i, conj (b.equivFun (T v) i) * b.equivFun (T v) i).re := by
          intro T _
          simp only [Complex.re_sum]
          refine Finset.sum_nonneg fun i _ => ?_
          rw [mul_comm, Complex.mul_conj]
          exact_mod_cast Complex.normSq_nonneg _
        have hsum : (∑ T ∈ S, (∑ i, conj (b.equivFun (T v) i) * b.equivFun (T v) i).re) = 0 := by
          have := congrArg Complex.re hv
          simpa [averagedInner, Complex.re_sum] using this
        have h1 := (Finset.sum_eq_zero_iff_of_nonneg hre).mp hsum 1 hone
        simp only [Module.End.one_apply, Complex.re_sum] at h1
        have hterm : ∀ i, (conj (b.equivFun v i) * b.equivFun v i).re = 0 := by
          intro i
          have hnn : ∀ j ∈ Finset.univ,
              0 ≤ (conj (b.equivFun v j) * b.equivFun v j).re := by
            intro j _
            rw [mul_comm, Complex.mul_conj]
            exact_mod_cast Complex.normSq_nonneg _
          exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h1 i (Finset.mem_univ i)
        have hzero : b.equivFun v = 0 := by
          funext i
          have := hterm i
          rw [mul_comm, Complex.mul_conj] at this
          simpa [Complex.normSq_eq_zero] using this
        exact b.equivFun.injective (by rw [hzero, map_zero]) }
  refine ⟨core, ?_⟩
  intro g v w
  change averagedInner A S (A.representation g v) (A.representation g w) =
    averagedInner A S v w
  unfold averagedInner
  refine Finset.sum_nbij' (fun T => T * A.representation g)
    (fun T => T * A.representation g⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro T hT
    obtain ⟨k, rfl⟩ := (hmemS T).mp hT
    exact (hmemS _).mpr ⟨k * g, map_mul _ _ _⟩
  · intro T hT
    obtain ⟨k, rfl⟩ := (hmemS T).mp hT
    exact (hmemS _).mpr ⟨k * g⁻¹, map_mul _ _ _⟩
  · intro T _
    simp [mul_assoc, ← map_mul]
  · intro T _
    simp [mul_assoc, ← map_mul]
  · intro T _
    rfl

/-- If `A` is equivalent to the twist of `B` by `χ` and both preserve positive
definite Hermitian forms, then `χ` takes values of modulus one: an eigenvalue `μ`
of `B g` and the eigenvalue `χ g μ` of `A g` both have modulus one. -/
theorem norm_eq_one_of_equiv_twist {A : FiniteRepresentation.{0, uG, uV} ℂ G}
    {B : FiniteRepresentation.{0, uG, uV} ℂ G} (hA : A.IsUnitary) (hB : B.IsUnitary)
    (hrank : 0 < B.rank) (χ : G →* ℂˣ) (e : Equiv A (twist χ B)) (g : G) :
    ‖(χ g : ℂ)‖ = 1 := by
  obtain ⟨hA, hAinv⟩ := hA
  obtain ⟨hB, hBinv⟩ := hB
  have : Nontrivial B := Module.nontrivial_of_finrank_pos hrank
  -- the inner products are sesquilinear
  have hsmul : ∀ (h : InnerProductSpace.Core ℂ A) (r : ℂ) (v : A),
      h.inner (r • v) (r • v) = (Complex.normSq r : ℂ) * h.inner v v := by
    intro h r v
    have h1 := h.smul_left v (r • v) r
    have h2 : h.inner v (r • v) = r * h.inner v v := by
      rw [← h.conj_inner_symm, h.smul_left, map_mul, Complex.conj_conj, h.conj_inner_symm]
    rw [h1, h2, ← mul_assoc, mul_comm (starRingEnd ℂ r) r, Complex.mul_conj]
  have hsmulB : ∀ (r : ℂ) (v : B),
      hB.inner (r • v) (r • v) = (Complex.normSq r : ℂ) * hB.inner v v := by
    intro r v
    have h1 := hB.smul_left v (r • v) r
    have h2 : hB.inner v (r • v) = r * hB.inner v v := by
      rw [← hB.conj_inner_symm, hB.smul_left, map_mul, Complex.conj_conj, hB.conj_inner_symm]
    rw [h1, h2, ← mul_assoc, mul_comm (starRingEnd ℂ r) r, Complex.mul_conj]
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (B.representation g)
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hBv : B.representation g v = μ • v := hv.apply_eq_smul
  have hv0 : v ≠ 0 := hv.2
  have hBvv : hB.inner v v ≠ 0 := fun h => hv0 (hB.definite v h)
  have hμ1 : Complex.normSq μ = 1 := by
    have := hBinv g v v
    rw [hBv, hsmulB] at this
    have h' : ((Complex.normSq μ : ℂ) - 1) * hB.inner v v = 0 := by
      rw [sub_mul, this, one_mul, sub_self]
    rcases mul_eq_zero.mp h' with h0 | h0
    · exact_mod_cast sub_eq_zero.mp h0
    · exact absurd h0 hBvv
  set u : A := e.symm v
  have heu : e u = v := e.apply_symm_apply v
  have hu0 : u ≠ 0 := by
    intro h
    apply hv0
    rw [← heu, h]
    exact map_zero e
  have hint : ∀ w : A, e (A.representation g w) = (twist χ B).representation g (e w) :=
    fun w => Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g w
  have hAu : A.representation g u = ((χ g : ℂ) * μ) • u := by
    apply EquivLike.injective e
    rw [hint, map_smul, heu]
    change ((χ g : ℂ) • B.representation g) v = ((χ g : ℂ) * μ) • v
    rw [LinearMap.smul_apply, hBv, smul_smul]
  have hAuu : hA.inner u u ≠ 0 := fun h => hu0 (hA.definite u h)
  have hprod : Complex.normSq ((χ g : ℂ) * μ) = 1 := by
    have := hAinv g u u
    rw [hAu, hsmul] at this
    have h' : ((Complex.normSq ((χ g : ℂ) * μ) : ℂ) - 1) * hA.inner u u = 0 := by
      rw [sub_mul, this, one_mul, sub_self]
    rcases mul_eq_zero.mp h' with h0 | h0
    · exact_mod_cast sub_eq_zero.mp h0
    · exact absurd h0 hAuu
  rw [Complex.normSq_mul, hμ1, mul_one] at hprod
  rw [Complex.norm_def, hprod, Real.sqrt_one]

end Langlands.FiniteRepresentation

namespace Langlands.VirtualRepresentation.Weil

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Classes of equal rank with equal underlying representation classes are equal. -/
theorem IrreducibleBasis.ext_underlyingClass {b b' : IrreducibleBasis.{uG, uV} G}
    (hrank : b.1 = b'.1) (hclass : underlyingClass G b = underlyingClass G b') : b = b' := by
  obtain ⟨n, c, hc⟩ := b
  obtain ⟨n', c', hc'⟩ := b'
  simp only at hrank
  subst hrank
  have : c = c' := FiniteRepresentation.forgetPropertyClass_injective _ hclass
  subst this
  rfl

/-- The underlying class of an irreducible basis class has its rank. -/
theorem classRank_underlyingClass (b : IrreducibleBasis.{uG, uV} G) :
    FiniteRepresentation.classRank (underlyingClass G b) = (b.1 : ℕ) :=
  b.2.property

/-- If an irreducible class and its twist by `χ` are both unitary, then `χ` takes
values of modulus one. -/
theorem norm_eq_one_of_isUnitaryClass_twist (χ : G →ₜ* ℂˣ) {b : IrreducibleBasis.{uG, uV} G}
    (hb : IsUnitaryClass G b) (hχb : IsUnitaryClass G (twistBasisEquiv χ b)) (g : G) :
    ‖(χ g : ℂ)‖ = 1 := by
  obtain ⟨A, hA, hAb⟩ := hb
  obtain ⟨B, hB, hBb⟩ := hχb
  rw [underlyingClass_twistBasisEquiv, ← hAb, FiniteRepresentation.twistClass_classOf] at hBb
  obtain ⟨e⟩ := (FiniteRepresentation.classOf_eq_iff _ _).mp hBb
  have hrank : 0 < A.rank := by
    have h := classRank_underlyingClass b
    rw [← hAb, FiniteRepresentation.classRank_classOf] at h
    rw [h]
    exact b.1.pos
  exact FiniteRepresentation.norm_eq_one_of_equiv_twist hB hA hrank χ.toMonoidHom e g

end Langlands.VirtualRepresentation.Weil

namespace Langlands.VirtualRepresentation.LocalWeil

universe uK uW

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

/-- A local Weil representation of Galois type factors through a finite quotient
of the absolute Galois group: its continuous extension has finite range, and the
quotient by the kernel of the extension is finite. -/
theorem exists_finiteQuotient_of_isLocalGaloisType
    (B : Weil.Local.LocalWeilRepresentation.{uK, uW} K)
    (hB : Weil.Local.IsLocalGaloisType K B) :
    ∃ (Q : Type uK) (_ : Group Q) (_ : Finite Q)
      (q : Field.absoluteGaloisGroup K.Carrier →* Q) (ρ : Representation ℂ Q B),
      ρ.comp (q.comp (Weil.Local.localProjection K).toMonoidHom) = B.representation := by
  obtain ⟨τ, hτc, hτr⟩ := hB
  have : CharZero K.Carrier :=
    charZero_of_injective_algebraMap (algebraMap (Padic p) K.Carrier).injective
  have : IsGalois K.Carrier (AlgebraicClosure K.Carrier) := ⟨⟩
  let := LocalClassField.absoluteGaloisNonarchimedean K.Carrier
  let : CompactSpace (Field.absoluteGaloisGroup K.Carrier) :=
    inferInstanceAs (CompactSpace Gal(AlgebraicClosure K.Carrier/K.Carrier))
  let := B.carrierNormedAddCommGroup
  let := B.carrierNormedSpace
  have hfin : (Set.range τ).Finite :=
    Weil.continuous_compact_nonarchimedean_representation_finite_range
      (Field.absoluteGaloisGroup K.Carrier) B τ
      ((FiniteRepresentation.isContinuous_of_iff τ).mp hτc)
  let φ := τ.toHomUnits
  let ρ : Representation ℂ (Field.absoluteGaloisGroup K.Carrier ⧸ φ.ker) B :=
    (Units.coeHom (Module.End ℂ B)).comp (QuotientGroup.kerLift φ)
  have hρ : ∀ g, ρ (QuotientGroup.mk g) = τ g := fun _ => rfl
  have hρinj : Function.Injective ρ := fun x y h =>
    QuotientGroup.kerLift_injective φ (Units.ext h)
  have hρrange : Set.range ρ ⊆ Set.range τ := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨g, (hρ g).symm⟩
  have : Finite (Field.absoluteGaloisGroup K.Carrier ⧸ φ.ker) := by
    have : Finite (Set.range ρ) := (hfin.subset hρrange).to_subtype
    exact Finite.of_injective_finite_range hρinj
  refine ⟨_, inferInstance, this, QuotientGroup.mk' φ.ker, ρ, ?_⟩
  rw [← hτr]
  rfl

/-- Every continuous irreducible class of the local Weil group is the twist by
the unramified character with value `z` at geometric Frobenius of a unitary
class factoring through a finite quotient of the absolute Galois group. -/
theorem exists_unramifiedTwist_finiteFactoring (b : Basis.{uK, uW} K) :
    ∃ (z : ℂˣ) (b₀ : UnitaryBasis.{uK, uW} K) (Q : Type uK) (_ : Group Q) (_ : Finite Q)
      (q : Field.absoluteGaloisGroup K.Carrier →* Q),
      generator b₀ ∈ unitaryFiniteFactoringSupported.{uK, uW, uK} K q ∧
      b₀.val = Weil.twistBasisEquiv (Weil.Local.localUnramifiedCharacter K z⁻¹) b := by
  obtain ⟨n, c, hc⟩ := b
  obtain ⟨⟨A, hAc, hAi⟩, rfl⟩ := Quotient.exists_rep c
  have hArank : A.rank = n := hc
  obtain ⟨⟨z, B, hBc, hBi, hBf, hBg, ⟨e⟩⟩, -⟩ :=
    Weil.Local.localWeilIrreducibleReductionFor.{uK, uW} K A hAc hAi
  have hBrank : B.rank = n := (FiniteRepresentation.rank_eq_of_equiv e).symm.trans hArank
  have hBu : B.IsUnitary := FiniteRepresentation.isUnitary_of_hasFiniteImage B hBf
  let b₀ : UnitaryBasis.{uK, uW} K := unitaryBasisClass B hBc hBi hBu n hBrank
  obtain ⟨Q, _, _, q, ρ, hρ⟩ := exists_finiteQuotient_of_isLocalGaloisType K B hBg
  refine ⟨z, b₀, Q, inferInstance, inferInstance, q, ?_, ?_⟩
  · refine Finsupp.single_mem_supported ℤ _ ?_
    refine ⟨FiniteRepresentation.of ρ, ?_⟩
    change FiniteRepresentation.classOf
        (FiniteRepresentation.of (ρ.comp (q.comp (Weil.Local.localProjection K).toMonoidHom))) =
      FiniteRepresentation.classOf B
    rw [hρ]
    exact (FiniteRepresentation.classOf_eq_iff _ _).mpr ⟨Representation.Equiv.refl _⟩
  · apply Weil.IrreducibleBasis.ext_underlyingClass
    · rfl
    · rw [Weil.underlyingClass_twistBasisEquiv]
      change FiniteRepresentation.classOf B =
        FiniteRepresentation.twistClass _ (FiniteRepresentation.classOf A)
      have hA : FiniteRepresentation.classOf A = FiniteRepresentation.classOf
          (FiniteRepresentation.twist (Weil.Local.localUnramifiedCharacter K z).toMonoidHom B) :=
        (FiniteRepresentation.classOf_eq_iff _ _).mpr ⟨e⟩
      have hinv : (Weil.Local.localUnramifiedCharacter K z⁻¹).toMonoidHom =
          ((Weil.Local.localUnramifiedCharacter K z).toMonoidHom)⁻¹ := by
        ext w
        simp [Weil.Local.localUnramifiedCharacter]
      rw [hA, ← FiniteRepresentation.twistClass_classOf, hinv,
        FiniteRepresentation.twistClass_inv_twistClass]

/-- In a decomposition of a unitary class as an unramified twist of a unitary
class, the twisting parameter has modulus one. -/
theorem norm_eq_one_of_isUnitaryClass {b : Basis.{uK, uW} K}
    (hb : Weil.IsUnitaryClass _ b) {z : ℂˣ} {b₀ : UnitaryBasis.{uK, uW} K}
    (hb₀ : b₀.val = Weil.twistBasisEquiv (Weil.Local.localUnramifiedCharacter K z⁻¹) b) :
    ‖(z : ℂ)‖ = 1 := by
  have h := Weil.norm_eq_one_of_isUnitaryClass_twist
    (Weil.Local.localUnramifiedCharacter K z⁻¹) hb (hb₀ ▸ b₀.property)
    (Weil.Local.localGeometricFrobenius K)
  have hval : (Weil.Local.localUnramifiedCharacter K z⁻¹ (Weil.Local.localGeometricFrobenius K))
      = z⁻¹ :=
    Weil.Local.unramifiedCharacter_degree_one _ _ (Weil.Local.localGeometricFrobenius_degree K)
  rw [hval, Units.val_inv_eq_inv_val, norm_inv, inv_eq_one] at h
  exact h

end Langlands.VirtualRepresentation.LocalWeil

namespace Langlands.VirtualRepresentation.LocalWeil

universe uK uW

/-- Every continuous irreducible class of the local Weil group of a p-adic field
is the twist, by the unramified character with value `z` at geometric
Frobenius, of a unitary class factoring through a finite quotient of the
absolute Galois group; when the class is unitary, `‖z‖ = 1`. -/
def UnramifiedTwistFiniteFactoringStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (b : Basis.{uK, uW} K),
    ∃ (z : ℂˣ) (b₀ : UnitaryBasis.{uK, uW} K) (Q : Type uK) (_ : Group Q) (_ : Finite Q)
      (q : Field.absoluteGaloisGroup K.Carrier →* Q),
      generator b₀ ∈ unitaryFiniteFactoringSupported.{uK, uW, uK} K q ∧
      Weil.twistBasisEquiv (Weil.Local.localUnramifiedCharacter K z) b₀.val = b ∧
      (Weil.IsUnitaryClass _ b → ‖(z : ℂ)‖ = 1)

theorem unramifiedTwistFiniteFactoring :
    UnramifiedTwistFiniteFactoringStatement.{uK, uW} := by
  intro p _ K b
  obtain ⟨z, b₀, Q, _, _, q, hq, hb₀⟩ := exists_unramifiedTwist_finiteFactoring K b
  refine ⟨z, b₀, Q, inferInstance, inferInstance, q, hq, ?_,
    fun hb => norm_eq_one_of_isUnitaryClass K hb hb₀⟩
  rw [hb₀, ← Equiv.trans_apply, Weil.twistBasisEquiv_mul]
  have : Weil.Local.localUnramifiedCharacter K z * Weil.Local.localUnramifiedCharacter K z⁻¹ = 1 := by
    ext w
    simp [Weil.Local.localUnramifiedCharacter]
  rw [this, Weil.twistBasisEquiv_one]
  rfl

end Langlands.VirtualRepresentation.LocalWeil
