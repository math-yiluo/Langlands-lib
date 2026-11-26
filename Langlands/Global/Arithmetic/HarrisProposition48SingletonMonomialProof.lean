import Langlands.LocalFactor.BrauerKernel.PlaceNorm
import Langlands.Global.Arithmetic.HarrisProposition48SingletonMonomialStatement
import Langlands.Global.HeckeConjugateInverseUnitary
import Langlands.Global.IdeleNormAbsoluteValue
import Langlands.Global.Factors.RelativeWeilAssemblyCharacters
import Langlands.Automorphic.InducedReciprocityIrreducible
import Langlands.Galois.ClosureMackeyGalois
import Langlands.Galois.LambdaAdicNormPullback
import Langlands.Galois.LambdaAdicHeckeRigidity
import Langlands.Galois.HeckeInductionNormalization
import Langlands.Weil.Representation.InductionSeparatedLines
import Langlands.VirtualRepresentation.ExactMackey
import Langlands.Global.Arithmetic.GeneralPositionMackeyProof
import Langlands.Galois.QuadraticFrobeniusPatching.Local

/-! # Restriction and irreducibility of the singleton monomial family -/

noncomputable section

universe uF

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Langlands.Global.Harris

open Langlands.GaloisRepresentation Langlands.FiniteRepresentation
open Langlands.Global.AdelicFunctoriality

section Hecke

variable {K : Type*} [Field K] [NumberField K]

/-- The twist by `‖·‖^{a/2}` of a character that is algebraic after the twist is algebraic. -/
theorem isAlgebraic_mul_normPower [NumberField.IsTotallyComplex K] (a : ℕ)
    (χ : HeckeCharacter K) (h : IsAlgebraicAfterTwist a χ) :
    IsAlgebraic (χ * HeckeCharacter.normPower K ((a : ℂ) / 2)) := by
  obtain ⟨t, ht⟩ := h
  refine ⟨t, ContinuousMonoidHom.ext fun x => Units.ext ?_⟩
  rw [← ht x]
  change (χ.atInfinity x : ℂ) *
      ((HeckeCharacter.normPower K ((a : ℂ) / 2)).atInfinity x : ℂ) = _
  congr 1
  change ((HeckeCharacter.normPower K ((a : ℂ) / 2))
    (ideleClassMap K (infiniteIdelesInclusion K x)) : ℂ) = _
  rw [HeckeCharacter.normPower_apply, IdeleAbsoluteValue.ideleClass_class,
    IdeleAbsoluteValue.full_infiniteIdelesInclusion, IdeleAbsoluteValue.coe_infinite]
  have hpos : ∀ v : NumberField.InfinitePlace K, 0 < ‖(x.val v)‖ := fun v => by
    have := (Units.map (Pi.evalRingHom (fun w : NumberField.InfinitePlace K => w.Completion)
      v).toMonoidHom x).ne_zero
    exact norm_pos_iff.mpr this
  have hmult : ∀ v : NumberField.InfinitePlace K, v.mult = 2 := fun v =>
    NumberField.InfinitePlace.mult_isComplex ⟨v, NumberField.IsTotallyComplex.isComplex v⟩
  have hcoord : ∀ v : NumberField.InfinitePlace K,
      ‖((InfinityType.coordinate v x : ℂˣ) : ℂ)‖ = ‖x.val v‖ := fun v =>
    (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero
      (map_zero _) _
  simp only [hmult, hcoord]
  rw [Real.log_prod (fun v _ => (pow_pos (hpos v) 2).ne'), Complex.ofReal_sum, Finset.mul_sum,
    Complex.exp_sum]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Real.log_pow, ← Complex.ofReal_pow]
  have h2 : (a : ℂ) / 2 * (((2 : ℕ) * Real.log ‖x.val v‖ : ℝ) : ℂ) =
      (((a : ℝ) * Real.log ‖x.val v‖ : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h2, ← Complex.ofReal_exp, Real.exp_nat_mul, Real.exp_log (hpos v)]

end Hecke

section Norm

universe u

variable {F F' : Type u} [Field F] [NumberField F] [Field F'] [NumberField F'] [Algebra F F']

theorem normComp_mul (χ₁ χ₂ : HeckeCharacter F) :
    HeckeCharacter.normComp (L := F') (χ₁ * χ₂) =
      HeckeCharacter.normComp (L := F') χ₁ * HeckeCharacter.normComp (L := F') χ₂ := rfl

/-- The norm pullback of a unitary character is unitary. -/
theorem normComp_isUnitary {χ : HeckeCharacter F} (hχ : χ.IsUnitary) :
    (HeckeCharacter.normComp (L := F') χ).IsUnitary :=
  fun y => hχ (ideleClassNorm (K := F) y)

end Norm

section Unitary

variable {K : Type*} [Field K] [NumberField K]

/-- The values of `‖·‖^{b/2}` are positive real numbers. -/
theorem normPower_half_eq_ofReal (b : ℕ) (z : IdeleClasses K) :
    ∃ r : ℝ, 0 < r ∧ ((HeckeCharacter.normPower K ((b : ℂ) / 2) z : ℂˣ) : ℂ) = r := by
  have hb : ((b : ℂ) / 2) = (((b : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hb, HeckeCharacter.normPower_ofReal_apply]
  have hpos : 0 < ((IdeleAbsoluteValue.ideleClass K z : NNReal) : ℝ) := by
    have := (IdeleAbsoluteValue.ideleClass K z).ne_zero
    positivity
  exact ⟨_, Real.rpow_pos_of_pos hpos _, rfl⟩

/-- A unitary character is recovered from its twist by `‖·‖^{b/2}`: equal twisted values
force equal values. -/
theorem eq_of_mul_normPower_eq {χ : HeckeCharacter K} (hχ : χ.IsUnitary) (b : ℕ)
    {z₁ z₂ : IdeleClasses K}
    (h : (χ * HeckeCharacter.normPower K ((b : ℂ) / 2)) z₁ =
      (χ * HeckeCharacter.normPower K ((b : ℂ) / 2)) z₂) : χ z₁ = χ z₂ := by
  obtain ⟨r₁, hr₁, h₁⟩ := normPower_half_eq_ofReal b z₁
  obtain ⟨r₂, hr₂, h₂⟩ := normPower_half_eq_ofReal b z₂
  have hv := congrArg (fun u : ℂˣ => (u : ℂ)) h
  change (χ z₁ : ℂ) * ((HeckeCharacter.normPower K ((b : ℂ) / 2) z₁ : ℂˣ) : ℂ) =
    (χ z₂ : ℂ) * ((HeckeCharacter.normPower K ((b : ℂ) / 2) z₂ : ℂˣ) : ℂ) at hv
  rw [h₁, h₂] at hv
  have hn := congrArg norm hv
  rw [norm_mul, norm_mul, hχ z₁, hχ z₂, one_mul, one_mul, Complex.norm_real,
    Complex.norm_real, Real.norm_of_nonneg hr₁.le, Real.norm_of_nonneg hr₂.le] at hn
  rw [hn] at hv
  apply Units.ext
  exact mul_right_cancel₀ (Complex.ofReal_ne_zero.mpr hr₂.ne') hv

end Unitary

namespace Proposition48Problem

variable (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L)

/-- The embedding of `E'` in the Mackey compositum at the identity, as in the statement. -/
abbrev mackeyEmbedding : Q.E' →+* Q.mackeyField D 1 :=
  (IntermediateField.inclusion (show Q.conjugateField 1 ≤ Q.mackeyField D 1 from le_sup_right)).toRingHom.comp
    (Q.conjugateEmbedding 1).equivFieldRange.toRingEquiv.toRingHom

theorem mackeyEmbedding_coe (a : Q.E') :
    ((Q.mackeyEmbedding D a : Q.mackeyField D 1) : Q.L) = algebraMap Q.E' Q.L a := by
  change (Q.conjugateEmbedding 1) a = _
  simp [conjugateEmbedding]

theorem algebraMap_mem_conjugateField_one (a : Q.E') :
    algebraMap Q.E' Q.L a ∈ Q.conjugateField 1 :=
  ⟨a, by simp [conjugateEmbedding]⟩

/-- The actual Mackey character at the identity is the norm pullback of `ξ` along the
displayed embedding of `E'`. -/
theorem mackeyCharacter_one_eq_normComp :
    letI : Algebra Q.E' (Q.mackeyField D 1) := (Q.mackeyEmbedding D).toAlgebra
    HeckeCharacter.normComp (L := Q.mackeyField D 1) Q.ξ = Q.mackeyCharacter D 1 := by
  letI : Algebra Q.E' (Q.mackeyField D 1) := (Q.mackeyEmbedding D).toAlgebra
  let : Algebra (Q.conjugateField 1) (Q.mackeyField D 1) :=
    (IntermediateField.inclusion
      (show Q.conjugateField 1 ≤ Q.mackeyField D 1 from le_sup_right)).toAlgebra
  let eA : Q.E' ≃+* Q.conjugateField 1 := (Q.conjugateEmbedding 1).equivFieldRange.toRingEquiv
  apply ContinuousMonoidHom.ext
  intro x
  have h := ideleClassNorm_equiv (K := Q.E') (L := Q.mackeyField D 1)
    (K' := Q.conjugateField 1) (L' := Q.mackeyField D 1) eA (RingEquiv.refl _)
    (fun _ => rfl) x
  rw [ideleClassEquiv_refl] at h
  change Q.ξ (ideleClassNorm (K := Q.E') x) =
    Q.ξ ((ideleClassEquiv eA).symm (ideleClassNorm (K := Q.conjugateField 1) x))
  change ideleClassNorm (K := Q.conjugateField 1) x =
    ideleClassEquiv eA (ideleClassNorm (K := Q.E') x) at h
  rw [h, ContinuousMulEquiv.symm_apply_apply]

/-- A single Mackey double coset writes every automorphism as an element fixing `D` times an
element fixing `E'`. -/
theorem exists_mul_of_card_mackeyIndex_eq_one (hcard : Nat.card (Q.MackeyIndex D) = 1)
    (σ : Q.L ≃ₐ[Q.E] Q.L) :
    ∃ a b : Q.L ≃ₐ[Q.E] Q.L, (∀ d : D, a (algebraMap D Q.L d) = algebraMap D Q.L d) ∧
      (∀ x : Q.E', b (algebraMap Q.E' Q.L x) = algebraMap Q.E' Q.L x) ∧ σ = a * b := by
  have hsub : Subsingleton (Q.MackeyIndex D) := (Nat.card_eq_one_iff_unique.mp hcard).1
  have heq : DoubleCoset.mk D.fixingSubgroup (Q.conjugateField 1).fixingSubgroup 1 =
      DoubleCoset.mk D.fixingSubgroup (Q.conjugateField 1).fixingSubgroup σ :=
    Subsingleton.elim (α := Q.MackeyIndex D) _ _
  obtain ⟨a, ha, b, hb, hσ⟩ := DoubleCoset.eq.mp heq
  refine ⟨a, b, fun d => ?_, fun x => ?_, by rw [hσ, mul_one]⟩
  · exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp ha _ d.2
  · exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hb _
      (Q.algebraMap_mem_conjugateField_one x)

section Tower

variable [Algebra D (Q.mackeyField D 1)] [Algebra Q.E' (Q.mackeyField D 1)]

omit [Algebra Q.E' (Q.mackeyField D 1)] in
theorem isScalarTower_mackeyD
    (hDM : ∀ d : D, ((algebraMap D (Q.mackeyField D 1) d : Q.mackeyField D 1) : Q.L) = d) :
    IsScalarTower Q.E D (Q.mackeyField D 1) :=
  IsScalarTower.of_algebraMap_eq fun c => Subtype.ext (hDM (algebraMap Q.E D c)).symm

omit [Algebra D (Q.mackeyField D 1)] in
theorem isScalarTower_mackeyE'
    (hE'M : ∀ a : Q.E', ((algebraMap Q.E' (Q.mackeyField D 1) a : Q.mackeyField D 1) : Q.L) =
      algebraMap Q.E' Q.L a) :
    IsScalarTower Q.E Q.E' (Q.mackeyField D 1) := by
  refine IsScalarTower.of_algebraMap_eq fun c => Subtype.ext ?_
  rw [hE'M, ← IsScalarTower.algebraMap_apply]
  rfl

omit [Algebra Q.E' (Q.mackeyField D 1)] in
theorem isScalarTower_mackeyL
    (hDM : ∀ d : D, ((algebraMap D (Q.mackeyField D 1) d : Q.mackeyField D 1) : Q.L) = d) :
    IsScalarTower D (Q.mackeyField D 1) Q.L :=
  IsScalarTower.of_algebraMap_eq fun d => (hDM d).symm

/-- Algebra maps out of the Mackey compositum over `D` are determined on `E'`. -/
theorem mackeyField_algHom_ext
    (hDM : ∀ d : D, ((algebraMap D (Q.mackeyField D 1) d : Q.mackeyField D 1) : Q.L) = d)
    (hE'M : ∀ a : Q.E', ((algebraMap Q.E' (Q.mackeyField D 1) a : Q.mackeyField D 1) : Q.L) =
      algebraMap Q.E' Q.L a)
    {Ω : Type*} [Field Ω] [Algebra Q.E Ω] [Algebra D Ω] [IsScalarTower Q.E D Ω]
    (φ₁ φ₂ : Q.mackeyField D 1 →ₐ[D] Ω)
    (h : ∀ a : Q.E', φ₁ (algebraMap Q.E' (Q.mackeyField D 1) a) =
      φ₂ (algebraMap Q.E' (Q.mackeyField D 1) a)) : φ₁ = φ₂ := by
  have := Q.isScalarTower_mackeyD D hDM
  apply AlgHom.restrictScalars_injective Q.E
  apply IntermediateField.algHom_ext_of_eq_adjoin Q.E (S := Q.mackeyField D 1)
    (s := (D : Set Q.L) ∪ (Q.conjugateField 1 : Set Q.L)) rfl
  intro x hx
  rcases hx with hx | hx
  · have hx' : (⟨x, (le_sup_left : D ≤ Q.mackeyField D 1) hx⟩ : Q.mackeyField D 1) =
        algebraMap D (Q.mackeyField D 1) ⟨x, hx⟩ := Subtype.ext (hDM ⟨x, hx⟩).symm
    change φ₁ _ = φ₂ _
    rw [hx', AlgHom.commutes, AlgHom.commutes]
  · obtain ⟨a, ha⟩ := hx
    change φ₁ _ = φ₂ _
    convert h a using 2 <;>
    · apply Subtype.ext
      change x = _
      rw [hE'M, ← ha]
      simp [conjugateEmbedding]

end Tower

open Langlands.ClassFieldTheory.Global.InducedReciprocityIrreducible in
/-- If the conjugate by `g` of the restricted character on the absolute group of `L` agrees with
the restricted character, then `g` lies in the image of the absolute group of the Mackey
compositum: the conjugate realizes a Galois conjugate of `ξ ∘ N_{L/E'}`, and relative
regularity forces the conjugating automorphism to fix `E'`. -/
theorem mem_range_of_transportConj_invariant
    [Algebra D (Q.mackeyField D 1)] [Algebra Q.E' (Q.mackeyField D 1)]
    (hDM : ∀ d : D, ((algebraMap D (Q.mackeyField D 1) d : Q.mackeyField D 1) : Q.L) = d)
    (hE'M : ∀ a : Q.E', ((algebraMap Q.E' (Q.mackeyField D 1) a : Q.mackeyField D 1) : Q.L) =
      algebraMap Q.E' Q.L a)
    [IsScalarTower D (Q.mackeyField D 1) Q.L] [Normal D Q.L]
    (hreg : IsRelativelyRegular Q.E Q.ξ) (hconj : IsConjugateInverse Q.ξ) (b : ℕ)
    {L : Type} [Field L] [NumberField L] (ι : L →+* ℂ)
    (ψ : (lam : FinitePlace L) → LambdaAdicCharacter Q.E' L lam)
    (hψ : IsCompatibleLambdaAdicRealization ι
      (Q.ξ * HeckeCharacter.normPower Q.E' ((b : ℂ) / 2)) ψ)
    (eM : AlgebraicClosure D →ₐ[D] AlgebraicClosure (Q.mackeyField D 1))
    (ej : AlgebraicClosure Q.E' →ₐ[Q.E'] AlgebraicClosure (Q.mackeyField D 1))
    (κ' : AlgebraicClosure (Q.mackeyField D 1) →ₐ[Q.mackeyField D 1] AlgebraicClosure Q.L)
    (lam : FinitePlace L) (g : Field.absoluteGaloisGroup D)
    (hinv : ∀ x : Field.absoluteGaloisGroup Q.L,
      ψ lam (restrictionAlongClosure ej (restrictionAlongClosure κ'
        (transportConj eM κ' g x))) =
      ψ lam (restrictionAlongClosure ej (restrictionAlongClosure κ' x))) :
    g ∈ (restrictionAlongClosure eM).toMonoidHom.range := by
  set ξalg := Q.ξ * HeckeCharacter.normPower Q.E' ((b : ℂ) / 2)
  have hunit : Q.ξ.IsUnitary := HeckeConjugateInverse.isUnitary_of_isConjugateInverse Q.ξ hconj
  -- the closure embedding of `E'` through `M`
  let θ : AlgebraicClosure Q.E' →ₐ[Q.E'] AlgebraicClosure Q.L :=
    { toRingHom := κ'.toRingHom.comp ej.toRingHom
      commutes' := fun a => by
        change κ' (ej (algebraMap Q.E' (AlgebraicClosure Q.E') a)) =
          algebraMap Q.E' (AlgebraicClosure Q.L) a
        rw [ej.commutes, IsScalarTower.algebraMap_apply Q.E' (Q.mackeyField D 1) (AlgebraicClosure (Q.mackeyField D 1)), κ'.commutes,
          IsScalarTower.algebraMap_apply Q.E' Q.L (AlgebraicClosure Q.L),
          IsScalarTower.algebraMap_apply (Q.mackeyField D 1) Q.L (AlgebraicClosure Q.L)]
        congr 1
        exact hE'M a }
  have hθ (y : Field.absoluteGaloisGroup Q.L) : restrictionAlongClosure θ y =
      restrictionAlongClosure ej (restrictionAlongClosure κ' y) :=
    restrictionAlongClosure_comp ej κ' θ (fun _ => rfl) y
  have hΨ := isCompatibleLambdaAdicRealization_normComp ι ξalg ψ hψ θ
  -- the transported automorphism and the twisted embedding of `E'`
  set τ := closureTransport eM κ' g
  set σ' := restrictedTransport eM κ' g
  let f' : Q.E' →+* Q.L := (σ' : Q.L →+* Q.L).comp (algebraMap Q.E' Q.L)
  have hΘ (a : Q.E') : (τ.toRingHom.comp θ.toRingHom) (algebraMap Q.E' (AlgebraicClosure Q.E') a) =
      algebraMap Q.L (AlgebraicClosure Q.L) (f' a) := by
    change τ (θ (algebraMap Q.E' (AlgebraicClosure Q.E') a)) = _
    rw [θ.commutes, IsScalarTower.algebraMap_apply Q.E' Q.L (AlgebraicClosure Q.L)]
    exact (restrictedTransport_spec eM κ' g _).symm
  let Θ := closureEmbeddingOfRingHom f' (τ.toRingHom.comp θ.toRingHom) hΘ
  have hΨ' := isCompatibleLambdaAdicRealization_normComp_hom f' ι ξalg ψ hψ Θ
  have hres (y : Field.absoluteGaloisGroup Q.L) :
      restrictionAlongClosureHom f' Θ y =
        restrictionAlongClosure θ (transportConj eM κ' g y) := by
    symm
    apply eq_restrictionAlongClosureHom_ofRingHom
    intro z
    change τ (θ (AlgEquiv.toRingEquiv
        (restrictionAlongClosure θ (transportConj eM κ' g y)) z)) =
      AlgEquiv.toRingEquiv y (τ (θ z))
    rw [restrictionAlongClosure_commutes]
    change τ (τ.symm (AlgEquiv.toRingEquiv y (τ (θ z)))) = _
    rw [AlgEquiv.apply_symm_apply]
  have heqΨ : ∀ y, ψ lam (restrictionAlongClosureHom f' Θ y) =
      ψ lam (restrictionAlongClosure θ y) := by
    intro y
    rw [hres, hθ, hθ]
    exact hinv y
  have hχ := heckeCharacter_eq_of_lambdaAdic_eq ι hΨ' hΨ lam heqΨ
  have htwist (y : IdeleClasses Q.L) :=
    ideleClassNorm_algebra_twist f'.toAlgebra Q.algebraE'L (σ'.symm : Q.L ≃ₐ[D] Q.L).toRingEquiv
      (fun x => by
        change σ'.symm (σ' (algebraMap Q.E' Q.L x)) = algebraMap Q.E' Q.L x
        exact σ'.symm_apply_apply _) y
  have hinvξ : ∀ y : IdeleClasses Q.L,
      Q.ξ (ideleClassNorm (K := Q.E') (ideleClassEquiv (σ'.symm : Q.L ≃ₐ[D] Q.L).toRingEquiv y)) =
        Q.ξ (ideleClassNorm (K := Q.E') y) := by
    intro y
    apply eq_of_mul_normPower_eq hunit b
    have h1 : ξalg (@ideleClassNorm Q.E' Q.L _ _ _ _ f'.toAlgebra y) =
        ξalg (ideleClassNorm (K := Q.E') y) := DFunLike.congr_fun hχ y
    rw [← htwist y] at h1
    exact h1
  have hfixE' : ∀ x : Q.E', σ' (algebraMap Q.E' Q.L x) = algebraMap Q.E' Q.L x := by
    intro x
    have h := fixes_of_ideleClassNorm_invariant (E := Q.E) Q.ξ hreg
      ((σ'.restrictScalars Q.E).symm) (fun a => hinvξ a) x
    exact ((AlgEquiv.symm_apply_eq _).mp h).symm
  have hfixM : ∀ m : Q.mackeyField D 1,
      σ' (algebraMap (Q.mackeyField D 1) Q.L m) = algebraMap (Q.mackeyField D 1) Q.L m := by
    have h := Q.mackeyField_algHom_ext D hDM hE'M (Ω := Q.L)
      ((σ' : Q.L ≃ₐ[D] Q.L).toAlgHom.comp (IsScalarTower.toAlgHom D (Q.mackeyField D 1) Q.L))
      (IsScalarTower.toAlgHom D (Q.mackeyField D 1) Q.L) (fun a => by
        change σ' ((algebraMap Q.E' (Q.mackeyField D 1) a : Q.mackeyField D 1) : Q.L) =
          ((algebraMap Q.E' (Q.mackeyField D 1) a : Q.mackeyField D 1) : Q.L)
        rw [hE'M]
        exact hfixE' a)
    intro m
    exact DFunLike.congr_fun h m
  have : IsScalarTower Q.E D (Q.mackeyField D 1) := Q.isScalarTower_mackeyD D hDM
  have : Algebra.IsAlgebraic D (Q.mackeyField D 1) :=
    Algebra.IsAlgebraic.tower_top (K := Q.E) D
  exact mem_range_of_restrictedTransport_fixes eM κ' g hfixM

attribute [local instance 1100] DivisionSemiring.to_moduleIsTorsionFree in
/-- The restriction to the absolute group of `D` of a member of the family induced from `ψ` is
induced from the restriction of `ψ` along `E' → M`, is irreducible, has scalar endomorphisms,
and is equivalent to any representation induced from that restricted character. -/
theorem pullbackAlongClosure_induced_spec
    [Algebra D (Q.mackeyField D 1)] [Algebra Q.E' (Q.mackeyField D 1)]
    (hDM : ∀ d : D, ((algebraMap D (Q.mackeyField D 1) d : Q.mackeyField D 1) : Q.L) = d)
    (hE'M : ∀ a : Q.E', ((algebraMap Q.E' (Q.mackeyField D 1) a : Q.mackeyField D 1) : Q.L) =
      algebraMap Q.E' Q.L a)
    (hcard : Nat.card (Q.MackeyIndex D) = 1) [Normal Q.E Q.L] [Normal Q.E D]
    (hreg : IsRelativelyRegular Q.E Q.ξ) (hconj : IsConjugateInverse Q.ξ) (b : ℕ)
    {L : Type} [Field L] [NumberField L] (ι : L →+* ℂ)
    (ψ : (lam : FinitePlace L) → LambdaAdicCharacter Q.E' L lam)
    (hψ : IsCompatibleLambdaAdicRealization ι
      (Q.ξ * HeckeCharacter.normPower Q.E' ((b : ℂ) / 2)) ψ)
    (e : AlgebraicClosure Q.E →ₐ[Q.E] AlgebraicClosure Q.E')
    (eD : AlgebraicClosure Q.E →ₐ[Q.E] AlgebraicClosure D)
    (eM : AlgebraicClosure D →ₐ[D] AlgebraicClosure (Q.mackeyField D 1))
    (ej : AlgebraicClosure Q.E' →ₐ[Q.E'] AlgebraicClosure (Q.mackeyField D 1))
    (lam : FinitePlace L) (A : LambdaAdic.{0, 0, 0} Q.E L lam)
    (A' : LambdaAdic.{0, 0, 0} D L lam)
    (hA : IsGaloisInductionOfCharacter e lam (ψ lam) A)
    (hA' : IsGaloisInductionOfCharacter eM lam ((ψ lam).comp (restrictionAlongClosure ej)) A') :
    IsGaloisInductionOfCharacter eM lam ((ψ lam).comp (restrictionAlongClosure ej))
        (pullbackAlongClosure eD A) ∧
      (pullbackAlongClosure eD A).val.representation.IsIrreducible ∧
      HasScalarEndomorphisms (pullbackAlongClosure eD A).val ∧
      Nonempty (FiniteRepresentation.Equiv (pullbackAlongClosure eD A).val A'.val) := by
  classical
  have : IsScalarTower Q.E D (Q.mackeyField D 1) := Q.isScalarTower_mackeyD D hDM
  have : IsScalarTower Q.E Q.E' (Q.mackeyField D 1) := Q.isScalarTower_mackeyE' D hE'M
  have : IsScalarTower D (Q.mackeyField D 1) Q.L := Q.isScalarTower_mackeyL D hDM
  have : Algebra.IsAlgebraic D (Q.mackeyField D 1) :=
    Algebra.IsAlgebraic.tower_top (K := Q.E) D
  have : Normal D Q.L := Normal.tower_top_of_normal Q.E D Q.L
  obtain ⟨hH, φ, hφ, ⟨eA⟩⟩ := hA
  obtain ⟨hS', φ', hφ', ⟨eA'⟩⟩ := hA'
  let H := (restrictionAlongClosure e).toMonoidHom.range
  let S := (restrictionAlongClosure eM).toMonoidHom.range
  let rD := (restrictionAlongClosure eD).toMonoidHom
  let x := mackeyElement e eD eM ej
  have hconjM (y : Field.absoluteGaloisGroup (Q.mackeyField D 1)) :
      x * rD (restrictionAlongClosure eM y) * x⁻¹ =
        restrictionAlongClosure e (restrictionAlongClosure ej y) :=
    mackeyElement_conj e eD eM ej y
  have hκmem : ∀ s : S, (MulAut.conj x).toMonoidHom (rD.comp S.subtype s) ∈ H := by
    rintro ⟨_, y, rfl⟩
    exact ⟨restrictionAlongClosure ej y, (hconjM y).symm⟩
  let κ : S →* H := ((MulAut.conj x).toMonoidHom.comp (rD.comp S.subtype)).codRestrict H hκmem
  have hS : ∀ ℓ, x * rD ℓ * x⁻¹ ∈ H → ℓ ∈ S := fun ℓ hℓ =>
    mem_range_of_conj_mem e eD eM ej
      (fun φ₁ φ₂ h => Q.mackeyField_algHom_ext D hDM hE'M φ₁ φ₂ h) ℓ hℓ
  have : rD.range.Normal := range_restrictionAlongClosure_normal eD
  have hcover : ∀ g, ∃ (h : H) (ℓ : Field.absoluteGaloisGroup D), g = h * (x * rD ℓ) :=
    fun g => exists_mul_mul_of_mul_cover H rD
      (fun g => exists_mul_of_galois_mul e eD (Q.exists_mul_of_card_mackeyIndex_eq_one D hcard) g)
      x g
  let A0 := FiniteRepresentation.twist φ (FiniteRepresentation.of (1 : Representation (FiniteCompletion L lam) H (FiniteCompletion L lam)))
  let E1 : FiniteRepresentation.Equiv (pullbackAlongClosure eD A).val (restrict rD A.val) :=
    { toLinearEquiv := LinearEquiv.refl _ _
      isIntertwining' := fun _ => rfl }
  let E2 : FiniteRepresentation.Equiv (restrict rD A.val) (restrict rD (induce H A0)) := restrictEquiv rD eA.symm
  let E3 : FiniteRepresentation.Equiv (restrict rD (induce H A0)) (induce S (restrict κ A0)) :=
    restrictInduceEquivOfOneCoset H rD x S κ (fun _ => rfl) hS hcover A0
  let E4 := induceEquiv S (restrictTwistLineEquiv κ φ)
  let Echain := E1.trans (E2.trans (E3.trans E4))
  have hφκ : (φ.comp κ).comp (restrictionAlongClosure eM).toMonoidHom.rangeRestrict =
      ((ψ lam).comp (restrictionAlongClosure ej)).toMonoidHom := by
    refine MonoidHom.ext fun y => ?_
    have h1 : κ ((restrictionAlongClosure eM).toMonoidHom.rangeRestrict y) =
        (restrictionAlongClosure e).toMonoidHom.rangeRestrict (restrictionAlongClosure ej y) :=
      Subtype.ext (hconjM y)
    change φ (κ ((restrictionAlongClosure eM).toMonoidHom.rangeRestrict y)) = _
    rw [h1]
    exact DFunLike.congr_fun hφ _
  have hval : ∀ (s : S) (w : Field.absoluteGaloisGroup (Q.mackeyField D 1)),
      (s : Field.absoluteGaloisGroup D) = restrictionAlongClosure eM w →
        (φ.comp κ) s = ψ lam (restrictionAlongClosure ej w) := fun s w hs => by
    rw [show s = (restrictionAlongClosure eM).toMonoidHom.rangeRestrict w from Subtype.ext hs]
    exact DFunLike.congr_fun hφκ w
  -- the normal subgroup coming from the absolute group of `L`
  let κ' : AlgebraicClosure (Q.mackeyField D 1) →ₐ[Q.mackeyField D 1] AlgebraicClosure Q.L :=
    IsAlgClosed.lift
  let rL := (restrictionAlongClosure (closureThroughM eM κ')).toMonoidHom
  have : rL.range.Normal := range_restrictionAlongClosure_closureThroughM_normal eM κ'
  have hNS : rL.range ≤ S := range_closureThroughM_le eM κ'
  have separate : ∀ x' y' : Field.absoluteGaloisGroup D,
      Induction.coset S x' ≠ Induction.coset S y' →
        ∃ n : rL.range,
          ((φ.comp κ).comp (Subgroup.inclusion hNS)) (MulAut.conjNormal x' n) ≠
          ((φ.comp κ).comp (Subgroup.inclusion hNS)) (MulAut.conjNormal y' n) := by
    intro x' y' hne
    by_contra hall
    push Not at hall
    apply hne
    apply Quotient.sound
    change QuotientGroup.rightRel S x' y'
    rw [QuotientGroup.rightRel_apply]
    apply Q.mem_range_of_transportConj_invariant D hDM hE'M hreg hconj b ι ψ hψ eM ej κ' lam
    intro z
    let m := restrictionAlongClosure (closureThroughM eM κ') z
    have hm : y'⁻¹ * m * y'⁻¹⁻¹ ∈ rL.range :=
      (inferInstance : rL.range.Normal).conj_mem m ⟨z, rfl⟩ y'⁻¹
    have h := hall ⟨y'⁻¹ * m * y'⁻¹⁻¹, hm⟩
    have h1 : ((Subgroup.inclusion hNS (MulAut.conjNormal x' ⟨y'⁻¹ * m * y'⁻¹⁻¹, hm⟩) : S) :
        Field.absoluteGaloisGroup D) = restrictionAlongClosure eM
          (restrictionAlongClosure κ' (transportConj eM κ' (y' * x'⁻¹) z)) := by
      refine Eq.trans ?_ (restrictionAlongClosure_closureThroughM eM κ' _)
      refine Eq.trans ?_ (conj_restrictionAlongClosure_closureThroughM eM κ' _ z)
      simp only [Subgroup.coe_inclusion, MulAut.conjNormal_apply, m]
      group
    have h2 : ((Subgroup.inclusion hNS (MulAut.conjNormal y' ⟨y'⁻¹ * m * y'⁻¹⁻¹, hm⟩) : S) :
        Field.absoluteGaloisGroup D) = restrictionAlongClosure eM (restrictionAlongClosure κ' z) := by
      refine Eq.trans ?_ (restrictionAlongClosure_closureThroughM eM κ' z)
      simp only [Subgroup.coe_inclusion, MulAut.conjNormal_apply, m]
      group
    exact (hval _ _ h1).symm.trans (h.trans (hval _ _ h2))
  obtain ⟨hirr, hscal⟩ := induce_twist_irreducible_scalar_of_separation S rL.range hNS
    (φ.comp κ) separate
  have hφeq : φ.comp κ = φ' :=
    (MonoidHom.cancel_right (MonoidHom.rangeRestrict_surjective _)).mp (hφκ.trans hφ'.symm)
  refine ⟨⟨hS', φ.comp κ, hφκ, ⟨Echain.symm⟩⟩, isIrreducible_of_equiv Echain.symm hirr,
    hasScalarEndomorphisms_of_equiv Echain.symm hscal,
    ⟨(Echain.trans (induceEquiv S (twistLineEquivOfEq hφeq))).trans eA'⟩⟩

end Proposition48Problem

attribute [local instance 1100] DivisionSemiring.to_moduleIsTorsionFree in
theorem proposition48SingletonMonomialRestriction :
    Proposition48SingletonMonomialRestrictionStatement.{uF} := by
  intro hRank hInd Q D hvalid hstep hcard M j e eD eM ej b ξalg
  letI : Algebra Q.E' M := j.toAlgebra
  letI : Algebra D M :=
    (IntermediateField.inclusion (show D ≤ M from le_sup_left)).toAlgebra
  obtain ⟨-, -, -, hclosure, -, -, -, -, -, halg, hreg, hconj, -⟩ := hvalid
  have hξalg : IsAlgebraic ξalg := isAlgebraic_mul_normPower b Q.ξ halg
  obtain ⟨L, fieldL, numberFieldL, ι, ψ, hψ⟩ := hRank Q.E' ξalg hξalg
  letI := fieldL
  letI := numberFieldL
  obtain ⟨R, S, P, hR, hrank, hmatch, hEuler⟩ := hInd Q.E Q.E' L e ι ξalg ψ hψ
  have hψM := isCompatibleLambdaAdicRealization_normComp ι ξalg ψ hψ ej
  obtain ⟨R', S', P', hR', hrank', hmatch', hEuler'⟩ := hInd D M L eM ι _ _ hψM
  have hunit : Q.ξ.IsUnitary := HeckeConjugateInverse.isUnitary_of_isConjugateInverse Q.ξ hconj
  have : Normal Q.E Q.L := by
    have := hclosure
    exact IsNormalClosure.normal (K := Q.E')
  have : Normal Q.E D := hstep.1.to_normal
  have hDM : ∀ d : D, ((algebraMap D M d : M) : Q.L) = d := fun _ => rfl
  have hE'M : ∀ a : Q.E', ((algebraMap Q.E' M a : M) : Q.L) = algebraMap Q.E' Q.L a :=
    Q.mackeyEmbedding_coe D
  have hspec (lam : {lam : FinitePlace L // lam ∉ (∅ : Finset (FinitePlace L))}) :=
    Q.pullbackAlongClosure_induced_spec D hDM hE'M hcard hreg hconj b ι ψ hψ e eD eM ej lam.val
      (R lam) (R' lam) (hR lam) (hR' lam)
  -- the norm pullback of `ξalg` is the actual Mackey character twisted by `‖·‖^{b/2}`
  have hξM : HeckeCharacter.normComp (L := M) Q.ξ = Q.mackeyCharacter D 1 :=
    Q.mackeyCharacter_one_eq_normComp D
  have hχM : HeckeCharacter.normComp (L := M) ξalg =
      Q.mackeyCharacter D 1 * HeckeCharacter.normPower M ((b : ℂ) / 2) := by
    rw [← hξM, ← Langlands.LocalFactor.NonabelianBrauer.normComp_normPower (k := Q.E') (M := M) ((b : ℂ) / 2)]
    rfl
  rw [hχM] at hEuler'
  have hunitM : (Q.mackeyCharacter D 1).IsUnitary := by
    rw [← hξM]
    exact normComp_isUnitary hunit
  have hnormD := matchesHeckeInduction_normPower (Q.mackeyCharacter D 1) hunitM b _ hEuler'
  refine ⟨L, fieldL, numberFieldL, ι, ψ, R, S, P, S', P', hψ, hR, hrank, hmatch,
    (matchesHeckeInduction_normPower Q.ξ hunit b _ hEuler).1,
    fun lam => ⟨(hspec lam).1, (hspec lam).2.1, (hspec lam).2.2.1⟩, ?_, hnormD.1, ?_⟩
  · intro lam v hv hchar
    obtain ⟨E⟩ := (hspec lam).2.2.2
    exact (QuadraticFrobeniusPatching.hasEulerPolynomialAt_equiv E v _).mpr
      (hmatch' lam v hv hchar)
  · filter_upwards [hnormD.2] with w hw
    obtain ⟨h0, hwt⟩ := hw
    have h0' : ((P' w).map ι).coeff 0 = 1 := h0
    refine ⟨ι.injective ?_, ?_⟩
    · rw [← Polynomial.coeff_map, h0', map_one]
    · rw [← reverse_map_of_injective ι.injective]
      exact hwt

end Langlands.Global.Harris
