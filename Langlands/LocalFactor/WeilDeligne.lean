import Langlands.WeilDeligne.Kernels
import Langlands.LocalFactor.Euler.Definitions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# The invariant quotient in Weil–Deligne local factors

This algebraic construction uses the parameter owner's actual representation,
monodromy kernel, and normal-subgroup invariants. A specified element acts on
the resulting subquotient. Its interpretation as geometric Frobenius requires
the corresponding local Weil-group specialization.
-/

noncomputable section

universe uK uG uV uW

open Polynomial

namespace Langlands.LocalFactor.WeilDeligne

variable {K : Type uK} {G : Type uG} [Field K] [Group G] {ν : G →* Kˣ}

/-- The actual normal-subgroup fixed representation of the underlying pair. -/
abbrev inertiaRepresentation (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (I : Subgroup G) [I.Normal] : FiniteRepresentation.{uK, uG, uV} K G :=
  FiniteRepresentation.invariants I A.toFiniteRepresentation

/-- The monodromy kernel as a subspace of the fixed space `V^I`. -/
def kernelInInvariants (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] : Submodule K (inertiaRepresentation A I) :=
  A.monodromy.ker.comap
    (FiniteRepresentation.invariantSubspace A.toFiniteRepresentation I).subtype

@[simp]
theorem mem_kernelInInvariants (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] (x : inertiaRepresentation A I) :
    x ∈ kernelInInvariants A I ↔ A.monodromy x.val = 0 := Iff.rfl

/-- Covariance of monodromy implies stability of the subspace inside `V^I`. -/
theorem kernelInInvariants_stable (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] (g : G) :
    kernelInInvariants A I ≤
      (kernelInInvariants A I).comap ((inertiaRepresentation A I).representation g) := by
  intro x hx
  exact A.kernelSubrepresentation.apply_mem_toSubmodule g hx

/-- The actual quotient representation on `V^I / (ker N)^I`. -/
def quotientRepresentation (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (I : Subgroup G) [I.Normal] : FiniteRepresentation.{uK, uG, uV} K G :=
  FiniteRepresentation.of
    ((inertiaRepresentation A I).representation.quotient
      (kernelInInvariants A I) (kernelInInvariants_stable A I))

/-- The quotient projection is an intertwiner for the induced action. -/
def quotientProjection (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] :
    (inertiaRepresentation A I).representation.IntertwiningMap
      (quotientRepresentation A I).representation :=
  ⟨(kernelInInvariants A I).mkQ, fun _ => rfl⟩

instance quotientRepresentation_isTrivial (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] :
    Representation.IsTrivial ((quotientRepresentation A I).representation.comp I.subtype) where
  out i := by
    apply (kernelInInvariants A I).quot_hom_ext
    intro x
    apply congrArg (kernelInInvariants A I).mkQ
    exact Representation.isTrivial_apply
      ((inertiaRepresentation A I).representation.comp I.subtype) i x

/-- Reordering the two subtype conditions identifies the subspace with the
parameter owner's actual inertia-fixed monodromy kernel. -/
def kernelInInvariantsEquiv (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] :
    kernelInInvariants A I ≃ₗ[K] A.inertiaKernelRepresentation I where
  toFun x := ⟨⟨x.val.val, x.property⟩, fun i => Subtype.ext (x.val.property i)⟩
  invFun x := ⟨⟨x.val.val, fun i => congrArg Subtype.val (x.property i)⟩, x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The quotient dimension is the intrinsic monodromy correction to the conductor. -/
def conductorCorrection (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] : ℕ :=
  (quotientRepresentation A I).rank

theorem conductorCorrection_add_kernelRank (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] :
    conductorCorrection A I + (A.inertiaKernelRepresentation I).rank =
      (inertiaRepresentation A I).rank := by
  change Module.finrank K ((inertiaRepresentation A I) ⧸ kernelInInvariants A I) +
    Module.finrank K (A.inertiaKernelRepresentation I) =
      Module.finrank K (inertiaRepresentation A I)
  rw [← (kernelInInvariantsEquiv A I).finrank_eq]
  exact (kernelInInvariants A I).finrank_quotient_add_finrank

theorem conductorCorrection_eq_rank_sub (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] :
    conductorCorrection A I = (inertiaRepresentation A I).rank -
      (A.inertiaKernelRepresentation I).rank :=
  Nat.eq_sub_of_add_eq (conductorCorrection_add_kernelRank A I)

/-- The action on inertia invariants, at an explicitly specified element. -/
abbrev inertiaOperator (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] (g : G) :
    Module.End K (inertiaRepresentation A I) :=
  (inertiaRepresentation A I).representation g

/-- The action on the inertia-fixed monodromy kernel. -/
abbrev kernelOperator (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] (g : G) :
    Module.End K (A.inertiaKernelRepresentation I) :=
  (A.inertiaKernelRepresentation I).representation g

/-- The action on the actual quotient, not the action on all of `V`. -/
abbrev quotientOperator (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] (g : G) :
    Module.End K (quotientRepresentation A I) :=
  (quotientRepresentation A I).representation g

/-- The Weil–Deligne Euler denominator `det(1 - X g | (ker N)^I)`. -/
def eulerPolynomial (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] (g : G) : K[X] :=
  LocalFactor.eulerPolynomial (kernelOperator A I g)

@[simp]
theorem eulerPolynomial_coeff_zero (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] (g : G) :
    (eulerPolynomial A I g).coeff 0 = 1 :=
  LocalFactor.eulerPolynomial_coeff_zero _

/-- The L-factor is a rational function, so poles have not been assigned finite values. -/
def rationalLFactor (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] (g : G) : RatFunc K :=
  LocalFactor.rationalFactor (kernelOperator A I g)

theorem rationalLFactor_ne_zero (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] (g : G) : rationalLFactor A I g ≠ 0 :=
  LocalFactor.rationalFactor_ne_zero _

/-- The finite-value domain of the actual reciprocal Euler polynomial. -/
abbrev RegularPoint (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] (g : G) :=
  LocalFactor.RegularPoint (kernelOperator A I g)

/-- Values are exposed only away from the Euler denominator's zeros. -/
def regularLValue (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] (g : G) (z : RegularPoint A I g) : Kˣ :=
  LocalFactor.regularFactorValue (kernelOperator A I g) z

theorem regularLValue_det (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] (g : G) (z : RegularPoint A I g) :
    (regularLValue A I g z : K) =
      (LinearMap.det (1 - z.val • kernelOperator A I g))⁻¹ :=
  LocalFactor.regularFactorValue_det _ _

/-- The constant correction retains the determinant on `V^I / (ker N)^I`. -/
def quotientDeterminant (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] (g : G) : K :=
  LinearMap.det (-quotientOperator A I g)

theorem quotientDeterminant_ne_zero (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] (g : G) : quotientDeterminant A I g ≠ 0 := by
  have h : quotientDeterminant A I g * quotientDeterminant A I g⁻¹ = 1 := by
    unfold quotientDeterminant quotientOperator
    rw [← map_mul, neg_mul_neg, ← map_mul, mul_inv_cancel, map_one, map_one]
  exact left_ne_zero_of_mul_eq_one h

/-- The spectral quotient correction, `det(-X g | V^I / (ker N)^I)`. -/
def quotientCorrectionPolynomial (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] (g : G) : K[X] :=
  Polynomial.monomial (conductorCorrection A I) (quotientDeterminant A I g)

/-- Evaluation agrees with the intrinsic determinant of the scalar-multiplied
quotient operator, including at zero. -/
theorem quotientCorrectionPolynomial_eval (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] (g : G) (z : K) :
    (quotientCorrectionPolynomial A I g).eval z =
      LinearMap.det (z • (-quotientOperator A I g)) := by
  rw [quotientCorrectionPolynomial, Polynomial.eval_monomial, LinearMap.det_smul]
  exact mul_comm _ _

@[simp]
theorem quotientCorrectionPolynomial_eval_one (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] (g : G) :
    (quotientCorrectionPolynomial A I g).eval 1 = quotientDeterminant A I g := by
  simp [quotientCorrectionPolynomial]

theorem quotientCorrectionPolynomial_ne_zero (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] (g : G) :
    quotientCorrectionPolynomial A I g ≠ 0 := by
  intro h
  have h1 := quotientCorrectionPolynomial_eval_one A I g
  rw [h, Polynomial.eval_zero] at h1
  exact quotientDeterminant_ne_zero A I g h1.symm

/-- The spectral correction as an actual rational function. -/
def quotientCorrection (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] (g : G) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (quotientCorrectionPolynomial A I g)

theorem quotientCorrection_ne_zero (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] (g : G) : quotientCorrection A I g ≠ 0 :=
  RatFunc.algebraMap_ne_zero (quotientCorrectionPolynomial_ne_zero A I g)

/-- The constant correction is a unit, by invertibility of the induced group action. -/
def quotientConstantCorrection (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] (g : G) : Kˣ :=
  Units.mk0 (quotientDeterminant A I g) (quotientDeterminant_ne_zero A I g)

/-- The spectral correction at a nonzero variable; its nonvanishing is intrinsic. -/
def quotientCorrectionValue (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] (g : G) (z : Kˣ) : Kˣ :=
  quotientConstantCorrection A I g * z ^ conductorCorrection A I

theorem quotientCorrectionValue_eq_eval (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] (g : G) (z : Kˣ) :
    (quotientCorrectionValue A I g z : K) =
      (quotientCorrectionPolynomial A I g).eval (z : K) := by
  simp [quotientCorrectionValue, quotientConstantCorrection, quotientCorrectionPolynomial]

theorem quotientCorrectionValue_det (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] (g : G) (z : Kˣ) :
    (quotientCorrectionValue A I g z : K) =
      LinearMap.det ((z : K) • (-quotientOperator A I g)) := by
  rw [quotientCorrectionValue_eq_eval, quotientCorrectionPolynomial_eval]

section Morphisms

variable (I : Subgroup G) [I.Normal]
    {A : WeilDeligneRepresentation.{uK, uG, uV} K G ν}
    {B : WeilDeligneRepresentation.{uK, uG, uW} K G ν}

/-- Pair morphisms carry the kernel subspace inside invariants to the corresponding
subspace. This follows from commutation with monodromy. -/
theorem invariantsMap_kernel_le (f : WeilDeligneRepresentation.Hom A B) :
    kernelInInvariants A I ≤ (kernelInInvariants B I).comap
      (FiniteRepresentation.invariantsMap I f.intertwiner).toLinearMap := by
  intro x hx
  change B.monodromy (f.intertwiner x.val) = 0
  have h := LinearMap.congr_fun f.comm_monodromy x.val
  change f.intertwiner (A.monodromy x.val) = B.monodromy (f.intertwiner x.val) at h
  rw [← h, (mem_kernelInInvariants A I x).mp hx, map_zero]

/-- The induced actual quotient intertwiner, with no extra stability assumption. -/
def quotientMap (f : WeilDeligneRepresentation.Hom A B) :
    (quotientRepresentation A I).representation.IntertwiningMap
      (quotientRepresentation B I).representation where
  toLinearMap := (kernelInInvariants A I).mapQ (kernelInInvariants B I)
    (FiniteRepresentation.invariantsMap I f.intertwiner).toLinearMap
    (invariantsMap_kernel_le I f)
  isIntertwining' g := by
    apply (kernelInInvariants A I).quot_hom_ext
    intro x
    exact congrArg (kernelInInvariants B I).mkQ
      (Representation.IntertwiningMap.isIntertwining _ _
        (FiniteRepresentation.invariantsMap I f.intertwiner) g x)

@[simp]
theorem quotientMap_mk (f : WeilDeligneRepresentation.Hom A B)
    (x : inertiaRepresentation A I) :
    quotientMap I f ((kernelInInvariants A I).mkQ x) =
      (kernelInInvariants B I).mkQ
        (FiniteRepresentation.invariantsMap I f.intertwiner x) := rfl

/-- A genuine pair equivalence induces a quotient equivalence, even between
independent carrier universes. -/
def quotientEquiv (e : WeilDeligneRepresentation.Equiv A B) :
    FiniteRepresentation.Equiv (quotientRepresentation A I) (quotientRepresentation B I) where
  toLinearEquiv := {
    (quotientMap I e.toHom).toLinearMap with
    invFun := quotientMap I e.symm.toHom
    left_inv := fun x => by
      obtain ⟨x, rfl⟩ := (kernelInInvariants A I).mkQ_surjective x
      change (kernelInInvariants A I).mkQ
        (FiniteRepresentation.invariantsMap I e.symm.toHom.intertwiner
          (FiniteRepresentation.invariantsMap I e.toHom.intertwiner x)) =
            (kernelInInvariants A I).mkQ x
      apply congrArg (kernelInInvariants A I).mkQ
      apply Subtype.ext
      exact e.representationEquiv.symm_apply_apply x.val
    right_inv := fun x => by
      obtain ⟨x, rfl⟩ := (kernelInInvariants B I).mkQ_surjective x
      change (kernelInInvariants B I).mkQ
        (FiniteRepresentation.invariantsMap I e.toHom.intertwiner
          (FiniteRepresentation.invariantsMap I e.symm.toHom.intertwiner x)) =
            (kernelInInvariants B I).mkQ x
      apply congrArg (kernelInInvariants B I).mkQ
      apply Subtype.ext
      exact e.representationEquiv.apply_symm_apply x.val }
  isIntertwining' := (quotientMap I e.toHom).isIntertwining'

/-- The kernel-invariant equivalence induced by a pair equivalence, with
independent carrier universes. -/
def kernelEquiv (e : WeilDeligneRepresentation.Equiv A B) :
    FiniteRepresentation.Equiv (A.inertiaKernelRepresentation I)
      (B.inertiaKernelRepresentation I) where
  toLinearEquiv := {
    (FiniteRepresentation.invariantsMap I (WeilDeligneRepresentation.kernelMap e.toHom)).toLinearMap
      with
    invFun := FiniteRepresentation.invariantsMap I
      (WeilDeligneRepresentation.kernelMap e.symm.toHom)
    left_inv := fun x => by
      apply Subtype.ext
      apply Subtype.ext
      exact e.representationEquiv.symm_apply_apply x.val.val
    right_inv := fun x => by
      apply Subtype.ext
      apply Subtype.ext
      exact e.representationEquiv.apply_symm_apply x.val.val }
  isIntertwining' :=
    (FiniteRepresentation.invariantsMap I
      (WeilDeligneRepresentation.kernelMap e.toHom)).isIntertwining'

theorem conductorCorrection_eq_of_equiv (e : WeilDeligneRepresentation.Equiv A B) :
    conductorCorrection A I = conductorCorrection B I :=
  (quotientEquiv I e).toLinearEquiv.finrank_eq

theorem eulerPolynomial_eq_of_equiv (e : WeilDeligneRepresentation.Equiv A B) (g : G) :
    eulerPolynomial A I g = eulerPolynomial B I g := by
  have h := LocalFactor.eulerPolynomial_conj
    (kernelEquiv I e).toLinearEquiv (kernelOperator A I g)
  rw [Representation.Equiv.conj_apply_self] at h
  exact h.symm

theorem rationalLFactor_eq_of_equiv (e : WeilDeligneRepresentation.Equiv A B) (g : G) :
    rationalLFactor A I g = rationalLFactor B I g := by
  change (algebraMap K[X] (RatFunc K) (eulerPolynomial A I g))⁻¹ =
    (algebraMap K[X] (RatFunc K) (eulerPolynomial B I g))⁻¹
  rw [eulerPolynomial_eq_of_equiv I e]

theorem quotientDeterminant_eq_of_equiv (e : WeilDeligneRepresentation.Equiv A B) (g : G) :
    quotientDeterminant A I g = quotientDeterminant B I g := by
  have hc := Representation.Equiv.conj_apply_self g (quotientEquiv I e)
  have hd := LinearMap.det_conj (-quotientOperator A I g) (quotientEquiv I e).toLinearEquiv
  change LinearMap.det ((quotientEquiv I e).toLinearEquiv.conj
    (-quotientOperator A I g)) = quotientDeterminant A I g at hd
  rw [map_neg, hc] at hd
  exact hd.symm

theorem quotientCorrectionPolynomial_eq_of_equiv
    (e : WeilDeligneRepresentation.Equiv A B) (g : G) :
    quotientCorrectionPolynomial A I g = quotientCorrectionPolynomial B I g := by
  simp only [quotientCorrectionPolynomial, conductorCorrection_eq_of_equiv I e,
    quotientDeterminant_eq_of_equiv I e]

theorem quotientCorrection_eq_of_equiv
    (e : WeilDeligneRepresentation.Equiv A B) (g : G) :
    quotientCorrection A I g = quotientCorrection B I g := by
  unfold quotientCorrection
  rw [quotientCorrectionPolynomial_eq_of_equiv I e]

end Morphisms

section Cosets

private theorem action_eq_of_coset
    {V : Type uV} [AddCommGroup V] [Module K V] (ρ : Representation K G V)
    (I : Subgroup G) [Representation.IsTrivial (ρ.comp I.subtype)]
    {g h : G} (hi : h * g⁻¹ ∈ I) : ρ h = ρ g := by
  have ht : ρ (h * g⁻¹) = 1 :=
    Representation.isTrivial_def (ρ.comp I.subtype) ⟨h * g⁻¹, hi⟩
  have hm := congrArg (fun f : Module.End K V => f * ρ g) ht
  simpa only [← map_mul, inv_mul_cancel_right, one_mul] using hm

/-- The induced quotient operator depends only on the element's inertia coset. -/
theorem quotientOperator_eq_of_coset (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] {g h : G} (hi : h * g⁻¹ ∈ I) :
    quotientOperator A I h = quotientOperator A I g :=
  action_eq_of_coset (quotientRepresentation A I).representation I hi

/-- The operator on the inertia-fixed monodromy kernel depends only on that coset. -/
theorem kernelOperator_eq_of_coset (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] {g h : G} (hi : h * g⁻¹ ∈ I) :
    kernelOperator A I h = kernelOperator A I g := by
  let : Representation.IsTrivial
      ((A.inertiaKernelRepresentation I).representation.comp I.subtype) :=
    inferInstanceAs (Representation.IsTrivial
      ((FiniteRepresentation.invariants I A.kernelRepresentation).representation.comp I.subtype))
  exact action_eq_of_coset (A.inertiaKernelRepresentation I).representation I hi

theorem rationalLFactor_eq_of_coset (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] {g h : G} (hi : h * g⁻¹ ∈ I) :
    rationalLFactor A I h = rationalLFactor A I g := by
  unfold rationalLFactor
  rw [kernelOperator_eq_of_coset A I hi]

theorem quotientDeterminant_eq_of_coset (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] {g h : G} (hi : h * g⁻¹ ∈ I) :
    quotientDeterminant A I h = quotientDeterminant A I g := by
  unfold quotientDeterminant
  rw [quotientOperator_eq_of_coset A I hi]

theorem quotientCorrection_eq_of_coset (A : WeilDeligneRepresentation K G ν)
    (I : Subgroup G) [I.Normal] {g h : G} (hi : h * g⁻¹ ∈ I) :
    quotientCorrection A I h = quotientCorrection A I g := by
  unfold quotientCorrection quotientCorrectionPolynomial
  rw [quotientDeterminant_eq_of_coset A I hi]

end Cosets

section ZeroMonodromy

theorem kernelInInvariants_eq_top_of_monodromy_zero
    (A : WeilDeligneRepresentation K G ν) (I : Subgroup G) [I.Normal]
    (hN : A.monodromy = 0) : kernelInInvariants A I = ⊤ := by
  ext x
  simp [mem_kernelInInvariants, hN]

theorem conductorCorrection_eq_zero_of_monodromy_zero
    (A : WeilDeligneRepresentation K G ν) (I : Subgroup G) [I.Normal]
    (hN : A.monodromy = 0) : conductorCorrection A I = 0 := by
  change Module.finrank K ((inertiaRepresentation A I) ⧸ kernelInInvariants A I) = 0
  rw [kernelInInvariants_eq_top_of_monodromy_zero A I hN]
  rw [Submodule.finrank_quotient, finrank_top, Nat.sub_self]

theorem quotientDeterminant_eq_one_of_monodromy_zero
    (A : WeilDeligneRepresentation K G ν) (I : Subgroup G) [I.Normal]
    (hN : A.monodromy = 0) (g : G) : quotientDeterminant A I g = 1 := by
  let : Subsingleton (quotientRepresentation A I) :=
    Submodule.Quotient.subsingleton_iff.mpr
      (kernelInInvariants_eq_top_of_monodromy_zero A I hN)
  have h : -quotientOperator A I g = 1 := Subsingleton.elim _ _
  simp only [quotientDeterminant, h, map_one]

theorem quotientCorrection_eq_one_of_monodromy_zero
    (A : WeilDeligneRepresentation K G ν) (I : Subgroup G) [I.Normal]
    (hN : A.monodromy = 0) (g : G) : quotientCorrection A I g = 1 := by
  simp [quotientCorrection, quotientCorrectionPolynomial,
    conductorCorrection_eq_zero_of_monodromy_zero A I hN,
    quotientDeterminant_eq_one_of_monodromy_zero A I hN]

end ZeroMonodromy

section IsomorphismClasses

/-- The conductor correction descends to actual pair-isomorphism classes. -/
def conductorCorrectionClass (I : Subgroup G) [I.Normal] :
    WeilDeligneRepresentation.IsomorphismClasses.{uK, uG, uV} K G ν → ℕ :=
  Quotient.lift (fun A => conductorCorrection A I)
    (fun _ _ ⟨e⟩ => conductorCorrection_eq_of_equiv I e)

/-- The rational L-factor descends to actual pair-isomorphism classes. -/
def rationalLFactorClass (I : Subgroup G) [I.Normal] (g : G) :
    WeilDeligneRepresentation.IsomorphismClasses.{uK, uG, uV} K G ν → RatFunc K :=
  Quotient.lift (fun A => rationalLFactor A I g)
    (fun _ _ ⟨e⟩ => rationalLFactor_eq_of_equiv I e g)

/-- The constant quotient determinant descends to actual pair-isomorphism classes. -/
def quotientDeterminantClass (I : Subgroup G) [I.Normal] (g : G) :
    WeilDeligneRepresentation.IsomorphismClasses.{uK, uG, uV} K G ν → K :=
  Quotient.lift (fun A => quotientDeterminant A I g)
    (fun _ _ ⟨e⟩ => quotientDeterminant_eq_of_equiv I e g)

/-- The rational quotient correction descends to actual pair-isomorphism classes. -/
def quotientCorrectionClass (I : Subgroup G) [I.Normal] (g : G) :
    WeilDeligneRepresentation.IsomorphismClasses.{uK, uG, uV} K G ν → RatFunc K :=
  Quotient.lift (fun A => quotientCorrection A I g)
    (fun _ _ ⟨e⟩ => quotientCorrection_eq_of_equiv I e g)

@[simp]
theorem rationalLFactorClass_classOf
    (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (I : Subgroup G) [I.Normal] (g : G) :
    rationalLFactorClass I g (WeilDeligneRepresentation.classOf A) =
      rationalLFactor A I g := rfl

@[simp]
theorem quotientCorrectionClass_classOf
    (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (I : Subgroup G) [I.Normal] (g : G) :
    quotientCorrectionClass I g (WeilDeligneRepresentation.classOf A) =
      quotientCorrection A I g := rfl

end IsomorphismClasses

section Spectral

variable {G : Type uG} [Group G] {ν : G →* ℂˣ}

/-- The regular spectral domain, with explicit positive residue-cardinality input. -/
abbrev SpectralRegularPoint (A : WeilDeligneRepresentation ℂ G ν)
    (I : Subgroup G) [I.Normal] (g : G) (q : ℝ) (hq : 0 < q) :=
  LocalFactor.SpectralRegularPoint (kernelOperator A I g) q hq

/-- At a regular point, the actual spectral factor is evaluated at `q^(-s)`. -/
def spectralLValue (A : WeilDeligneRepresentation ℂ G ν)
    (I : Subgroup G) [I.Normal] (g : G) (q : ℝ) (hq : 0 < q)
    (s : SpectralRegularPoint A I g q hq) : ℂˣ :=
  LocalFactor.spectralFactorValue (kernelOperator A I g) q hq s

theorem spectralLValue_det (A : WeilDeligneRepresentation ℂ G ν)
    (I : Subgroup G) [I.Normal] (g : G) (q : ℝ) (hq : 0 < q)
    (s : SpectralRegularPoint A I g q hq) :
    (spectralLValue A I g q hq s : ℂ) =
      (LinearMap.det (1 - (Complex.exp (-s.val * (Real.log q : ℂ))) •
        kernelOperator A I g))⁻¹ :=
  LocalFactor.spectralFactorValue_det _ _ _ _

end Spectral

end Langlands.LocalFactor.WeilDeligne
