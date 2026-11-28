import Langlands.Algebra.CentralSimple.NumberFieldLocalGlobalEmbeddingStatement
import Langlands.Algebra.NumberFieldBrauerSplitting
import Langlands.Algebra.ReducedCharpolyFromSplitFactors
import Langlands.Algebra.ReducedCharpolyRootSplitting

/-! # The local–global principle for embeddings of maximal subfields: proof

`Langlands.CentralSimple.numberFieldLocalGlobalEmbedding` proves
`NumberFieldLocalGlobalEmbeddingStatement`. The local splitting step
`LocalGlobalEmbedding.isSplit_of_local` shows that an injective local embedding of
`K ⊗[F] P` into `K ⊗[F] B` that is the identity on `E` splits `M ⊗[E] B` for every field
`M` over `K` and `E` containing a root of the minimal polynomial of a generator of `P/E`.
Brauer–Hasse–Noether over the factor fields of that polynomial and the realization of
separable polynomials as reduced characteristic polynomials then give the global
embedding. -/

noncomputable section

universe u

open Polynomial
open scoped TensorProduct

namespace Langlands.CentralSimple.LocalGlobalEmbedding

section Descend

variable (F E : Type u) [Field F] [Field E] [Algebra F E]
variable (L : Type u) [Field L] [Algebra E L] [Algebra F L] [IsScalarTower F E L]
variable (X : Type u) [Ring X] [Algebra E X] [Algebra F X] [IsScalarTower F E X]

/-- The natural surjection `L ⊗[F] X → L ⊗[E] X`, `l ⊗ x ↦ l ⊗ x`. -/
def descend : L ⊗[F] X →ₐ[L] L ⊗[E] X :=
  Algebra.TensorProduct.lift Algebra.TensorProduct.includeLeft
    ((Algebra.TensorProduct.includeRight : X →ₐ[E] L ⊗[E] X).restrictScalars F)
    (fun l x => by
      simp only [Commute, SemiconjBy, Algebra.TensorProduct.includeLeft_apply,
        AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul])

@[simp] theorem descend_tmul (l : L) (x : X) :
    descend F E L X (l ⊗ₜ[F] x) = l ⊗ₜ[E] x := by
  change (l ⊗ₜ[E] (1 : X)) * ((1 : L) ⊗ₜ[E] x) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The map `L ⊗[F] E → L ⊗[F] X` induced by the structure map `E → X`. -/
def incl : L ⊗[F] E →ₐ[L] L ⊗[F] X :=
  Algebra.TensorProduct.map (AlgHom.id L L) (IsScalarTower.toAlgHom F E X)

omit [Algebra E L] [IsScalarTower F E L] in
@[simp] theorem incl_tmul (l : L) (e : E) :
    incl F E L X (l ⊗ₜ[F] e) = l ⊗ₜ[F] algebraMap E X e := by
  simp [incl]

omit [Algebra F L] [IsScalarTower F E L] [Algebra F X] [IsScalarTower F E X] in
/-- In `L ⊗[E] X` the two images of `E` agree. -/
theorem one_tmul_algebraMap (e : E) :
    (1 : L) ⊗ₜ[E] algebraMap E X e = algebraMap L (L ⊗[E] X) (algebraMap E L e) := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one e,
    ← TensorProduct.smul_tmul, Algebra.algebraMap_self_apply, Algebra.smul_def, mul_one]

end Descend

section Idempotent

variable (F E : Type u) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  [Algebra.IsSeparable F E]
variable (L : Type u) [Field L] [Algebra E L] [Algebra F L] [IsScalarTower F E L]

/-- The primitive element of `E/F` used to split `L ⊗[F] E`. -/
abbrev prim : E := (Field.powerBasisOfFiniteOfSeparable F E).gen

/-- The cofactor `h` in `g = (X - α) h` over `L`, for the minimal polynomial `g` of the
primitive element `α` and its image in `L`. -/
def cofactor : L[X] :=
  ((minpoly F (prim F E)).map (algebraMap F L)) /ₘ (X - C (algebraMap E L (prim F E)))

theorem isRoot_minpoly_map :
    IsRoot ((minpoly F (prim F E)).map (algebraMap F L)) (algebraMap E L (prim F E)) := by
  rw [IsRoot, eval_map_algebraMap, aeval_algebraMap_apply, minpoly.aeval, map_zero]

theorem X_sub_C_mul_cofactor :
    (X - C (algebraMap E L (prim F E))) * cofactor F E L =
      (minpoly F (prim F E)).map (algebraMap F L) :=
  mul_divByMonic_eq_iff_isRoot.mpr (isRoot_minpoly_map F E L)

theorem cofactor_eval_ne_zero :
    (cofactor F E L).eval (algebraMap E L (prim F E)) ≠ 0 := by
  intro h0
  have hsep : ((minpoly F (prim F E)).map (algebraMap F L)).Separable :=
    Polynomial.Separable.map (Algebra.IsSeparable.isSeparable F (prim F E))
  have hz := hsep.eval₂_derivative_ne_zero (RingHom.id L) (x := algebraMap E L (prim F E))
    (by rw [eval₂_id]; exact isRoot_minpoly_map F E L)
  apply hz
  rw [eval₂_id, ← X_sub_C_mul_cofactor F E L, derivative_mul]
  simp [h0]

/-- The idempotent `h(1 ⊗ α) / h(α)` of `L ⊗[F] E`. It cuts out the factor `L` of
`L ⊗[F] E` given by the multiplication map `L ⊗[F] E → L`. -/
def idem : L ⊗[F] E :=
  ((cofactor F E L).eval (algebraMap E L (prim F E)))⁻¹ •
    aeval ((1 : L) ⊗ₜ[F] prim F E) (cofactor F E L)

/-- The idempotent annihilates `1 ⊗ α - α ⊗ 1`. -/
theorem idem_mul_sub :
    idem F E L * ((1 : L) ⊗ₜ[F] prim F E -
      algebraMap L (L ⊗[F] E) (algebraMap E L (prim F E))) = 0 := by
  have h1 : aeval ((1 : L) ⊗ₜ[F] prim F E) (minpoly F (prim F E)) = 0 := by
    have := aeval_algHom_apply
      (Algebra.TensorProduct.includeRight : E →ₐ[F] L ⊗[F] E) (prim F E) (minpoly F (prim F E))
    rw [minpoly.aeval, map_zero] at this
    exact this
  have h2 : aeval ((1 : L) ⊗ₜ[F] prim F E) ((minpoly F (prim F E)).map (algebraMap F L)) = 0 := by
    rw [aeval_map_algebraMap, h1]
  rw [← X_sub_C_mul_cofactor F E L, aeval_mul] at h2
  simp only [aeval_sub, aeval_X, aeval_C] at h2
  rw [idem, smul_mul_assoc, mul_comm (aeval _ _) _, h2, smul_zero]

/-- After multiplication by the idempotent, the two images of `E` in `L ⊗[F] E` agree. -/
theorem idem_mul_tmul (e : E) :
    idem F E L * ((1 : L) ⊗ₜ[F] e) = idem F E L * (algebraMap E L e ⊗ₜ[F] 1) := by
  obtain ⟨q, rfl⟩ := (Field.powerBasisOfFiniteOfSeparable F E).exists_eq_aeval' e
  set t : L ⊗[F] E := (1 : L) ⊗ₜ[F] prim F E
  set s : L ⊗[F] E := algebraMap L (L ⊗[F] E) (algebraMap E L (prim F E))
  have ht : (1 : L) ⊗ₜ[F] aeval (prim F E) q = aeval t q := by
    have := aeval_algHom_apply
      (Algebra.TensorProduct.includeRight : E →ₐ[F] L ⊗[F] E) (prim F E) q
    exact this.symm
  have hs : algebraMap E L (aeval (prim F E) q) ⊗ₜ[F] (1 : E) = aeval s q := by
    rw [aeval_algebraMap_apply, aeval_algebraMap_apply]
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
  rw [ht, hs]
  obtain ⟨c, hc⟩ := sub_dvd_eval_sub t s (q.map (algebraMap F (L ⊗[F] E)))
  rw [eval_map_algebraMap, eval_map_algebraMap] at hc
  rw [← sub_eq_zero, ← mul_sub, hc, ← mul_assoc, idem_mul_sub, zero_mul]

/-- An `L`-algebra map that sends `1 ⊗ α` to `α` sends the idempotent to `1`. -/
theorem idem_map_eq_one {R : Type u} [Ring R] [Algebra L R] (χ : L ⊗[F] E →ₐ[L] R)
    (hχ : χ ((1 : L) ⊗ₜ[F] prim F E) = algebraMap L R (algebraMap E L (prim F E))) :
    χ (idem F E L) = 1 := by
  rw [idem, map_smul, ← aeval_algHom_apply, hχ, aeval_algebraMap_apply, coe_aeval_eq_eval,
    Algebra.smul_def, ← map_mul, inv_mul_cancel₀ (cofactor_eval_ne_zero F E L), map_one]

end Idempotent

section Section

variable (F E : Type u) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  [Algebra.IsSeparable F E]
variable (L : Type u) [Field L] [Algebra E L] [Algebra F L] [IsScalarTower F E L]
variable (X : Type u) [Ring X] [Algebra E X] [Algebra F X] [IsScalarTower F E X]

/-- The image of the idempotent in `L ⊗[F] X` identifies the two images of `E`. -/
theorem incl_idem_mul_tmul (e : E) :
    incl F E L X (idem F E L) * ((1 : L) ⊗ₜ[F] algebraMap E X e) =
      incl F E L X (idem F E L) * (algebraMap E L e ⊗ₜ[F] 1) := by
  have h := congrArg (incl F E L X) (idem_mul_tmul F E L e)
  simpa only [map_mul, incl_tmul, map_one] using h

/-- The additive map `L ⊗[E] X → L ⊗[F] X`, `l ⊗ x ↦ ε (l ⊗ x)`, for the image `ε` of the
idempotent. It is well defined by `incl_idem_mul_tmul`. -/
def cut : L ⊗[E] X →+ L ⊗[F] X :=
  TensorProduct.liftAddHom
    { toFun := fun l =>
        { toFun := fun x => incl F E L X (idem F E L) * (l ⊗ₜ[F] x)
          map_zero' := by simp
          map_add' := fun x y => by simp [TensorProduct.tmul_add, mul_add] }
      map_zero' := by ext; simp
      map_add' := fun l m => by ext; simp [TensorProduct.add_tmul, mul_add] }
    (fun e l x => by
      change incl F E L X (idem F E L) * ((e • l) ⊗ₜ[F] x) =
        incl F E L X (idem F E L) * (l ⊗ₜ[F] (e • x))
      have h1 : (e • l) ⊗ₜ[F] x = (algebraMap E L e ⊗ₜ[F] (1 : X)) * (l ⊗ₜ[F] x) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.smul_def]
      have h2 : l ⊗ₜ[F] (e • x) = ((1 : L) ⊗ₜ[F] algebraMap E X e) * (l ⊗ₜ[F] x) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.smul_def]
      rw [h1, h2, ← mul_assoc, ← mul_assoc, incl_idem_mul_tmul])

/-- Composing `cut` with `descend` is multiplication by the image of the idempotent, so the
kernel of `descend` is killed by the idempotent. -/
theorem cut_descend (y : L ⊗[F] X) :
    cut F E L X (descend F E L X y) = incl F E L X (idem F E L) * y := by
  induction y using TensorProduct.inductionOn with
  | tmul l x => rw [descend_tmul]; rfl
  | add y z hy hz => rw [map_add, map_add, hy, hz, mul_add]

end Section

section Field

variable {F E B P : Type u} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  [Algebra.IsSeparable F E]
  [Ring B] [Algebra E B] [Algebra F B] [IsScalarTower F E B]
  [FiniteDimensional E B] [Algebra.IsCentral E B] [IsSimpleRing B]
  [Field P] [Algebra E P] [Algebra F P] [IsScalarTower F E P]

/-- The power basis `1 ⊗ θ^i` of `L ⊗[E] P`. -/
def tensorPowerBasis (L : Type u) [Field L] [Algebra E L] (pb : PowerBasis E P) :
    PowerBasis L (L ⊗[E] P) where
  gen := (1 : L) ⊗ₜ[E] pb.gen
  dim := pb.dim
  basis := Algebra.TensorProduct.basis L pb.basis
  basis_eq_pow i := by
    rw [Algebra.TensorProduct.basis_apply, pb.basis_eq_pow, Algebra.TensorProduct.tmul_pow,
      one_pow]

omit [FiniteDimensional F E] [Algebra.IsSeparable F E] [FiniteDimensional E B]
  [Algebra.IsCentral E B] [IsSimpleRing B] in
theorem tensorPowerBasis_gen (L : Type u) [Field L] [Algebra E L] (pb : PowerBasis E P) :
    (tensorPowerBasis L pb).gen = (1 : L) ⊗ₜ[E] pb.gen := rfl

omit [FiniteDimensional F E] [Algebra.IsSeparable F E] [FiniteDimensional E B]
  [Algebra.IsCentral E B] [IsSimpleRing B] in
theorem tensorPowerBasis_dim (L : Type u) [Field L] [Algebra E L] (pb : PowerBasis E P) :
    (tensorPowerBasis L pb).dim = pb.dim := rfl

/-- An injective embedding over a field `L` that contains a root of the minimal polynomial
splits `L ⊗[E] B`. -/
theorem isSplit_of_embedding (pb : PowerBasis E P) (hsep : (minpoly E pb.gen).Separable)
    (hdim : Module.finrank E B = pb.dim ^ 2)
    (L : Type u) [Field L] [Algebra E L] [Algebra F L] [IsScalarTower F E L]
    (φ : L ⊗[F] P →ₐ[L] L ⊗[F] B) (hφ : Function.Injective φ)
    (hE : ∀ e : E, φ ((1 : L) ⊗ₜ[F] algebraMap E P e) = (1 : L) ⊗ₜ[F] algebraMap E B e)
    (r : L) (hr : aeval r (minpoly E pb.gen) = 0) :
    Brauer.IsSplit (Brauer.baseChange L ({ toAlgCat := AlgCat.of E B } : CSA.{u, u} E)) := by
  let := isSimpleRing_baseChange E B L
  let := isCentral_baseChange E B L
  set θ := pb.gen
  set a : L ⊗[E] B := descend F E L B (φ ((1 : L) ⊗ₜ[F] θ)) with ha
  have hφincl : φ.comp (incl F E L P) = incl F E L B := by
    apply Algebra.TensorProduct.ext'
    intro l e
    rw [AlgHom.comp_apply, incl_tmul, incl_tmul, ← mul_one l, ← smul_eq_mul,
      ← TensorProduct.smul_tmul', map_smul, hE, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hidem : φ (incl F E L P (idem F E L)) = incl F E L B (idem F E L) := by
    rw [← AlgHom.comp_apply, hφincl]
  have hdesc : descend F E L P (incl F E L P (idem F E L)) = 1 := by
    apply idem_map_eq_one F E L ((descend F E L P).comp (incl F E L P))
    rw [AlgHom.comp_apply, incl_tmul, descend_tmul, one_tmul_algebraMap]
  have hA : ∀ q : L[X], aeval a q = 0 → aeval ((1 : L) ⊗ₜ[E] θ) q = 0 := by
    intro q hq
    have h1 : aeval a q = descend F E L B (φ (aeval ((1 : L) ⊗ₜ[F] θ) q)) := by
      rw [aeval_algHom_apply, aeval_algHom_apply]
    have h2 : incl F E L B (idem F E L) * φ (aeval ((1 : L) ⊗ₜ[F] θ) q) = 0 := by
      rw [← cut_descend, ← h1, hq, map_zero]
    rw [← hidem, ← map_mul] at h2
    have h3 := (map_eq_zero_iff φ hφ).mp h2
    have h4 := congrArg (descend F E L P) h3
    rwa [map_mul, hdesc, one_mul, ← aeval_algHom_apply, descend_tmul, map_zero] at h4
  let κ : P →ₐ[E] L ⊗[E] B :=
    { toRingHom := ((descend F E L B).toRingHom.comp φ.toRingHom).comp
        (Algebra.TensorProduct.includeRight : P →ₐ[F] L ⊗[F] P).toRingHom
      commutes' := fun e => by
        change descend F E L B (φ ((1 : L) ⊗ₜ[F] algebraMap E P e)) = _
        rw [hE, descend_tmul, one_tmul_algebraMap, ← IsScalarTower.algebraMap_apply] }
  have hκ : κ θ = a := rfl
  have hfa : aeval a (minpoly E θ) = 0 := by
    rw [← hκ, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hint : IsIntegral L a := IsIntegral.of_finite L a
  have hm1 : pb.dim ≤ (minpoly L a).natDegree :=
    (tensorPowerBasis L pb).dim_le_natDegree_of_root (minpoly.ne_zero hint)
      (hA _ (minpoly.aeval L a))
  set fL := (minpoly E θ).map (algebraMap E L) with hfL
  have hfLm : fL.Monic := (minpoly.monic pb.isIntegral_gen).map _
  have hfLd : fL.natDegree = pb.dim := by rw [natDegree_map, pb.natDegree_minpoly]
  have hfLa : aeval a fL = 0 := by rw [aeval_map_algebraMap, hfa]
  have hmf : fL = minpoly L a :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hfLm (minpoly.dvd L a hfLa)
      (by rw [hfLd]; exact hm1)
  have hdeg : reducedDegree E B = pb.dim := by
    rw [reducedDegree, hdim, Nat.sqrt_eq']
  have hc1 := reducedCharpoly_monic L (L ⊗[E] B) a
  have hc2 : (reducedCharpoly L (L ⊗[E] B) a).natDegree = pb.dim := by
    rw [reducedCharpoly_natDegree, reducedDegree_baseChange, hdeg]
  have hc3 : aeval a (reducedCharpoly L (L ⊗[E] B) a) = 0 := aeval_reducedCharpoly a
  have hcm : reducedCharpoly L (L ⊗[E] B) a = minpoly L a :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hc1 (minpoly.dvd L a hc3)
      (by rw [hc2]; exact hm1)
  have hcf : reducedCharpoly L (L ⊗[E] B) a = fL := hcm.trans hmf.symm
  have hs : fL.Separable := hsep.map
  have hrL : IsRoot fL r := by rw [IsRoot, hfL, eval_map_algebraMap, hr]
  have hmult : (reducedCharpoly L (L ⊗[E] B) a).rootMultiplicity r = 1 := by
    rw [hcf]
    exact le_antisymm (rootMultiplicity_le_one_of_separable hs r)
      ((rootMultiplicity_pos hs.ne_zero).mpr hrL)
  exact isSplit_of_simple_root (Brauer.baseChange L ({ toAlgCat := AlgCat.of E B } : CSA.{u, u} E))
    a r hmult

omit [Algebra F E] [IsScalarTower F E B] [IsScalarTower F E P] [FiniteDimensional F E]
  [Algebra.IsSeparable F E] [FiniteDimensional E B] [Algebra.IsCentral E B]
  [IsSimpleRing B] in
/-- Scalar extension of an injective embedding along a field extension `L/K`. -/
theorem exists_baseChange_embedding (K : Type u) [Field K] [Algebra F K]
    (φ : K ⊗[F] P →ₐ[K] K ⊗[F] B) (hφ : Function.Injective φ)
    (hE : ∀ e : E, φ ((1 : K) ⊗ₜ[F] algebraMap E P e) = (1 : K) ⊗ₜ[F] algebraMap E B e)
    (L : Type u) [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L] :
    ∃ ψ : L ⊗[F] P →ₐ[L] L ⊗[F] B, Function.Injective ψ ∧
      ∀ e : E, ψ ((1 : L) ⊗ₜ[F] algebraMap E P e) = (1 : L) ⊗ₜ[F] algebraMap E B e := by
  let τ (Y : Type u) [Ring Y] [Algebra F Y] : L ⊗[K] (K ⊗[F] Y) ≃ₐ[L] L ⊗[F] Y :=
    (Algebra.TensorProduct.assoc F K L L K Y).symm.trans
      (Algebra.TensorProduct.congr (Algebra.TensorProduct.rid K L L) AlgEquiv.refl)
  have hτ (Y : Type u) [Ring Y] [Algebra F Y] (l : L) (k : K) (y : Y) :
      τ Y (l ⊗ₜ[K] (k ⊗ₜ[F] y)) = (k • l) ⊗ₜ[F] y := by
    simp [τ]
  have hτs (Y : Type u) [Ring Y] [Algebra F Y] (y : Y) :
      (τ Y).symm ((1 : L) ⊗ₜ[F] y) = (1 : L) ⊗ₜ[K] ((1 : K) ⊗ₜ[F] y) := by
    apply (τ Y).injective
    rw [AlgEquiv.apply_symm_apply, hτ, one_smul]
  let μ : L ⊗[K] (K ⊗[F] P) →ₐ[L] L ⊗[K] (K ⊗[F] B) :=
    Algebra.TensorProduct.map (AlgHom.id L L) φ
  have hμ : Function.Injective μ := by
    have h := Module.Flat.lTensor_preserves_injective_linearMap (M := L) φ.toLinearMap hφ
    have heq : (μ : L ⊗[K] (K ⊗[F] P) → L ⊗[K] (K ⊗[F] B)) = φ.toLinearMap.lTensor L := by
      funext y
      induction y using TensorProduct.inductionOn with
      | tmul l x => simp [μ]
      | add y z hy hz => rw [map_add, map_add, hy, hz]
    rw [heq]
    exact h
  refine ⟨((τ B).toAlgHom.comp μ).comp (τ P).symm.toAlgHom,
    (τ B).injective.comp (hμ.comp (τ P).symm.injective), fun e => ?_⟩
  change τ B (μ ((τ P).symm ((1 : L) ⊗ₜ[F] algebraMap E P e))) = _
  rw [hτs, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hE, hτ, one_smul]

/-- **Local splitting.** An injective embedding over a field `K` and a field `M` over `K` and
`E` containing a root of the minimal polynomial split `M ⊗[E] B`. -/
theorem isSplit_of_local (pb : PowerBasis E P) (hsep : (minpoly E pb.gen).Separable)
    (hdim : Module.finrank E B = pb.dim ^ 2)
    (K : Type u) [Field K] [Algebra F K]
    (φ : K ⊗[F] P →ₐ[K] K ⊗[F] B) (hφ : Function.Injective φ)
    (hE : ∀ e : E, φ ((1 : K) ⊗ₜ[F] algebraMap E P e) = (1 : K) ⊗ₜ[F] algebraMap E B e)
    (M : Type u) [Field M] [Algebra E M] [Algebra K M]
    (hKM : ∀ x : F, algebraMap K M (algebraMap F K x) = algebraMap E M (algebraMap F E x))
    (r : M) (hr : aeval r (minpoly E pb.gen) = 0) :
    Brauer.IsSplit (Brauer.baseChange M ({ toAlgCat := AlgCat.of E B } : CSA.{u, u} E)) := by
  let : Algebra F M := ((algebraMap E M).comp (algebraMap F E)).toAlgebra
  have : IsScalarTower F E M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower F K M := IsScalarTower.of_algebraMap_eq fun x => (hKM x).symm
  obtain ⟨ψ, hψ, hψE⟩ := exists_baseChange_embedding K φ hφ hE M
  exact isSplit_of_embedding pb hsep hdim M ψ hψ hψE r hr

end Field

section Global

open NumberField IsDedekindDomain
open scoped NumberField.LiesOver Langlands.Global.AdelicFunctoriality.FiniteExtension

variable {F E B P : Type u} [Field F] [NumberField F] [Field E] [Algebra F E]
  [FiniteDimensional F E]
  [Ring B] [Algebra E B] [Algebra F B] [IsScalarTower F E B]
  [FiniteDimensional E B] [Algebra.IsCentral E B] [IsSimpleRing B]
  [Field P] [Algebra E P] [Algebra F P] [IsScalarTower F E P]

/-- Under the local hypotheses of the target statement, the field obtained by adjoining a
root of any irreducible factor of the minimal polynomial of the generator splits `B`. The
proof applies Brauer–Hasse–Noether over that number field and `isSplit_of_local` at each of
its places. -/
theorem isSplit_adjoinRoot [Algebra.IsSeparable F E] (pb : PowerBasis E P)
    (hsep : (minpoly E pb.gen).Separable) (hdim : Module.finrank E B = pb.dim ^ 2)
    (hloc : ∀ v : Global.Place F,
      ∃ φ : Global.placeCompletion F v ⊗[F] P →ₐ[Global.placeCompletion F v]
          Global.placeCompletion F v ⊗[F] B,
        Function.Injective φ ∧
          ∀ e : E, φ ((1 : Global.placeCompletion F v) ⊗ₜ[F] algebraMap E P e) =
            (1 : Global.placeCompletion F v) ⊗ₜ[F] algebraMap E B e)
    (p : E[X]) [hp : Fact (Irreducible p)] (hpf : p ∣ minpoly E pb.gen) :
    Brauer.IsSplit (Brauer.baseChange (AdjoinRoot p)
      ({ toAlgCat := AlgCat.of E B } : CSA.{u, u} E)) := by
  let A : CSA.{u, u} E := { toAlgCat := AlgCat.of E B }
  let L := AdjoinRoot p
  have : FiniteDimensional E L := (AdjoinRoot.powerBasis hp.out.ne_zero).finite
  have : FiniteDimensional F L := Module.Finite.trans E L
  have : NumberField L := NumberField.of_module_finite F L
  have hroot (M : Type u) [Field M] [Algebra E M] [Algebra L M] [IsScalarTower E L M] :
      aeval (algebraMap L M (AdjoinRoot.root p)) (minpoly E pb.gen) = 0 := by
    obtain ⟨q, hq⟩ := hpf
    rw [aeval_algebraMap_apply, hq, aeval_mul, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self,
      zero_mul, map_zero]
  have htransfer (M : Type u) [Field M] [Algebra E M] [Algebra L M] [IsScalarTower E L M]
      (h : Brauer.IsSplit (Brauer.baseChange M A)) :
      Brauer.IsSplit (Brauer.baseChange M (Brauer.baseChange L A)) := by
    obtain ⟨n, hn, ⟨e⟩⟩ := h
    exact ⟨n, hn, ⟨(Brauer.baseChangeTowerEquiv L M A).trans e⟩⟩
  apply Brauer.numberFieldBrauerSplitting L (Brauer.baseChange L A)
  · intro w
    let v := Langlands.ClassFieldTheory.Global.placeBelow F w
    let : w.asIdeal.LiesOver v.asIdeal := Langlands.ClassFieldTheory.Global.liesOver_placeBelow F w
    let K := v.adicCompletion F
    let M := w.adicCompletion L
    let : Algebra E M := ((algebraMap L M).comp (algebraMap E L)).toAlgebra
    have : IsScalarTower E L M := IsScalarTower.of_algebraMap_eq fun _ => rfl
    apply htransfer M
    obtain ⟨φ, hφ, hφE⟩ := hloc (.inr v)
    refine isSplit_of_local pb hsep hdim K φ hφ hφE M (fun x => ?_) _ (hroot M)
    change Langlands.Global.AdelicFunctoriality.FiniteExtension.completionMap v w
      (algebraMap F K x) = algebraMap L M (algebraMap E L (algebraMap F E x))
    rw [Langlands.Global.AdelicFunctoriality.FiniteExtension.completionMap_coe,
      ← IsScalarTower.algebraMap_apply F E L]
  · intro w
    let v := w.comap (algebraMap F L)
    let : w.LiesOver v := ⟨rfl⟩
    let K := v.Completion
    let M := w.Completion
    let : Algebra E M := ((algebraMap L M).comp (algebraMap E L)).toAlgebra
    have : IsScalarTower E L M := IsScalarTower.of_algebraMap_eq fun _ => rfl
    apply htransfer M
    obtain ⟨φ, hφ, hφE⟩ := hloc (.inl v)
    refine isSplit_of_local pb hsep hdim K φ hφ hφE M (fun x => ?_) _ (hroot M)
    change NumberField.LiesOver.completionMap v w (algebraMap F K x) =
      algebraMap L M (algebraMap E L (algebraMap F E x))
    rw [← IsScalarTower.algebraMap_apply F E L]
    exact NumberField.LiesOver.completionMap_coe (v := v) (w := w) (WithAbs.toAbs v.1 x)

end Global

end Langlands.CentralSimple.LocalGlobalEmbedding

namespace Langlands.CentralSimple

open Polynomial LocalGlobalEmbedding

/-- **The local–global principle for embeddings of maximal subfields** over number fields. -/
theorem numberFieldLocalGlobalEmbedding : NumberFieldLocalGlobalEmbeddingStatement.{u} := by
  intro F E B P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hdim hloc
  have : NumberField E := NumberField.of_module_finite F E
  let pb := Field.powerBasisOfFiniteOfSeparable E P
  have hsep : (minpoly E pb.gen).Separable := Algebra.IsSeparable.isSeparable E pb.gen
  have hdim' : Module.finrank E B = pb.dim ^ 2 := by rw [hdim, pb.finrank]
  let A : CSA.{u, u} E := { toAlgCat := AlgCat.of E B }
  have hred : reducedDegree E A = pb.dim := by
    change Nat.sqrt (Module.finrank E B) = pb.dim
    rw [hdim', Nat.sqrt_eq']
  obtain ⟨a, ha⟩ := exists_reducedCharpoly_eq_of_split_factors A (minpoly E pb.gen)
    (minpoly.monic pb.isIntegral_gen) hsep (by rw [pb.natDegree_minpoly, hred])
    (fun p _ hp hpf => by
      let : Fact (Irreducible p) := ⟨hp⟩
      exact isSplit_adjoinRoot pb hsep hdim' hloc p hpf)
  have haeval : aeval a (minpoly E pb.gen) = 0 := by
    rw [← ha]
    exact aeval_reducedCharpoly a
  exact ⟨pb.lift a haeval⟩

end Langlands.CentralSimple
