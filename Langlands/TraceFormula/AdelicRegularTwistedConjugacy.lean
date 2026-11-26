import Langlands.BaseChange.CyclicBasisTwistedIntertwiner
import Langlands.BaseChange.CyclicAlgebraBaseChange
import Langlands.BaseChange.CyclicNormLemma
import Langlands.BaseChange.RegularSemisimpleOrbit
import Langlands.BaseChange.RegularOrbitParameters
import Langlands.BaseChange.GeneralLinearFiniteAlgebra
import Langlands.Global.AdelicIdempotentPatching
import Langlands.Global.CyclicAdeleFixedCoefficients
import Langlands.Global.AdelicGLDeterminantNormOne
import Langlands.Global.PrincipalAdelesDiscreteProof
import Langlands.TraceFormula.TwistedOrbital
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! # Regular cyclic norm fibres on adelic matrix groups -/

noncomputable section

universe u

open Function Matrix NumberField Polynomial IsDedekindDomain
open scoped TensorProduct
open Langlands.BaseChange Langlands.Global Langlands.JacquetLanglands

namespace Langlands.TraceFormula

private theorem exists_conj_of_charpoly_of_finite_reduced {F S : Type*} [Field F]
    [CommRing S] [Algebra F S] [Module.Finite F S] [IsReduced S] {n : ℕ}
    {p : F[X]} (hp : p.Separable) (A B : GeneralLinear n S)
    (hA : A.val.charpoly = p.map (algebraMap F S)) (hB : B.val.charpoly = A.val.charpoly) :
    ∃ g : GeneralLinear n S, g⁻¹ * A * g = B := by
  classical
  let : IsArtinianRing S := IsArtinianRing.of_finite F S
  let e := generalLinearResidueEquiv S n
  have h (m : MaximalSpectrum S) :
      ∃ g : GeneralLinear n (S ⧸ m.asIdeal), g⁻¹ * e A m * g = e B m := by
    let : Field (S ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
    let f := Ideal.Quotient.mk m.asIdeal
    have hsep : (e A m).val.charpoly.Separable := by
      change (A.val.map f).charpoly.Separable
      rw [Matrix.charpoly_map, hA]
      exact hp.map.map
    have hchar : (e B m).val.charpoly = (e A m).val.charpoly := by
      change (B.val.map f).charpoly = (A.val.map f).charpoly
      rw [Matrix.charpoly_map, Matrix.charpoly_map, hB]
    obtain ⟨g, hg⟩ := exists_matrix_conj_of_charpoly_eq_of_separable _ _ hsep hchar
    exact ⟨g⁻¹, Units.ext (by simpa only [inv_inv, Units.val_mul] using hg)⟩
  choose gs hgs using h
  refine ⟨e.symm gs, e.injective ?_⟩
  rw [map_mul, map_mul, map_inv, e.apply_symm_apply]
  funext m
  exact hgs m

section Tensor

variable {K L : Type u} [Field K] [Field L] [NumberField K] [Algebra K L]
  {n l : ℕ} {σ : L ≃ₐ[K] L}

private def tensorCyclicAut (R : Type u) [CommRing R] [Algebra K R] :
    (L ≃ₐ[K] L) →* (R ⊗[K] L ≃ₐ[K] R ⊗[K] L) where
  toFun s := (tensorFactorAut R s).restrictScalars K
  map_one' := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply Algebra.TensorProduct.ext'
    intro a b
    rfl
  map_mul' s t := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply Algebra.TensorProduct.ext'
    intro a b
    rfl

local notation "R" => Adeles K
local notation "S" => R ⊗[K] L
local notation "T[" m "]" => (R ⧸ m) ⊗[K] L

private def tensorSpecialization (m : Ideal R) : S →ₐ[K] T[m] :=
  Algebra.TensorProduct.map (Ideal.Quotient.mkₐ K m) (AlgHom.id K L)

private theorem tensorSpecialization_surjective (m : Ideal R) :
    Surjective (tensorSpecialization (L := L) m) := by
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨c ⊗ₜ[K] b, rfl⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩

private theorem tensorSpecialization_equivariant (m : Ideal R) (x : S) :
    tensorSpecialization m (tensorCyclicAut R σ x) =
      tensorFactorAut (R ⧸ m) σ (tensorSpecialization m x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem tensorSpecialization_base (m : Ideal R) (r : R) :
    tensorSpecialization (L := L) m (algebraMap R S r) =
      algebraMap (R ⧸ m) T[m] (Ideal.Quotient.mk m r) := rfl

private theorem tensorCyclicAut_base (s : L ≃ₐ[K] L) (r : R) :
    tensorCyclicAut R s (algebraMap R S r) = algebraMap R S r :=
  (tensorFactorAut R s).commutes r

omit [NumberField K] in
private theorem tensorCyclicAut_pow_eq_one (A : Type u) [CommRing A] [Algebra K A]
    (hcyc : IsCyclicAlgebra σ l) : tensorCyclicAut A σ ^ l = 1 := by
  rw [← map_pow, hcyc.pow_eq_one, map_one]

set_option maxHeartbeats 800000 in
private theorem exists_specialized_cyclicIntertwiner (hcyc : IsCyclicAlgebra σ l)
    (m : Ideal R) [m.IsMaximal] (a b : GeneralLinear n S) {p : K[X]} (hp : p.Separable)
    (hA : (cyclicNorm (tensorCyclicAut R σ) l a).val.charpoly = p.map (algebraMap K S))
    (hB : (cyclicNorm (tensorCyclicAut R σ) l b).val.charpoly =
      (cyclicNorm (tensorCyclicAut R σ) l a).val.charpoly) :
    ∃ x : GeneralLinear n T[m],
      cyclicIntertwinerStep (tensorFactorAut (R ⧸ m) σ)
        (GeneralLinearGroup.map (tensorSpecialization (L := L) m).toRingHom a)
        (GeneralLinearGroup.map (tensorSpecialization (L := L) m).toRingHom b) x.val = x.val := by
  let k := R ⧸ m
  let : Field k := Ideal.Quotient.field m
  let q := tensorSpecialization (L := L) m
  let t := tensorFactorAut k σ
  let a' := GeneralLinearGroup.map q.toRingHom a
  let b' := GeneralLinearGroup.map q.toRingHom b
  have ht : IsCyclicAlgebra t l := cyclicAlgebraBaseChange K L k σ l hcyc
  let : Module.Finite k T[m] := ht.1
  let : IsReduced T[m] := ht.2.2.1
  have hnorm (x : GeneralLinear n S) : cyclicNorm t l (GeneralLinearGroup.map q.toRingHom x) =
      GeneralLinearGroup.map q.toRingHom (cyclicNorm (tensorCyclicAut R σ) l x) :=
    (map_cyclicNorm_of_equivariant q.toRingHom (tensorSpecialization_equivariant m) x l).symm
  have hpa : (cyclicNorm t l a').val.charpoly = (p.map (algebraMap K k)).map (algebraMap k T[m]) := by
    rw [hnorm]
    change (((cyclicNorm (tensorCyclicAut R σ) l a).val).map q.toRingHom).charpoly = _
    rw [Matrix.charpoly_map, hA, Polynomial.map_map, Polynomial.map_map]
    apply congrArg (fun f : K →+* T[m] => p.map f)
    exact RingHom.ext fun r => (q.commutes r).trans (IsScalarTower.algebraMap_apply K k T[m] r)
  have hpb : (cyclicNorm t l b').val.charpoly = (cyclicNorm t l a').val.charpoly := by
    rw [hnorm, hnorm]
    change ((cyclicNorm (tensorCyclicAut R σ) l b).val.map q.toRingHom).charpoly =
      ((cyclicNorm (tensorCyclicAut R σ) l a).val.map q.toRingHom).charpoly
    rw [Matrix.charpoly_map, Matrix.charpoly_map, hB]
  obtain ⟨x, hx⟩ := ((cyclicNormLemma k T[m] t l n ht).2.2 a' b')
    (exists_conj_of_charpoly_of_finite_reduced hp.map _ _ hpa hpb)
  refine ⟨x, (cyclicIntertwinerStep_eq_self_iff _ _ _ _).mpr ?_⟩
  have hmul : a' * entrywiseAut t n x = x * b' := by
    rw [← hx]
    group
  exact congrArg Units.val hmul

variable [FiniteDimensional K L]

private theorem isUnit_of_tensorAlgebraNorm (x : S) (hx : IsUnit (Algebra.norm R x)) :
    IsUnit x := by
  let f := Algebra.lmul R S x
  have hf : IsUnit f := (LinearMap.isUnit_iff_isUnit_det f).2 hx
  obtain ⟨g, hg⟩ := hf
  have he := LinearMap.congr_fun g.val_inv (1 : S)
  rw [hg] at he
  exact isUnit_iff_exists_inv.mpr ⟨g⁻¹.val 1, he⟩

omit [FiniteDimensional K L] in
private theorem step_tensor_smul (a b : GeneralLinear n S) (r : R)
    (X : Matrix (Fin n) (Fin n) S) :
    cyclicIntertwinerStep (tensorCyclicAut R σ) a b (algebraMap R S r • X) =
      algebraMap R S r • cyclicIntertwinerStep (tensorCyclicAut R σ) a b X := by
  have he : (algebraMap R S r • X).map (tensorCyclicAut R σ).toRingHom =
      algebraMap R S r • X.map (tensorCyclicAut R σ).toRingHom := by
    ext i j
    change tensorCyclicAut R σ (algebraMap R S r * X i j) =
      algebraMap R S r * tensorCyclicAut R σ (X i j)
    rw [map_mul, tensorCyclicAut_base]
  rw [cyclicIntertwinerStep_apply, cyclicIntertwinerStep_apply, he, Matrix.mul_smul, Matrix.smul_mul]

omit [FiniteDimensional K L] in
private theorem specialize_smul (m : Ideal R) (r : R) (X : Matrix (Fin n) (Fin n) S) :
    (tensorSpecialization (L := L) m).toRingHom.mapMatrix (algebraMap R S r • X) =
      algebraMap (R ⧸ m) T[m] (Ideal.Quotient.mk m r) •
        (tensorSpecialization (L := L) m).toRingHom.mapMatrix X := by
  ext i j
  change tensorSpecialization m (algebraMap R S r * X i j) =
    algebraMap (R ⧸ m) T[m] (Ideal.Quotient.mk m r) * tensorSpecialization m (X i j)
  rw [map_mul, tensorSpecialization_base]

set_option maxHeartbeats 1000000 in
private theorem adelicTensor_exists_twisted_conj (hcyc : IsCyclicAlgebra σ l)
    (a b : GeneralLinear n S) {p : K[X]} (hp : p.Separable)
    (hA : (cyclicNorm (tensorCyclicAut R σ) l a).val.charpoly = p.map (algebraMap K S))
    (hB : (cyclicNorm (tensorCyclicAut R σ) l b).val.charpoly =
      (cyclicNorm (tensorCyclicAut R σ) l a).val.charpoly)
    {v : Fin n → S}
    (hv : IsUnit (cyclicBasisMatrix (cyclicNorm (tensorCyclicAut R σ) l b).val v)) :
    ∃ x : GeneralLinear n S, x⁻¹ * a * entrywiseAut (tensorCyclicAut R σ) n x = b := by
  classical
  let s := tensorCyclicAut R σ
  let step := cyclicIntertwinerStep s a b
  let V := {X : Matrix (Fin n) (Fin n) S // step X = X}
  let d (X : V) : R := Algebra.norm R X.val.det
  have hspec (m : Ideal R) (X : Matrix (Fin n) (Fin n) S) :
      Algebra.norm (R ⧸ m) (X.map (tensorSpecialization (L := L) m).toRingHom).det =
        Ideal.Quotient.mk m (Algebra.norm R X.det) := by
    let qm := Ideal.Quotient.mkₐ K m
    change Algebra.norm (R ⧸ m) ((tensorSpecialization (L := L) m).toRingHom.mapMatrix X).det = _
    rw [← RingHom.map_det]
    exact Langlands.Algebra.norm_tensor_map_of_basis (Module.Free.chooseBasis K L) qm X.det
  have havoid (m : Ideal R) (hm : m.IsMaximal) : ∃ X : V, d X ∉ m := by
    let := hm
    let : Field (R ⧸ m) := Ideal.Quotient.field m
    let q := tensorSpecialization (L := L) m
    obtain ⟨x, hx⟩ := exists_specialized_cyclicIntertwiner hcyc m a b hp hA hB
    obtain ⟨X, hX, hXq⟩ := exists_cyclicIntertwiner_lift q.toRingHom
      (tensorSpecialization_surjective m) (tensorCyclicAut_pow_eq_one R hcyc)
      (cyclicAlgebraBaseChange K L (R ⧸ m) σ l hcyc).pow_eq_one (tensorSpecialization_equivariant m)
      a b hB.symm hv hx
    have hl : IsUnit (l : T[m]) := by
      have hpos : (l : K) ≠ 0 := Nat.cast_ne_zero.mpr hcyc.pos.ne'
      simpa only [map_natCast] using (isUnit_iff_ne_zero.mpr hpos).map (algebraMap K T[m])
    have hu : IsUnit (X.map q.toRingHom).det := by
      rw [hXq, ← Nat.cast_smul_eq_nsmul T[m]]
      exact (Matrix.det_smul x.val (l : T[m])).symm ▸ (hl.pow _).mul (Matrix.isUnits_det_units x)
    refine ⟨⟨X, hX⟩, ?_⟩
    intro hm'
    have hn := hu.map (Algebra.norm (R ⧸ m))
    rw [hspec] at hn
    exact hn.ne_zero (Ideal.Quotient.eq_zero_iff_mem.mpr hm')
  have hs : Ideal.span (Set.range d) = ⊤ := by
    by_contra ht
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ ht
    obtain ⟨x, hx⟩ := havoid m hm
    exact hx (hle (Ideal.subset_span ⟨x, rfl⟩))
  obtain ⟨D, hD, hDtop⟩ := (Ideal.span_eq_top_iff_finite _).mp hs
  choose X hX using fun i : D => hD i.property
  have hd : Ideal.span (Set.range fun i : D => d (X i)) = ⊤ := by
    have he : Set.range (fun i : D => d (X i)) = (D : Set R) := by
      simp only [hX]
      exact Subtype.range_coe
    rwa [he]
  obtain ⟨e, hesum, heidemp, heorthog, hunit⟩ := exists_adele_idempotent_patch (fun i : D => d (X i)) hd
  let Y : Matrix (Fin n) (Fin n) S := ∑ i : D, algebraMap R S (e i) • (X i).val
  have hy : step Y = Y := by
    change step (∑ i : D, _) = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by
      change cyclicIntertwinerStep s a b (algebraMap R S (e i) • (X i).val) = _
      rw [step_tensor_smul, show cyclicIntertwinerStep s a b (X i).val = (X i).val from (X i).property]
  have hyd : IsUnit (Algebra.norm R Y.det) := by
    by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ (Ideal.span_singleton_ne_top h)
    let : m.IsMaximal := hm
    let : Field (R ⧸ m) := Ideal.Quotient.field m
    let qm := Ideal.Quotient.mk m
    let q := tensorSpecialization (L := L) m
    have hes : ∑ i : D, qm (e i) = 1 := by
      simpa only [map_sum, map_one] using congrArg qm hesum
    have he' : ∃ i : D, qm (e i) ≠ 0 := by
      by_contra! hall
      simp only [hall, Finset.sum_const_zero, zero_ne_one] at hes
    obtain ⟨j, hj⟩ := he'
    have hj1 : qm (e j) = 1 := by
      apply mul_left_cancel₀ hj
      rw [mul_one, ← map_mul]
      exact congrArg qm (heidemp j)
    have hj0 (i : D) (hij : i ≠ j) : qm (e i) = 0 := by
      have h := congrArg qm (heorthog i j hij)
      simpa only [map_mul, map_zero, hj1, mul_one] using h
    have hds : qm (∑ i : D, e i * d (X i)) = qm (d (X j)) := by
      rw [map_sum]
      rw [Finset.sum_eq_single j]
      · rw [map_mul, hj1, one_mul]
      · intro i _ hij
        rw [map_mul, hj0 i hij, zero_mul]
      · simp
    have hY : q.toRingHom.mapMatrix Y = q.toRingHom.mapMatrix (X j).val := by
      change (tensorSpecialization (L := L) m).toRingHom.mapMatrix (∑ i : D, _) = _
      rw [map_sum]
      simp_rw [specialize_smul]
      rw [Finset.sum_eq_single j]
      · rw [hj1, map_one, one_smul]
      · intro i _ hij
        rw [hj0 i hij, map_zero]
        ext k i
        exact zero_mul _
      · simp
    have hmY : qm (Algebra.norm R Y.det) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span (Set.mem_singleton _)))
    have hmX : qm (d (X j)) = 0 := by
      change qm (Algebra.norm R (X j).val.det) = 0
      rw [← hspec m, ← show Y.map q.toRingHom = (X j).val.map q.toRingHom from hY, hspec m]
      exact hmY
    exact (hunit.map qm).ne_zero (hds.trans hmX)
  have hu : IsUnit Y := (Matrix.isUnit_iff_isUnit_det Y).mpr (isUnit_of_tensorAlgebraNorm _ hyd)
  let x := hu.unit
  have hx : x.val = Y := hu.unit_spec
  have hstep := (cyclicIntertwinerStep_eq_self_iff s a b Y).mp hy
  rw [← hx] at hstep
  have hmul : a * entrywiseAut s n x = x * b := Units.ext hstep
  exact ⟨x, by rw [mul_assoc, hmul, inv_mul_cancel_left]⟩

end Tensor

section MatrixAdeles

open Langlands.Global.AdelicFunctoriality
open Langlands.ClassFieldTheory.Global.IdeleGaloisDescentProof
open Langlands.BaseChange.SigmaLiftCharacterIdentity (coefficients continuous_coefficients)
open scoped NNReal

variable {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] {n l : ℕ} {σ : L ≃ₐ[K] L}

local instance (priority := low) adelicUpperAlgebra : Algebra K (Adeles L) :=
  ((algebraMap L (Adeles L)).comp (algebraMap K L)).toAlgebra

local notation "S" => Adeles K ⊗[K] L
local notation "Θ" => adeleCoefficientAut K L σ

omit [NumberField K] [FiniteDimensional K L] in
/-- The cyclic relation persists for the upper adelic coefficient automorphism. -/
theorem adeleCoefficientAut_pow_eq_one (hcyc : IsCyclicAlgebra σ l) : Θ ^ l = 1 := by
  rw [← map_pow, hcyc.pow_eq_one, map_one]

omit [NumberField K] [FiniteDimensional K L] in
/-- The ordered cyclic norm of a principal matrix is the principal image of its rational norm. -/
theorem cyclicNorm_adelicRational (σ : L ≃ₐ[K] L) (l : ℕ) (δ : GeneralLinear n L) :
    cyclicNorm (adeleCoefficientAut K L σ) l (AdelicGL.rational L n δ) =
      AdelicGL.rational L n (cyclicNorm σ l δ) :=
  (map_cyclicNorm_of_equivariant (algebraMap L (Adeles L)) (s := σ)
    (t := adeleCoefficientAut K L σ) (fun a => (adeleEquiv_diagonal σ.toRingEquiv a).symm) δ l).symm

private def tensorAdeles : S ≃+* Adeles L :=
  (Algebra.TensorProduct.comm K (Adeles K) L).toRingEquiv.trans
    (numberFieldAdeleTensorEquiv K L).toRingEquiv

omit [FiniteDimensional K L] in
private theorem tensorAdeles_equivariant (x : S) :
    tensorAdeles (tensorCyclicAut (Adeles K) σ x) = Θ (tensorAdeles x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    change numberFieldAdeleTensorEquiv K L (σ b ⊗ₜ[K] a) =
      adeleEquiv σ.toRingEquiv (numberFieldAdeleTensorEquiv K L (b ⊗ₜ[K] a))
    rw [numberFieldAdeleTensorEquiv_tmul, numberFieldAdeleTensorEquiv_tmul, map_mul,
      adeleEquiv_diagonal, adeleEquiv_adeleInclusion]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

set_option maxHeartbeats 1500000 in
/-- The twisted adelic orbit of a rational matrix with regular cyclic norm is the fibre of
the characteristic polynomial of that norm. -/
theorem adelic_twistedConjugate_iff_cyclicNorm_charpoly (hcyc : IsCyclicAlgebra σ l)
    (δ : GeneralLinear n L) (hδ : IsSigmaRegular σ l δ) (b : AdelicGL L n) :
    (∃ x : AdelicGL L n, twistedConj (AdelicGLTransport.adelicEquiv n σ.toRingEquiv)
      x (AdelicGL.rational L n δ) = b) ↔
    (cyclicNorm Θ l b).val.charpoly = (cyclicNorm Θ l (AdelicGL.rational L n δ)).val.charpoly := by
  let a := AdelicGL.rational L n δ
  constructor
  · rintro ⟨x, hx⟩
    change x⁻¹ * a * entrywiseAut Θ n x = b at hx
    rw [← hx, cyclicNorm_twistedConj, adeleCoefficientAut_pow_eq_one hcyc, entrywiseAut_one_apply]
    simpa only [Units.val_mul, Matrix.coe_units_inv] using
      Matrix.charpoly_units_conj' x (cyclicNorm Θ l a).val
  · intro hb
    obtain ⟨γ, hγ, hsep⟩ := hδ
    let j : S ≃+* Adeles L := tensorAdeles
    let m := GeneralLinearGroup.map (n := Fin n) j.toRingHom
    let i : L →ₐ[K] S := Algebra.TensorProduct.includeRight
    let aS := GeneralLinearGroup.map i.toRingHom δ
    let bS := GeneralLinearGroup.map j.symm.toRingHom b
    let s := tensorCyclicAut (Adeles K) σ
    have hma : m aS = a := by
      ext k i'
      change numberFieldAdeleTensorEquiv K L (δ k i' ⊗ₜ[K] (1 : Adeles K)) = _
      rw [numberFieldAdeleTensorEquiv_tmul, map_one, mul_one]
      rfl
    have hmb : m bS = b := by
      ext k i'
      exact j.apply_symm_apply (b k i')
    have hm (g : GeneralLinear n S) :
        m (cyclicNorm s l g) = cyclicNorm Θ l (m g) :=
      map_cyclicNorm_of_equivariant j.toRingHom tensorAdeles_equivariant g l
    have haS : cyclicNorm s l aS = GeneralLinearGroup.map i.toRingHom (cyclicNorm σ l δ) :=
      (map_cyclicNorm_of_equivariant i.toRingHom (fun _ => rfl) δ l).symm
    have hp : (cyclicNorm s l aS).val.charpoly = γ.val.charpoly.map (algebraMap K S) := by
      rw [haS]
      change ((cyclicNorm σ l δ).val.map i.toRingHom).charpoly = _
      rw [Matrix.charpoly_map, charpoly_norm_of_associated hγ, Polynomial.map_map]
      exact congrArg (fun f : K →+* S => γ.val.charpoly.map f) (RingHom.ext i.commutes)
    have hp' : (cyclicNorm s l bS).val.charpoly = (cyclicNorm s l aS).val.charpoly := by
      apply Polynomial.map_injective (f := j.toRingHom) j.injective
      rw [← Matrix.charpoly_map, ← Matrix.charpoly_map]
      change (m (cyclicNorm s l bS)).val.charpoly = (m (cyclicNorm s l aS)).val.charpoly
      rwa [hm, hm, hma, hmb]
    have hsep' : (cyclicNorm σ l δ).val.charpoly.Separable := by
      rw [charpoly_norm_of_associated hγ]
      exact hsep.map
    obtain ⟨v, hv⟩ := regularCyclicBasis L n (cyclicNorm σ l δ).val hsep'
    have hvS : IsUnit (cyclicBasisMatrix (cyclicNorm s l aS).val (i ∘ v)) := by
      rw [haS]
      change IsUnit (cyclicBasisMatrix ((cyclicNorm σ l δ).val.map i.toRingHom) (i ∘ v))
      change IsUnit (cyclicBasisMatrix ((cyclicNorm σ l δ).val.map i.toRingHom) (i.toRingHom ∘ v))
      exact (cyclicBasisMatrix_map i.toRingHom _ v) ▸ (hv.map i.toRingHom.mapMatrix)
    obtain ⟨x, hx⟩ := adelicTensor_exists_twisted_conj hcyc bS aS hsep (hp'.trans hp) hp'.symm hvS
    have hmap (z : GeneralLinear n S) :
        m (entrywiseAut s n z) = AdelicGLTransport.adelicEquiv n σ.toRingEquiv (m z) := by
      ext k i'
      exact tensorAdeles_equivariant (z k i')
    have hx' : twistedConj (AdelicGLTransport.adelicEquiv n σ.toRingEquiv) (m x) b = a := by
      have he := congrArg m hx
      rw [map_mul, map_mul, map_inv, hmap, hma, hmb] at he
      exact he
    refine ⟨(m x)⁻¹, ?_⟩
    change twistedConj (AdelicGLTransport.adelicEquiv n σ.toRingEquiv) (m x)⁻¹ a = b
    rw [← hx', twistedConj_mul, mul_inv_cancel, twistedConj_one]

omit [NumberField K] [FiniteDimensional K L] in
private theorem continuous_adelic_cyclicNorm (σ : L ≃ₐ[K] L) (l : ℕ) :
    Continuous (fun x : AdelicGL L n => cyclicNorm (adeleCoefficientAut K L σ) l x) := by
  induction l with
  | zero => simpa only [cyclicNorm_zero] using continuous_const
  | succ k ih =>
    simp_rw [cyclicNorm_succ, ← map_pow, entrywiseAut_adeleCoefficientAut]
    exact ih.mul (AdelicGLTransport.adelicEquiv n (σ ^ k).toRingEquiv).continuous

omit [FiniteDimensional K L] in
private theorem exists_twistFixed_scalar_determinantNorm (σ : L ≃ₐ[K] L) (hn : n ≠ 0)
    (d : ℝ≥0ˣ) : ∃ z : AdelicGL L n,
    (∀ g : AdelicGL L n, Commute z g) ∧ AdelicGLTransport.adelicEquiv n σ.toRingEquiv z = z ∧
    AdelicBlockDeterminantCharacter.determinantNorm L n z = d := by
  let k := Module.finrank ℚ L * n
  have hk : k ≠ 0 := Nat.mul_ne_zero Module.finrank_pos.ne' hn
  obtain ⟨t, ht⟩ := NNReal.rpow_left_surjective (x := (k : ℝ)) (Nat.cast_ne_zero.mpr hk) d.val
  change t ^ (k : ℝ) = d.val at ht
  rw [NNReal.rpow_natCast] at ht
  have ht0 : t ≠ 0 := by
    intro e
    rw [e, zero_pow hk] at ht
    exact d.ne_zero ht.symm
  let a : ℝ≥0ˣ := Units.mk0 t ht0
  let z := AdelicGL.scalar L n (PositiveRealIdeles.full L a)
  refine ⟨z, fun g => AdelicGL.scalar_commute L n _ g, adelicEquiv_scalar_positiveReal K L σ n a, ?_⟩
  rw [AdelicBlockDeterminantCharacter.determinantNorm_scalar, PositiveRealIdeles.absoluteValue_full,
    ← pow_mul]
  exact Units.ext ht

set_option maxHeartbeats 1200000 in
private theorem isClosed_range_adelic_twistedConj (hcyc : IsCyclicAlgebra σ l)
    (δ : GeneralLinear n L) (hδ : IsSigmaRegular σ l δ) :
    IsClosed (Set.range fun x : AdelicGL L n =>
      twistedConj (AdelicGLTransport.adelicEquiv n σ.toRingEquiv) x
        (AdelicGL.rational L n δ)) := by
  let : T2Space (Adeles L) := adeles_t2Space L
  let : Nontrivial (Adeles L) := (AdeleRing.algebraMap_injective (𝓞 L) L).nontrivial
  let a := AdelicGL.rational L n δ
  let t := AdelicGLTransport.adelicEquiv n σ.toRingEquiv
  let P (b : AdelicGL L n) : Fin n → Adeles L := coefficients (cyclicNorm Θ l b)
  have hP : Continuous P := continuous_coefficients.comp (continuous_adelic_cyclicNorm σ l)
  have hf : Set.range (fun x : AdelicGL L n => twistedConj t x a) = P ⁻¹' {P a} := by
    apply Set.ext
    intro b
    change (∃ x : AdelicGL L n, twistedConj t x a = b) ↔ P b = P a
    rw [adelic_twistedConjugate_iff_cyclicNorm_charpoly hcyc δ hδ b]
    constructor
    · intro h
      exact funext fun j => congrArg (fun p : (Adeles L)[X] => p.coeff j.val) h
    · intro h
      exact (polynomialOfCoefficients_coefficients _).symm.trans
        ((congrArg polynomialOfCoefficients h).trans (polynomialOfCoefficients_coefficients _))
  change IsClosed (Set.range fun x : AdelicGL L n => twistedConj t x a)
  rw [hf]
  exact isClosed_singleton.preimage hP

set_option maxHeartbeats 700000 in
omit [FiniteDimensional K L] in
private theorem exists_determinantNormOne_twistedConjugator (hn : n ≠ 0)
    (a x : AdelicGL L n) : ∃ y : AdelicGL.determinantNormOne L n,
    twistedConj (AdelicGLTransport.adelicEquiv n σ.toRingEquiv) y.val a =
      twistedConj (AdelicGLTransport.adelicEquiv n σ.toRingEquiv) x a := by
  let t := AdelicGLTransport.adelicEquiv n σ.toRingEquiv
  let b := twistedConj t x a
  let D := AdelicBlockDeterminantCharacter.determinantNorm L n
  obtain ⟨z, hz, hzt, hzd⟩ := exists_twistFixed_scalar_determinantNorm σ hn (D x)⁻¹
  have hxz : x * z ∈ AdelicGL.determinantNormOne L n := by
    change D (x * z) = 1
    rw [map_mul, hzd, mul_inv_cancel]
  refine ⟨⟨x * z, hxz⟩, ?_⟩
  change twistedConj t (x * z) a = b
  rw [← twistedConj_mul, show twistedConj t x a = b from rfl, twistedConj_apply,
    show t z = z from hzt, mul_assoc, ← (hz b).eq, inv_mul_cancel_left]

set_option maxHeartbeats 700000 in
/-- The orbit under determinant-norm-one conjugators is closed in the full adelic matrix
space. A twist-fixed positive scalar corrects the determinant norm of any conjugator. -/
theorem isClosed_range_adelic_normOne_twistedConj (hcyc : IsCyclicAlgebra σ l)
    (hn : n ≠ 0) (δ : GeneralLinear n L) (hδ : IsSigmaRegular σ l δ) :
    IsClosed (Set.range fun x : AdelicGL.determinantNormOne L n =>
      twistedConj (AdelicGLTransport.adelicEquiv n σ.toRingEquiv) x.val
        (AdelicGL.rational L n δ)) := by
  let t := AdelicGLTransport.adelicEquiv n σ.toRingEquiv
  let a := AdelicGL.rational L n δ
  have he : Set.range (fun x : AdelicGL.determinantNormOne L n => twistedConj t x.val a) =
      Set.range (fun x : AdelicGL L n => twistedConj t x a) := by
    apply Set.ext
    intro b
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x.val, hx⟩
    · rintro ⟨x, rfl⟩
      exact exists_determinantNormOne_twistedConjugator (σ := σ) hn a x
  change IsClosed (Set.range fun x : AdelicGL.determinantNormOne L n => twistedConj t x.val a)
  rw [he]
  exact isClosed_range_adelic_twistedConj hcyc δ hδ

end MatrixAdeles

end Langlands.TraceFormula
