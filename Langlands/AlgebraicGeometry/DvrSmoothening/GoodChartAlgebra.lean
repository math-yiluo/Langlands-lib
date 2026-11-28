import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Smooth.Locus

/-! # Geometric reducedness, generic smoothness and generic freeness over a field -/

open scoped TensorProduct

universe u

namespace Langlands.AlgebraicGeometry.DvrSmoothening

section Reduced

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]

/-- A `k`-algebra which embeds into a product of geometrically reduced `k`-algebras is
geometrically reduced. -/
theorem isGeometricallyReduced_of_forall_eq_zero {ι : Type*} (B : ι → Type u)
    [∀ i, CommRing (B i)] [∀ i, Algebra k (B i)] [∀ i, Algebra.IsGeometricallyReduced k (B i)]
    (f : ∀ i, A →ₐ[k] B i) (hf : ∀ a, (∀ i, f i a = 0) → a = 0) :
    Algebra.IsGeometricallyReduced k A := by
  rw [Algebra.isGeometricallyReduced_field_iff]
  let L := AlgebraicClosure k
  let b := Module.Free.chooseBasis k L
  have hredB : ∀ i, IsReduced (B i ⊗[k] L) := fun i => by
    have : IsReduced (L ⊗[k] B i) :=
      (Algebra.isGeometricallyReduced_field_iff k (B i)).mp inferInstance
    exact isReduced_of_injective (Algebra.TensorProduct.comm k (B i) L)
      (AlgEquiv.injective _)
  have hnat : ∀ i j (y : A ⊗[k] L),
      (Algebra.TensorProduct.basis (B i) b).repr
        (Algebra.TensorProduct.map (f i) (AlgHom.id k L) y) j =
      f i ((Algebra.TensorProduct.basis A b).repr y j) := by
    intro i j y
    induction y using TensorProduct.inductionOn with
    | tmul a m =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
        Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
        smul_eq_mul, map_mul, AlgHom.commutes]
    | add y z hy hz => simp only [map_add, Finsupp.add_apply, hy, hz]
  have hred : IsReduced (A ⊗[k] L) := by
    constructor
    intro x hx
    have himg : ∀ i, Algebra.TensorProduct.map (f i) (AlgHom.id k L) x = 0 := fun i =>
      (hx.map (Algebra.TensorProduct.map (f i) (AlgHom.id k L))).eq_zero
    apply (Algebra.TensorProduct.basis A b).repr.injective
    ext j
    rw [map_zero, Finsupp.coe_zero, Pi.zero_apply]
    apply hf
    intro i
    rw [← hnat, himg i, map_zero, Finsupp.coe_zero, Pi.zero_apply]
  exact isReduced_of_injective (Algebra.TensorProduct.comm k L A) (AlgEquiv.injective _)

/-- Localizations of geometrically reduced algebras are geometrically reduced. -/
theorem isGeometricallyReduced_localization [Algebra.IsGeometricallyReduced k A]
    (M : Submonoid A) : Algebra.IsGeometricallyReduced k (Localization M) := by
  rw [Algebra.isGeometricallyReduced_field_iff]
  let L := AlgebraicClosure k
  letI : Algebra (L ⊗[k] A) (L ⊗[k] Localization M) :=
    (Algebra.TensorProduct.map (AlgHom.id k L) (IsScalarTower.toAlgHom k _ _)).toAlgebra
  haveI : IsScalarTower L (L ⊗[k] A) (L ⊗[k] Localization M) :=
    .of_algebraMap_eq <| by intro; simp [RingHom.algebraMap_toAlgebra]
  haveI := IsLocalization.tensorProduct_tensorProduct_right k L M (Localization M)
    (by ext; simp [RingHom.algebraMap_toAlgebra])
  have hred : IsReduced (L ⊗[k] A) :=
    (Algebra.isGeometricallyReduced_field_iff k A).mp inferInstance
  exact isReduced_localizationPreserves
    (M.map (Algebra.TensorProduct.includeRight (R := k) (A := L))) (L ⊗[k] Localization M) hred

end Reduced

section Field

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- Over a field `k` of characteristic `p`, the `p`-th powers of a finite `k`-linearly independent
set of elements of a geometrically reduced field extension are again linearly independent. -/
theorem linearIndepOn_pow_of_isGeometricallyReduced [Algebra.IsGeometricallyReduced k K]
    (p : ℕ) (hp : p.Prime) [CharP k p] (s : Finset K) (hs : LinearIndepOn k id (s : Set K)) :
    LinearIndepOn k (· ^ p) (s : Set K) := by
  classical
  let L := AlgebraicClosure k
  have hred : IsReduced (L ⊗[k] K) := (Algebra.isGeometricallyReduced_field_iff k K).mp inferInstance
  have hchar : CharP (L ⊗[k] K) p :=
    charP_of_injective_algebraMap (algebraMap k (L ⊗[k] K)).injective p
  have hli : LinearIndependent L (fun x : (s : Set K) => (1 : L) ⊗ₜ[k] (x : K)) :=
    Module.Flat.linearIndependent_one_tmul hs
  rw [LinearIndepOn, Fintype.linearIndependent_iff]
  intro g hg i
  choose d hd using fun x : (s : Set K) => IsAlgClosed.exists_pow_nat_eq (algebraMap k L (g x))
    hp.pos
  let z : L ⊗[k] K := ∑ x, d x • ((1 : L) ⊗ₜ[k] (x : K))
  have : ExpChar (L ⊗[k] K) p := ExpChar.prime hp
  have hz : z ^ p = 0 := by
    have : z ^ p = ∑ x, (1 : L) ⊗ₜ[k] (g x • (x : K) ^ p) := by
      simp only [z, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [sum_pow_char p]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Algebra.TensorProduct.tmul_pow, hd, ← TensorProduct.smul_tmul, Algebra.smul_def,
        mul_one]
    rw [this, ← TensorProduct.tmul_sum, hg, TensorProduct.tmul_zero]
  have hz0 : z = 0 := IsNilpotent.eq_zero ⟨p, hz⟩
  have hd0 := (Fintype.linearIndependent_iff.mp hli) d hz0 i
  have := hd i
  rw [hd0, zero_pow hp.ne_zero] at this
  exact (map_eq_zero_iff _ (algebraMap k L).injective).mp this.symm

/-- A finitely generated geometrically reduced field extension is formally smooth. -/
theorem formallySmooth_of_isGeometricallyReduced [Algebra.IsGeometricallyReduced k K]
    [Algebra.EssFiniteType k K] : Algebra.FormallySmooth k K := by
  obtain _ | ⟨p, hp, hpk⟩ := CharP.exists' k
  · have : PerfectField k := PerfectField.ofCharZero
    infer_instance
  · have : ExpChar k p := .prime hp.out
    obtain ⟨t, ht, hsep⟩ :=
      exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType p hp.out
        (fun s hs => linearIndepOn_pow_of_isGeometricallyReduced (k := k) (K := K) p hp.out s hs)
    have : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range ((↑) : t → K))) K := by
      convert! hsep <;> simp
    exact Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable ht.1

end Field

section Generic

variable {k B : Type u} [Field k] [CommRing B] [Algebra k B]

/-- Generic smoothness and generic freeness: a nonzero geometrically reduced `k`-algebra `B` of
finite type has a prime `q` and elements `r₁, r₂ ∉ q` such that a given finite module `M` becomes
free over `B[1/r₁]` and `B[1/r₂]` is smooth over `k`. -/
theorem exists_free_smooth [Algebra.FiniteType k B] [Algebra.IsGeometricallyReduced k B]
    [Nontrivial B] (M : Type u) [AddCommGroup M] [Module B M] [Module.Finite B M] :
    ∃ q : Ideal B, q.IsPrime ∧ ∃ r₁ ∉ q, ∃ r₂ ∉ q,
      Module.Free (Localization.Away r₁) (LocalizedModule.Away r₁ M) ∧
      Algebra.Smooth k (Localization.Away r₂) := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have : IsReduced B := Algebra.isReduced_of_isGeometricallyReduced k
  obtain ⟨⟨q, hq⟩⟩ := Ideal.nonempty_minimalPrimes (I := (⊥ : Ideal B)) bot_ne_top
  have hqp : q.IsPrime := hq.1.1
  have hqmin : q ∈ minimalPrimes B := hq
  have : Ring.KrullDimLE 0 (Localization.AtPrime q) :=
    Ring.KrullDimLE.of_isLocalization q hqmin (Localization.AtPrime q)
  have hfield : IsField (Localization.AtPrime q) := Ring.KrullDimLE.isField_of_isReduced
  have : Module.FinitePresentation B M := Module.finitePresentation_of_finite B M
  have hfree : Module.Free (Localization.AtPrime q) (LocalizedModule q.primeCompl M) := by
    letI : Field (Localization.AtPrime q) := hfield.toField
    exact Module.Free.of_divisionRing _ _
  obtain ⟨r₁, hr₁, hfree₁, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    q.primeCompl (LocalizedModule.mkLinearMap q.primeCompl M) (Localization.AtPrime q)
  have : Algebra.IsGeometricallyReduced k (Localization.AtPrime q) :=
    isGeometricallyReduced_localization q.primeCompl
  have hsm : Algebra.IsSmoothAt k q := by
    letI : Field (Localization.AtPrime q) := hfield.toField
    exact formallySmooth_of_isGeometricallyReduced
  have : Algebra.FinitePresentation k B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨r₂, hr₂, hsm₂⟩ := Algebra.IsSmoothAt.exists_notMem_smooth k q
  exact ⟨q, hqp, r₁, hr₁, r₂, hr₂, hfree₁, hsm₂⟩

end Generic

end Langlands.AlgebraicGeometry.DvrSmoothening
