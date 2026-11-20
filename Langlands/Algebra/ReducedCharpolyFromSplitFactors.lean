import Langlands.Algebra.BrauerSplitting
import Langlands.Algebra.ReducedCharpoly
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.SimpleModule.WedderburnArtin

/-! # Constructing a reduced characteristic polynomial from splitting factors -/

noncomputable section

universe u v

open Polynomial UniqueFactorizationMonoid
open scoped TensorProduct

namespace Langlands.CentralSimple

/-- Reduced Cayley–Hamilton for an arbitrary central simple algebra. -/
theorem aeval_reducedCharpoly {K A : Type u} [Field K] [Ring A] [Algebra K A]
    [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A] (a : A) :
    aeval a (reducedCharpoly K A a) = 0 := by
  let L := finiteGaloisSplittingField K A
  let e := finiteGaloisSplittingChart K A
  let ι : A →ₐ[K] L ⊗[K] A := Algebra.TensorProduct.includeRight
  let j := (e.restrictScalars K).toAlgHom.comp ι
  have hj : Function.Injective j :=
    e.injective.comp (Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective)
  apply hj
  rw [map_zero, ← aeval_algHom_apply j]
  have hh := Matrix.aeval_self_charpoly (e ((1 : L) ⊗ₜ[K] a))
  rw [← reducedCharpoly_map_chart K A e, aeval_map_algebraMap] at hh
  exact hh

private theorem nonempty_regularModuleEquiv_of_finrank_eq {K A : Type u} [Field K] [Ring A]
    [Algebra K A] [FiniteDimensional K A] [IsSimpleRing A]
    (V : Type v) [AddCommGroup V] [Module K V] [Module A V]
    [IsScalarTower K A V] [FiniteDimensional K V] (h : Module.finrank K A = Module.finrank K V) :
    Nonempty (A ≃ₗ[A] V) := by
  let : IsArtinianRing A := IsArtinianRing.of_finite K A
  let : Module.Finite A V := Module.Finite.of_restrictScalars_finite K A V
  obtain ⟨S, hS⟩ := IsAtomic.exists_atom (Submodule A (A × V))
  let : IsSimpleModule A S := isSimpleModule_iff_isAtom.mpr hS
  let : Nontrivial S := IsSimpleModule.nontrivial A S
  let : FiniteDimensional K S := Module.Finite.of_injective
    (S.restrictScalars K).subtype Subtype.val_injective
  have htyp := IsSimpleRing.isIsotypic A (A × V) S
  obtain ⟨m, ⟨e⟩⟩ := (htyp.of_injective (LinearMap.inl A A V) LinearMap.inl_injective).linearEquiv_fun
  obtain ⟨n, ⟨f⟩⟩ := (htyp.of_injective (LinearMap.inr A A V) LinearMap.inr_injective).linearEquiv_fun
  rw [(e.restrictScalars K).finrank_eq, (f.restrictScalars K).finrank_eq] at h
  simp only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at h
  have hs : 0 < Module.finrank K S := Module.finrank_pos
  have hmn : m = n := Nat.eq_of_mul_eq_mul_right hs h
  subst n
  exact ⟨e.trans f.symm⟩

variable {K : Type u} [Field K] (A : CSA.{u, u} K)

/-- A product of pairwise coprime monic irreducibles of total degree equal to the reduced
 degree is a reduced characteristic polynomial if each factor field splits the algebra. -/
theorem exists_reducedCharpoly_eq_prod_of_split {I : Type v} [Fintype I]
    (p : I → K[X]) (hp : ∀ i, (p i).Monic) (hirr : ∀ i, Irreducible (p i))
    (hc : Pairwise (fun i j => IsCoprime (p i) (p j)))
    (hd : (∑ i, (p i).natDegree) = reducedDegree K A)
    (hs : ∀ i, letI : Fact (Irreducible (p i)) := ⟨hirr i⟩
      Brauer.IsSplit (Brauer.baseChange (AdjoinRoot (p i)) A)) :
    ∃ a : A, reducedCharpoly K A a = ∏ i, p i := by
  classical
  let E (i : I) := AdjoinRoot (p i)
  let _ (i : I) : Fact (Irreducible (p i)) := ⟨hirr i⟩
  let _ (i : I) : Field (E i) := inferInstanceAs (Field (AdjoinRoot (p i)))
  let _ (i : I) : FiniteDimensional K (E i) := (AdjoinRoot.powerBasis (hp i).ne_zero).finite
  let d := reducedDegree K A
  let V (i : I) := Fin d → E i
  let _ : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (reducedDegree_pos K A)
  have hchart (i : I) : Nonempty (E i ⊗[K] A ≃ₐ[E i] Matrix (Fin d) (Fin d) (E i)) := by
    obtain ⟨n, _, ⟨f⟩⟩ := hs i
    have hn : n = d := matrix_size_eq_reducedDegree K A (E i) n f
    subst n
    exact ⟨f⟩
  let rep (i : I) : A →ₐ[K] Module.End (E i) (V i) :=
    (((hchart i).some.trans Matrix.toLinAlgEquiv').restrictScalars K).toAlgHom.comp
      Algebra.TensorProduct.includeRight
  let _ (i : I) : Module A (V i) := Module.compHom (V i) (rep i).toRingHom
  let _ (i : I) : IsScalarTower K A (V i) := ⟨fun k a x => by
    change rep i (k • a) x = k • rep i a x
    rw [map_smul, LinearMap.smul_apply]⟩
  have hm (i : I) : Module.finrank K (V i) = (p i).natDegree * d := by
    rw [← Module.finrank_mul_finrank K (E i) (V i)]
    have hE : Module.finrank K (E i) = (p i).natDegree :=
      (AdjoinRoot.powerBasis (hp i).ne_zero).finrank
    rw [hE]
    simp [V]
  have heq : Module.finrank K A = Module.finrank K ((i : I) → V i) := by
    rw [Module.finrank_pi_fintype, finrank_eq_reducedDegree_mul_self]
    simp only [hm, ← Finset.sum_mul, hd, d]
  obtain ⟨e⟩ := nonempty_regularModuleEquiv_of_finrank_eq (K := K) (A := A) ((i : I) → V i) heq
  let r : ((i : I) → E i) →ₐ[K] Module.End A ((i : I) → V i) :=
    { toFun := fun s =>
        { toFun := fun x i => s i • x i
          map_add' := fun x y => funext fun i => smul_add (s i) (x i) (y i)
          map_smul' := fun a x => funext fun i => ((rep i a).map_smul (s i) (x i)).symm }
      map_one' := by
        apply LinearMap.ext
        intro x
        funext i
        exact one_smul (E i) (x i)
      map_mul' := by
        intro s t
        apply LinearMap.ext
        intro x
        funext i
        exact mul_smul (s i) (t i) (x i)
      map_zero' := by
        apply LinearMap.ext
        intro x
        funext i
        exact zero_smul (E i) (x i)
      map_add' := by
        intro s t
        apply LinearMap.ext
        intro x
        funext i
        exact add_smul (s i) (t i) (x i)
      commutes' := by
        intro k
        apply LinearMap.ext
        intro x
        funext i
        exact algebraMap_smul (E i) k (x i) }
  have hr : Function.Injective r := by
    intro s t h
    funext i
    obtain ⟨j⟩ := (inferInstance : Nonempty (Fin d))
    have hz := congrArg (fun f : Module.End A ((i : I) → V i) => f (fun i j => 1) i j) h
    change s i * 1 = t i * 1 at hz
    simpa only [mul_one] using hz
  let t : (i : I) → E i := fun i => AdjoinRoot.root (p i)
  let R := (e.conjAlgEquiv K).symm
  let a : A := ((AlgEquiv.moduleEndSelf K).symm (R (r t))).unop
  have ha : (e.conjAlgEquiv K) (AlgEquiv.moduleEndSelf K (MulOpposite.op a)) = r t := by
    simp only [a, R, MulOpposite.op_unop, AlgEquiv.apply_symm_apply]
  let g := reducedCharpoly K A a
  have hg : aeval (r t) g = 0 := by
    rw [← ha, aeval_algHom_apply, aeval_algHom_apply, aeval_op_apply, aeval_reducedCharpoly,
      MulOpposite.op_zero, map_zero, map_zero]
  have ht : aeval t g = 0 := by
    apply hr
    rw [← aeval_algHom_apply, hg, map_zero]
  have hdiv (i : I) : p i ∣ g := by
    have hz := congrArg (Pi.evalAlgHom K E i) ht
    rw [← aeval_algHom_apply, map_zero] at hz
    change aeval (AdjoinRoot.root (p i)) g = 0 at hz
    rw [AdjoinRoot.aeval_eq] at hz
    exact AdjoinRoot.mk_eq_zero.mp hz
  have hdiv' : (∏ i, p i) ∣ g := Fintype.prod_dvd_of_coprime hc hdiv
  refine ⟨a, eq_of_monic_of_dvd_of_natDegree_le (monic_prod_of_monic _ _ fun i _ => hp i)
    (reducedCharpoly_monic K A a) hdiv' ?_⟩
  rw [reducedCharpoly_natDegree, natDegree_prod_of_monic Finset.univ p (fun i _ => hp i), hd]

/-- The factor-field splitting criterion suffices to realize a monic separable polynomial
of the reduced degree as a reduced characteristic polynomial. -/
theorem exists_reducedCharpoly_eq_of_split_factors (f : K[X]) (hf : f.Monic)
    (hsep : f.Separable) (hd : f.natDegree = reducedDegree K A)
    (hs : ∀ p : K[X], p.Monic → ∀ hp : Irreducible p, p ∣ f →
      letI : Fact (Irreducible p) := ⟨hp⟩
      Brauer.IsSplit (Brauer.baseChange (AdjoinRoot p) A)) :
    ∃ a : A, reducedCharpoly K A a = f := by
  classical
  let S := (normalizedFactors f).toFinset
  let p : S → K[X] := Subtype.val
  have hmem (i : S) : p i ∈ normalizedFactors f := Multiset.mem_toFinset.mp i.property
  have hfac (i : S) : Irreducible (p i) ∧ (p i).Monic ∧ p i ∣ f :=
    (Polynomial.mem_normalizedFactors_iff hf.ne_zero).mp (hmem i)
  have hprod : (∏ i : S, p i) = f := by
    rw [show (∏ i : S, p i) = ∏ i ∈ S, i from Finset.prod_coe_sort S id]
    have hn := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hf.ne_zero).mp
      hsep.squarefree
    change S.prod id = f
    rw [← Finset.prod_val S]
    rw [show S.val = normalizedFactors f from (Multiset.toFinset_val _).trans hn.dedup]
    simpa only [hf.leadingCoeff, map_one, one_mul] using leadingCoeff_mul_prod_normalizedFactors f
  have hc : Pairwise (fun i j : S => IsCoprime (p i) (p j)) := by
    intro i j hij
    by_contra h
    have hdiv := (hfac i).1.dvd_iff_not_isCoprime.mpr h
    apply hij
    exact Subtype.ext (eq_of_monic_of_associated (hfac i).2.1 (hfac j).2.1
      ((hfac i).1.associated_of_dvd (hfac j).1 hdiv))
  have hdeg : (∑ i : S, (p i).natDegree) = reducedDegree K A := by
    rw [← natDegree_prod_of_monic Finset.univ p (fun i _ => (hfac i).2.1), hprod, hd]
  obtain ⟨a, ha⟩ := exists_reducedCharpoly_eq_prod_of_split A p
    (fun i => (hfac i).2.1) (fun i => (hfac i).1) hc hdeg
    (fun i => hs _ (hfac i).2.1 (hfac i).1 (hfac i).2.2)
  exact ⟨a, ha.trans hprod⟩

/-- The sufficiency direction of the splitting-field criterion for separable polynomials. -/
def ReducedCharpolyFromSplitFactorsStatement : Prop :=
  ∀ (K : Type u) [Field K] (A : CSA.{u, u} K) (f : K[X]), f.Monic → f.Separable →
    f.natDegree = reducedDegree K A →
    (∀ p : K[X], p.Monic → ∀ hp : Irreducible p, p ∣ f →
      letI : Fact (Irreducible p) := ⟨hp⟩
      Brauer.IsSplit (Brauer.baseChange (AdjoinRoot p) A)) →
    ∃ a : A, reducedCharpoly K A a = f

/-- A separable polynomial with splitting factor fields is realized by an algebra element. -/
theorem reducedCharpolyFromSplitFactors : ReducedCharpolyFromSplitFactorsStatement.{u} := by
  intro K _ A f hf hsep hd hs
  exact exists_reducedCharpoly_eq_of_split_factors A f hf hsep hd hs

end Langlands.CentralSimple
