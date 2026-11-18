import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.Algebra.MvPolynomial.Derivation
import Langlands.Algebra.SymmetricAlgebraHomogeneous

/-! # Endomorphism derivations of the genuine symmetric algebra -/

noncomputable section

universe u v w

namespace Langlands.Algebra.SymmetricDerivation

open Module

variable {R : Type u} {M : Type v} {I : Type w}
  [CommRing R] [AddCommGroup M] [Module R M]

/-- The derivation of the genuine symmetric algebra induced by a module
endomorphism, constructed in the polynomial coordinates of a supplied basis. -/
def ofBasis (b : Basis I R M) (f : Module.End R M) :
    Derivation R (SymmetricAlgebra R M) (SymmetricAlgebra R M) where
  toLinearMap :=
    (SymmetricAlgebra.equivMvPolynomial b).symm.toLinearMap.comp
      ((MvPolynomial.mkDerivation R (fun i =>
        SymmetricAlgebra.equivMvPolynomial b (SymmetricAlgebra.ι R M (f (b i))))).toLinearMap.comp
          (SymmetricAlgebra.equivMvPolynomial b).toLinearMap)
  map_one_eq_zero' := by simp
  leibniz' a c := by
    change (SymmetricAlgebra.equivMvPolynomial b).symm
      (MvPolynomial.mkDerivation R (fun i =>
        SymmetricAlgebra.equivMvPolynomial b (SymmetricAlgebra.ι R M (f (b i))))
          (SymmetricAlgebra.equivMvPolynomial b (a * c))) = _
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, AlgEquiv.symm_apply_apply]
    rfl

@[simp]
theorem ofBasis_ι (b : Basis I R M) (f : Module.End R M) (x : M) :
    ofBasis b f (SymmetricAlgebra.ι R M x) = SymmetricAlgebra.ι R M (f x) := by
  have h : (ofBasis b f).toLinearMap.comp (SymmetricAlgebra.ι R M) =
      (SymmetricAlgebra.ι R M).comp f := by
    apply b.ext
    intro i
    simp [ofBasis]
  exact LinearMap.congr_fun h x

/-- Endomorphism derivations do not depend on the polynomial basis used to
construct them. -/
theorem ofBasis_eq {J : Type*} (b : Basis I R M) (c : Basis J R M)
    (f : Module.End R M) : ofBasis b f = ofBasis c f := by
  apply Derivation.ext
  intro a
  induction a using SymmetricAlgebra.induction with
  | algebraMap r => simp
  | add a c ha hc => simp only [map_add, ha, hc]
  | ι x => simp
  | mul a c ha hc => simp only [Derivation.leibniz, ha, hc]

/-- The canonical derivation induced by an endomorphism of a free module. -/
def induced [Module.Free R M] (f : Module.End R M) :
    Derivation R (SymmetricAlgebra R M) (SymmetricAlgebra R M) :=
  ofBasis (Module.Free.chooseBasis R M) f

@[simp]
theorem induced_ι [Module.Free R M] (f : Module.End R M) (x : M) :
    induced f (SymmetricAlgebra.ι R M x) = SymmetricAlgebra.ι R M (f x) :=
  ofBasis_ι _ _ _

open SymmetricGrading

/-- The induced derivation preserves each genuine homogeneous component. -/
theorem induced_mem_homogeneousSpan [Module.Free R M] (f : Module.End R M)
    (d : ℕ) {a : SymmetricAlgebra R M} (ha : a ∈ homogeneousSpan R M d) :
    induced f a ∈ homogeneousSpan R M d := by
  have hprod : ∀ l : List M,
      induced f ((l.map (SymmetricAlgebra.ι R M)).prod) ∈
        homogeneousSpan R M l.length := by
    intro l
    induction l with
    | nil => simp
    | cons x l ih =>
      simp only [List.map_cons, List.prod_cons, Derivation.leibniz, induced_ι,
        smul_eq_mul]
      apply (homogeneousSpan R M (x :: l).length).add_mem
      · simpa only [List.length_cons, Nat.add_comm 1] using
          mul_mem_homogeneousSpan R M
            (show SymmetricAlgebra.ι R M x ∈ homogeneousSpan R M 1 from
              by simpa using prod_mem_homogeneousSpan R M [x]) ih
      · simpa only [List.length_cons] using
          mul_mem_homogeneousSpan R M
            (prod_mem_homogeneousSpan R M l)
            (show SymmetricAlgebra.ι R M (f x) ∈ homogeneousSpan R M 1 from
              by simpa using prod_mem_homogeneousSpan R M [f x])
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨l, rfl, rfl⟩ := ha
    exact hprod l
  | zero => simp
  | add a c ha hc iha ihc =>
    simpa only [map_add] using (homogeneousSpan R M d).add_mem iha ihc
  | smul r a ha iha =>
    simpa only [Derivation.map_smul] using (homogeneousSpan R M d).smul_mem r iha

/-- The induced endomorphism of an individual homogeneous component. -/
def homogeneous [Module.Free R M] (f : Module.End R M) (d : ℕ) :
    Module.End R (homogeneousSpan R M d) :=
  (induced f).toLinearMap.restrict (fun _ ha => induced_mem_homogeneousSpan f d ha)

@[simp]
theorem homogeneous_apply [Module.Free R M] (f : Module.End R M) (d : ℕ)
    (a : homogeneousSpan R M d) : (homogeneous f d a : SymmetricAlgebra R M) =
      induced f a := rfl

end Langlands.Algebra.SymmetricDerivation
