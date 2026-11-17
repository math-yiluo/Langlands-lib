import Mathlib.RingTheory.Bialgebra.TensorProduct
import Langlands.AnthropicFLT.Theorems.Thm_Algebra_exists_algEquiv_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit

/-! # Bialgebra isomorphisms spread along filtered scalar extensions -/

noncomputable section

universe u v w z

open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.BialgebraSpreading

section TensorSquare

variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (A : Type w) [CommRing A] [Algebra R A]

/-- Scalar extension commutes with the tensor square. -/
def tensorSquareIso : (S ⊗[R] A) ⊗[S] (S ⊗[R] A) ≃ₐ[S] S ⊗[R] (A ⊗[R] A) :=
  (Algebra.TensorProduct.tensorTensorTensorComm R R S S S A S A).trans
    (Algebra.TensorProduct.congr (Algebra.TensorProduct.lid S S)
      (AlgEquiv.refl : (A ⊗[R] A) ≃ₐ[R] (A ⊗[R] A)))

@[simp]
theorem tensorSquareIso_tmul (s t : S) (a b : A) :
    tensorSquareIso R S A ((s ⊗ₜ[R] a) ⊗ₜ[S] (t ⊗ₜ[R] b)) =
      (s * t) ⊗ₜ[R] (a ⊗ₜ[R] b) := by
  simp [tensorSquareIso]

@[simp]
theorem tensorSquareIso_symm_tmul (s : S) (a b : A) :
    (tensorSquareIso R S A).symm (s ⊗ₜ[R] (a ⊗ₜ[R] b)) =
      (s ⊗ₜ[R] a) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] b) := by
  apply (tensorSquareIso R S A).injective
  simp

end TensorSquare

section Bialgebra

variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (A : Type w) [CommRing A] [Bialgebra R A]

/-- The comultiplication of a scalar extension in the scalar extension of
the original tensor square. -/
def comul : S ⊗[R] A →ₐ[S] S ⊗[R] (A ⊗[R] A) :=
  Algebra.TensorProduct.map (AlgHom.id S S) (Bialgebra.comulAlgHom R A)

/-- The counit of a scalar extension before cancelling its scalar tensor factor. -/
def counit : S ⊗[R] A →ₐ[S] S ⊗[R] R :=
  Algebra.TensorProduct.map (AlgHom.id S S) (Bialgebra.counitAlgHom R A)

theorem tensorSquareIso_comul (x : S ⊗[R] A) :
    tensorSquareIso R S A (Coalgebra.comul (R := S) x) = comul R S A x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s a =>
    rw [TensorProduct.comul_tmul]
    change tensorSquareIso R S A
      (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R S R S S S A A
        (Coalgebra.comul (R := S) s ⊗ₜ[R] Coalgebra.comul (R := R) a)) =
        s ⊗ₜ[R] Coalgebra.comul (R := R) a
    rw [CommSemiring.comul_apply]
    induction Coalgebra.comul (R := R) a using TensorProduct.inductionOn with
    | add x y hx hy => simp_all only [TensorProduct.tmul_add, map_add]
    | tmul a b => simp [tensorSquareIso, Algebra.TensorProduct.map_tmul]

theorem rid_counit (x : S ⊗[R] A) :
    Algebra.TensorProduct.rid R S S (counit R S A x) = Coalgebra.counit (R := S) x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s a => simp [counit, TensorProduct.counit_tmul, Algebra.smul_def]

end Bialgebra

section Transition

variable {R : Type u} [CommRing R]
    {S : Type v} [CommRing S] [Algebra R S]
    {T : Type z} [CommRing T] [Algebra R T]
    {A B C : Type w} [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]

/-- The transition on scalar extensions induced by an algebra map. -/
abbrev transition (f : S →ₐ[R] T) (A : Type w) [CommRing A] [Algebra R A] :=
  Algebra.TensorProduct.map f (AlgHom.id R A)

/-- Extend a map of scalar extensions along a map of coefficient rings. -/
def extend (f : S →ₐ[R] T) (φ : S ⊗[R] A →ₐ[S] S ⊗[R] B) :
    T ⊗[R] A →ₐ[T] T ⊗[R] B :=
  Algebra.TensorProduct.lift Algebra.TensorProduct.includeLeft
    ((transition f B).comp ((φ.restrictScalars R).comp Algebra.TensorProduct.includeRight))
    (fun _ _ => Commute.all _ _)

@[simp]
theorem extend_tmul (f : S →ₐ[R] T) (φ : S ⊗[R] A →ₐ[S] S ⊗[R] B)
    (t : T) (a : A) :
    extend f φ (t ⊗ₜ[R] a) =
      (t ⊗ₜ[R] (1 : B)) * transition f B (φ ((1 : S) ⊗ₜ[R] a)) := rfl

theorem hom_tmul (φ : S ⊗[R] A →ₐ[S] S ⊗[R] B) (s : S) (a : A) :
    φ (s ⊗ₜ[R] a) = (s ⊗ₜ[R] (1 : B)) * φ ((1 : S) ⊗ₜ[R] a) := by
  have hc : φ (s ⊗ₜ[R] (1 : A)) = s ⊗ₜ[R] (1 : B) := by
    simpa using φ.commutes s
  rw [← hc, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem extend_transition (f : S →ₐ[R] T) (φ : S ⊗[R] A →ₐ[S] S ⊗[R] B)
    (x : S ⊗[R] A) :
    extend f φ (transition f A x) = transition f B (φ x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s a =>
    simp only [transition, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, extend_tmul]
    rw [hom_tmul φ s a, map_mul]
    simp only [Algebra.TensorProduct.map_tmul, map_one]

theorem extend_id (f : S →ₐ[R] T) :
    extend f (AlgHom.id S (S ⊗[R] A)) = AlgHom.id T (T ⊗[R] A) := by
  apply Algebra.TensorProduct.ext
  · exact Subsingleton.elim _ _
  · ext a
    simp [extend_tmul, transition]

theorem extend_comp (f : S →ₐ[R] T) (φ : S ⊗[R] A →ₐ[S] S ⊗[R] B)
    (ψ : S ⊗[R] B →ₐ[S] S ⊗[R] C) :
    (extend f ψ).comp (extend f φ) = extend f (ψ.comp φ) := by
  apply Algebra.TensorProduct.ext
  · exact Subsingleton.elim _ _
  · ext a
    change extend f ψ (extend f φ ((1 : T) ⊗ₜ[R] a)) =
      extend f (ψ.comp φ) ((1 : T) ⊗ₜ[R] a)
    simp only [extend_tmul, ← Algebra.TensorProduct.one_def, one_mul, AlgHom.comp_apply]
    exact extend_transition f ψ (φ ((1 : S) ⊗ₜ[R] a))

/-- Extend an algebra equivalence along a map of coefficient rings. -/
def extendEquiv (f : S →ₐ[R] T) (e : S ⊗[R] A ≃ₐ[S] S ⊗[R] B) :
    T ⊗[R] A ≃ₐ[T] T ⊗[R] B :=
  AlgEquiv.ofAlgHom (extend f e.toAlgHom) (extend f e.symm.toAlgHom)
    (by rw [extend_comp, e.comp_symm, extend_id])
    (by rw [extend_comp, e.symm_comp, extend_id])

theorem tensorSquareIso_transition (f : S →ₐ[R] T) (x y : S ⊗[R] A) :
    transition f (A ⊗[R] A) (tensorSquareIso R S A (x ⊗ₜ[S] y)) =
      tensorSquareIso R T A (transition f A x ⊗ₜ[T] transition f A y) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
  | tmul s a =>
    induction y using TensorProduct.inductionOn with
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | tmul t b => simp [transition, map_mul]

/-- Tensor squares of maps, expressed over the original coefficient ring. -/
def tensorSquareMap (φ : S ⊗[R] A →ₐ[S] S ⊗[R] B) :
    S ⊗[R] (A ⊗[R] A) →ₐ[S] S ⊗[R] (B ⊗[R] B) :=
  (tensorSquareIso R S B).toAlgHom.comp
    ((Algebra.TensorProduct.map φ φ).comp (tensorSquareIso R S A).symm.toAlgHom)

theorem tensorSquareMap_transition (f : S →ₐ[R] T)
    (φ : S ⊗[R] A →ₐ[S] S ⊗[R] B) (ψ : T ⊗[R] A →ₐ[T] T ⊗[R] B)
    (h : ∀ x, ψ (transition f A x) = transition f B (φ x))
    (x : S ⊗[R] (A ⊗[R] A)) :
    transition f (B ⊗[R] B) (tensorSquareMap φ x) =
      tensorSquareMap ψ (transition f (A ⊗[R] A) x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s x =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | tmul a b =>
      simp only [tensorSquareMap, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
        tensorSquareIso_symm_tmul, Algebra.TensorProduct.map_tmul]
      rw [tensorSquareIso_transition]
      rw [← h, ← h]
      simp [transition]

end Transition

section BialgebraEquations

variable {R : Type u} [CommRing R]
    {S : Type v} [CommRing S] [Algebra R S]
    {T : Type z} [CommRing T] [Algebra R T]
    {A B : Type w} [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B]

theorem comul_transition (f : S →ₐ[R] T) (x : S ⊗[R] A) :
    transition f (A ⊗[R] A) (comul R S A x) = comul R T A (transition f A x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s a => simp [comul, transition]

theorem counit_transition (f : S →ₐ[R] T) (x : S ⊗[R] A) :
    transition f R (counit R S A x) = counit R T A (transition f A x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s a => simp [counit, transition]

/-- The scalar-extended counit and comultiplication equations suffice for a
bialgebra equivalence. -/
def ofFlatEquations (e : S ⊗[R] A ≃ₐ[S] S ⊗[R] B)
    (hε : (counit R S B).comp e.toAlgHom = counit R S A)
    (hδ : (tensorSquareMap e.toAlgHom).comp (comul R S A) =
      (comul R S B).comp e.toAlgHom) :
    S ⊗[R] A ≃ₐc[S] S ⊗[R] B := by
  refine BialgEquiv.ofAlgEquiv e ?_ ?_
  · apply AlgHom.ext
    intro x
    change Coalgebra.counit (R := S) (e x) = Coalgebra.counit (R := S) x
    have h := congrArg (Algebra.TensorProduct.rid R S S) (AlgHom.congr_fun hε x)
    simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, rid_counit] using h
  · apply AlgHom.ext
    intro x
    apply (tensorSquareIso R S B).injective
    have h := AlgHom.congr_fun hδ x
    change tensorSquareIso R S B ((Algebra.TensorProduct.map e.toAlgHom e.toAlgHom)
      ((tensorSquareIso R S A).symm (comul R S A x))) = comul R S B (e x) at h
    rw [← tensorSquareIso_comul R S A x, AlgEquiv.symm_apply_apply,
      ← tensorSquareIso_comul R S B (e x)] at h
    exact h

theorem counit_comp_bialgEquiv (e : S ⊗[R] A ≃ₐc[S] S ⊗[R] B) :
    (counit R S B).comp e.toAlgEquiv.toAlgHom = counit R S A := by
  apply AlgHom.ext
  intro x
  apply (Algebra.TensorProduct.rid R S S).injective
  change Algebra.TensorProduct.rid R S S (counit R S B (e x)) =
    Algebra.TensorProduct.rid R S S (counit R S A x)
  rw [rid_counit, rid_counit]
  exact CoalgHomClass.counit_comp_apply e x

theorem comul_comp_bialgEquiv (e : S ⊗[R] A ≃ₐc[S] S ⊗[R] B) :
    (tensorSquareMap e.toAlgEquiv.toAlgHom).comp (comul R S A) =
      (comul R S B).comp e.toAlgEquiv.toAlgHom := by
  apply AlgHom.ext
  intro x
  change tensorSquareMap e.toAlgEquiv.toAlgHom (comul R S A x) =
    comul R S B (e x)
  rw [← tensorSquareIso_comul R S A x]
  simp only [tensorSquareMap, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply]
  rw [← tensorSquareIso_comul R S B (e x)]
  apply (tensorSquareIso R S B).congr_arg
  exact CoalgHomClass.map_comp_comul_apply e x

end BialgebraEquations

section DirectedLimit

variable {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (R : Type u) [CommRing R]
    (G : ι → Type u) [∀ i, CommRing (G i)] [∀ i, Algebra R (G i)]
    (f : ∀ i j, i ≤ j → G i →ₐ[R] G j)
    [DirectedSystem G (fun i j h => ⇑(f i j h))]
    (L : Type u) [CommRing L] [Algebra R L]
    [∀ i, Algebra (G i) L] [∀ i, IsScalarTower R (G i) L]
    (hL : IsDirectLimit (fun i j h => ⇑(f i j h)) (fun i => ⇑(algebraMap (G i) L)))
    (A B : Type u) [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B]
    [Algebra.FinitePresentation R A] [Algebra.FinitePresentation R B]

include f hL in
/-- A bialgebra equivalence between finitely presented scalar extensions at
a directed limit already exists at one stage. -/
theorem exists_bialgEquiv
    (e : L ⊗[R] A ≃ₐc[L] L ⊗[R] B) :
    ∃ i, Nonempty (G i ⊗[R] A ≃ₐc[G i] G i ⊗[R] B) := by
  obtain ⟨i, e₀, he₀⟩ :=
    Algebra.exists_algEquiv_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit
      R G f L hL A B e.toAlgEquiv
  let l : G i →ₐ[R] L := IsScalarTower.toAlgHom R (G i) L
  have hrec (x : G i ⊗[R] A) : e (transition l A x) = transition l B (e₀ x) := he₀ x
  have hε (x : G i ⊗[R] A) :
      transition l R (((counit R (G i) B).comp e₀.toAlgHom) x) =
        transition l R (counit R (G i) A x) := by
    change transition l R (counit R (G i) B (e₀ x)) = _
    rw [counit_transition, ← hrec]
    have he := AlgHom.congr_fun (counit_comp_bialgEquiv e) (transition l A x)
    change counit R L B (e (transition l A x)) = counit R L A (transition l A x) at he
    rw [he, ← counit_transition]
  have hδ (x : G i ⊗[R] A) :
      transition l (B ⊗[R] B)
        (((tensorSquareMap e₀.toAlgHom).comp (comul R (G i) A)) x) =
      transition l (B ⊗[R] B) (((comul R (G i) B).comp e₀.toAlgHom) x) := by
    change transition l (B ⊗[R] B) (tensorSquareMap e₀.toAlgHom (comul R (G i) A x)) = _
    rw [tensorSquareMap_transition l e₀.toAlgHom e.toAlgEquiv.toAlgHom hrec,
      comul_transition]
    have he := AlgHom.congr_fun (comul_comp_bialgEquiv e) (transition l A x)
    change tensorSquareMap e.toAlgEquiv.toAlgHom (comul R L A (transition l A x)) =
      comul R L B (e (transition l A x)) at he
    rw [he, hrec, ← comul_transition]
    rfl
  obtain ⟨jε, hiε, hjε⟩ :=
    Algebra.exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit
      R G f L hL A R ((counit R (G i) B).comp e₀.toAlgHom) (counit R (G i) A) hε
  obtain ⟨jδ, hiδ, hjδ⟩ :=
    Algebra.exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit
      R G f L hL A (B ⊗[R] B)
      ((tensorSquareMap e₀.toAlgHom).comp (comul R (G i) A))
      ((comul R (G i) B).comp e₀.toAlgHom) hδ
  obtain ⟨k, hεk, hδk⟩ := exists_ge_ge jε jδ
  let hik : i ≤ k := hiε.trans hεk
  have hstep {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k)
      (C : Type u) [CommRing C] [Algebra R C] (x : G i ⊗[R] C) :
      transition (f j k hjk) C (transition (f i j hij) C x) =
        transition (f i k (hij.trans hjk)) C x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s c =>
      simp only [transition, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      congr 1
      exact DirectedSystem.map_map (f := fun i j h => ⇑(f i j h)) hij hjk s
  have hkε (x : G i ⊗[R] A) :
      transition (f i k hik) R (counit R (G i) B (e₀ x)) =
        transition (f i k hik) R (counit R (G i) A x) := by
    have hh := congrArg (transition (f jε k hεk) R) (hjε x)
    simpa only [hstep, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] using hh
  have hkδ (x : G i ⊗[R] A) :
      transition (f i k hik) (B ⊗[R] B) (tensorSquareMap e₀.toAlgHom (comul R (G i) A x)) =
        transition (f i k hik) (B ⊗[R] B) (comul R (G i) B (e₀ x)) := by
    have hh := congrArg (transition (f jδ k hδk) (B ⊗[R] B)) (hjδ x)
    simpa only [hstep, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] using hh
  let e₁ := extendEquiv (f i k hik) e₀
  have he₁ (x : G i ⊗[R] A) :
      e₁ (transition (f i k hik) A x) = transition (f i k hik) B (e₀ x) :=
    extend_transition (f i k hik) e₀.toAlgHom x
  refine ⟨k, ⟨ofFlatEquations e₁ ?_ ?_⟩⟩
  · have hh (x : G i ⊗[R] A) :
        counit R (G k) B (e₁ (transition (f i k hik) A x)) =
          counit R (G k) A (transition (f i k hik) A x) := by
      rw [he₁, ← counit_transition, ← counit_transition]
      exact hkε x
    apply Algebra.TensorProduct.ext
    · exact Subsingleton.elim _ _
    · ext a
      change counit R (G k) B (e₁ ((1 : G k) ⊗ₜ[R] a)) =
        counit R (G k) A ((1 : G k) ⊗ₜ[R] a)
      simpa only [transition, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
        using hh ((1 : G i) ⊗ₜ[R] a)
  · have hh (x : G i ⊗[R] A) :
        tensorSquareMap e₁.toAlgHom (comul R (G k) A (transition (f i k hik) A x)) =
          comul R (G k) B (e₁ (transition (f i k hik) A x)) := by
      rw [← comul_transition,
        ← tensorSquareMap_transition (f i k hik) e₀.toAlgHom e₁.toAlgHom he₁,
        he₁, ← comul_transition]
      exact hkδ x
    apply Algebra.TensorProduct.ext
    · exact Subsingleton.elim _ _
    · ext a
      change tensorSquareMap e₁.toAlgHom (comul R (G k) A ((1 : G k) ⊗ₜ[R] a)) =
        comul R (G k) B (e₁ ((1 : G k) ⊗ₜ[R] a))
      simpa only [transition, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
        using hh ((1 : G i) ⊗ₜ[R] a)

end DirectedLimit

end Langlands.BialgebraSpreading
