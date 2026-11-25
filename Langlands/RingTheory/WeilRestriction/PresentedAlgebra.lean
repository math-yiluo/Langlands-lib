module

public import Langlands.RingTheory.Extension.Presentation.MapsOut
public import Langlands.RingTheory.IsTensorProduct.PushoutExt
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TensorProduct.Finite

/-! # The algebra representing tensor-valued points along a finite projective extension

Let `B` be an `A`-algebra that is finite and projective as an `A`-module. For a presentation `P`
of a `B`-algebra `C`, `Langlands.Algebra.WeilRestriction.OfPresentation A B P` is an `A`-algebra
representing `T ↦ (C →ₐ[B] B ⊗[A] T)`, with universal point `OfPresentation.universalPoint` and
representing bijection `OfPresentation.homEquiv`. For finitely presented `C`,
`Langlands.Algebra.WeilRestriction A B C` is the instance attached to Mathlib's chosen finite
presentation; it is finitely presented over `A` (`WeilRestriction.instFinitePresentation`), its
bijection `WeilRestriction.homEquiv` is natural in `T` (`WeilRestriction.homEquiv_comp`), it is
functorial in `C` (`WeilRestriction.map`), and for `C = B ⊗[A] D` it represents
`T ↦ (D →ₐ[A] T ⊗[A] B)` (`WeilRestriction.tensorHomEquiv`).
-/

noncomputable section

open Algebra MvPolynomial TensorProduct

namespace Langlands.Algebra.WeilRestriction

private structure Frame (A B : Type*) [CommSemiring A] [AddCommMonoid B] [Module A B] where
  size : ℕ
  vector : Fin size → B
  dual : Fin size → Module.Dual A B
  expand (b : B) : ∑ j, dual j b • vector j = b

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
  {ι σ : Type*}

private def frame (A B : Type*) [CommSemiring A] [AddCommMonoid B] [Module A B]
    [Module.Finite A B] [Module.Projective A B] : Frame A B := by
  apply Classical.choice
  obtain ⟨n, p, s, _, _, split⟩ := Module.Finite.exists_comp_eq_id_of_projective A B
  refine ⟨⟨n, fun j => p (Pi.single j 1), fun j => (LinearMap.proj j).comp s, ?_⟩⟩
  intro b
  calc
    _ = p (∑ j, s b j • Pi.single j 1) := by simp
    _ = p (s b) := congrArg p (pi_eq_sum_univ' _).symm
    _ = b := LinearMap.congr_fun split b

variable (F : Frame A B) {T U : Type*} [CommRing T] [Algebra A T] [CommRing U] [Algebra A U]

private def coeff (j : Fin F.size) : B ⊗[A] T →ₗ[A] T :=
  _root_.TensorProduct.lift (LinearMap.lsmul A T ∘ₗ F.dual j)

private theorem expandTensor (w : B ⊗[A] T) :
    ∑ j : Fin F.size, (F.vector j ⊗ₜ[A] coeff F j w) = w := by
  induction w using TensorProduct.inductionOn with
  | tmul b t =>
    change ∑ j : Fin F.size, (F.vector j ⊗ₜ[A] (F.dual j b • t)) = b ⊗ₜ[A] t
    conv_rhs => rw [← F.expand b, sum_tmul]
    simp only [smul_tmul]
  | add x y hx hy => simpa [tmul_add, Finset.sum_add_distrib] using congrArg₂ (· + ·) hx hy

private theorem coeff_map (g : T →ₐ[A] U) (j : Fin F.size) (w : B ⊗[A] T) :
    coeff F j (Algebra.TensorProduct.lTensor (S := B) B g w) = g (coeff F j w) := by
  induction w using TensorProduct.inductionOn with
  | tmul b t => exact (map_smul g (F.dual j b) t).symm
  | add x y hx hy => simp_all

private abbrev Polys (ι : Type*) := MvPolynomial (ι × Fin F.size) A

private def generic (i : ι) : B ⊗[A] Polys F ι := ∑ j : Fin F.size, (F.vector j ⊗ₜ[A] X (i, j))

private def evaluate (z : ι → B ⊗[A] T) : Polys F ι →ₐ[A] T :=
  aeval fun (ij : ι × Fin F.size) => coeff F ij.2 (z ij.1)

private theorem evaluate_generic (z : ι → B ⊗[A] T) (i : ι) :
    Algebra.TensorProduct.lTensor (S := B) B (evaluate F z) (generic F i) = z i := by
  simpa [evaluate, generic] using expandTensor F (z i)

variable (P : Presentation B C ι σ)

private def equation : (ι × Fin F.size) ⊕ (σ × Fin F.size) → Polys F ι :=
  Sum.elim (fun ij => X ij - coeff F ij.2 (generic F ij.1))
    (fun rj => coeff F rj.2 (aeval (generic F) (P.relation rj.1)))

private abbrev equations := Ideal.span (Set.range (equation F P))
private abbrev Model := Polys F ι ⧸ equations F P
private abbrev quotient := Ideal.Quotient.mkₐ A (equations F P)

private theorem quotient_equation (q) : quotient F P (equation F P q) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self q))

private abbrev reduceTensor : B ⊗[A] Polys F ι →ₐ[B] B ⊗[A] Model F P :=
  Algebra.TensorProduct.lTensor B (quotient F P)

private theorem reduce_coeff (r : σ) (j : Fin F.size) :
    coeff F j (reduceTensor F P (aeval (generic F) (P.relation r))) = 0 := by
  exact (coeff_map F (quotient F P) j _).trans (quotient_equation F P (.inr (r, j)))

private theorem reduce_relation (r : σ) :
    reduceTensor F P (aeval (generic F) (P.relation r)) = 0 := by
  rw [← expandTensor F (reduceTensor F P _)]
  simp only [reduce_coeff, tmul_zero, Finset.sum_const_zero]

private theorem vanish_relation (r : σ) :
    aeval (fun i => reduceTensor F P (generic F i)) (P.relation r) = 0 := by
  have commute := MvPolynomial.comp_aeval_apply (R := B) (σ := ι) (S₁ := B ⊗[A] Polys F ι)
    (B := B ⊗[A] Model F P) (generic F) (reduceTensor F P) (P.relation r)
  exact commute.symm.trans (reduce_relation F P r)

private def universal : C →ₐ[B] B ⊗[A] Model F P :=
  P.lift (fun i => reduceTensor F P (generic F i)) (vanish_relation F P)

private theorem universal_val (i : ι) :
    universal F P (P.val i) = reduceTensor F P (generic F i) := by
  unfold universal
  rw [Presentation.lift_val]

private theorem evaluate_equation (h : C →ₐ[B] B ⊗[A] T) (q) :
    evaluate F (h ∘ P.val) (equation F P q) = 0 := by
  rcases q with ⟨i, j⟩ | ⟨r, j⟩
  · change evaluate F _ (X (i, j) - coeff F j (generic F i)) = 0
    rw [map_sub, ← coeff_map, evaluate_generic, sub_eq_zero]
    exact aeval_X _ _
  · change evaluate F _ (coeff F j _) = 0
    rw [← coeff_map, comp_aeval_apply]
    simp only [Function.comp_def, evaluate_generic]
    simp only [← Function.comp_def, ← comp_aeval_apply, P.aeval_val_relation, map_zero]

private def classify (h : C →ₐ[B] B ⊗[A] T) : Model F P →ₐ[A] T :=
  Ideal.Quotient.liftₐ _ (evaluate F (h ∘ P.val)) (by
    have hk : equations F P ≤ RingHom.ker (evaluate F (h ∘ P.val)) :=
      Ideal.span_le.mpr (Set.range_subset_iff.mpr (evaluate_equation F P h))
    exact fun p hp => hk hp)

private theorem classify_poly (h : C →ₐ[B] B ⊗[A] T) :
    (classify F P h).comp (quotient F P) = evaluate F (h ∘ P.val) :=
  Ideal.Quotient.liftₐ_comp ..

private theorem specialize_generic (g : Model F P →ₐ[A] T) (i : ι) :
    Algebra.TensorProduct.lTensor (S := B) B g (universal F P (P.val i)) =
      Algebra.TensorProduct.lTensor (S := B) B (g.comp (quotient F P)) (generic F i) := by
  simp only [universal_val, Algebra.TensorProduct.lTensor, Algebra.TensorProduct.map_id_comp,
    AlgHom.comp_apply]

private def equivalence (T : Type*) [CommRing T] [Algebra A T] :
    (Model F P →ₐ[A] T) ≃ (C →ₐ[B] B ⊗[A] T) where
  toFun g := (Algebra.TensorProduct.lTensor (S := B) B g).comp (universal F P)
  invFun := classify F P
  right_inv h := by
    apply P.algHom_ext
    intro i
    change Algebra.TensorProduct.lTensor (S := B) B _ (universal F P (P.val i)) = _
    rw [specialize_generic, classify_poly]
    exact evaluate_generic F (h ∘ P.val) i
  left_inv g := by
    apply Ideal.Quotient.algHom_ext A
    rw [classify_poly]
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    have fix := quotient_equation F P (.inl (i, j))
    change quotient F P (X (i, j) - coeff F j (generic F i)) = 0 at fix
    rw [map_sub, sub_eq_zero] at fix
    simp only [evaluate, aeval_X, Function.comp_apply, AlgHom.comp_apply, specialize_generic,
      coeff_map]
    exact congrArg g fix.symm

end Langlands.Algebra.WeilRestriction

public section

namespace Langlands.Algebra.WeilRestriction

/-- The `A`-algebra representing `T ↦ (C →ₐ[B] B ⊗[A] T)`, built from a presentation `P` of
`C`. Only the generators need to be finite for it to be of finite type. -/
def OfPresentation (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [Module.Projective A B] {C ι σ : Type*}
    [CommRing C] [Algebra B C] (P : Presentation B C ι σ) : Type _ :=
  Model (frame A B) P
deriving CommRing, Algebra A

namespace OfPresentation

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]
  {C ι σ : Type*} [CommRing C] [Algebra B C] (P : Presentation B C ι σ)

/-- The universal point of `OfPresentation A B P`. -/
def universalPoint : C →ₐ[B] B ⊗[A] OfPresentation A B P := universal (frame A B) P

/-- The representing bijection: `g` goes to the universal point followed by `B ⊗[A] g`. -/
def homEquiv (T : Type*) [CommRing T] [Algebra A T] :
    (OfPresentation A B P →ₐ[A] T) ≃ (C →ₐ[B] B ⊗[A] T) := equivalence (frame A B) P T

variable {A B P} in
/-- Finitely many generators give an algebra of finite type, whatever the relations. -/
instance [Finite ι] : FiniteType A (OfPresentation A B P) := by
  change FiniteType A (Model (frame A B) P)
  exact FiniteType.of_surjective (quotient (frame A B) P) (Ideal.Quotient.mkₐ_surjective A _)

variable {A B P} in
/-- `homEquiv` composes the universal point with `B ⊗[A] g`. -/
@[simp]
theorem homEquiv_apply {T : Type*} [CommRing T] [Algebra A T] (g : OfPresentation A B P →ₐ[A] T) :
    homEquiv A B P T g = (Algebra.TensorProduct.lTensor B g).comp (universalPoint A B P) := by
  rfl

end OfPresentation
end Langlands.Algebra.WeilRestriction

namespace Langlands.Algebra

variable (A B C : Type*) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
  [Module.Finite A B] [Module.Projective A B] [FinitePresentation B C]

/-- The **Weil restriction** of a finitely presented `B`-algebra `C` along the finite projective
`A`-algebra `B`: an `A`-algebra representing `T ↦ (C →ₐ[B] B ⊗[A] T)`. -/
def WeilRestriction : Type _ :=
  WeilRestriction.OfPresentation A B (Presentation.ofFinitePresentation B C)
deriving CommRing, Algebra A

namespace WeilRestriction

/-- The universal point of the Weil restriction. -/
def universalPoint : C →ₐ[B] B ⊗[A] WeilRestriction A B C :=
  OfPresentation.universalPoint A B (Presentation.ofFinitePresentation B C)

/-- The universal property of the Weil restriction. -/
def homEquiv (T : Type*) [CommRing T] [Algebra A T] :
    (WeilRestriction A B C →ₐ[A] T) ≃ (C →ₐ[B] B ⊗[A] T) :=
  OfPresentation.homEquiv A B (Presentation.ofFinitePresentation B C) T

variable {A B C} in
/-- The Weil restriction is finitely presented: finitely many variables, finitely many equations. -/
instance instFinitePresentation : FinitePresentation A (WeilRestriction A B C) := by
  apply FinitePresentation.quotient
  apply Submodule.fg_span
  exact Set.finite_range _

variable {A B C} {T : Type*} [CommRing T] [Algebra A T]

/-- `homEquiv` composes the universal point with `B ⊗[A] g`. -/
@[simp] theorem homEquiv_apply (g : WeilRestriction A B C →ₐ[A] T) :
    homEquiv A B C T g =
      (Algebra.TensorProduct.lTensor (S := B) B g).comp (universalPoint A B C) := by rfl

/-- Naturality of `homEquiv` in the test algebra. -/
theorem homEquiv_comp {T' : Type*} [CommRing T'] [Algebra A T']
    (g : WeilRestriction A B C →ₐ[A] T) (h : T →ₐ[A] T') :
    homEquiv A B C T' (h.comp g) =
      (Algebra.TensorProduct.lTensor (S := B) B h).comp (homEquiv A B C T g) := by
  rw [homEquiv_apply, homEquiv_apply]
  exact congrArg (fun k => AlgHom.comp k (universalPoint A B C))
    (Algebra.TensorProduct.map_id_comp h g)

/-- Maps out of the Weil restriction are determined by the points they classify. -/
@[ext] theorem hom_ext {g₁ g₂ : WeilRestriction A B C →ₐ[A] T}
    (h : (Algebra.TensorProduct.lTensor (S := B) B g₁).comp (universalPoint A B C) =
      (Algebra.TensorProduct.lTensor (S := B) B g₂).comp (universalPoint A B C)) : g₁ = g₂ :=
  (homEquiv A B C T).injective h

variable {D : Type*} [CommRing D] [Algebra B D] [FinitePresentation B D]

variable (A B) in
/-- The map of Weil restrictions classifying the universal point of `D` precomposed with `φ`. -/
def map (φ : C →ₐ[B] D) : WeilRestriction A B C →ₐ[A] WeilRestriction A B D :=
  (homEquiv A B C _).symm <| (universalPoint A B D).comp φ

/-- `map φ` classifies the universal point of `D` precomposed with `φ`. -/
theorem homEquiv_map (φ : C →ₐ[B] D) :
    homEquiv A B C _ (map A B φ) = (universalPoint A B D).comp φ := by
  exact (homEquiv A B C _).apply_symm_apply _

/-- `map φ` carries the universal point of `C` to the universal point of `D`, along `φ`. -/
@[simp]
theorem lTensor_map_universalPoint (φ : C →ₐ[B] D) (c : C) :
    Algebra.TensorProduct.lTensor (S := B) B (map A B φ) (universalPoint A B C c) =
      universalPoint A B D (φ c) := by
  have h := homEquiv_map (A := A) φ
  rw [homEquiv_apply] at h
  exact DFunLike.congr_fun h c

/-- The identity of `C` induces the identity of the Weil restriction. -/
@[simp]
theorem map_id : map A B (AlgHom.id B C) = AlgHom.id A (WeilRestriction A B C) := by
  apply (homEquiv A B C _).injective
  rw [homEquiv_map, homEquiv_apply, AlgHom.comp_id]
  simp only [Algebra.TensorProduct.lTensor, Algebra.TensorProduct.map_id, AlgHom.id_comp]

section Tensor

variable (A B D : Type*) [CommRing A] [CommRing B] [CommRing D] [Algebra A B] [Algebra A D]
  [Module.Finite A B] [Module.Projective A B] [FinitePresentation A D] (T : Type*) [CommRing T]
  [Algebra A T]

/-- For `C = B ⊗[A] D`, maps out of the Weil restriction are `A`-algebra maps `D → T ⊗[A] B`. -/
def tensorHomEquiv : (WeilRestriction A B (B ⊗[A] D) →ₐ[A] T) ≃ (D →ₐ[A] T ⊗[A] B) :=
  let restrict := (AlgHom.liftEquiv A B D (B ⊗[A] T)).symm
  ((homEquiv A B (B ⊗[A] D) T).trans restrict).trans
    (AlgEquiv.arrowCongr AlgEquiv.refl (Algebra.TensorProduct.comm A B T))

variable {A B D T}

private theorem tensorHomEquiv_apply (g : WeilRestriction A B (B ⊗[A] D) →ₐ[A] T) (d : D) :
    tensorHomEquiv A B D T g d =
      Algebra.TensorProduct.comm A B T (homEquiv A B (B ⊗[A] D) T g (1 ⊗ₜ d)) := by rfl

/-- Naturality of `tensorHomEquiv` in the test algebra. -/
theorem tensorHomEquiv_comp {T' : Type*} [CommRing T'] [Algebra A T']
    (g : WeilRestriction A B (B ⊗[A] D) →ₐ[A] T) (k : T →ₐ[A] T') :
    tensorHomEquiv A B D T' (k.comp g) =
      (Algebra.TensorProduct.map k (AlgHom.id A B)).comp (tensorHomEquiv A B D T g) := by
  apply AlgHom.ext
  intro d
  simp only [AlgHom.comp_apply, tensorHomEquiv_apply, homEquiv_comp]
  exact Algebra.TensorProduct.comm_comp_map_apply (.id A B) k _

end Tensor
end WeilRestriction
end Langlands.Algebra
