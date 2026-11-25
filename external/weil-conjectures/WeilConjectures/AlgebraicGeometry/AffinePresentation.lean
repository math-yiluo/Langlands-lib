/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RingHom.StandardSmooth

/-! # Affine presentations of schemes of finite type over a field

We collect elementary scheme-theoretic and commutative-algebra facts about affine schemes of
finite type over a field `k₀`:

* every affine `k₀`-scheme of finite type is isomorphic over `Spec k₀` to the spectrum of a
  quotient of a polynomial ring `k₀[X₀, …, X_{n-1}]`;
* the projection `Spec (k₀[X₀, …, Xₙ] ⧸ I) ⟶ 𝔸ⁿ` forgetting the last coordinate, and the
  description of its fibres over `k₀`-points as spectra of quotients of `k₀[X]`;
* finiteness of `Spec (k₀[X] ⧸ J)` for `J ≠ ⊥` and smoothness of `𝔸¹`;
* descent of Frobenius-fixed points of affine schemes over a finite field.
-/

@[expose] public section

universe u

open CategoryTheory Limits MvPolynomial

namespace AlgebraicGeometry

section SpecIso

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- An isomorphism of `R`-algebras `A ≃ₐ[R] B` induces an isomorphism `Spec B ≅ Spec A`. -/
noncomputable def specIsoOfAlgEquiv (ε : A ≃ₐ[R] B) : Spec (.of B) ≅ Spec (.of A) :=
  Scheme.Spec.mapIso ε.toRingEquiv.toCommRingCatIso.op

/-- The isomorphism `specIsoOfAlgEquiv` is `Spec.map` of the ring isomorphism. -/
lemma specIsoOfAlgEquiv_hom (ε : A ≃ₐ[R] B) :
    (specIsoOfAlgEquiv ε).hom = Spec.map (CommRingCat.ofHom ε.toRingHom) :=
  rfl

/-- The isomorphism `specIsoOfAlgEquiv` is compatible with the structure maps to `Spec R`. -/
@[reassoc (attr := simp)]
lemma specIsoOfAlgEquiv_hom_comp (ε : A ≃ₐ[R] B) :
    (specIsoOfAlgEquiv ε).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  rw [specIsoOfAlgEquiv_hom, ← Spec.map_comp]
  congr 1
  ext x
  simp

end SpecIso

section Presentation

variable {k₀ : Type u} [Field k₀]

/-- An affine scheme locally of finite type over a field `k₀` is isomorphic over `Spec k₀` to the
spectrum of a quotient of a polynomial ring in finitely many variables over `k₀`. -/
theorem exists_iso_spec_mvPolynomial_quotient {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (.of k₀))
    [IsAffine X₀] [LocallyOfFiniteType f₀] :
    ∃ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) k₀))
      (e : X₀ ≅ Spec (.of (MvPolynomial (Fin n) k₀ ⧸ I))),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ (MvPolynomial (Fin n) k₀ ⧸ I))) =
        f₀ := by
  let g : CommRingCat.of k₀ ⟶ Γ(X₀, ⊤) := (Scheme.ΓSpecIso _).inv ≫ f₀.appTop
  have hf₀ : f₀ = X₀.isoSpec.hom ≫ Spec.map g := by
    rw [Spec.map_comp, Scheme.isoSpec_hom_naturality_assoc, Scheme.isoSpec_hom,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have hg : g.hom.FiniteType := by
    have := HasRingHomProperty.appTop (P := @LocallyOfFiniteType) f₀ ‹_›
    exact this.comp (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.symm.surjective)
  let := g.hom.toAlgebra
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hg
  refine ⟨n, RingHom.ker f, X₀.isoSpec ≪≫ specIsoOfAlgEquiv
    (Ideal.quotientKerAlgEquivOfSurjective hf), ?_⟩
  rw [Iso.trans_hom, Category.assoc, specIsoOfAlgEquiv_hom_comp, hf₀]
  rfl


end Presentation

section BaseCases

variable {k₀ : Type u} [Field k₀]

/-- `Spec (k₀[∅] ⧸ I) ⟶ Spec k₀` is finite. -/
theorem isFinite_spec_mvPolynomial_fin_zero_quotient (I : Ideal (MvPolynomial (Fin 0) k₀)) :
    IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k₀ (MvPolynomial (Fin 0) k₀ ⧸ I)))) := by
  rw [IsFinite.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.finite_algebraMap]
  have : Module.Finite k₀ (MvPolynomial (Fin 0) k₀) :=
    Module.Finite.equiv (isEmptyAlgEquiv k₀ (Fin 0)).symm.toLinearEquiv
  exact Module.Finite.of_surjective (Ideal.Quotient.mkₐ k₀ I).toLinearMap
    Ideal.Quotient.mk_surjective

/-- For a nonzero ideal `J` of `k₀[X]`, the quotient `k₀[X] ⧸ J` is a finite `k₀`-module. -/
lemma module_finite_mvPolynomial_fin_one_quotient {J : Ideal (MvPolynomial (Fin 1) k₀)}
    (hJ : J ≠ ⊥) : Module.Finite k₀ (MvPolynomial (Fin 1) k₀ ⧸ J) := by
  obtain ⟨f, hfJ, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  let ε := uniqueAlgEquiv k₀ (Fin 1)
  have hg : ε f ≠ 0 := by simpa using hf0
  have : Module.Finite k₀ (Polynomial k₀ ⧸ Ideal.span {ε f}) := (AdjoinRoot.powerBasis hg).finite
  obtain ⟨φ, hφ⟩ : ∃ φ : (Polynomial k₀ ⧸ Ideal.span {ε f}) →ₐ[k₀] MvPolynomial (Fin 1) k₀ ⧸ J,
      ∀ p, φ (Ideal.Quotient.mk _ (ε p)) = Ideal.Quotient.mk J p := by
    refine ⟨Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ k₀ J).comp ε.symm.toAlgHom) ?_, ?_⟩
    · intro p hp
      obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hp
      simp [Ideal.Quotient.eq_zero_iff_mem.mpr hfJ]
    · intro p
      rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
      simp
  refine Module.Finite.of_surjective φ.toLinearMap ?_
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk _ (ε p), hφ p⟩

/-- For a nonzero ideal `J` of `k₀[X]`, `Spec (k₀[X] ⧸ J) ⟶ Spec k₀` is finite. -/
theorem isFinite_spec_mvPolynomial_fin_one_quotient {J : Ideal (MvPolynomial (Fin 1) k₀)}
    (hJ : J ≠ ⊥) :
    IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k₀ (MvPolynomial (Fin 1) k₀ ⧸ J)))) := by
  rw [IsFinite.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.finite_algebraMap]
  exact module_finite_mvPolynomial_fin_one_quotient hJ


/-- The polynomial algebra `R[X₀, …, X_{n-1}]` is standard smooth of relative dimension `n`
over `R`. -/
lemma isStandardSmoothOfRelativeDimension_mvPolynomial (R : Type u) [CommRing R] (n : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension n R (MvPolynomial (Fin n) R) := by
  let v : PEmpty.{1} → MvPolynomial (Fin n) R := PEmpty.elim
  let P : Algebra.PreSubmersivePresentation R
      (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range v)) (Fin n) PEmpty.{1} :=
    .naive PEmpty.elim (fun a ↦ a.elim)
  let Q : Algebra.SubmersivePresentation R _ (Fin n) PEmpty.{1} :=
    { P with jacobian_isUnit := by simp [P.jacobian_eq_jacobiMatrix_det] }
  let e : (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range v)) ≃ₐ[R] MvPolynomial (Fin n) R :=
    (Ideal.quotientEquivAlgOfEq R (by simp [v])).trans (AlgEquiv.quotientBot R _)
  exact (Q.ofAlgEquiv e).isStandardSmoothOfRelativeDimension
    (by simp [Algebra.Presentation.dimension])

/-- The affine line `Spec k₀[X] ⟶ Spec k₀` is smooth of relative dimension `1`. -/
theorem smoothOfRelativeDimension_spec_mvPolynomial_fin_one :
    SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ (MvPolynomial (Fin 1) k₀)))) := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1), CommRingCat.hom_ofHom]
  exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
    ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).2
      (isStandardSmoothOfRelativeDimension_mvPolynomial k₀ 1))


/-- The isomorphism `Spec (k₀[X] ⧸ ⊥) ≅ Spec k₀[X]`. -/
noncomputable def specMvPolynomialQuotientBotIso :
    Spec (.of (MvPolynomial (Fin 1) k₀ ⧸ (⊥ : Ideal (MvPolynomial (Fin 1) k₀)))) ≅
      Spec (.of (MvPolynomial (Fin 1) k₀)) :=
  specIsoOfAlgEquiv (AlgEquiv.quotientBot k₀ _).symm

/-- The isomorphism `specMvPolynomialQuotientBotIso` is compatible with the structure maps. -/
@[reassoc (attr := simp)]
lemma specMvPolynomialQuotientBotIso_hom_comp :
    (specMvPolynomialQuotientBotIso (k₀ := k₀)).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap k₀ (MvPolynomial (Fin 1) k₀))) =
      Spec.map (CommRingCat.ofHom (algebraMap k₀
        (MvPolynomial (Fin 1) k₀ ⧸ (⊥ : Ideal (MvPolynomial (Fin 1) k₀))))) :=
  specIsoOfAlgEquiv_hom_comp _

end BaseCases

section Projection

variable {k₀ : Type u} [Field k₀] {n : ℕ}

/-- The ring map `k₀[X₀, …, X_{n-1}] →+* k₀[X₀, …, Xₙ] ⧸ I` induced by the inclusion of the
first `n` variables. -/
noncomputable def mvPolynomialQuotientProjectionRingHom
    (I : Ideal (MvPolynomial (Fin (n + 1)) k₀)) :
    MvPolynomial (Fin n) k₀ →+* MvPolynomial (Fin (n + 1)) k₀ ⧸ I :=
  (Ideal.Quotient.mk I).comp (rename Fin.castSucc).toRingHom

/-- The projection `Spec (k₀[X₀, …, Xₙ] ⧸ I) ⟶ Spec k₀[X₀, …, X_{n-1}]` forgetting the last
coordinate. -/
noncomputable def mvPolynomialQuotientProjection (I : Ideal (MvPolynomial (Fin (n + 1)) k₀)) :
    Spec (.of (MvPolynomial (Fin (n + 1)) k₀ ⧸ I)) ⟶ Spec (.of (MvPolynomial (Fin n) k₀)) :=
  Spec.map (CommRingCat.ofHom (mvPolynomialQuotientProjectionRingHom I))

/-- The projection `mvPolynomialQuotientProjection` commutes with the structure maps to
`Spec k₀`. -/
@[reassoc (attr := simp)]
lemma mvPolynomialQuotientProjection_comp (I : Ideal (MvPolynomial (Fin (n + 1)) k₀)) :
    mvPolynomialQuotientProjection I ≫
        Spec.map (CommRingCat.ofHom (algebraMap k₀ (MvPolynomial (Fin n) k₀))) =
      Spec.map (CommRingCat.ofHom (algebraMap k₀ (MvPolynomial (Fin (n + 1)) k₀ ⧸ I))) := by
  rw [mvPolynomialQuotientProjection, ← Spec.map_comp]
  congr 1
  ext c
  simp [mvPolynomialQuotientProjectionRingHom, ← Ideal.Quotient.mk_algebraMap]

/-- Evaluation of the first `n` variables of `k₀[X₀, …, Xₙ]` at `a`, sending the last variable
to the variable of `k₀[X]`. -/
noncomputable def evalInitAlgHom (a : Fin n → k₀) :
    MvPolynomial (Fin (n + 1)) k₀ →ₐ[k₀] MvPolynomial (Fin 1) k₀ :=
  aeval (Fin.snoc (α := fun _ ↦ MvPolynomial (Fin 1) k₀) (fun i ↦ C (a i)) (X 0))

/-- `evalInitAlgHom a` sends the `i`-th of the first `n` variables to `a i`. -/
@[simp]
lemma evalInitAlgHom_X_castSucc (a : Fin n → k₀) (i : Fin n) :
    evalInitAlgHom a (X i.castSucc) = C (a i) := by
  simp [evalInitAlgHom]

/-- `evalInitAlgHom a` sends the last variable to the variable of `k₀[X]`. -/
@[simp]
lemma evalInitAlgHom_X_last (a : Fin n → k₀) : evalInitAlgHom a (X (Fin.last n)) = X 0 := by
  simp [evalInitAlgHom]

/-- The ideal of `k₀[X]` obtained from `I` by evaluating the first `n` variables at `a`. -/
noncomputable def evalInitIdeal (a : Fin n → k₀) (I : Ideal (MvPolynomial (Fin (n + 1)) k₀)) :
    Ideal (MvPolynomial (Fin 1) k₀) :=
  I.map (evalInitAlgHom a).toRingHom

/-- The image of a constant polynomial in a quotient of a polynomial ring is the image of the
constant under the algebra map. -/
lemma _root_.MvPolynomial.quotient_mk_C {R σ : Type*} [CommRing R] (J : Ideal (MvPolynomial σ R))
    (c : R) : Ideal.Quotient.mk J (C c) = algebraMap R (MvPolynomial σ R ⧸ J) c := by
  rw [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]

/-- The ring map `k₀[X₀, …, Xₙ] ⧸ I →+* k₀[X] ⧸ evalInitIdeal a I` induced by
`evalInitAlgHom a`. -/
noncomputable def evalInitQuotientRingHom (a : Fin n → k₀)
    (I : Ideal (MvPolynomial (Fin (n + 1)) k₀)) :
    MvPolynomial (Fin (n + 1)) k₀ ⧸ I →+* MvPolynomial (Fin 1) k₀ ⧸ evalInitIdeal a I :=
  Ideal.quotientMap _ (evalInitAlgHom a).toRingHom Ideal.le_comap_map

/-- `evalInitQuotientRingHom` on residue classes of polynomials. -/
@[simp]
lemma evalInitQuotientRingHom_mk (a : Fin n → k₀) (I : Ideal (MvPolynomial (Fin (n + 1)) k₀))
    (p : MvPolynomial (Fin (n + 1)) k₀) :
    evalInitQuotientRingHom a I (Ideal.Quotient.mk I p) =
      Ideal.Quotient.mk _ (evalInitAlgHom a p) :=
  rfl

/-- `evalInitQuotientRingHom` is a map of `k₀`-algebras. -/
@[simp]
lemma evalInitQuotientRingHom_algebraMap (a : Fin n → k₀)
    (I : Ideal (MvPolynomial (Fin (n + 1)) k₀)) (c : k₀) :
    evalInitQuotientRingHom a I (algebraMap k₀ _ c) = algebraMap k₀ _ c := by
  rw [← MvPolynomial.quotient_mk_C, evalInitQuotientRingHom_mk, evalInitAlgHom, aeval_C,
    MvPolynomial.algebraMap_eq, MvPolynomial.quotient_mk_C]

variable {T : Type*} [CommRing T]

/-- Given a commutative square out of `k₀[X₀, …, X_{n-1}]`, the composite of evaluation with
the induced map on `k₀[X]` agrees with the given map on `k₀[X₀, …, Xₙ]`. -/
lemma eval₂Hom_comp_evalInitAlgHom (I : Ideal (MvPolynomial (Fin (n + 1)) k₀))
    (φ : MvPolynomial (Fin n) k₀ →ₐ[k₀] k₀) (α : MvPolynomial (Fin (n + 1)) k₀ ⧸ I →+* T)
    (β : k₀ →+* T) (h : α.comp (mvPolynomialQuotientProjectionRingHom I) = β.comp φ.toRingHom) :
    (eval₂Hom β fun _ ↦ α (Ideal.Quotient.mk I (X (Fin.last n)))).comp
        (evalInitAlgHom fun i ↦ φ (X i)).toRingHom =
      α.comp (Ideal.Quotient.mk I) := by
  have h' (p : MvPolynomial (Fin n) k₀) :
      α (Ideal.Quotient.mk I (rename Fin.castSucc p)) = β (φ p) := congr($h p)
  refine MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun i ↦ ?_)
  · simpa using (h' (C c)).symm
  · induction i using Fin.lastCases with
    | last => simp
    | cast j => simpa using (h' (X j)).symm

/-- The map out of `k₀[X] ⧸ evalInitIdeal a I` induced by a commutative square out of
`k₀[X₀, …, X_{n-1}]`. -/
noncomputable def evalInitDesc (I : Ideal (MvPolynomial (Fin (n + 1)) k₀))
    (φ : MvPolynomial (Fin n) k₀ →ₐ[k₀] k₀) (α : MvPolynomial (Fin (n + 1)) k₀ ⧸ I →+* T)
    (β : k₀ →+* T) (h : α.comp (mvPolynomialQuotientProjectionRingHom I) = β.comp φ.toRingHom) :
    MvPolynomial (Fin 1) k₀ ⧸ evalInitIdeal (fun i ↦ φ (X i)) I →+* T :=
  Ideal.Quotient.lift _ (eval₂Hom β fun _ ↦ α (Ideal.Quotient.mk I (X (Fin.last n)))) <| by
    have hle : evalInitIdeal (fun i ↦ φ (X i)) I ≤
        RingHom.ker (eval₂Hom β fun _ ↦ α (Ideal.Quotient.mk I (X (Fin.last n)))) := by
      refine Ideal.map_le_iff_le_comap.mpr fun p hp ↦ ?_
      rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply,
        eval₂Hom_comp_evalInitAlgHom I φ α β h, RingHom.comp_apply,
        Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
    exact fun x hx ↦ hle hx

/-- `evalInitDesc` on residue classes of polynomials. -/
@[simp]
lemma evalInitDesc_mk (I : Ideal (MvPolynomial (Fin (n + 1)) k₀))
    (φ : MvPolynomial (Fin n) k₀ →ₐ[k₀] k₀) (α : MvPolynomial (Fin (n + 1)) k₀ ⧸ I →+* T)
    (β : k₀ →+* T) (h : α.comp (mvPolynomialQuotientProjectionRingHom I) = β.comp φ.toRingHom)
    (p : MvPolynomial (Fin 1) k₀) :
    evalInitDesc I φ α β h (Ideal.Quotient.mk _ p) =
      eval₂Hom β (fun _ ↦ α (Ideal.Quotient.mk I (X (Fin.last n)))) p :=
  rfl

/-- `evalInitDesc` restricts to `β` on `k₀`. -/
@[simp]
lemma evalInitDesc_algebraMap (I : Ideal (MvPolynomial (Fin (n + 1)) k₀))
    (φ : MvPolynomial (Fin n) k₀ →ₐ[k₀] k₀) (α : MvPolynomial (Fin (n + 1)) k₀ ⧸ I →+* T)
    (β : k₀ →+* T) (h : α.comp (mvPolynomialQuotientProjectionRingHom I) = β.comp φ.toRingHom)
    (c : k₀) : evalInitDesc I φ α β h (algebraMap k₀ _ c) = β c := by
  rw [← MvPolynomial.quotient_mk_C, evalInitDesc_mk, eval₂Hom_C]

/-- The square of rings defining the fibre of `mvPolynomialQuotientProjection` over the
`k₀`-point given by `φ` is a pushout. -/
theorem isPushout_evalInit (I : Ideal (MvPolynomial (Fin (n + 1)) k₀))
    (φ : MvPolynomial (Fin n) k₀ →ₐ[k₀] k₀) :
    IsPushout (CommRingCat.ofHom (mvPolynomialQuotientProjectionRingHom I))
      (CommRingCat.ofHom φ.toRingHom)
      (CommRingCat.ofHom (evalInitQuotientRingHom (fun i ↦ φ (X i)) I))
      (CommRingCat.ofHom
        (algebraMap k₀ (MvPolynomial (Fin 1) k₀ ⧸ evalInitIdeal (fun i ↦ φ (X i)) I))) := by
  have hw : CommRingCat.ofHom (mvPolynomialQuotientProjectionRingHom I) ≫
      CommRingCat.ofHom (evalInitQuotientRingHom (fun i ↦ φ (X i)) I) =
      CommRingCat.ofHom φ.toRingHom ≫ CommRingCat.ofHom
        (algebraMap k₀ (MvPolynomial (Fin 1) k₀ ⧸ evalInitIdeal (fun i ↦ φ (X i)) I)) := by
    ext : 1
    refine MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun i ↦ ?_)
    · simp [mvPolynomialQuotientProjectionRingHom, MvPolynomial.quotient_mk_C]
    · simp [mvPolynomialQuotientProjectionRingHom, MvPolynomial.quotient_mk_C]
  refine IsPushout.of_isColimit (PushoutCocone.IsColimit.mk hw
    (fun s ↦ CommRingCat.ofHom (evalInitDesc I φ s.inl.hom s.inr.hom
      congr(($(s.condition)).hom))) (fun s ↦ ?_) (fun s ↦ ?_) (fun s m h₁ h₂ ↦ ?_))
  · ext : 1
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun p ↦ ?_)
    simpa using congr($(eval₂Hom_comp_evalInitAlgHom I φ s.inl.hom s.inr.hom
      congr(($(s.condition)).hom)) p)
  · ext c
    simp [← MvPolynomial.quotient_mk_C]
  · ext : 1
    refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun i ↦ ?_))
    · have := congr(($h₂).hom c)
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
        Function.comp_apply] at this
      simp [MvPolynomial.quotient_mk_C, this]
    · have := congr(($h₁).hom (Ideal.Quotient.mk I (X (Fin.last n))))
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
        Function.comp_apply, evalInitQuotientRingHom_mk, evalInitAlgHom_X_last] at this
      simp [Subsingleton.elim i 0, this]

/-- The fibre of `mvPolynomialQuotientProjection I` over a `k₀`-point of
`Spec k₀[X₀, …, X_{n-1}]` is isomorphic over `Spec k₀` to the spectrum of a quotient of `k₀[X]`.
-/
theorem exists_iso_pullback_mvPolynomialQuotientProjection
    (I : Ideal (MvPolynomial (Fin (n + 1)) k₀))
    (y₀ : Spec (.of k₀) ⟶ Spec (.of (MvPolynomial (Fin n) k₀)))
    (hy₀ : y₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ (MvPolynomial (Fin n) k₀))) = 𝟙 _) :
    ∃ (J : Ideal (MvPolynomial (Fin 1) k₀))
      (e : pullback (mvPolynomialQuotientProjection I) y₀ ≅
        Spec (.of (MvPolynomial (Fin 1) k₀ ⧸ J))),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ (MvPolynomial (Fin 1) k₀ ⧸ J))) =
        pullback.snd (mvPolynomialQuotientProjection I) y₀ := by
  obtain ⟨g, rfl⟩ := Spec.map_surjective y₀
  rw [← Spec.map_comp, ← Spec.map_id, Spec.map_inj] at hy₀
  let φ : MvPolynomial (Fin n) k₀ →ₐ[k₀] k₀ :=
    { g.hom with commutes' c := congr(($hy₀).hom c) }
  have h := isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_evalInit I φ)
  exact ⟨_, h.isoPullback.symm, h.isoPullback_inv_snd⟩


end Projection

section Frobenius

/-- In a field `k` over a finite field `k₀`, the fixed points of `x ↦ x ^ #k₀` are exactly the
elements of the image of `k₀`. -/
lemma _root_.FiniteField.mem_range_algebraMap_of_pow_card_eq {k₀ k : Type*} [Field k₀] [Fintype k₀]
    [Field k] [Algebra k₀ k] {x : k} (hx : x ^ Fintype.card k₀ = x) :
    x ∈ (algebraMap k₀ k).range := by
  classical
  let P : Polynomial k := Polynomial.X ^ Fintype.card k₀ - Polynomial.X
  have hP : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero k Fintype.one_lt_card
  have hdeg : P.natDegree = Fintype.card k₀ :=
    FiniteField.X_pow_card_sub_X_natDegree_eq k Fintype.one_lt_card
  have hsub : Finset.univ.image (algebraMap k₀ k) ⊆ P.roots.toFinset := by
    intro y hy
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hy
    simp [P, hP, ← map_pow, FiniteField.pow_card]
  have hcard : P.roots.toFinset.card ≤ (Finset.univ.image (algebraMap k₀ k)).card := by
    rw [Finset.card_image_of_injective _ (algebraMap k₀ k).injective, Finset.card_univ, ← hdeg]
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' P)
  have hx' : x ∈ P.roots.toFinset := by simp [P, hP, hx]
  rw [← Finset.eq_of_subset_of_card_le hsub hcard] at hx'
  obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hx'
  exact ⟨c, rfl⟩

/-- A ring map `A →+* k` to a field over a finite field `k₀` whose values are fixed by
`x ↦ x ^ #k₀` factors through `k₀`. -/
lemma _root_.FiniteField.exists_ringHom_of_pow_card_eq {k₀ k A : Type*} [Field k₀] [Fintype k₀]
    [Field k] [Algebra k₀ k] [CommRing A] (g : A →+* k)
    (hg : ∀ a, g a ^ Fintype.card k₀ = g a) :
    ∃ φ : A →+* k₀, (algebraMap k₀ k).comp φ = g := by
  let e : k₀ ≃+* (algebraMap k₀ k).range :=
    RingEquiv.ofBijective (algebraMap k₀ k).rangeRestrict
      ⟨fun a b h ↦ (algebraMap k₀ k).injective (congr_arg Subtype.val h),
        (algebraMap k₀ k).rangeRestrict_surjective⟩
  refine ⟨(e.symm : _ →+* k₀).comp
    (g.codRestrict _ fun a ↦ FiniteField.mem_range_algebraMap_of_pow_card_eq (hg a)), ?_⟩
  ext a
  have h := e.apply_symm_apply ⟨g a, FiniteField.mem_range_algebraMap_of_pow_card_eq (hg a)⟩
  exact congr_arg Subtype.val h

/-- Descent of Frobenius-fixed points of affine schemes over a finite field `k₀`: a `k`-point of
`Spec A` over `k₀` which is fixed by the `#k₀`-power Frobenius of `k` comes from a `k₀`-point. -/
theorem exists_spec_point_of_frobenius_comp_eq {k₀ k A : Type u} [Field k₀] [Fintype k₀]
    [Field k] [Algebra k₀ k] [CommRing A] [Algebra k₀ A] (y : Spec (.of k) ⟶ Spec (.of A))
    (hy : y ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ A)) =
      Spec.map (CommRingCat.ofHom (algebraMap k₀ k)))
    (hfrob : Spec.map (CommRingCat.ofHom
      ((FiniteField.frobeniusAlgHom k₀ k : k →ₐ[k₀] k) : k →+* k)) ≫ y = y) :
    ∃ y₀ : Spec (.of k₀) ⟶ Spec (.of A),
      Spec.map (CommRingCat.ofHom (algebraMap k₀ k)) ≫ y₀ = y ∧
        y₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ A)) = 𝟙 _ := by
  obtain ⟨g, rfl⟩ := Spec.map_surjective y
  rw [← Spec.map_comp, Spec.map_inj] at hy hfrob
  obtain ⟨φ, hφ⟩ := FiniteField.exists_ringHom_of_pow_card_eq g.hom fun a ↦
    congr($(hfrob).hom a)
  refine ⟨Spec.map (CommRingCat.ofHom φ), ?_, ?_⟩
  · rw [← Spec.map_comp]
    congr 1
    ext a
    exact congr($hφ a)
  · rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext c
    apply (algebraMap k₀ k).injective
    have h1 := congr($hφ (algebraMap k₀ A c))
    have h2 := congr($(hy).hom c)
    simp only [RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_comp,
      CommRingCat.hom_ofHom] at h1 h2
    simp [h1, h2]


end Frobenius

end AlgebraicGeometry
