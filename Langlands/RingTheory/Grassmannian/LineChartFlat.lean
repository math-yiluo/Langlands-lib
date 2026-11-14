import Langlands.RingTheory.Grassmannian.ProperFinitePresentation
import Langlands.CommutativeAlgebra.FibrewiseRegularFlat
import Langlands.CommutativeAlgebra.FibreLocalDomain
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis

/-! # Flatness of the Grassmannian of rank-one quotients of a finite projective module

For a finite projective module `M` over a noetherian ring `R`, the symmetric algebra `Sym M` is a
retract of a polynomial ring, hence flat with polynomial (domain) fibres. The chart algebra of a
point `x` of `M` is `Sym M ⧸ (x - 1)`, and `x - 1` is nonzero in every fibre; by the fibrewise
criterion it is flat. Hence the representing scheme of the Grassmannian of rank-one quotients of
`M` is flat over `R`. -/

universe u

open TensorProduct

namespace Langlands.RingTheory.Grassmannian.LineChartFlat

section Sym

variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Module.Projective R M]

/-- The symmetric algebra of a finite projective module is a retract of a polynomial ring. -/
lemma exists_retract : ∃ (n : ℕ) (F : SymmetricAlgebra R (Fin n → R) →ₐ[R] SymmetricAlgebra R M)
    (G : SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R (Fin n → R)),
      F.comp G = AlgHom.id R _ := by
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  refine ⟨n, SymmetricAlgebra.lift ((SymmetricAlgebra.ι R M).comp f),
    SymmetricAlgebra.lift ((SymmetricAlgebra.ι R (Fin n → R)).comp g), ?_⟩
  apply SymmetricAlgebra.algHom_ext
  refine LinearMap.ext fun m => ?_
  have hm : f (g m) = m := LinearMap.congr_fun hfg m
  simp [hm]

/-- **The symmetric algebra of a finite projective module is flat.** -/
theorem flat_symmetricAlgebra : Module.Flat R (SymmetricAlgebra R M) := by
  obtain ⟨n, F, G, hFG⟩ := exists_retract R M
  have : Module.Flat R (SymmetricAlgebra R (Fin n → R)) :=
    Module.Flat.of_linearEquiv (SymmetricAlgebra.equivMvPolynomial (Pi.basisFun R (Fin n))).toLinearEquiv
  refine Module.Flat.of_retract G.toLinearMap F.toLinearMap ?_
  ext y
  exact congrArg (fun h : SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R M => h y) hFG

/-- **The fibres of the symmetric algebra of a finite projective module are domains.** -/
theorem isDomain_tensor (K : Type u) [Field K] [Algebra R K] :
    IsDomain (K ⊗[R] SymmetricAlgebra R M) := by
  obtain ⟨n, F, G, hFG⟩ := exists_retract R M
  let G' : K ⊗[R] SymmetricAlgebra R M →ₐ[K] K ⊗[R] SymmetricAlgebra R (Fin n → R) :=
    Algebra.TensorProduct.map (AlgHom.id K K) G
  let F' : K ⊗[R] SymmetricAlgebra R (Fin n → R) →ₐ[K] K ⊗[R] SymmetricAlgebra R M :=
    Algebra.TensorProduct.map (AlgHom.id K K) F
  have hFG' : F'.comp G' = AlgHom.id K _ := by
    apply Algebra.TensorProduct.ext
    · ext
    · ext y
      have hy := congrArg (fun h : SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R M =>
        h (SymmetricAlgebra.ι R M y)) hFG
      simp only [AlgHom.comp_apply, AlgHom.id_apply] at hy
      simp [F', G', hy]
  have hinj : Function.Injective G' :=
    Function.LeftInverse.injective (g := F') fun x => congrArg (fun h => h x) hFG'
  let e₁ : K ⊗[R] SymmetricAlgebra R (Fin n → R) ≃ₐ[R] K ⊗[R] MvPolynomial (Fin n) R :=
    Algebra.TensorProduct.congr AlgEquiv.refl
      (SymmetricAlgebra.equivMvPolynomial (Pi.basisFun R (Fin n)))
  let e₂ : K ⊗[R] MvPolynomial (Fin n) R ≃ₐ[K] MvPolynomial (Fin n) K :=
    MvPolynomial.algebraTensorAlgEquiv R K
  let f : K ⊗[R] SymmetricAlgebra R M →+* MvPolynomial (Fin n) K :=
    e₂.toRingHom.comp (e₁.toRingHom.comp G'.toRingHom)
  have hf : Function.Injective f := e₂.injective.comp (e₁.injective.comp hinj)
  exact hf.isDomain f

omit [Module.Finite R M] [Module.Projective R M] in
/-- The augmentation sends `1 ⊗ (ι v - 1)` to `-1`; in particular it is nonzero in every fibre. -/
theorem one_tmul_ne_zero (K : Type u) [Field K] [Algebra R K] (v : M) :
    (1 : K) ⊗ₜ[R] (SymmetricAlgebra.ι R M v - 1) ≠ 0 := by
  intro h
  let ε : SymmetricAlgebra R M →ₐ[R] R := SymmetricAlgebra.lift (0 : M →ₗ[R] R)
  let E : K ⊗[R] SymmetricAlgebra R M →ₐ[K] K :=
    (Algebra.TensorProduct.rid R K K).toAlgHom.comp (Algebra.TensorProduct.map (AlgHom.id K K) ε)
  have h1 := congrArg E h
  have hε : ε (SymmetricAlgebra.ι R M v - 1) = -1 := by
    simp [ε]
  have h2 : E ((1 : K) ⊗ₜ[R] (SymmetricAlgebra.ι R M v - 1)) = -1 := by
    simp only [E, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hε]
    simp
  rw [h2, map_zero] at h1
  exact one_ne_zero (neg_eq_zero.mp h1)

end Sym

section Chart

variable (R : Type u) [CommRing R] [IsNoetherianRing R] {M : Type u} [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Module.Projective R M]

/-- **The chart algebras of the Grassmannian of rank-one quotients are flat.** -/
theorem flat_chartAlgebra (x : Fin 1 → M) :
    Module.Flat R (Module.Grassmannian.ChartAlgebra.S R x) := by
  have : Module.Projective R (Fin 1 → M) :=
    Module.Projective.of_equiv' (DFinsupp.linearEquivFunOnFintype (R := R)
      (M := fun _ : Fin 1 => M))
  let Sy := SymmetricAlgebra R (Fin 1 → M)
  have : Module.Flat R Sy := flat_symmetricAlgebra R (Fin 1 → M)
  have : Algebra.FinitePresentation R Sy :=
    SymmetricAlgebra.finitePresentation_of_projective R (Fin 1 → M)
  have : IsNoetherianRing Sy := Algebra.FiniteType.isNoetherianRing R Sy
  let s : Sy := SymmetricAlgebra.ι R _ (Pi.single 0 (x 0)) - 1
  have hrels : Ideal.span (Module.Grassmannian.ChartAlgebra.rels R x) = Ideal.span {s} := by
    congr 1
    ext a
    simp only [Module.Grassmannian.ChartAlgebra.rels, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, j, rfl⟩
      rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
      simp [s]
    · rintro rfl
      exact ⟨0, 0, by simp [s]⟩
  have hs : ∀ (P : Ideal Sy) [P.IsMaximal], IsSMulRegular (Localization.AtPrime P ⧸
      (P.comap (algebraMap R Sy)).map (algebraMap R (Localization.AtPrime P)))
        (algebraMap Sy (Localization.AtPrime P) s) := by
    intro P _
    exact Langlands.CommutativeAlgebra.FibreLocalDomain.isSMulRegular_of_isDomain_fiber P s
      (isDomain_tensor R (Fin 1 → M) _) (one_tmul_ne_zero R (Fin 1 → M) _ _)
  have h := (Langlands.CommutativeAlgebra.FibrewiseRegular.regular_and_flat_quotient s hs).2
  change Module.Flat R (Sy ⧸ Ideal.span (Module.Grassmannian.ChartAlgebra.rels R x))
  rw [hrels]
  exact h

end Chart

end Langlands.RingTheory.Grassmannian.LineChartFlat

namespace Module.Grassmannian.ProjectiveEmbedding

open AlgebraicGeometry CategoryTheory

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {M : Type u} [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Module.Projective R M] (D : Rep R M 1)

/-- **The Grassmannian of rank-one quotients of a finite projective module over a noetherian ring
is flat.** -/
theorem Rep.flat_p : AlgebraicGeometry.Flat D.p := by
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @AlgebraicGeometry.Flat.{u})
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @AlgebraicGeometry.Flat) D.V D.hV fun x => ?_
  rw [← sV_gS D x, Category.assoc, ← specMap_algebraMap_S]
  have h1 : AlgebraicGeometry.Flat (Spec.map (CommRingCat.ofHom (algebraMap R (S D x)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Flat)]
    have : Module.Flat R (ChartAlgebra.S R x) :=
      Langlands.RingTheory.Grassmannian.LineChartFlat.flat_chartAlgebra R x
    have : Module.Flat R (S D x) := Module.Flat.of_linearEquiv (chartAlgEquiv D x).toLinearEquiv
    exact RingHom.flat_algebraMap_iff.mpr this
  infer_instance

end Module.Grassmannian.ProjectiveEmbedding
