import Langlands.CommutativeAlgebra.GradedPolynomialKernels

/-! # Homogeneous relation submodules and arbitrary polynomial kernels -/

universe u v w

namespace Langlands.CommutativeAlgebra

section FiniteExtraction

variable {A : Type*} [Semiring A] {V : Type*} {W : Type*}
variable [AddCommMonoid W] [Module A W] [IsNoetherian A W]

private theorem exists_finset_span_image_homogenized (g : V → W) (s : Set V) :
    ∃ t : Finset V, (↑t : Set V) ⊆ s ∧
      Submodule.span A (g '' (↑t : Set V)) = Submodule.span A (g '' s) := by
  classical
  obtain ⟨t, ht, hspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset (g '' s)).1
      (IsNoetherian.noetherian (R := A) (Submodule.span A (g '' s)))
  have hpre : ∀ y : (t : Set W), ∃ x : V, x ∈ s ∧ g x = (y : W) :=
    fun y => ht y.property
  choose lift hlift hglift using hpre
  let t' : Finset V := t.attach.image lift
  have hsub : (↑t' : Set V) ⊆ s := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.1 hx
    exact hlift y
  refine ⟨t', hsub, le_antisymm (Submodule.span_mono (Set.image_mono hsub)) ?_⟩
  rw [hspan]
  apply Submodule.span_mono
  intro y hy
  refine ⟨lift ⟨y, hy⟩, ?_, hglift ⟨y, hy⟩⟩
  exact Finset.mem_image.2 ⟨⟨y, hy⟩, Finset.mem_attach _ _, rfl⟩

end FiniteExtraction

section GeneralGraded

variable {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
variable {σ : Type v} [Finite σ] {n : ℕ}
variable {N : Type w} [AddCommGroup N] [Module R N] [Module.IsTorsionFree R N]

private theorem gradedSubmodule_le_of_reduction
    (K : Submodule (MvPolynomial σ R) (Fin n → MvPolynomial σ R))
    (hKg : PolynomialVectorGraded K)
    (F : (Fin n → MvPolynomial σ R) →ₗ[R] N)
    (hKF : K.restrictScalars R ≤ LinearMap.ker F)
    (hcomplete : ∀ d x, x ∈ homogeneousPolynomialVectors R σ n d →
      F x = 0 → x ∈ K)
    (L : Submodule (MvPolynomial σ R) (Fin n → MvPolynomial σ R))
    (hL : L ≤ K) (hLg : PolynomialVectorGraded L)
    (I : Ideal R) (hI : I ≤ Ideal.jacobson ⊥)
    (hred : ∀ x ∈ K, ∃ y ∈ L,
      polynomialVectorReduction I n y = polynomialVectorReduction I n x) : K ≤ L := by
  have hpiece (d : ℕ) (x : Fin n → MvPolynomial σ R)
      (hx : x ∈ K) (hxd : x ∈ homogeneousPolynomialVectors R σ n d) : x ∈ L := by
    let H := homogeneousPolynomialVectors R σ n d
    let fd := F.comp H.subtype
    let gd := homogeneousPolynomialVectorReduction (σ := σ) I n d
    let Ld := (L.restrictScalars R).comap H.subtype
    have := homogeneousPolynomialVectors_finite (R := R) (σ := σ) n d
    have hLd : Ld ≤ LinearMap.ker fd := by
      intro z hz
      exact hKF (hL hz)
    have himage : (LinearMap.ker fd).map gd ≤ Ld.map gd := by
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨y, hy, hzy⟩ := hred z.val (hcomplete d z.val z.property hz)
      let yd : H := ⟨homogeneousPolynomialVectorComponent n d y,
        homogeneousPolynomialVectorComponent_mem n d y⟩
      refine ⟨yd, hLg d y hy, ?_⟩
      change polynomialVectorReduction I n
        (homogeneousPolynomialVectorComponent n d y) = polynomialVectorReduction I n z.val
      rw [polynomialVectorReduction_component, hzy,
        ← polynomialVectorReduction_component,
        homogeneousPolynomialVectorComponent_eq_self n d z.val z.property]
    have hle := valuationKernel_le_of_reduction_image_le fd gd I hI
      (homogeneousPolynomialVectorReduction_ker I n d) Ld hLd himage
    exact hle (show (⟨x, hxd⟩ : H) ∈ LinearMap.ker fd from hKF hx)
  intro x hx
  obtain ⟨D, hD⟩ := sum_homogeneousPolynomialVectorComponent x
  rw [← hD]
  apply Submodule.sum_mem
  intro d _
  exact hpiece d _ (hKg d x hx) (homogeneousPolynomialVectorComponent_mem n d x)

/-- A graded submodule whose homogeneous pieces are actual torsion-free-target
kernels is finitely generated over the polynomial ring. -/
theorem polynomialGradedSubmodule_fg_of_piece_kernels
    (K : Submodule (MvPolynomial σ R) (Fin n → MvPolynomial σ R))
    (hKg : PolynomialVectorGraded K)
    (F : (Fin n → MvPolynomial σ R) →ₗ[R] N)
    (hKF : K.restrictScalars R ≤ LinearMap.ker F)
    (hcomplete : ∀ d x, x ∈ homogeneousPolynomialVectors R σ n d →
      F x = 0 → x ∈ K) : K.FG := by
  classical
  let I := IsLocalRing.maximalIdeal R
  let : Field (R ⧸ I) := Ideal.Quotient.field I
  let g := polynomialVectorQuotientMap (σ := σ) I n
  let S : Set (Fin n → MvPolynomial σ R) :=
    {x | x ∈ K ∧ ∃ d, x ∈ homogeneousPolynomialVectors R σ n d}
  have hS : Submodule.span (MvPolynomial σ R) S = K :=
    polynomialVectorGraded_span_homogeneous _ hKg
  obtain ⟨t, htS, htspan⟩ := exists_finset_span_image_homogenized
    (A := MvPolynomial σ (R ⧸ I)) g S
  let L := Submodule.span (MvPolynomial σ R) (↑t : Set (Fin n → MvPolynomial σ R))
  have hL : L ≤ K := by
    apply Submodule.span_le.2
    exact fun x hx => (htS hx).1
  have hLg : PolynomialVectorGraded L :=
    polynomialVectorGraded_span _ (fun x hx => (htS hx).2)
  have : RingHomSurjective (MvPolynomial.map (σ := σ) (Ideal.Quotient.mk I)) :=
    ⟨MvPolynomial.map_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective⟩
  have hKL : K ≤ L := by
    apply gradedSubmodule_le_of_reduction K hKg F hKF hcomplete L hL hLg I
      (IsLocalRing.maximalIdeal_le_jacobson ⊥)
    intro x hx
    have hxspan : g x ∈ Submodule.span (MvPolynomial σ (R ⧸ I)) (g '' S) := by
      apply Submodule.image_span_subset_span g S
      exact ⟨x, hS.symm ▸ hx, rfl⟩
    rw [← htspan, Submodule.span_image g] at hxspan
    obtain ⟨y, hy, hgy⟩ := hxspan
    exact ⟨y, hy, hgy⟩
  have heq : L = K := le_antisymm hL hKL
  exact heq ▸ Submodule.fg_span t.finite_toSet

end GeneralGraded

section HomogeneousLifts

variable {R : Type u} [CommRing R] {σ : Type v} {n : ℕ}

/-- Evaluation of the additional variable at one, retaining the original variables. -/
noncomputable def polynomialDehomogenization :
    MvPolynomial (Option σ) R →ₐ[R] MvPolynomial σ R :=
  MvPolynomial.aeval (fun o : Option σ => o.elim 1 MvPolynomial.X)

@[simp]
theorem polynomialDehomogenization_X_none :
    polynomialDehomogenization (R := R) (σ := σ) (MvPolynomial.X none) = 1 := by
  simp [polynomialDehomogenization]

@[simp]
theorem polynomialDehomogenization_rename (p : MvPolynomial σ R) :
    polynomialDehomogenization (MvPolynomial.rename Option.some p) = p := by
  have h : polynomialDehomogenization.comp (MvPolynomial.rename Option.some) =
      AlgHom.id R (MvPolynomial σ R) := by
    ext i
    simp [polynomialDehomogenization]
  exact DFunLike.congr_fun h p

/-- Renaming a polynomial vector into the ring with the additional variable. -/
noncomputable def polynomialVectorRename :
    (Fin n → MvPolynomial σ R) →ₗ[R] (Fin n → MvPolynomial (Option σ) R) :=
  (MvPolynomial.rename (R := R) Option.some).toLinearMap.compLeft (Fin n)

/-- Evaluation of the additional variable on polynomial vectors, with polynomial semilinearity. -/
noncomputable def polynomialVectorDehomogenization (n : ℕ) :
    (Fin n → MvPolynomial (Option σ) R) →ₛₗ[
      (polynomialDehomogenization (R := R) (σ := σ)).toRingHom]
      (Fin n → MvPolynomial σ R) where
  toFun x i := polynomialDehomogenization (x i)
  map_add' x y := by funext i; exact map_add _ _ _
  map_smul' p x := by funext i; exact map_mul _ _ _

@[simp]
theorem polynomialVectorDehomogenization_apply (n : ℕ)
    (x : Fin n → MvPolynomial (Option σ) R) (i : Fin n) :
    polynomialVectorDehomogenization n x i = polynomialDehomogenization (x i) := rfl

@[simp]
theorem polynomialVectorDehomogenization_rename (x : Fin n → MvPolynomial σ R) :
    polynomialVectorDehomogenization n (polynomialVectorRename x) = x := by
  funext i
  exact polynomialDehomogenization_rename (x i)

/-- A vector homogenization to a specified common degree. -/
noncomputable def polynomialVectorHomogenize (D : ℕ) (x : Fin n → MvPolynomial σ R) :
    Fin n → MvPolynomial (Option σ) R :=
  ∑ d ∈ Finset.range (D + 1), (MvPolynomial.X (R := R) (none : Option σ)) ^ (D - d) •
    polynomialVectorRename (homogeneousPolynomialVectorComponent n d x)

theorem polynomialVectorHomogenize_mem (D : ℕ) (x : Fin n → MvPolynomial σ R) :
    polynomialVectorHomogenize D x ∈ homogeneousPolynomialVectors R (Option σ) n D := by
  classical
  unfold polynomialVectorHomogenize
  apply Submodule.sum_mem
  intro d hd
  have hle : d ≤ D := Nat.lt_succ_iff.1 (Finset.mem_range.1 hd)
  have hrename : polynomialVectorRename (homogeneousPolynomialVectorComponent n d x) ∈
      homogeneousPolynomialVectors R (Option σ) n d := by
    intro i _
    exact (MvPolynomial.homogeneousComponent_isHomogeneous d (x i)).rename_isHomogeneous
  have hm := homogeneousPolynomialVectors_smul_mem
    (MvPolynomial.isHomogeneous_X_pow (none : Option σ) (D - d)) hrename
  simpa only [Nat.sub_add_cancel hle] using hm

theorem exists_homogeneous_polynomialVector_lift (x : Fin n → MvPolynomial σ R) :
    ∃ (D : ℕ) (y : Fin n → MvPolynomial (Option σ) R),
      y ∈ homogeneousPolynomialVectors R (Option σ) n D ∧
      polynomialVectorDehomogenization n y = x := by
  classical
  obtain ⟨D, hD⟩ := sum_homogeneousPolynomialVectorComponent x
  refine ⟨D, polynomialVectorHomogenize D x, polynomialVectorHomogenize_mem D x, ?_⟩
  unfold polynomialVectorHomogenize
  rw [map_sum]
  have hterm (d : ℕ) :
      polynomialVectorDehomogenization n
        ((MvPolynomial.X (R := R) (none : Option σ)) ^ (D - d) •
          polynomialVectorRename (homogeneousPolynomialVectorComponent n d x)) =
        homogeneousPolynomialVectorComponent n d x := by
    rw [(polynomialVectorDehomogenization (R := R) (σ := σ) n).map_smulₛₗ]
    change polynomialDehomogenization ((MvPolynomial.X none) ^ (D - d)) •
      polynomialVectorDehomogenization n
        (polynomialVectorRename (homogeneousPolynomialVectorComponent n d x)) = _
    rw [map_pow, polynomialDehomogenization_X_none, one_pow,
      polynomialVectorDehomogenization_rename, one_smul]
  simpa only [hterm] using hD

end HomogeneousLifts

section ArbitraryKernels

variable {R : Type u} [CommRing R] {σ : Type v} {n m : ℕ}

/-- The span, after adjoining a variable, of homogeneous vectors whose
dehomogenizations are relations for the given polynomial map. -/
noncomputable def homogeneousPolynomialRelations
    (f : (Fin n → MvPolynomial σ R) →ₗ[MvPolynomial σ R]
      (Fin m → MvPolynomial σ R)) :
    Submodule (MvPolynomial (Option σ) R) (Fin n → MvPolynomial (Option σ) R) :=
  Submodule.span (MvPolynomial (Option σ) R)
    {y | f (polynomialVectorDehomogenization n y) = 0 ∧
      ∃ d, y ∈ homogeneousPolynomialVectors R (Option σ) n d}

theorem homogeneousPolynomialRelations_le_comap
    (f : (Fin n → MvPolynomial σ R) →ₗ[MvPolynomial σ R]
      (Fin m → MvPolynomial σ R)) :
    homogeneousPolynomialRelations f ≤
      (LinearMap.ker f).comap (polynomialVectorDehomogenization n) := by
  apply Submodule.span_le.2
  exact fun _ hy => hy.1

variable [IsDomain R] [ValuationRing R] [Finite σ]

theorem homogeneousPolynomialRelations_fg
    (f : (Fin n → MvPolynomial σ R) →ₗ[MvPolynomial σ R]
      (Fin m → MvPolynomial σ R)) :
    (homogeneousPolynomialRelations f).FG := by
  let K := homogeneousPolynomialRelations f
  let D : (Fin n → MvPolynomial (Option σ) R) →ₗ[R]
      (Fin n → MvPolynomial σ R) :=
    (polynomialDehomogenization (R := R) (σ := σ)).toLinearMap.compLeft (Fin n)
  let F := (f.restrictScalars R).comp D
  have hKg : PolynomialVectorGraded K :=
    polynomialVectorGraded_span _ (fun _ hy => hy.2)
  have hKF : K.restrictScalars R ≤ LinearMap.ker F := by
    intro y hy
    exact homogeneousPolynomialRelations_le_comap f hy
  apply polynomialGradedSubmodule_fg_of_piece_kernels K hKg F hKF
  intro d y hyd hy
  exact Submodule.subset_span ⟨hy, d, hyd⟩

/-- Every finite matrix over a finite-variable polynomial ring over a
valuation domain has a finitely generated relation submodule. -/
theorem polynomialKernel_fg_of_valuationRing
    (f : (Fin n → MvPolynomial σ R) →ₗ[MvPolynomial σ R]
      (Fin m → MvPolynomial σ R)) :
    (LinearMap.ker f).FG := by
  have : RingHomSurjective
      (polynomialDehomogenization (R := R) (σ := σ)).toRingHom := by
    constructor
    intro p
    exact ⟨MvPolynomial.rename Option.some p, polynomialDehomogenization_rename p⟩
  have heq : (homogeneousPolynomialRelations f).map
      (polynomialVectorDehomogenization n) = LinearMap.ker f := by
    apply le_antisymm
    · exact Submodule.map_le_iff_le_comap.2 (homogeneousPolynomialRelations_le_comap f)
    · intro x hx
      obtain ⟨d, y, hyd, hyx⟩ := exists_homogeneous_polynomialVector_lift x
      refine ⟨y, Submodule.subset_span ⟨?_, d, hyd⟩, hyx⟩
      rw [hyx]
      exact hx
  rw [← heq]
  exact (homogeneousPolynomialRelations_fg f).map (polynomialVectorDehomogenization n)

/-- Finite-variable polynomial rings over arbitrary valuation domains
satisfy the finite-free-submodule coherence condition. -/
theorem finiteFreeSubmoduleCoherent_mvPolynomial_of_valuationRing :
    FiniteFreeSubmoduleCoherent (MvPolynomial σ R) := by
  intro n K hK
  let : Module.Finite (MvPolynomial σ R) K := Module.Finite.of_fg hK
  obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' (MvPolynomial σ R) K
  have hfg := polynomialKernel_fg_of_valuationRing (K.subtype.comp f)
  rw [LinearMap.ker_comp_of_ker_eq_bot f K.ker_subtype] at hfg
  exact Module.finitePresentation_of_surjective f hf hfg

end ArbitraryKernels

end Langlands.CommutativeAlgebra
