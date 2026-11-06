import Langlands.RingTheory.Grassmannian.Representability
import Langlands.RingTheory.Grassmannian.ProjectiveEmbedding
import Langlands.AlgebraicGeometry.ProjectiveSpace.Charts
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Proper

universe u

/-! # The represented quotient Grassmannian is proper and of finite presentation

For a finite projective module `M`, every scheme representing rank-`k` locally free
quotients of base changes of `M`, together with its affine chart cover, is proper and
locally of finite presentation over the base. See the paired Markdown.
-/

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry

set_option autoImplicit false

namespace Algebra.FinitePresentation

variable {R A B : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-- An algebra retract of a finitely presented algebra is finitely presented. -/
theorem of_retract [FinitePresentation R A] (f : A →ₐ[R] B) (g : B →ₐ[R] A)
    (hfg : f.comp g = AlgHom.id R B) : FinitePresentation R B := by
  classical
  obtain ⟨s, hs⟩ := (FiniteType.out : (⊤ : Subalgebra R A).FG)
  have hfg' : ∀ b, f (g b) = b := fun b => AlgHom.congr_fun hfg b
  have hsurj : Function.Surjective f := fun b => ⟨g b, hfg' b⟩
  refine of_surjective hsurj ⟨s.image fun a => a - g (f a), ?_⟩
  apply le_antisymm
  · rw [Ideal.span_le]
    intro y hy
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hy
    obtain ⟨a, -, rfl⟩ := hy
    change f.toRingHom (a - g (f a)) = 0
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, hfg', sub_self]
  · intro a ha
    let I : Ideal A := Ideal.span ↑(s.image fun a => a - g (f a))
    have hq : Ideal.Quotient.mkₐ R I = (Ideal.Quotient.mkₐ R I).comp (g.comp f) := by
      refine AlgHom.ext_of_adjoin_eq_top hs fun b hb => ?_
      simp only [AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
      rw [Ideal.Quotient.eq]
      exact Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_coe.mp hb)))
    have hfa : f a = 0 := ha
    have h := AlgHom.congr_fun hq a
    simp only [AlgHom.coe_comp, Function.comp_apply, hfa, map_zero, Ideal.Quotient.mkₐ_eq_mk] at h
    exact Ideal.Quotient.eq_zero_iff_mem.mp h

end Algebra.FinitePresentation

namespace SymmetricAlgebra

variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]

/-- The symmetric algebra of a finite projective module is finitely presented. -/
theorem finitePresentation_of_projective [Module.Finite R M] [Module.Projective R M] :
    Algebra.FinitePresentation R (SymmetricAlgebra R M) := by
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  have : Algebra.FinitePresentation R (SymmetricAlgebra R (Fin n → R)) :=
    .equiv (SymmetricAlgebra.equivMvPolynomial (Pi.basisFun R (Fin n))).symm
  refine .of_retract (SymmetricAlgebra.lift ((SymmetricAlgebra.ι R M).comp f))
    (SymmetricAlgebra.lift ((SymmetricAlgebra.ι R (Fin n → R)).comp g)) ?_
  apply SymmetricAlgebra.algHom_ext
  refine LinearMap.ext fun m => ?_
  have hm : f (g m) = m := LinearMap.congr_fun hfg m
  simp [hm]

end SymmetricAlgebra

namespace Module.Grassmannian.ChartAlgebra

variable (R : Type u) [CommRing R] {M : Type u} [AddCommGroup M] [Module R M] {k : ℕ}

/-- The algebra of the standard affine chart is finitely presented when `M` is finite
projective. -/
theorem finitePresentation [Module.Finite R M] [Module.Projective R M] (x : Fin k → M) :
    Algebra.FinitePresentation R (S R x) := by
  have : Module.Projective R (Fin k → M) :=
    Module.Projective.of_equiv' (DFinsupp.linearEquivFunOnFintype (R := R) (M := fun _ : Fin k => M))
  have := SymmetricAlgebra.finitePresentation_of_projective R (Fin k → M)
  refine Algebra.FinitePresentation.quotient (Submodule.fg_span ?_)
  refine (Set.finite_range fun ij : Fin k × Fin k =>
    SymmetricAlgebra.ι R (Fin k → M) (Pi.single ij.1 (x ij.2)) - if ij.1 = ij.2 then 1 else 0).subset ?_
  rintro a ⟨i, j, rfl⟩
  exact ⟨(i, j), rfl⟩

end Module.Grassmannian.ChartAlgebra

namespace Module.Grassmannian.ProjectiveEmbedding

open Module.Grassmannian.ChartLinear (Chart chartEquiv)

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M] {k : ℕ}

/-- Points of the standard chart are classified by algebra maps out of the chart algebra. -/
noncomputable def chartClassifier (x : Fin k → M) (A : Type u) [CommRing A] [Algebra R A] :
    Chart R x A ≃ (ChartAlgebra.S R x →ₐ[R] A) :=
  (chartEquiv x).trans (ChartAlgebra.homEquivPt x)

theorem chartClassifier_map (x : Fin k → M) {A B : Type u} [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) (N : Chart R x A) :
    chartClassifier x B ⟨Module.Grassmannian.map φ N.1, ChartLinear.map_mem_chart x φ N⟩ =
      φ.comp (chartClassifier x A N) := by
  simp only [chartClassifier, Equiv.trans_apply]
  rw [ChartLinear.chartEquiv_map]
  exact ChartAlgebra.homEquivPt_natural x φ _ _ fun m i => ChartLinear.pushHomX_apply x φ _ m i

section chartAlgebraEquiv

variable (D : Rep R M k) (x : Fin k → M)

/-- The universal point of the standard chart, over the chart algebra. -/
noncomputable def univChart : Chart R x (ChartAlgebra.S R x) :=
  (chartClassifier x _).symm (AlgHom.id R _)

/-- The classifying map of the chart point over the affine chart of the representing scheme. -/
noncomputable def toChartAlg : ChartAlgebra.S R x →ₐ[R] S D x :=
  chartClassifier x _ ⟨NS D x, NS_inChart D x⟩

theorem range_univChart_subset :
    Set.range (D.pt _ (univChart x).1).1.base ⊆ Set.range (gS D x).base := by
  rw [range_gS]
  exact (D.hVchart x _ _).mpr (univChart x).2

/-- The universal chart point factors through the affine chart of the representing scheme. -/
noncomputable def univSpecLift :
    Spec (CommRingCat.of (ChartAlgebra.S R x)) ⟶ Spec (CommRingCat.of (S D x)) :=
  IsOpenImmersion.lift (gS D x) (D.pt _ (univChart x).1).1 (range_univChart_subset D x)

theorem univSpecLift_fac : univSpecLift D x ≫ gS D x = (D.pt _ (univChart x).1).1 :=
  IsOpenImmersion.lift_fac _ _ _

theorem univSpecLift_over :
    univSpecLift D x ≫ Spec.map (CommRingCat.ofHom (algebraMap R (S D x))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (ChartAlgebra.S R x))) := by
  rw [specMap_algebraMap_S, ← Category.assoc, univSpecLift_fac]
  exact (D.pt _ (univChart x).1).2

/-- The algebra map inverse to `toChartAlg`. -/
noncomputable def fromChartAlg : S D x →ₐ[R] ChartAlgebra.S R x :=
  (exists_algHom (univSpecLift D x) (univSpecLift_over D x)).choose

theorem specMap_fromChartAlg :
    Spec.map (CommRingCat.ofHom (fromChartAlg D x).toRingHom) = univSpecLift D x :=
  (exists_algHom (univSpecLift D x) (univSpecLift_over D x)).choose_spec

theorem fromChartAlg_comp_toChartAlg :
    (fromChartAlg D x).comp (toChartAlg D x) = AlgHom.id R _ := by
  have hmap : Module.Grassmannian.map (fromChartAlg D x) (NS D x) = (univChart x).1 := by
    apply map_eq_of_pt D
    rw [specMap_fromChartAlg, pt_NS, univSpecLift_fac]
  unfold toChartAlg
  rw [← chartClassifier_map]
  calc chartClassifier x _ ⟨Module.Grassmannian.map (fromChartAlg D x) (NS D x), _⟩
      = chartClassifier x _ (univChart x) := congrArg _ (Subtype.ext hmap)
    _ = AlgHom.id R _ := (chartClassifier x _).apply_symm_apply _

theorem toChartAlg_comp_fromChartAlg :
    (toChartAlg D x).comp (fromChartAlg D x) = AlgHom.id R (S D x) := by
  have hmap : Module.Grassmannian.map (toChartAlg D x) (univChart x).1 = NS D x := by
    have h1 : chartClassifier x _ ⟨Module.Grassmannian.map (toChartAlg D x) (univChart x).1,
        ChartLinear.map_mem_chart x _ (univChart x)⟩ = chartClassifier x _ ⟨NS D x, NS_inChart D x⟩ := by
      rw [chartClassifier_map]
      unfold univChart
      rw [Equiv.apply_symm_apply]
      rfl
    exact congrArg Subtype.val ((chartClassifier x _).injective h1)
  have hspec : Spec.map (CommRingCat.ofHom ((toChartAlg D x).comp (fromChartAlg D x)).toRingHom) ≫
      gS D x = 𝟙 _ ≫ gS D x := by
    rw [Category.id_comp]
    have : CommRingCat.ofHom ((toChartAlg D x).comp (fromChartAlg D x)).toRingHom =
        CommRingCat.ofHom (fromChartAlg D x).toRingHom ≫ CommRingCat.ofHom (toChartAlg D x).toRingHom :=
      rfl
    rw [this, Spec.map_comp, Category.assoc, specMap_fromChartAlg, univSpecLift_fac,
      ← D.hpt _ _ (toChartAlg D x) (univChart x).1, hmap, pt_NS]
  have h2 := (cancel_mono (gS D x)).mp hspec
  have h3 : CommRingCat.ofHom ((toChartAlg D x).comp (fromChartAlg D x)).toRingHom = 𝟙 _ :=
    Spec.map_injective (h2.trans (Spec.map_id _).symm)
  exact AlgHom.ext fun s => congrArg (fun f => f.hom s) h3

/-- The coordinate ring of an affine chart of a representing scheme is the chart algebra. -/
noncomputable def chartAlgEquiv : S D x ≃ₐ[R] ChartAlgebra.S R x :=
  AlgEquiv.ofAlgHom (fromChartAlg D x) (toChartAlg D x) (fromChartAlg_comp_toChartAlg D x)
    (toChartAlg_comp_fromChartAlg D x)

theorem finitePresentation_S [Module.Finite R M] [Module.Projective R M] :
    Algebra.FinitePresentation R (S D x) :=
  have := ChartAlgebra.finitePresentation R x
  .equiv (chartAlgEquiv D x).symm

end chartAlgebraEquiv

variable (D : Rep R M k)

/-- A representing scheme of the Grassmannian of a finite projective module is locally of
finite presentation over the base. -/
theorem Rep.locallyOfFinitePresentation_p [Module.Finite R M] [Module.Projective R M] :
    LocallyOfFinitePresentation D.p := by
  -- Instance search does not find these instances here, so they are supplied explicitly.
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation.{u})
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @LocallyOfFinitePresentation) D.V D.hV
    fun x => ?_
  rw [← sV_gS D x, Category.assoc, ← specMap_algebraMap_S]
  have h1 : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R (S D x)))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr
      (RingHom.finitePresentation_algebraMap.mpr (finitePresentation_S D x))
  have h0 : LocallyOfFinitePresentation (sV D x) := locallyOfFinitePresentation_of_isOpenImmersion _
  exact locallyOfFinitePresentation_comp _ _

/-- A representing scheme of the Grassmannian of a finite module is proper over the base. -/
theorem Rep.isProper_p [Module.Finite R M] : IsProper D.p := by
  obtain ⟨m, ι, hι, hιp⟩ := Module.Grassmannian.exists_isClosedImmersion_toProjSpace_of_represents
    R M k D.Gr D.p D.pt D.hpt D.V D.hV D.hVaff D.hVchart
  rw [← hιp]
  have : IsProper (ProjSpace.π R m) := Langlands.AlgebraicGeometry.projectiveSpaceToSpec_isProper R m
  infer_instance

end Module.Grassmannian.ProjectiveEmbedding

open Module.Grassmannian.ProjectiveEmbedding in
/-- The Grassmannian of rank-`k` quotients of a finite projective module is represented by a
scheme that is proper and locally of finite presentation over the base. -/
theorem Module.Grassmannian.exists_scheme_represents_isProper_locallyOfFinitePresentation
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] (k : ℕ) :
    ∃ (Gr : Scheme.{u}) (p : Gr ⟶ Spec (CommRingCat.of R))
      (pt : ∀ (A : Type u) [CommRing A] [Algebra R A],
        Module.Grassmannian A (A ⊗[R] M) k ≃
          {g : Spec (CommRingCat.of A) ⟶ Gr // g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A))}),
      (∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B)
          (N : Module.Grassmannian A (A ⊗[R] M) k),
        (pt B (Module.Grassmannian.map φ N)).1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (pt A N).1) ∧
      IsProper p ∧ LocallyOfFinitePresentation p := by
  obtain ⟨Gr, p, pt, V, hpt, hV, hVaff, hVchart⟩ :=
    Module.Grassmannian.exists_scheme_represents_and_isAffineOpen_chart_cover R M k
  let D : Rep R M k := ⟨Gr, p, pt, hpt, V, hV, hVaff, hVchart⟩
  exact ⟨Gr, p, pt, hpt, D.isProper_p, D.locallyOfFinitePresentation_p⟩
