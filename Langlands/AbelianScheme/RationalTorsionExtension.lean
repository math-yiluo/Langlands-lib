import Langlands.AbelianScheme.RaynaudSemiabelianCriterionStatement
import Langlands.AbelianScheme.TorsionFiniteEtale
import Langlands.AbelianScheme.KernelBaseChange
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricCardinality
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.FieldTheory.Minpoly.Field

/-! # Rational torsion after a finite extension of the base field -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

namespace Langlands.AbelianScheme

namespace RationalTorsionExtension

section Algebra

variable (K A : Type u) [Field K] [CommRing A] [Algebra K A] [Module.Finite K A]

/-- The product of the minimal polynomials of the vectors of a chosen basis. -/
def basisMinpolyProduct : K[X] :=
  ∏ i, minpoly K (Module.Free.chooseBasis K A i)

/-- The product of the basis minimal polynomials is nonzero, each factor being the minimal
polynomial of an integral element. -/
theorem basisMinpolyProduct_ne_zero : basisMinpolyProduct K A ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ _ => minpoly.ne_zero (IsIntegral.of_finite K _)

/-- If the basis minimal polynomials split in `L`, every algebra map from the finite
algebra to an extension field of `L` takes values in `L`. -/
theorem exists_algHom_factor_of_splits (L Ω : Type u) [Field L] [Algebra K L] [Field Ω]
    [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
    (hL : ((basisMinpolyProduct K A).map (algebraMap K L)).Splits) (φ : A →ₐ[K] Ω) :
    ∃ ψ : A →ₐ[K] L, (IsScalarTower.toAlgHom K L Ω).comp ψ = φ := by
  let incl := IsScalarTower.toAlgHom K L Ω
  let b := Module.Free.chooseBasis K A
  have hbasis : ∀ i, φ (b i) ∈ incl.range := by
    intro i
    have hdvd : minpoly K (b i) ∣ basisMinpolyProduct K A :=
      Finset.dvd_prod_of_mem (fun j => minpoly K (b j)) (Finset.mem_univ i)
    have hsplit : ((minpoly K (b i)).map (algebraMap K L)).Splits :=
      hL.of_dvd (Polynomial.map_ne_zero (basisMinpolyProduct_ne_zero K A))
        (Polynomial.map_dvd _ hdvd)
    have hne : (minpoly K (b i)).map (algebraMap K L) ≠ 0 :=
      Polynomial.map_ne_zero (minpoly.ne_zero (IsIntegral.of_finite K _))
    have hroot : (((minpoly K (b i)).map (algebraMap K L)).map (algebraMap L Ω)).IsRoot
        (φ (b i)) := by
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq, Polynomial.IsRoot,
        Polynomial.eval_map_algebraMap, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    obtain ⟨y, hy⟩ := hsplit.mem_range_of_isRoot hne hroot
    exact ⟨y, hy⟩
  have hall : ∀ a, φ a ∈ incl.range := by
    intro a
    have hspan : a ∈ Submodule.span K (Set.range b) := by
      rw [b.span_eq]
      exact Submodule.mem_top
    refine Submodule.span_induction (p := fun a _ => φ a ∈ incl.range) ?_ ?_ ?_ ?_ hspan
    · rintro _ ⟨i, rfl⟩
      exact hbasis i
    · simp
    · intro x y _ _ hx hy
      rw [map_add]
      exact add_mem hx hy
    · intro c x _ hx
      rw [map_smul]
      exact Subalgebra.smul_mem _ hx c
  let e : L ≃ₐ[K] incl.range := AlgEquiv.ofInjective incl incl.toRingHom.injective
  refine ⟨e.symm.toAlgHom.comp (φ.codRestrict incl.range hall), ?_⟩
  ext a
  have h := e.apply_symm_apply ⟨φ a, hall a⟩
  exact congrArg Subtype.val h

end Algebra

section Points

open Langlands.AlgebraicGeometry.FiniteEtale

variable {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))

/-- The spectrum maps of a scalar tower of fields compose to the spectrum map of the
composite. -/
theorem specAlgebraMap_comp (L Ω : Type u) [Field L] [Algebra K L] [Field Ω] [Algebra L Ω]
    [Algebra K Ω] [IsScalarTower K L Ω] :
    Spec.algebraMap L Ω ≫ Spec.algebraMap K L = Spec.algebraMap K Ω := by
  rw [Spec.algebraMap, Spec.algebraMap, Spec.algebraMap, ← Spec.map_comp]
  congr 1
  ext r
  exact (IsScalarTower.algebraMap_apply K L Ω r).symm

/-- On global sections, the inverse of `X.isoSpec` is inverse to the identification of
`Γ(Spec Γ(X, ⊤), ⊤)` with `Γ(X, ⊤)`. -/
theorem isoSpec_inv_appTop_ΓSpecIso_hom [IsAffine X] :
    X.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso Γ(X, ⊤)).hom = 𝟙 _ := by
  simpa only [Scheme.Hom.comp_appTop, Scheme.isoSpec_hom,
    Scheme.toSpecΓ_appTop, Scheme.Hom.id_appTop] using
    congrArg Scheme.Hom.appTop X.isoSpec.hom_inv_id

/-- The morphism `Spec R → X` defined by a ring map `φ : Γ(X, ⊤) → R` induces `φ` on
global sections. -/
theorem specMap_isoSpec_inv_appTop [IsAffine X] {R : CommRingCat.{u}} (φ : Γ(X, ⊤) ⟶ R) :
    (Spec.map φ ≫ X.isoSpec.inv).appTop ≫ (Scheme.ΓSpecIso R).hom = φ := by
  rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality,
    ← Category.assoc, isoSpec_inv_appTop_ΓSpecIso_hom, Category.id_comp]

/-- A point of `X` over `K` with values in a field `Ω` gives a `K`-algebra map from the
global functions of `X` to `Ω`. -/
def pointAlgHom (Ω : Type u) [Field Ω] [Algebra K Ω]
    (x : Spec (CommRingCat.of Ω) ⟶ X) (hx : x ≫ f = Spec.algebraMap K Ω) :
    letI := coordinateAlgebra f
    Γ(X, ⊤) →ₐ[K] Ω := by
  letI := coordinateAlgebra f
  exact
    { toRingHom := (x.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom).hom
      commutes' := fun r => by
        have h : (Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫ x.appTop ≫
            (Scheme.ΓSpecIso (.of Ω)).hom = CommRingCat.ofHom (algebraMap K Ω) := by
          rw [← Category.assoc f.appTop, ← Scheme.Hom.comp_appTop, hx, Spec.algebraMap,
            Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
        exact congrArg (fun g : CommRingCat.of K ⟶ CommRingCat.of Ω => g.hom r) h }

/-- `pointAlgHom` is the map induced on global sections. -/
theorem pointAlgHom_apply (Ω : Type u) [Field Ω] [Algebra K Ω]
    (x : Spec (CommRingCat.of Ω) ⟶ X) (hx : x ≫ f = Spec.algebraMap K Ω) (a : Γ(X, ⊤)) :
    pointAlgHom f Ω x hx a = (x.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom).hom a :=
  rfl

/-- For a finite morphism to the spectrum of a field `K`, there is a finite extension `L`
of `K` such that every point of the source with values in an extension field of `L`
factors through an `L`-point. -/
theorem exists_finite_pointFactorization [IsFinite f] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L), Module.Finite K L ∧
      ∀ (Ω : Type u) [Field Ω] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
        (x : Spec (CommRingCat.of Ω) ⟶ X), x ≫ f = Spec.algebraMap K Ω →
        ∃ y : Spec (CommRingCat.of L) ⟶ X, y ≫ f = Spec.algebraMap K L ∧
          Spec.algebraMap L Ω ≫ y = x := by
  have : IsAffine X := isAffine_of_isAffineHom f
  let := coordinateAlgebra f
  have : Module.Finite K Γ(X, ⊤) :=
    RingHom.Finite.comp f.finite_appTop
      (RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).2)
  refine ⟨(basisMinpolyProduct K Γ(X, ⊤)).SplittingField, inferInstance, inferInstance,
    inferInstance, ?_⟩
  intro Ω _ _ _ _ x hx
  set L := (basisMinpolyProduct K Γ(X, ⊤)).SplittingField
  obtain ⟨ψ, hψ⟩ := exists_algHom_factor_of_splits K Γ(X, ⊤) L Ω
    (SplittingField.splits _) (pointAlgHom f Ω x hx)
  let ψ' : Γ(X, ⊤) ⟶ CommRingCat.of L := CommRingCat.ofHom ψ.toRingHom
  refine ⟨Spec.map ψ' ≫ X.isoSpec.inv, ?_, ?_⟩
  · apply ext_of_isAffine
    apply (cancel_mono (Scheme.ΓSpecIso (CommRingCat.of L)).hom).1
    rw [Scheme.Hom.comp_appTop, Category.assoc, specMap_isoSpec_inv_appTop, Spec.algebraMap,
      Scheme.ΓSpecIso_naturality]
    apply (cancel_epi (Scheme.ΓSpecIso (CommRingCat.of K)).inv).1
    rw [Iso.inv_hom_id_assoc]
    ext r
    exact ψ.commutes r
  · apply ext_of_isAffine
    apply (cancel_mono (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom).1
    rw [Scheme.Hom.comp_appTop, Category.assoc, Spec.algebraMap, Scheme.ΓSpecIso_naturality,
      ← Category.assoc, specMap_isoSpec_inv_appTop]
    ext a
    exact congrArg (fun g : Γ(X, ⊤) →ₐ[K] Ω => g a) hψ

end Points

end RationalTorsionExtension

namespace RationalTorsionExtension

variable {S S' : Scheme.{u}} (b : S' ⟶ S) (G : Grp (Over S)) [IsCommMonObj G.X]

/-- A torsion point of a base change lifts to the torsion subgroup scheme of the original
group scheme after pushing the test scheme forward. -/
theorem exists_torsion_lift_baseChange (n : ℤ) (T : Over S')
    (x : T ⟶ ((Over.pullback b).mapGrp.obj G).X) (hx : x ^ n = 1) :
    ∃ z : (Over.map b).obj T ⟶ (GroupScheme.torsion G n).X,
      z ≫ (GroupScheme.torsionι G n).hom.hom = GroupScheme.baseChangePointsEquiv b G T x := by
  have hex : GroupScheme.baseChangePointsEquiv b G T x ^ n = 1 := by
    rw [← map_zpow, hx, map_one]
  obtain ⟨z, hz, -⟩ :=
    (GroupScheme.existsUnique_torsion_lift_iff G n ((Over.map b).obj T)
      (GroupScheme.baseChangePointsEquiv b G T x)).mpr hex
  exact ⟨z, hz⟩

/-- A point of the base change whose pushed-forward point factors through a lift of the
test-scheme map is the restriction of the corresponding point. -/
theorem baseChange_point_restrict {T T₀ : Over S'} (a : T ⟶ T₀) (n : ℤ)
    (x : T ⟶ ((Over.pullback b).mapGrp.obj G).X)
    (z : (Over.map b).obj T ⟶ (GroupScheme.torsion G n).X)
    (hz : z ≫ (GroupScheme.torsionι G n).hom.hom = GroupScheme.baseChangePointsEquiv b G T x)
    (w : (Over.map b).obj T₀ ⟶ (GroupScheme.torsion G n).X)
    (hw : a.left ≫ w.left = z.left) :
    a ≫ (GroupScheme.baseChangePointsEquiv b G T₀).symm
      (w ≫ (GroupScheme.torsionι G n).hom.hom) = x := by
  apply (GroupScheme.baseChangePointsEquiv b G T).injective
  rw [GroupScheme.baseChangePointsEquiv_naturality, MulEquiv.apply_symm_apply, ← hz,
    ← Category.assoc]
  congr 1
  apply Over.OverMorphism.ext
  simpa using hw

end RationalTorsionExtension

open RationalTorsionExtension in
/-- For `n` positive and invertible in `K`, the `n`-torsion of an abelian variety over `K`
becomes rational over a finite extension of `K`. -/
theorem exists_finite_hasRationalGeometricTorsion (K : Type u) [Field K]
    (B : AbelianScheme (Spec (CommRingCat.of K))) (n : ℕ) (hn : 0 < n) (hu : IsUnit (n : K)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L), Module.Finite K L ∧
      HasRationalGeometricTorsion ((baseChange (Spec.algebraMap K L)).obj B) n := by
  have hu' : IsUnit ((n : ℕ) : Γ(Spec (CommRingCat.of K), ⊤)) := by
    simpa using hu.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  obtain ⟨hfin, -⟩ := torsionFiniteEtale (Spec (CommRingCat.of K)) B n hn hu'
  obtain ⟨L, _, _, hL, hfac⟩ :=
    exists_finite_pointFactorization (GroupScheme.torsion B.toGrp (n : ℤ)).X.hom
  refine ⟨L, inferInstance, inferInstance, hL, ?_⟩
  intro x hx
  have hx' : x ^ (n : ℤ) = 1 := (GroupScheme.mem_torsionPoints _ _ _ _).mp hx
  obtain ⟨z, hz⟩ := exists_torsion_lift_baseChange (Spec.algebraMap K L) B.toGrp (n : ℤ) _ x hx'
  have hzK : z.left ≫ (GroupScheme.torsion B.toGrp (n : ℤ)).X.hom =
      Spec.algebraMap K (AlgebraicClosure L) := by
    rw [Over.w z]
    exact specAlgebraMap_comp L (AlgebraicClosure L)
  obtain ⟨y₀, hy₀K, hy₀⟩ := hfac (AlgebraicClosure L) z.left hzK
  let w : (Over.map (Spec.algebraMap K L)).obj (Over.mk (𝟙 (Spec (CommRingCat.of L)))) ⟶
      (GroupScheme.torsion B.toGrp (n : ℤ)).X :=
    Over.homMk y₀ (by simpa using hy₀K)
  let a : Over.mk (Spec.algebraMap L (AlgebraicClosure L)) ⟶
      Over.mk (𝟙 (Spec (CommRingCat.of L))) :=
    Over.homMk (Spec.algebraMap L (AlgebraicClosure L))
  exact ⟨_, baseChange_point_restrict (Spec.algebraMap K L) B.toGrp a (n : ℤ) x z hz w hy₀⟩

end Langlands.AbelianScheme
