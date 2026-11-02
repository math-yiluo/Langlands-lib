import Langlands.CommutativeAlgebra.PolynomialModuleResolution
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves

/-! # Projective dimension under polynomial induction -/

universe u v

namespace Langlands.CommutativeAlgebra

open Polynomial PolynomialModule CategoryTheory

variable {R : Type u} [CommRing R]

/-- The coefficientwise map on polynomial modules, with its polynomial linearity. -/
noncomputable def polynomialModuleMap {M N : Type v} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) :
    PolynomialModule R M →ₗ[R[X]] PolynomialModule R N where
  __ := PolynomialModule.map R f
  map_smul' p q := by simpa using PolynomialModule.map_smul R f p q

@[simp]
theorem polynomialModuleMap_coeff {M N : Type v} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) (p : PolynomialModule R M) (n : ℕ) :
    (polynomialModuleMap f p).coeff n = f (p.coeff n) := rfl

@[simp]
theorem polynomialModuleMap_single {M N : Type v} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) (n : ℕ) (m : M) :
    polynomialModuleMap f (single R n m) = single R n (f m) :=
  PolynomialModule.map_single ..

/-- Induction from `R` modules to polynomial modules over `R[X]`. -/
noncomputable def polynomialModuleFunctor (R : Type u) [CommRing R] :
    ModuleCat.{v} R ⥤ ModuleCat.{v} R[X] where
  obj M := ModuleCat.of R[X] (PolynomialModule R M)
  map f := ModuleCat.ofHom (polynomialModuleMap f.hom)
  map_id M := by
    apply ModuleCat.hom_ext
    ext p n
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    ext p n
    rfl

instance polynomialModuleFunctor_additive :
    (polynomialModuleFunctor.{u, v} R).Additive where
  map_add := by
    intro X Y f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro p
    change polynomialModuleMap (f + g).hom p =
      polynomialModuleMap f.hom p + polynomialModuleMap g.hom p
    apply PolynomialModule.ext
    ext n
    rfl

theorem polynomialModuleMap_injective {M N : Type v} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) (hf : Function.Injective f) :
    Function.Injective (polynomialModuleMap f) := by
  intro p q h
  apply PolynomialModule.ext
  ext n
  exact hf (congrArg (fun s : PolynomialModule R N => s.coeff n) h)

theorem polynomialModuleMap_surjective {M N : Type v} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Function.Surjective (polynomialModuleMap f) := by
  intro p
  obtain ⟨q, hq⟩ := Finsupp.mapRange_surjective f f.map_zero hf p.coeff
  exact ⟨PolynomialModule.ofCoeff R q, PolynomialModule.ext hq⟩

theorem polynomialModuleFunctor_shortExact {S : ShortComplex (ModuleCat.{v} R)}
    (hS : S.ShortExact) : (S.map (polynomialModuleFunctor R)).ShortExact := by
  classical
  apply ModuleCat.shortComplex_shortExact
  · apply Function.Exact.of_comp_eq_zero_of_ker_in_range
    · funext p
      apply PolynomialModule.ext
      ext n
      exact S.moduleCat_zero_apply _
    · intro p hp
      have hcoeff (n : ℕ) : S.g (p.coeff n) = 0 :=
        congrArg (fun q : PolynomialModule R S.X₃ => q.coeff n) hp
      choose a ha using fun n =>
        (ShortComplex.moduleCat_exact_iff S).1 hS.exact (p.coeff n) (hcoeff n)
      refine ⟨∑ n ∈ p.coeff.support, single R n (a n), ?_⟩
      apply PolynomialModule.ext
      ext n
      change (polynomialModuleMap S.f.hom (∑ i ∈ p.coeff.support,
        single R i (a i))).coeff n = p.coeff n
      simp [map_sum, ha, Finsupp.single_apply,
        Finset.sum_ite_eq', Finsupp.mem_support_iff]
      exact fun h => h.symm
  · exact polynomialModuleMap_injective S.f.hom hS.moduleCat_injective_f
  · exact polynomialModuleMap_surjective S.g.hom hS.moduleCat_surjective_g

instance polynomialModuleFunctor_preservesProjectiveObjects [Small.{v} R] :
    (polynomialModuleFunctor.{u, v} R).PreservesProjectiveObjects where
  projective_obj M {proj} := by
    have : Module.Projective R M := ModuleCat.projective_of_module_projective M
    have : Module.Projective R[X] (PolynomialModule R M) :=
      Module.Projective.of_equiv (polynomialTensorProductLEquivPolynomialModule R M)
    exact ModuleCat.projective_of_categoryTheory_projective
      (ModuleCat.of R[X] (PolynomialModule R M))

/-- Induction to polynomial modules preserves a finite projective-dimension bound. -/
theorem polynomialModule_hasProjectiveDimensionLE [Small.{v} R] (n : ℕ)
    (M : ModuleCat.{v} R) [HasProjectiveDimensionLE M n] :
    HasProjectiveDimensionLE ((polynomialModuleFunctor R).obj M) n := by
  induction n generalizing M with
  | zero =>
    have h : Projective M := projective_iff_hasProjectiveDimensionLT_one.2 ‹_›
    have : Projective ((polynomialModuleFunctor R).obj M) :=
      (polynomialModuleFunctor R).projective_obj_of_projective h
    infer_instance
  | succ n ih =>
    obtain ⟨⟨P, f⟩⟩ := ModuleCat.enoughProjectives.1 M
    let T := ShortComplex.mk (Limits.kernel.ι f) f (Limits.kernel.condition f)
    have hT : T.ShortExact := { exact := ShortComplex.exact_kernel f }
    have hTP := polynomialModuleFunctor_shortExact hT
    have hP : Projective (T.map (polynomialModuleFunctor R)).X₂ :=
      (polynomialModuleFunctor R).projective_obj _
    have := (hT.hasProjectiveDimensionLT_X₃_iff n ‹_›).1 ‹_›
    exact (hTP.hasProjectiveDimensionLT_X₃_iff n hP).2 (ih (Limits.kernel f))

/-- A compatible polynomial action raises an underlying finite dimension bound by at most one. -/
theorem polynomialAction_hasProjectiveDimensionLE [Small.{v} R] (n : ℕ)
    (M : Type v) [AddCommGroup M] [Module R M] [Module R[X] M]
    [IsScalarTower R R[X] M] [HasProjectiveDimensionLE (ModuleCat.of R M) n] :
    HasProjectiveDimensionLE (ModuleCat.of R[X] M) (n + 1) := by
  have h := polynomialModule_hasProjectiveDimensionLE n (ModuleCat.of R M)
  have : HasProjectiveDimensionLE (ModuleCat.of R[X] (PolynomialModule R M)) n := h
  have h₁ : HasProjectiveDimensionLT
      (polynomialActionShortComplex (R := R) (M := M)).X₁ (n + 1) := h
  have h₂ : HasProjectiveDimensionLT
      (polynomialActionShortComplex (R := R) (M := M)).X₂ (n + 1 + 1) :=
    hasProjectiveDimensionLT_of_ge (ModuleCat.of R[X] (PolynomialModule R M))
      (n + 1) (n + 1 + 1) (Nat.le_succ _)
  exact (polynomialActionShortComplex_shortExact (R := R) (M := M)).hasProjectiveDimensionLT_X₃
    (n + 1) h₁ h₂

end Langlands.CommutativeAlgebra
