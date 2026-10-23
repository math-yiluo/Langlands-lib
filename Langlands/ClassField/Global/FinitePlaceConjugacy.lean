import Langlands.ClassField.Global.IdeleLocalInjectivity
import Langlands.Cohomology.OrdinaryInnerConjugation
import Langlands.ClassFieldTheory.Local.Conjugacy

/-! # Finite-place conjugacy and localization -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology CategoryTheory
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local FundamentalClass

universe u

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
  [w.asIdeal.LiesOver v.asIdeal]

local instance conjugatePlaceLiesOver (g : E ≃ₐ[F] E) :
    (finitePlaceEquiv g.toRingEquiv w).asIdeal.LiesOver v.asIdeal :=
  liesOver_finitePlaceEquiv v w g

/-- Completion transport along a base automorphism fixes the completed base field. -/
theorem finiteCompletionEquiv_algebraMap (g : E ≃ₐ[F] E) (x : v.adicCompletion F) :
    finiteCompletionEquiv g.toRingEquiv w
      (algebraMap (v.adicCompletion F)
        ((finitePlaceEquiv g.toRingEquiv w).adicCompletion E) x) =
      algebraMap (v.adicCompletion F) (w.adicCompletion E) x := by
  have heq := (denseRange_algebraMap F v).equalizer
    ((continuous_finiteCompletionEquiv g.toRingEquiv w).comp
      (FiniteExtension.continuous_completionMap v (finitePlaceEquiv g.toRingEquiv w)))
    (FiniteExtension.continuous_completionMap v w) (funext fun a => by
      simp only [Function.comp_apply, FiniteExtension.completionMap_coe,
        finiteCompletionEquiv_coe]
      change algebraMap E _ (g (algebraMap F E a)) = _
      rw [g.commutes])
  exact congrFun heq x

/-- The corresponding completions are isomorphic as algebras over the same completed base. -/
def finiteCompletionAlgEquiv (g : E ≃ₐ[F] E) :
    (finitePlaceEquiv g.toRingEquiv w).adicCompletion E ≃ₐ[v.adicCompletion F]
      w.adicCompletion E where
  __ := finiteCompletionEquiv g.toRingEquiv w
  commutes' := finiteCompletionEquiv_algebraMap v w g

@[simp]
theorem finiteCompletionAlgEquiv_coe (g : E ≃ₐ[F] E) (x : E) :
    finiteCompletionAlgEquiv v w g
      (algebraMap E ((finitePlaceEquiv g.toRingEquiv w).adicCompletion E) x) =
      algebraMap E (w.adicCompletion E) (g x) :=
  finiteCompletionEquiv_coe g.toRingEquiv w x

/-- The algebra equivalence determines the compatible field square used in relative conjugacy. -/
theorem finiteCompletionCompatible (g : E ≃ₐ[F] E) :
    CompatibleFieldEquivalences (RingEquiv.refl (v.adicCompletion F))
      (finiteCompletionAlgEquiv v w g).toRingEquiv :=
  fun x => (finiteCompletionAlgEquiv v w g).commutes x

variable [Normal F E]

/-- Decomposition homomorphisms conjugate with the actual completion isomorphism. -/
theorem decompositionHom_finiteCompletionConjugacy (g : E ≃ₐ[F] E)
    (σ : (finitePlaceEquiv g.toRingEquiv w).adicCompletion E ≃ₐ[v.adicCompletion F]
      (finitePlaceEquiv g.toRingEquiv w).adicCompletion E) :
    decompositionHom v w
      (galoisConjugacy (RingEquiv.refl (v.adicCompletion F))
        (finiteCompletionAlgEquiv v w g).toRingEquiv (finiteCompletionCompatible v w g) σ) =
      g * decompositionHom v (finitePlaceEquiv g.toRingEquiv w) σ * g⁻¹ := by
  ext x
  apply (algebraMap E (w.adicCompletion E)).injective
  rw [algebraMap_decompositionHom]
  change finiteCompletionAlgEquiv v w g
      (σ ((finiteCompletionAlgEquiv v w g).symm (algebraMap E (w.adicCompletion E) x))) =
    algebraMap E (w.adicCompletion E)
      (g (decompositionHom v (finitePlaceEquiv g.toRingEquiv w) σ (g.symm x)))
  have hs : (finiteCompletionAlgEquiv v w g).symm (algebraMap E (w.adicCompletion E) x) =
      algebraMap E ((finitePlaceEquiv g.toRingEquiv w).adicCompletion E) (g.symm x) := by
    apply (finiteCompletionAlgEquiv v w g).injective
    simp only [AlgEquiv.apply_symm_apply, finiteCompletionAlgEquiv_coe]
  rw [hs, ← algebraMap_decompositionHom, finiteCompletionAlgEquiv_coe]

/-- The inverse local conjugacy restricts to conjugation by the inverse global automorphism. -/
theorem decompositionHom_finiteCompletionConjugacy_symm (g : E ≃ₐ[F] E)
    (σ : w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E) :
    decompositionHom v (finitePlaceEquiv g.toRingEquiv w)
      ((galoisConjugacy (RingEquiv.refl (v.adicCompletion F))
        (finiteCompletionAlgEquiv v w g).toRingEquiv
        (finiteCompletionCompatible v w g)).symm σ) =
      g⁻¹ * decompositionHom v w σ * g := by
  have h := decompositionHom_finiteCompletionConjugacy v w g
    ((galoisConjugacy (RingEquiv.refl (v.adicCompletion F))
      (finiteCompletionAlgEquiv v w g).toRingEquiv
      (finiteCompletionCompatible v w g)).symm σ)
  rw [MulEquiv.apply_symm_apply] at h
  rw [h]
  group

/-- Finite localization intertwines the global inner-conjugation map with completion transport. -/
theorem innerConjugationMap_comp_ideleLocalMap (g : E ≃ₐ[F] E) (n : ℕ) :
    Langlands.OrdinaryCohomology.innerConjugationMap (relativeIdeleRepresentation F E) g⁻¹ n ≫
      ideleLocalMap v w n =
    ideleLocalMap v (finitePlaceEquiv g.toRingEquiv w) n ≫
      (relativeConjugacy (RingEquiv.refl (v.adicCompletion F))
        (finiteCompletionAlgEquiv v w g).toRingEquiv
        (finiteCompletionCompatible v w g) n).hom := by
  unfold relativeConjugacy groupCohomology.mapIso
  rw [← groupCohomology.map_comp, ← groupCohomology.map_comp]
  apply groupCohomology.map_congr
  · ext σ : 1
    change g⁻¹ * decompositionHom v w σ * (g⁻¹)⁻¹ = _
    rw [inv_inv]
    exact (decompositionHom_finiteCompletionConjugacy_symm v w g σ).symm
  · ext a
    change Additive.ofMul (ideleCoordinate w
        (relativeIdeleAut F E (g⁻¹)⁻¹ (@Additive.toMul (IdeleGroup (𝓞 E) E) a))) =
      Additive.ofMul (Units.map (finiteCompletionAlgEquiv v w g).toRingEquiv.toMonoidHom
        (ideleCoordinate (finitePlaceEquiv g.toRingEquiv w)
          (@Additive.toMul (IdeleGroup (𝓞 E) E) a)))
    rw [inv_inv]
    apply congrArg Additive.ofMul
    apply Units.ext
    exact ideleCoordinate_relativeIdeleAut g w _

/-- Degree-two finite localization is independent of conjugate places after actual transport. -/
theorem ideleLocalMap_finiteCompletionConjugacy (g : E ≃ₐ[F] E) :
    ideleLocalMap v (finitePlaceEquiv g.toRingEquiv w) 2 ≫
      (relativeConjugacy (RingEquiv.refl (v.adicCompletion F))
        (finiteCompletionAlgEquiv v w g).toRingEquiv
        (finiteCompletionCompatible v w g) 2).hom =
      ideleLocalMap v w 2 := by
  rw [← innerConjugationMap_comp_ideleLocalMap,
    Langlands.OrdinaryCohomology.innerConjugationMap_two, Category.id_comp]

/-- Evaluation of the degree-two localization comparison on an idele-cohomology class. -/
theorem ideleLocalMap_finiteCompletionConjugacy_apply (g : E ≃ₐ[F] E)
    (c : relativeIdeleCohomology F E 2) :
    (relativeConjugacy (RingEquiv.refl (v.adicCompletion F))
      (finiteCompletionAlgEquiv v w g).toRingEquiv
      (finiteCompletionCompatible v w g) 2).hom
        (ideleLocalMap v (finitePlaceEquiv g.toRingEquiv w) 2 c) =
      ideleLocalMap v w 2 c :=
  ConcreteCategory.congr_hom (ideleLocalMap_finiteCompletionConjugacy v w g) c

end Langlands.ClassField.Global
