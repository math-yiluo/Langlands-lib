import Langlands.ClassField.Global.IdeleCohomology
import Langlands.Global.AdelicFunctoriality.LocalDegree
import Langlands.ClassFieldTheory.Local.CyclicClassAlgebra
import Langlands.Global.Arithmetic.LocalNormSymbol
import Langlands.Global.Arithmetic.CyclotomicAuxiliary
import Langlands.ClassField.Global.IdeleSemilocal

/-! # Completions in towers of number fields

For a tower `F ⊆ K ⊆ L` of number fields and places `v | w | u`, the completion maps form a
scalar tower `F_v → K_w → L_u`, the decomposition maps commute with restriction, and local
restriction of automorphisms is surjective. The local component of a global carry class is
the local carry class of the restricted character.
-/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local
open CategoryTheory

namespace Langlands.ClassField.Global

universe u

namespace CompletionTower

section Tower

variable {F : Type*} {K : Type*} {L : Type*} [Field F] [Field K] [Field L] [NumberField F] [NumberField K]
  [NumberField L] [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
  (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal] [u.asIdeal.LiesOver w.asIdeal] [u.asIdeal.LiesOver v.asIdeal]

/-- The completion maps of a tower compose. -/
theorem completionMap_comp :
    (FiniteExtension.completionMap w u).comp (FiniteExtension.completionMap v w) =
      FiniteExtension.completionMap v u := by
  have hd := denseRange_algebraMap (K := F) (v := v)
  have h1 : Continuous ((FiniteExtension.completionMap w u).comp
      (FiniteExtension.completionMap v w)) :=
    (FiniteExtension.continuous_completionMap w u).comp
      (FiniteExtension.continuous_completionMap v w)
  have h2 := FiniteExtension.continuous_completionMap v u
  have heq := hd.equalizer h1 h2 (funext fun x => by
    simp only [Function.comp_apply, RingHom.coe_comp, FiniteExtension.completionMap_coe]
    rw [IsScalarTower.algebraMap_apply F K L])
  exact RingHom.ext fun x => congrFun heq x

instance isScalarTower_completion :
    IsScalarTower (v.adicCompletion F) (w.adicCompletion K) (u.adicCompletion L) :=
  .of_algebraMap_eq fun x => (congrArg (fun f => f x) (completionMap_comp v w u)).symm

end Tower

section Decomposition

open FundamentalClass

variable {F K L : Type u} [Field F] [Field K] [Field L] [NumberField F] [NumberField K]
  [NumberField L] [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
  [IsGalois F K] [IsGalois F L]
  (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal] [u.asIdeal.LiesOver w.asIdeal] [u.asIdeal.LiesOver v.asIdeal]

instance normal_completion : Normal (v.adicCompletion F) (w.adicCompletion K) :=
  have := isGalois_adicCompletion v w
  inferInstance

/-- Restricting a local automorphism of `L_u` to `K_w` corresponds to restricting the global
automorphism of `L` to `K`. -/
theorem decompositionHom_restrictNormal
    (σ : u.adicCompletion L ≃ₐ[v.adicCompletion F] u.adicCompletion L) :
    (decompositionHom v u σ).restrictNormal K =
      decompositionHom v w (σ.restrictNormal (w.adicCompletion K)) := by
  apply AlgEquiv.ext
  intro x
  apply (algebraMap K (u.adicCompletion L)).injective
  have h1 : algebraMap K (u.adicCompletion L) ((decompositionHom v u σ).restrictNormal K x) =
      σ (algebraMap K (u.adicCompletion L) x) := by
    rw [IsScalarTower.algebraMap_apply K L (u.adicCompletion L),
      AlgEquiv.restrictNormal_commutes, algebraMap_decompositionHom,
      ← IsScalarTower.algebraMap_apply K L (u.adicCompletion L)]
  have h2 : algebraMap K (u.adicCompletion L)
      (decompositionHom v w (σ.restrictNormal (w.adicCompletion K)) x) =
      σ (algebraMap K (u.adicCompletion L) x) := by
    rw [IsScalarTower.algebraMap_apply K (w.adicCompletion K) (u.adicCompletion L),
      algebraMap_decompositionHom, AlgEquiv.restrictNormal_commutes,
      ← IsScalarTower.algebraMap_apply K (w.adicCompletion K) (u.adicCompletion L)]
  rw [h1, h2]

/-- Local restriction of automorphisms is surjective. -/
theorem restrictNormalHom_surjective_completion :
    Function.Surjective (AlgEquiv.restrictNormalHom (F := v.adicCompletion F)
      (K₁ := u.adicCompletion L) (w.adicCompletion K)) :=
  AlgEquiv.restrictNormalHom_surjective _

end Decomposition

section LocalComponent

open FundamentalClass

variable {F E : Type u} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [IsGalois F E] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
  [w.asIdeal.LiesOver v.asIdeal]

/-- The local component of a global carry class is the local carry class of the character
restricted along the decomposition map. -/
theorem unitsLocalMap_cyclicClass {n : ℕ} [NeZero n]
    (χ : (E ≃ₐ[F] E) →* Multiplicative (ZMod n)) (a : Fˣ) :
    (unitsLocalMap v w 2).hom (cyclicClass F E χ a) =
      cyclicClass (padicField v).Carrier (w.adicCompletion E) (χ.comp (decompositionHom v w))
        (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a) := by
  refine CyclicClassAlgebra.map_cyclicClass _ _ χ a _ ?_
  apply Units.ext
  exact (IsScalarTower.algebraMap_apply F E (w.adicCompletion E) (a : F)).symm.trans
    (IsScalarTower.algebraMap_apply F (v.adicCompletion F) (w.adicCompletion E) (a : F))

end LocalComponent

section NormTower

variable {F : Type*} {K : Type*} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] (p₀ : HeightOneSpectrum (𝓞 ℚ)) (v : HeightOneSpectrum (𝓞 F))
  (w : HeightOneSpectrum (𝓞 K)) [v.asIdeal.LiesOver p₀.asIdeal] [w.asIdeal.LiesOver v.asIdeal]
  [w.asIdeal.LiesOver p₀.asIdeal]

/-- Transitivity of local norms in a tower of completions. -/
theorem localNorm_localNorm (x : w.adicCompletion K) :
    FiniteExtension.localNorm p₀ v (FiniteExtension.localNorm v w x) =
      FiniteExtension.localNorm p₀ w x := by
  have : Module.Finite (v.adicCompletion F) (w.adicCompletion K) := FiniteExtension.local_finite v w
  have : Module.Finite (p₀.adicCompletion ℚ) (v.adicCompletion F) :=
    FiniteExtension.local_finite p₀ v
  exact Algebra.norm_norm (S := v.adicCompletion F) (a := x)

/-- The cyclotomic symbol of a local norm in a tower. -/
theorem normSymbolAt_localNorm (m : ℕ) [NeZero m] (b : (w.adicCompletion K)ˣ) :
    Langlands.Global.CyclotomicSymbol.normSymbolAt m p₀ v
        (Units.map (FiniteExtension.localNorm v w) b) =
      Langlands.Global.CyclotomicSymbol.normSymbolAt m p₀ w b := by
  rw [Langlands.Global.CyclotomicSymbol.normSymbolAt_apply,
    Langlands.Global.CyclotomicSymbol.normSymbolAt_apply]
  congr 1
  apply Units.ext
  change (Rat.HeightOneSpectrum.adicCompletion.padicEquiv p₀)
      (FiniteExtension.localNorm p₀ v (FiniteExtension.localNorm v w (b : w.adicCompletion K))) = _
  rw [localNorm_localNorm]
  rfl

end NormTower

section FixedField

open FundamentalClass

variable {F L : Type u} [Field F] [Field L] [NumberField F] [NumberField L] [Algebra F L]
  [IsGalois F L] (H : Subgroup (L ≃ₐ[F] L)) [H.Normal]
  (v : HeightOneSpectrum (𝓞 F)) (u : HeightOneSpectrum (𝓞 L)) [u.asIdeal.LiesOver v.asIdeal]

instance numberField_fixedField : NumberField (IntermediateField.fixedField H) :=
  Langlands.Global.intermediateField_numberField _

/-- The place of the fixed field `L^H` below `u`. -/
abbrev fixedFieldPlace : HeightOneSpectrum (𝓞 (IntermediateField.fixedField H)) :=
  u.under (𝓞 (IntermediateField.fixedField H))

instance liesOver_fixedFieldPlace :
    (fixedFieldPlace H u).asIdeal.LiesOver v.asIdeal :=
  Ideal.LiesOver.tower_bot u.asIdeal _ _

/-- A local automorphism of `L_u` acts trivially on the completion of `L^H` exactly when its
global image lies in `H`. -/
theorem restrictNormal_eq_one_iff
    (σ : u.adicCompletion L ≃ₐ[v.adicCompletion F] u.adicCompletion L) :
    σ.restrictNormal ((fixedFieldPlace H u).adicCompletion (IntermediateField.fixedField H)) = 1 ↔
      decompositionHom v u σ ∈ H := by
  rw [← (decompositionHom_injective v (fixedFieldPlace H u)).eq_iff, map_one,
    ← decompositionHom_restrictNormal v (fixedFieldPlace H u) u σ]
  change AlgEquiv.restrictNormalHom (IntermediateField.fixedField H) (decompositionHom v u σ) = 1 ↔ _
  rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker,
    IntermediateField.fixingSubgroup_fixedField]

end FixedField

section Factor

/-- A homomorphism whose kernel is the kernel of a surjection factors through it injectively. -/
theorem exists_injective_factor {G Q M : Type*} [Group G] [Group Q] [Group M] (r : G →* Q)
    (hr : Function.Surjective r) (θ : G →* M) (hker : ∀ g, r g = 1 ↔ θ g = 1) :
    ∃ θ' : Q →* M, Function.Injective θ' ∧ ∀ g, θ' (r g) = θ g := by
  have hk : r.ker = θ.ker := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact hker g
  let e := QuotientGroup.quotientKerEquivOfSurjective r hr
  let θ' : Q →* M := (QuotientGroup.kerLift θ).comp
    ((QuotientGroup.quotientMulEquivOfEq hk).toMonoidHom.comp e.symm.toMonoidHom)
  refine ⟨θ', ?_, fun g => ?_⟩
  · exact (QuotientGroup.kerLift_injective θ).comp
      ((QuotientGroup.quotientMulEquivOfEq hk).injective.comp e.symm.injective)
  · have h1 : e.symm (r g) = (g : G ⧸ r.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    change QuotientGroup.kerLift θ (QuotientGroup.quotientMulEquivOfEq hk (e.symm (r g))) = θ g
    rw [h1]
    rfl

end Factor

end CompletionTower

end Langlands.ClassField.Global
