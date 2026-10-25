import Langlands.ClassField.Global.IdeleSemilocal

/-! # The decomposition field of a finite place

For a finite Galois extension `E / F` of number fields and a finite place `w | v`, the
decomposition field `F' ⊆ E` is the fixed field of the image of the decomposition map
`decompositionHom v w : Gal(E_w/F_v) → Gal(E/F)`. The decomposition map identifies
`Gal(E_w/F_v)` with `Gal(E/F')`, so `[F' : F]` is the index of the image and, when `E_w / F_v`
is Galois, `[E : F'] = [E_w : F_v]`. The identity of `C_E` then identifies the cohomology of
`C_E` over `Gal(E/F')` with its cohomology over `Gal(E_w/F_v)`, and turns restriction from
`Gal(E/F)` to `Gal(E/F')` into `decompositionRestriction v w`.
-/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open CategoryTheory FundamentalClass

universe u

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Normal F E] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
  [w.asIdeal.LiesOver v.asIdeal]

/-- The decomposition field of `w | v`: the fixed field in `E` of the image of
`decompositionHom v w : Gal(E_w/F_v) → Gal(E/F)`. -/
def decompositionField : IntermediateField F E :=
  IntermediateField.fixedField (decompositionHom v w).range

/-- `Gal(E_w/F_v) ≃ Gal(E/F')` for the decomposition field `F'`: the injective decomposition
map onto its image, followed by the Galois correspondence for that image. -/
def decompositionEquiv :
    (w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E) ≃*
      (E ≃ₐ[decompositionField v w] E) :=
  (MonoidHom.ofInjective (decompositionHom_injective v w)).trans
    (IntermediateField.subgroupEquivAlgEquiv _)

/-- Forgetting `F'`-linearity of `decompositionEquiv v w σ` gives `decompositionHom v w σ`. -/
theorem restrictScalars_decompositionEquiv
    (σ : w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E) :
    (decompositionEquiv v w σ).restrictScalars F = decompositionHom v w σ :=
  AlgEquiv.ext fun _ => rfl

/-- `decompositionHom v w` factors as `decompositionEquiv v w` followed by forgetting
`F'`-linearity. -/
theorem restrictScalarsHom_comp_decompositionEquiv :
    (AlgEquiv.restrictScalarsHom F).comp (decompositionEquiv v w).toMonoidHom =
      decompositionHom v w :=
  MonoidHom.ext (restrictScalars_decompositionEquiv v w)

/-- The local automorphism corresponding to `g ∈ Gal(E/F')` restricts on `E` to `g`. -/
theorem decompositionHom_decompositionEquiv_symm (g : E ≃ₐ[decompositionField v w] E) :
    decompositionHom v w ((decompositionEquiv v w).symm g) = g.restrictScalars F := by
  rw [← restrictScalars_decompositionEquiv, MulEquiv.apply_symm_apply]

/-- `[F' : F]` is the index of the image of the decomposition map. -/
theorem finrank_decompositionField [IsGalois F E] :
    Module.finrank F (decompositionField v w) = (decompositionHom v w).range.index := by
  rw [IntermediateField.finrank_eq_fixingSubgroup_index, decompositionField,
    IntermediateField.fixingSubgroup_fixedField]

/-- `[E : F']` is the order of `Gal(E_w/F_v)`. -/
theorem finrank_decompositionField_eq_card :
    Module.finrank (decompositionField v w) E =
      Nat.card (w.adicCompletion E ≃ₐ[v.adicCompletion F] w.adicCompletion E) := by
  rw [decompositionField, IntermediateField.finrank_fixedField_eq_card]
  exact Nat.card_congr (MonoidHom.ofInjective (decompositionHom_injective v w)).toEquiv.symm

/-- `[E : F'] = [E_w : F_v]` when `E_w / F_v` is Galois. -/
theorem finrank_decompositionField_eq_local
    [IsGalois (padicField v).Carrier (w.adicCompletion E)] :
    Module.finrank (decompositionField v w) E =
      Module.finrank (padicField v).Carrier (w.adicCompletion E) := by
  have : FiniteDimensional (padicField v).Carrier (w.adicCompletion E) :=
    FiniteExtension.local_finite v w
  rw [finrank_decompositionField_eq_card]
  exact IsGalois.card_aut_eq_finrank _ _

/-- `[E : F] / [E_w : F_v] = [F' : F]` when `E_w / F_v` is Galois. -/
theorem finrank_div_finrank_local
    [IsGalois (padicField v).Carrier (w.adicCompletion E)] :
    Module.finrank F E / Module.finrank (padicField v).Carrier (w.adicCompletion E) =
      Module.finrank F (decompositionField v w) := by
  rw [← finrank_decompositionField_eq_local,
    ← Module.finrank_mul_finrank F (decompositionField v w) E,
    Nat.mul_div_cancel _ Module.finrank_pos]

/-- `Hⁿ(Gal(E/F'), C_E) ≅ Hⁿ(Gal(E_w/F_v), C_E)`, induced by `decompositionEquiv v w` and the
identity of `C_E`, where `Gal(E_w/F_v)` acts on `C_E` through `decompositionHom v w`. -/
def decompositionCohomologyIso (n : ℕ) :
    relativeIdeleClassCohomology (decompositionField v w) E n ≅
      groupCohomology (Rep.res (decompositionHom v w) (relativeIdeleClassRepresentation F E)) n :=
  groupCohomology.mapIso (decompositionEquiv v w).symm (LinearEquiv.refl _ _) (fun g => by
    ext a
    change Additive.ofMul (relativeIdeleClassAut _ E g a.toMul) =
      Additive.ofMul (relativeIdeleClassAut F E
        (decompositionHom v w ((decompositionEquiv v w).symm g)) a.toMul)
    rw [decompositionHom_decompositionEquiv_symm]
    rfl) n

/-- Restriction from `Gal(E/F)` to `Gal(E/F')` followed by `decompositionCohomologyIso v w n`
is the restriction `decompositionRestriction v w n` along `decompositionHom v w`. -/
def DecompositionRestrictionFactors (n : ℕ) : Prop :=
  relativeIdeleClassRestriction F (decompositionField v w) E n ≫
      (decompositionCohomologyIso v w n).hom =
    decompositionRestriction v w n

/-- Restriction to the decomposition field followed by `decompositionCohomologyIso v w n` is
the restriction `decompositionRestriction v w n` along `decompositionHom v w`. -/
theorem relativeIdeleClassRestriction_comp_decompositionCohomologyIso (n : ℕ) :
    relativeIdeleClassRestriction F (decompositionField v w) E n ≫
        (decompositionCohomologyIso v w n).hom =
      decompositionRestriction v w n := by
  show _ ≫ groupCohomology.map _ _ n = _
  rw [← groupCohomology.map_comp]
  exact groupCohomology.map_congr (restrictScalarsHom_comp_decompositionEquiv v w) rfl n

theorem decompositionRestrictionFactors (n : ℕ) : DecompositionRestrictionFactors v w n :=
  relativeIdeleClassRestriction_comp_decompositionCohomologyIso v w n

/-- Elementwise form of `relativeIdeleClassRestriction_comp_decompositionCohomologyIso`. -/
theorem decompositionCohomologyIso_relativeIdeleClassRestriction (n : ℕ)
    (b : relativeIdeleClassCohomology F E n) :
    (decompositionCohomologyIso v w n).hom
        (relativeIdeleClassRestriction F (decompositionField v w) E n b) =
      decompositionRestriction v w n b := by
  rw [← relativeIdeleClassRestriction_comp_decompositionCohomologyIso v w n]
  rfl

end Langlands.ClassField.Global
