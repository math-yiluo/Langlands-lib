import Langlands.GroupScheme.IntegralModel.Iso
import Langlands.GroupScheme.IntegralModel.BaseChangeCoefficientHom
import Langlands.GroupScheme.Descent.FpqcHomDescent
import Langlands.GroupScheme.Descent.AffineDatumMorphisms
import Langlands.GroupScheme.BaseChangeReflection

/-! # Descent of actual compatible model morphisms over a coefficient square -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.IntegralModel

open Descent

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G H : GroupScheme (Spec (CommRingCat.of K))}
  {M : IntegralModel R K G} {N : IntegralModel R K H} {f : G ⟶ H}
  (A L : Type u) [CommRing A] [IsDomain A] [Field L]
  [Algebra R A] [Algebra A L] [IsFractionRing A L]
  [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]

/-- Recover generic compatibility of an actual model map from a compatible
coefficient extension of that same map. -/
theorem generic_comm_of_coefficientExtension
    (g : M.group ⟶ N.group)
    (φ : (M.baseChange A L).Hom (N.baseChange A L)
      ((GroupScheme.baseChange (Spec.algebraMap K L)).map f))
    (hg : (GroupScheme.baseChange (Spec.algebraMap R A)).map g = φ.hom) :
    (GroupScheme.baseChange (Spec.algebraMap R K)).map g ≫ N.genericIso.hom =
      M.genericIso.hom ≫ f := by
  let f₀ : G ⟶ H := M.genericIso.inv ≫
    (GroupScheme.baseChange (Spec.algebraMap R K)).map g ≫ N.genericIso.hom
  let ψ : M.Hom N f₀ :=
    ⟨g, by simp [f₀]⟩
  have h₀ := (ψ.baseChangeCoefficients A L).generic_comm
  have h₁ : (GroupScheme.baseChange (Spec.algebraMap K L)).map f₀ =
      (GroupScheme.baseChange (Spec.algebraMap K L)).map f := by
    apply (cancel_epi (M.baseChange A L).genericIso.hom).mp
    rw [← h₀, ← φ.generic_comm]
    change (GroupScheme.baseChange (Spec.algebraMap A L)).map
        ((GroupScheme.baseChange (Spec.algebraMap R A)).map g) ≫ _ = _
    rw [hg]
  let : Flat (Spec.algebraMap K L) := (fieldExtension_fpqc K L).2.1
  let : Surjective (Spec.algebraMap K L) := (fieldExtension_fpqc K L).1
  let : QuasiCompact (Spec.algebraMap K L) := (fieldExtension_fpqc K L).2.2
  have hf : f₀ = f := (GroupScheme.baseChange (Spec.algebraMap K L)).map_injective h₁
  rw [← hf]
  exact ψ.generic_comm

variable [Flat (Spec.algebraMap R A)] [Surjective (Spec.algebraMap R A)]

private theorem hom_ext {a b : M.Hom N f} (h : a.hom = b.hom) : a = b := by
  cases a
  cases b
  cases h
  rfl

/-- Descend an actual compatible model homomorphism through the fpqc coefficient
cover, retaining the prescribed original generic map. -/
def Hom.descendCoefficients
    (φ : (M.baseChange A L).Hom (N.baseChange A L)
      ((GroupScheme.baseChange (Spec.algebraMap K L)).map f))
    (hφ : Compatible (canonicalDatum (Spec.algebraMap R A) M.group)
      (canonicalDatum (Spec.algebraMap R A) N.group) φ.hom) : M.Hom N f where
  hom := FpqcHomDescent.hom (Spec.algebraMap R A) φ.hom hφ
  generic_comm := generic_comm_of_coefficientExtension A L _ φ
    (FpqcHomDescent.baseChange_hom (Spec.algebraMap R A) φ.hom hφ)

/-- Coefficient base change recovers the supplied extending morphism exactly. -/
theorem Hom.baseChange_descendCoefficients
    (φ : (M.baseChange A L).Hom (N.baseChange A L)
      ((GroupScheme.baseChange (Spec.algebraMap K L)).map f))
    (hφ : Compatible (canonicalDatum (Spec.algebraMap R A) M.group)
      (canonicalDatum (Spec.algebraMap R A) N.group) φ.hom) :
    ((φ.descendCoefficients A L hφ).baseChangeCoefficients A L).hom = φ.hom :=
  FpqcHomDescent.baseChange_hom (Spec.algebraMap R A) φ.hom hφ

/-- Any original extension inducing the supplied map equals its descent. -/
theorem Hom.descendCoefficients_unique
    (φ : (M.baseChange A L).Hom (N.baseChange A L)
      ((GroupScheme.baseChange (Spec.algebraMap K L)).map f))
    (hφ : Compatible (canonicalDatum (Spec.algebraMap R A) M.group)
      (canonicalDatum (Spec.algebraMap R A) N.group) φ.hom)
    (ψ : M.Hom N f) (hψ : (ψ.baseChangeCoefficients A L).hom = φ.hom) :
    ψ = φ.descendCoefficients A L hφ := by
  have h : ψ.hom = (φ.descendCoefficients A L hφ).hom :=
    FpqcHomDescent.unique (Spec.algebraMap R A) φ.hom hφ ψ.hom hψ
  exact hom_ext h

variable {f : G ≅ H}

/-- Descend an actual compatible model isomorphism and retain the prescribed
generic isomorphism of the original models. -/
def Iso.descendCoefficients
    (e : (M.baseChange A L).Iso (N.baseChange A L)
      ((GroupScheme.baseChange (Spec.algebraMap K L)).mapIso f))
    (he : Compatible (canonicalDatum (Spec.algebraMap R A) M.group)
      (canonicalDatum (Spec.algebraMap R A) N.group) e.iso.hom) : M.Iso N f where
  iso := Solution.descendIso
    (canonicalSolution (Spec.algebraMap R A) M.group)
    (canonicalSolution (Spec.algebraMap R A) N.group) e.iso he
  generic_comm := generic_comm_of_coefficientExtension A L _ e.toHom (by
    simpa only [Solution.descendIso, Iso.toHom, canonicalSolution,
      CategoryTheory.Iso.refl_hom, Category.id_comp, Category.comp_id] using
      Solution.baseChange_descendHom
        (canonicalSolution (Spec.algebraMap R A) M.group)
        (canonicalSolution (Spec.algebraMap R A) N.group) e.iso.hom he)

/-- The actual descended isomorphism pulls back to the supplied isomorphism. -/
theorem Iso.baseChange_descendCoefficients
    (e : (M.baseChange A L).Iso (N.baseChange A L)
      ((GroupScheme.baseChange (Spec.algebraMap K L)).mapIso f))
    (he : Compatible (canonicalDatum (Spec.algebraMap R A) M.group)
      (canonicalDatum (Spec.algebraMap R A) N.group) e.iso.hom) :
    (GroupScheme.baseChange (Spec.algebraMap R A)).mapIso
      (e.descendCoefficients A L he).iso = e.iso := by
  simpa only [Iso.descendCoefficients, canonicalSolution, CategoryTheory.Iso.trans_refl,
    CategoryTheory.Iso.refl_trans] using
    Solution.baseChange_descendIso
      (canonicalSolution (Spec.algebraMap R A) M.group)
      (canonicalSolution (Spec.algebraMap R A) N.group) e.iso he

end Langlands.GroupScheme.IntegralModel
