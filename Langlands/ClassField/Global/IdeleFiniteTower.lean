import Langlands.ClassField.Global.IdeleCohomologyTower
import Langlands.ClassField.Global.ReciprocityTower

/-! # Finite local components of idele cohomology in towers -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local CategoryTheory FundamentalClass

universe u

section Components

variable (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
  (hI : ∀ (p : ℕ) [Fact p.Prime], (I p).RelativeImages)
  {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E]
  (wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v)

/-- The finitely supported family of finite invariants of an idele-cohomology class. -/
def finiteIdeleInvariantVector :
    relativeIdeleCohomology F E 2 →+ (HeightOneSpectrum (𝓞 F) →₀ RationalModIntegers) where
  toFun c := Finsupp.ofSupportFinite
    (fun v => haveI := (wf v).2; finiteIdeleInvariant I v (wf v).1 c)
    (finite_support_finiteIdeleInvariant I hI wf c)
  map_zero' := by
    ext v
    have := (wf v).2
    exact (finiteIdeleInvariant I v (wf v).1).map_zero
  map_add' x y := by
    ext v
    have := (wf v).2
    exact (finiteIdeleInvariant I v (wf v).1).map_add x y

@[simp] theorem finiteIdeleInvariantVector_apply
    (c : relativeIdeleCohomology F E 2) (v : HeightOneSpectrum (𝓞 F)) :
    finiteIdeleInvariantVector I hI wf c v =
      haveI := (wf v).2; finiteIdeleInvariant I v (wf v).1 c := rfl

end Components

section Coordinate

variable {E L : Type u} [Field E] [Field L] [NumberField E] [NumberField L]
  [Algebra E L] (w : HeightOneSpectrum (𝓞 E)) (q : HeightOneSpectrum (𝓞 L))
  [q.asIdeal.LiesOver w.asIdeal]

/-- An included idele has the completed image of its lower coordinate. -/
theorem ideleCoordinate_ideleInclusion (a : IdeleGroup (𝓞 E) E) :
    ideleCoordinate q (ideleInclusion a) =
      Units.map (algebraMap (w.adicCompletion E) (q.adicCompletion L)).toMonoidHom
        (ideleCoordinate w a) := by
  have hw : w = q.under (𝓞 E) := HeightOneSpectrum.ext (Ideal.over_def q.asIdeal w.asIdeal)
  subst w
  rfl

end Coordinate

section Inflation

variable {F E L : Type u} [Field F] [Field E] [Field L]
  [NumberField F] [NumberField E] [NumberField L]
  [Algebra F E] [Algebra E L] [Algebra F L] [IsScalarTower F E L]
  [IsGalois F E] [IsGalois F L]
  (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
  (q : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [q.asIdeal.LiesOver w.asIdeal] [q.asIdeal.LiesOver v.asIdeal]

/-- Finite localization of idele cohomology commutes with inflation in every degree. -/
theorem relativeIdeleInflation_comp_ideleLocalMap (n : ℕ) :
    relativeIdeleInflation F E L n ≫ ideleLocalMap v q n =
      ideleLocalMap v w n ≫
        relativeInflation (padicField v).Carrier (w.adicCompletion E) (q.adicCompletion L) n := by
  rw [← groupCohomology.map_comp, ← groupCohomology.map_comp]
  apply groupCohomology.map_congr
  · ext σ : 1
    exact CompletionTower.decompositionHom_restrictNormal v w q σ
  · ext a
    exact congrArg Additive.ofMul
      (ideleCoordinate_ideleInclusion w q (@Additive.toMul (IdeleGroup (𝓞 E) E) a))

/-- Evaluation form of the finite localization/inflation square. -/
theorem ideleLocalMap_relativeIdeleInflation (n : ℕ) (c : relativeIdeleCohomology F E n) :
    ideleLocalMap v q n (relativeIdeleInflation F E L n c) =
      relativeInflation (padicField v).Carrier (w.adicCompletion E) (q.adicCompletion L) n
        (ideleLocalMap v w n c) :=
  ConcreteCategory.congr_hom (relativeIdeleInflation_comp_ideleLocalMap v w q n) c

/-- Inflation preserves each finite idele invariant at compatible choices of places. -/
theorem finiteIdeleInvariant_relativeIdeleInflation
    (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
    (hI : ∀ (p : ℕ) [Fact p.Prime], (I p).InflationCompatibility)
    (c : relativeIdeleCohomology F E 2) :
    finiteIdeleInvariant I v q (relativeIdeleInflation F E L 2 c) =
      finiteIdeleInvariant I v w c := by
  have := isGalois_adicCompletion v w
  have := isGalois_adicCompletion v q
  have := FiniteExtension.local_finite v w
  have := FiniteExtension.local_finite v q
  have := FiniteExtension.local_finite w q
  change (I (residuePrime v)).relative (padicField v) (q.adicCompletion L)
      (ideleLocalMap v q 2 (relativeIdeleInflation F E L 2 c)) =
    (I (residuePrime v)).relative (padicField v) (w.adicCompletion E) (ideleLocalMap v w 2 c)
  rw [ideleLocalMap_relativeIdeleInflation v w q]
  exact hI (residuePrime v) (padicField v) (w.adicCompletion E) (q.adicCompletion L) _

end Inflation

section Restriction

variable {F K L : Type u} [Field F] [Field K] [Field L]
  [NumberField F] [NumberField K] [NumberField L]
  [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
  [IsGalois F L] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K))
  (q : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [q.asIdeal.LiesOver w.asIdeal] [q.asIdeal.LiesOver v.asIdeal]

/-- Finite localization of idele cohomology commutes with restriction in every degree. -/
theorem relativeIdeleRestriction_comp_ideleLocalMap (n : ℕ) :
    haveI := IsGalois.tower_top_of_isGalois F K L
    relativeIdeleRestriction F K L n ≫ ideleLocalMap w q n =
      ideleLocalMap v q n ≫
        relativeRestriction (padicField v).Carrier (w.adicCompletion K) (q.adicCompletion L) n := by
  have := IsGalois.tower_top_of_isGalois F K L
  rw [← groupCohomology.map_comp, ← groupCohomology.map_comp]
  apply groupCohomology.map_congr
  · ext σ x : 2
    apply (algebraMap L (q.adicCompletion L)).injective
    change algebraMap L (q.adicCompletion L) (decompositionHom w q σ x) =
      algebraMap L (q.adicCompletion L) (decompositionHom v q
        (σ.restrictScalars (v.adicCompletion F)) x)
    rw [algebraMap_decompositionHom, algebraMap_decompositionHom]
    rfl
  · rfl

/-- Evaluation form of the finite localization/restriction square. -/
theorem ideleLocalMap_relativeIdeleRestriction (n : ℕ) (c : relativeIdeleCohomology F L n) :
    haveI := IsGalois.tower_top_of_isGalois F K L
    ideleLocalMap w q n (relativeIdeleRestriction F K L n c) =
      relativeRestriction (padicField v).Carrier (w.adicCompletion K) (q.adicCompletion L) n
        (ideleLocalMap v q n c) :=
  ConcreteCategory.congr_hom (relativeIdeleRestriction_comp_ideleLocalMap v w q n) c

end Restriction

section Sum

variable {F E L : Type u} [Field F] [Field E] [Field L]
  [NumberField F] [NumberField E] [NumberField L]
  [Algebra F E] [Algebra E L] [Algebra F L] [IsScalarTower F E L]
  [IsGalois F E] [IsGalois F L]
  (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
  (hI : ∀ (p : ℕ) [Fact p.Prime], (I p).RelativeImages)
  (hInf : ∀ (p : ℕ) [Fact p.Prime], (I p).InflationCompatibility)

include hInf in
/-- The entire finitely supported vector of finite invariants is preserved by inflation. -/
theorem finiteIdeleInvariantVector_relativeIdeleInflation
    (wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v)
    (wf' : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove L v)
    (hw : ∀ v, (wf' v).1.asIdeal.LiesOver (wf v).1.asIdeal)
    (c : relativeIdeleCohomology F E 2) :
    finiteIdeleInvariantVector I hI wf' (relativeIdeleInflation F E L 2 c) =
      finiteIdeleInvariantVector I hI wf c := by
  ext v
  have := (wf v).2
  have := (wf' v).2
  have := hw v
  exact finiteIdeleInvariant_relativeIdeleInflation v (wf v).1 (wf' v).1 I hInf c

include hInf in
/-- The finite sum of invariants is preserved by inflation, with compatible place choices. -/
theorem finiteIdeleInvariantSum_relativeIdeleInflation
    (wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v)
    (wf' : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove L v)
    (hw : ∀ v, (wf' v).1.asIdeal.LiesOver (wf v).1.asIdeal)
    (c : relativeIdeleCohomology F E 2) :
    finiteIdeleInvariantSum I hI wf' (relativeIdeleInflation F E L 2 c) =
      finiteIdeleInvariantSum I hI wf c := by
  change (∑ᶠ v, haveI := (wf' v).2;
    finiteIdeleInvariant I v (wf' v).1 (relativeIdeleInflation F E L 2 c)) =
      ∑ᶠ v, haveI := (wf v).2; finiteIdeleInvariant I v (wf v).1 c
  congr 1
  funext v
  have := (wf v).2
  have := (wf' v).2
  have := hw v
  exact finiteIdeleInvariant_relativeIdeleInflation v (wf v).1 (wf' v).1 I hInf c

end Sum

end Langlands.ClassField.Global
