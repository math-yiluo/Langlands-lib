import Langlands.BruhatTits.SpecialCompact.JointBasisProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.Representation.CuspidalSupport.NormalHeckeTwist
import Langlands.Representation.CuspidalSupport.RationalSummandInductionSupercuspidal
import Langlands.Representation.Exponents.RepresentedCompactRestrictionSupercuspidal

/-! # Proper parabolic induction has no irreducible supercuspidal subquotient -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.5.2 for every proper represented rational parabolic. -/
theorem leviInductionNoSupercuspidalSubquotient :
    LeviInductionNoSupercuspidalSubquotientStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul hproper
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  intro ρ σ hσ hsub hcuspidal
  have : σ.representation.IsIrreducible := hσ
  have : Nontrivial σ :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (rationalPoints G)) σ.representation.asModule
  have : IsTopologicalGroup (rationalPoints G) :=
    Langlands.AlgebraicGeometry.PointTopology.rationalPoint_isTopologicalGroup k G
  let H := Plancherel.rationalCommonNormKernel G
  let τ := SmoothRep.restrictSubgroup H σ
  have hcompact : HasCompactNormKernelRestriction σ :=
    compactRestriction_of_isSupercuspidal parabolicDynamic standardCocharacter
      relativeRootSystem BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence hG σ hcuspidal
  have hinj : Function.Injective (SmoothRep.hom (𝟙 τ)) := fun _ _ h => h
  let C := CuspidalSupport.rationalNormKernelSummandInduction G τ
  have hprojective : Projective C :=
    CuspidalSupport.rationalNormKernelSummandInduction_projective G σ τ (𝟙 τ) hcompact hinj
  have hC : IsSupercuspidal C :=
    isSupercuspidal_rationalNormKernelSummandInduction σ hcuspidal τ (𝟙 τ) hinj
  let e := CuspidalSupport.NormalHecke.inducedHomEquiv H τ
    (Plancherel.isOpen_rationalCommonNormKernel G) σ
  let f : C ⟶ σ := e.symm (SmoothRep.hom (𝟙 τ))
  have hf : f ≠ 0 := by
    intro hf0
    have he : e f = SmoothRep.hom (𝟙 τ) := e.apply_symm_apply _
    rw [hf0, map_zero] at he
    obtain ⟨x, hx⟩ := exists_ne (0 : σ)
    exact hx (congrArg (fun a => a x) he).symm
  let A := (leviInductionFunctor p l r hp hr hl hmul).obj ρ
  change σ.IsSubquotient A at hsub
  obtain ⟨S, T, ⟨iso⟩⟩ := hsub
  let q : SmoothRep.subrepresentation A S ⟶ A.subquotient S T :=
    SmoothRep.mkQ (SmoothRep.subrepresentation A S) T
  have hq : Epi q := (SmoothRep.epi_iff_surjective q).mpr (SmoothRep.mkQ_surjective _ T)
  obtain ⟨g, hg⟩ := @Projective.factors _ _ C hprojective _ _ (f ≫ iso.hom) q hq
  let i := SmoothRep.subtype A S
  have : Mono i := (SmoothRep.mono_iff_injective i).mpr (SmoothRep.subtype_injective A S)
  have hgi : g ≫ i = 0 := by
    have h := hom_induction_eq_zero_of_supercuspidal hG p l r hp hl hr hmul
      hproper C hC ρ (SmoothRep.hom (g ≫ i))
    ext x
    exact congrArg (fun a => a x) h
  have hg0 : g = 0 := (cancel_mono i).mp (by simpa only [zero_comp] using hgi)
  apply hf
  calc
    f = (f ≫ iso.hom) ≫ iso.inv := by rw [Category.assoc, iso.hom_inv_id, Category.comp_id]
    _ = 0 := by rw [← hg, hg0, zero_comp, zero_comp]

end Langlands.Aubert.General.RepresentedParabolic
