import Langlands.GroupScheme.UniformExponentLocality
import Langlands.AbelianScheme.GroupSchemeSubalgebraDescentProof
import Langlands.GroupScheme.Descent.Data
import Langlands.AlgebraicGeometry.SchemePureFibreDimensionDescent
import Langlands.AlgebraicGeometry.NoetherianApproximation.LineBundleDescentBridge
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone

/-! # Noetherian approximation for uniform exponents -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.UniformExponentApproximation

open Langlands.AlgebraicGeometry
open AffineLimit SchemeLimitModel.Geometry SchemeFiberGeometry
open Langlands.AlgebraicGeometry.NoetherianApproximation
open P2MW.S_AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone.LimBC

private def coefficientStages (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A] : FGIndex R A →o Subalgebra R A where
  toFun i := i.1
  monotone' _ _ h := h

private theorem coefficientStages_cover {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A] (a : A) :
    ∃ i : FGIndex R A, a ∈ coefficientStages R A i := by
  classical
  refine ⟨⟨Algebra.adjoin R ↑({a} : Finset A), Subalgebra.fg_adjoin_finset _⟩, ?_⟩
  exact Algebra.subset_adjoin (by simp)

private theorem structure_comparison {S X T : Scheme.{u}}
    (f : X ⟶ S) (q : T ⟶ S) :
    LocallyQuasiFinite (baseChangeMap f (𝟙 S) f (by simp) q) ↔
      LocallyQuasiFinite (pullback.snd f q) := by
  let P : MorphismProperty Scheme.{u} := @LocallyQuasiFinite
  have hc : baseChangeMap f (𝟙 S) f (by simp) q ≫ pullback.fst q (𝟙 S) =
      (pullbackSymmetry q f).hom ≫ pullback.snd f q := by simp
  calc
    P (baseChangeMap f (𝟙 S) f (by simp) q) ↔
        P (baseChangeMap f (𝟙 S) f (by simp) q ≫ pullback.fst q (𝟙 S)) :=
      (P.cancel_right_of_respectsIso _ _).symm
    _ ↔ P ((pullbackSymmetry q f).hom ≫ pullback.snd f q) := by rw [hc]
    _ ↔ P (pullback.snd f q) := P.cancel_left_of_respectsIso _ _

/-- Local quasi-finiteness of a finitely presented scheme model is detected
over one finitely generated coefficient subalgebra. -/
theorem exists_fg_locallyQuasiFinite
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (hqf : LocallyQuasiFinite (pullback.snd f (Spec.algebraMap R A))) :
    ∃ (T : Subalgebra R A), T.FG ∧
      LocallyQuasiFinite (pullback.snd f (Spec.algebraMap R T)) := by
  let S := coefficientStages R A
  let D := SubalgebraStages.specDiagram S
  let t : D ⟶ (Functor.const _).obj (Spec (CommRingCat.of R)) :=
    { app i := SubalgebraStages.specHom S i.unop
      naturality := by
        intro i j r
        change SubalgebraStages.specTrans S r.unop.le ≫
          SubalgebraStages.specHom S j.unop =
          SubalgebraStages.specHom S i.unop ≫ 𝟙 _
        rw [Category.comp_id]
        exact SubalgebraStages.specTrans_specHom S r.unop.le }
  obtain ⟨hc⟩ := nonempty_isLimit_specCone S coefficientStages_cover
  have hft {T : Scheme.{u}} (q : T ⟶ Spec (CommRingCat.of R)) :
      LocallyOfFiniteType (baseChangeMap f (𝟙 _) f (by simp) q) :=
    MorphismProperty.of_isPullback
      (baseChangeMap_cartesian f (𝟙 _) f (by simp) q).flip
      (inferInstance : LocallyOfFiniteType f)
  have hqf' : LocallyQuasiFinite
      (baseChangeMap f (𝟙 _) f (by simp) (Spec.algebraMap R A)) :=
    (structure_comparison f _).mpr hqf
  have := hft (Spec.algebraMap R A)
  have hdim : HasPureDimensionFibers 0
      (baseChangeMap f (𝟙 _) f (by simp) (Spec.algebraMap R A)) :=
    (hasPureDimensionFibers_zero_iff_locallyQuasiFinite _).mpr hqf'
  obtain ⟨i, hi⟩ := (SchemeLimitModel.relativePureFibreDimensionDescent
    0 _ D _ _ _ t f (𝟙 _) f (by simp) (SubalgebraStages.specCone S) hc
    (SubalgebraStages.specHomTop (A₀ := R) (A := A))
    (SubalgebraStages.specCone_π_app_specHom S)).mp hdim
  have := hft (t.app i)
  exact ⟨i.unop.1, i.unop.2, (structure_comparison f _).mp
    ((hasPureDimensionFibers_zero_iff_locallyQuasiFinite _).mp hi)⟩

/-- The affine uniform-exponent assertion over noetherian coefficient rings. -/
def NoetherianAffineStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))),
    IsCommMonObj G.X →
    LocallyOfFinitePresentation G.X.hom → QuasiCompact G.X.hom →
    QuasiSeparated G.X.hom → LocallyQuasiFinite G.X.hom →
    ∃ n : ℕ, 0 < n ∧
      ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ G.X), x ^ n = 1

private theorem points_pow_of_iso {S : Scheme.{u}} {G H : GroupScheme S}
    (e : G ≅ H) {n : ℕ}
    (h : ∀ (T : Over S) (x : T ⟶ H.X), x ^ n = 1) :
    ∀ (T : Over S) (x : T ⟶ G.X), x ^ n = 1 := by
  intro T x
  apply (cancel_mono e.hom.hom.hom).mp
  rw [MonObj.pow_comp, h, MonObj.one_comp]

private theorem property_of_iso (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] {S : Scheme.{u}} {G H : GroupScheme S}
    (e : G ≅ H) (h : P G.X.hom) : P H.X.hom := by
  have sq : IsPullback e.inv.hom.hom.left H.X.hom G.X.hom (𝟙 S) :=
    IsPullback.of_horiz_isIso
      ⟨by rw [Category.comp_id]; exact e.inv.hom.hom.w⟩
  exact MorphismProperty.of_isPullback sq h

/-- General affine bases reduce to noetherian affine bases using finite
presentation of the scheme and its entire group law. -/
theorem affine_of_noetherian (h : NoetherianAffineStatement.{u}) :
    UniformExponentLocality.AffineStatement.{u} := by
  intro R _ G hcomm hfp hqc hqs hqf
  let := hcomm
  let := hfp
  let := hqc
  let := hqs
  let := hqf
  let R₀ := ↥(⊥ : Subalgebra ℤ R)
  have hR₀ : Algebra.FiniteType ℤ R₀ :=
    (Subalgebra.fg_iff_finiteType _).mp Subalgebra.fg_bot
  have : IsNoetherianRing R₀ := Algebra.FiniteType.isNoetherianRing ℤ R₀
  obtain ⟨T, hT, -, X₀, f₀, π, hfp₀, hqc₀, hqs₀, hπ⟩ :=
    exists_fg_subalgebra_isPullback_of_locallyOfFinitePresentation
      (A₀ := R₀) G.X.hom (∅ : Finset R)
  have := hfp₀
  have := hqc₀
  have := hqs₀
  have : Algebra.FiniteType R₀ T := (Subalgebra.fg_iff_finiteType _).mp hT
  have : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing R₀ T
  obtain ⟨U, hU, -, H, a, ha, hcommH, ⟨e⟩⟩ :=
    subalgebraDescent f₀ G π hπ (∅ : Finset R)
  have hfpH : LocallyOfFinitePresentation H.X.hom :=
    MorphismProperty.of_isPullback ha hfp₀
  have hqcH : QuasiCompact H.X.hom := MorphismProperty.of_isPullback ha hqc₀
  have hqsH : QuasiSeparated H.X.hom := MorphismProperty.of_isPullback ha hqs₀
  have : IsCommMonObj H.X := hcommH hcomm
  have : Algebra.FiniteType T U := (Subalgebra.fg_iff_finiteType _).mp hU
  have : IsNoetherianRing U := Algebra.FiniteType.isNoetherianRing T U
  let : CommRing U := inferInstance
  let : Algebra U R := U.toAlgebra
  have hqfH : LocallyQuasiFinite (pullback.snd H.X.hom (Spec.algebraMap U R)) :=
    property_of_iso @LocallyQuasiFinite e hqf
  have hex : ∃ (V : Subalgebra U R), V.FG ∧
      LocallyQuasiFinite (pullback.snd H.X.hom (Spec.algebraMap U V)) :=
    exists_fg_locallyQuasiFinite (R := U) (A := R) H.X.hom hqfH
  obtain ⟨V, hV, hqfV⟩ := hex
  have : Algebra.FiniteType U V := (Subalgebra.fg_iff_finiteType _).mp hV
  have : IsNoetherianRing V := Algebra.FiniteType.isNoetherianRing U V
  let H' := (baseChange (Spec.algebraMap U V)).obj H
  have hcomm' : IsCommMonObj H'.X := baseChange_isCommMonObj _ H
  have hfp' : LocallyOfFinitePresentation H'.X.hom := by
    change LocallyOfFinitePresentation (pullback.snd H.X.hom _)
    infer_instance
  have hqc' : QuasiCompact H'.X.hom := by
    change QuasiCompact (pullback.snd H.X.hom _)
    infer_instance
  have hqs' : QuasiSeparated H'.X.hom := by
    change QuasiSeparated (pullback.snd H.X.hom _)
    infer_instance
  obtain ⟨n, hn, hpow⟩ := h V H' hcomm' hfp' hqc' hqs' hqfV
  have hcomp : Spec.algebraMap V R ≫ Spec.algebraMap U V = Spec.algebraMap U R := by
    rw [Spec.algebraMap, Spec.algebraMap, Spec.algebraMap,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let e' : G ≅ (baseChange (Spec.algebraMap V R)).obj H' :=
    e ≪≫ (Descent.pullbackComparison (Spec.algebraMap U V)
      (Spec.algebraMap V R) (Spec.algebraMap U R) hcomp H).symm
  exact ⟨n, hn, points_pow_of_iso e'
    (UniformExponentLocality.points_pow_baseChange H' hpow _)⟩

/-- The noetherian affine assertion suffices for the unchanged theorem. -/
theorem uniformExponent_of_noetherian (h : NoetherianAffineStatement.{u}) :
    QuasiFiniteCommutativeUniformExponentStatement.{u} :=
  UniformExponentLocality.uniformExponent_of_affine (affine_of_noetherian h)

end Langlands.GroupScheme.UniformExponentApproximation
