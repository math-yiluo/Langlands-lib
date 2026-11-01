import Langlands.AlgebraicGeometry.Picard.AmpleIsoProof
import Langlands.AlgebraicGeometry.Picard.TranslationInvariantH0VanishingStatement
import Langlands.AlgebraicGeometry.Picard.TranslationInvariantPullbackIdentitiesProof
import Langlands.AlgebraicGeometry.Picard.LineBundleSectionVanishingProof
import Langlands.AlgebraicGeometry.Picard.AffineGenerationLocusIntersectionProof
import Langlands.AlgebraicGeometry.Modules.ResidueLocalChartProof
import Langlands.AlgebraicGeometry.Modules.OpenCoverHomGluing
import Langlands.AbelianScheme.SmoothGeometricIntegralityProof
import Langlands.AlgebraicGeometry.FieldSmoothProperConnectedGlobalFunctionsProof

/-! # Degree-zero vanishing for nontrivial translation-invariant line bundles -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule Langlands.Scheme.Modules

variable {X : Scheme.{u}}

/-- On a reduced scheme, a line-bundle section with empty trivialization open is zero. -/
theorem LineBundle.eq_zero_of_trivializationOpen_eq_bot [IsReduced X] (L : LineBundle X)
    (s : GlobalSections L.obj) (h : trivializationOpen L.obj s = ⊥) : s = 0 := by
  rw [← sectionHom_eq_zero_iff]
  have hloc : ∀ x : X, (Scheme.Modules.restrictFunctor (L.trivializingOpen x).ι).map
      (sectionHom L.obj s) = 0 := by
    intro x
    let W := L.trivializingOpen x
    let e : L.obj.restrict W.ι ≅ structureModule W.toScheme := L.localTrivialization x
    let ψ : structureModule W.toScheme ⟶ structureModule W.toScheme :=
      (Scheme.Modules.restrictUnitIso W.ι).inv ≫
        (Scheme.Modules.restrictFunctor W.ι).map (sectionHom L.obj s) ≫ e.hom
    have hψ : ψ = 0 := by
      rw [structureModule_hom_eq_zero_iff, ← basicOpen_eq_bot_iff,
        Scheme.basicOpen_eq_bot_iff_forall_evaluation_eq_zero]
      rintro ⟨y, hy⟩
      by_contra hne
      have hn : NonvanishingAt L.obj s (W.ι y) :=
        (residueLocalChartCriterion X L.obj s W y e).mpr hne
      have hmem : W.ι y ∈ nonvanishingLocus L.obj s := hn
      rw [lineBundleResidueOpenComparison X L s, h] at hmem
      exact hmem
    have hcomp : (Scheme.Modules.restrictFunctor W.ι).map (sectionHom L.obj s) =
        (Scheme.Modules.restrictUnitIso W.ι).hom ≫ ψ ≫ e.inv := by
      simp [ψ]
    rw [hcomp, hψ, zero_comp, comp_zero]
  let V : X → X.Opens := L.trivializingOpen
  have hV : IsOpenCover V :=
    IsOpenCover.mk (eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, L.mem_trivializingOpen x⟩)
  let 𝒰 := X.openCoverOfIsOpenCover V hV
  obtain ⟨g, -, hg⟩ := OpenCoverHomGluing.openCoverHomGluing X 𝒰 (structureModule X) L.obj
    (fun _ ↦ 0) (by intro i j; simp)
  have h1 : ∀ i, (Scheme.Modules.pullback (𝒰.f i)).map (sectionHom L.obj s) = 0 := fun i ↦
    (map_eq_zero_iff_of_natIso (Scheme.Modules.restrictFunctorIsoPullback (V i).ι) _).mp
      (hloc i)
  have h2 : ∀ i, (Scheme.Modules.pullback (𝒰.f i)).map
      (0 : structureModule X ⟶ L.obj) = 0 := fun i ↦ Functor.map_zero _ _ _
  exact (hg _ h1).trans (hg _ h2).symm

/-- A unit global function trivializes the structure sheaf everywhere. -/
lemma trivializationOpen_structureSheaf_of_isUnit {g : Γ(X, ⊤)} (hg : IsUnit g) :
    trivializationOpen (structureSheaf X) g = ⊤ := by
  apply trivializationOpen_eq_top_of_isIso
  let φ : structureModule X ⟶ structureModule X := sectionHom (structureSheaf X) g
  have hφ : unitEndCoefficient φ ⊤ = g := by
    change (sectionHom (structureSheaf X) g).app ⊤ (1 : Γ(X, ⊤)) = g
    rw [sectionHom_app_one]
    change (structureSheaf X).presheaf.map (𝟙 _) g = g
    simp
  change IsIso φ
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro U
  apply unitEnd_app_isIso
  rw [unitEndCoefficient_res φ (homOfLE le_top : U ⟶ ⊤), hφ]
  exact hg.map (X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom

/-- On an integral scheme whose global functions form a field, a line bundle `L` admitting
an isomorphism `L ⊗ f^*L ≅ 𝒪_X` along a surjective endomorphism `f` and not isomorphic to
the structure sheaf has no nonzero global section. -/
theorem LineBundle.eq_zero_of_tensor_pullback_iso [IsIntegral X] (hΓ : IsField Γ(X, ⊤))
    (L : LineBundle X) (f : X ⟶ X) (hf : Function.Surjective f)
    (φ : tensorObj L.obj ((Scheme.Modules.pullback f).obj L.obj) ≅ structureSheaf X)
    (hL : ¬ Nonempty (L ≅ LineBundle.trivial X)) (s : GlobalSections L.obj) : s = 0 := by
  let M : LineBundle X := (LineBundle.pullback f).obj L
  let t : GlobalSections M.obj := pullbackSection f L.obj s
  have ht : trivializationOpen M.obj t = f ⁻¹ᵁ trivializationOpen L.obj s :=
    lineBundlePullbackSectionOpen X X f L s
  let g : Γ(X, ⊤) := φ.hom.app ⊤ (tensorSection L.obj M.obj s t)
  have hg : trivializationOpen (structureSheaf X) g =
      trivializationOpen L.obj s ⊓ f ⁻¹ᵁ trivializationOpen L.obj s := by
    rw [← ht, ← tensorSectionGenerationLocus X L M s t]
    exact trivializationOpen_mapIso φ _
  by_cases hg0 : g = 0
  · apply LineBundle.eq_zero_of_trivializationOpen_eq_bot L s
    have hbot : trivializationOpen L.obj s ⊓ f ⁻¹ᵁ trivializationOpen L.obj s = ⊥ := by
      rw [← hg, hg0]
      exact trivializationOpen_zero (LineBundle.trivial X)
    by_contra hne
    obtain ⟨x, hx⟩ := Opens.ne_bot_iff_nonempty _ |>.mp hne
    obtain ⟨y, rfl⟩ := hf x
    obtain ⟨z, hz⟩ := nonempty_preirreducible_inter (trivializationOpen L.obj s).isOpen
      (f ⁻¹ᵁ trivializationOpen L.obj s).isOpen ⟨f y, hx⟩ ⟨y, hx⟩
    have hz' : z ∈ trivializationOpen L.obj s ⊓ f ⁻¹ᵁ trivializationOpen L.obj s := hz
    rw [hbot] at hz'
    exact hz'
  · exfalso
    have hu : IsUnit g := by
      obtain ⟨b, hb⟩ := hΓ.mul_inv_cancel hg0
      exact IsUnit.of_mul_eq_one _ hb
    have htop := trivializationOpen_structureSheaf_of_isUnit hu
    rw [hg] at htop
    have hs : trivializationOpen L.obj s = ⊤ := top_le_iff.mp (htop.symm ▸ inf_le_left)
    have := isIso_sectionHom_of_trivializationOpen_eq_top L.obj s hs
    exact hL ⟨(ObjectProperty.isoMk _ (asIso (sectionHom L.obj s)) :
      LineBundle.trivial X ≅ L).symm⟩

end Langlands.AlgebraicGeometry.Picard

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.Modules
open Langlands.SchemeModule Langlands.Scheme.Modules
open scoped CategoryTheory.MonObj

/-- Inversion on a group scheme is an involution of the underlying scheme. -/
lemma inversion_left_comp_inversion_left {S : Scheme.{u}} (A : AbelianScheme S) :
    ((𝟙 A.X : A.X ⟶ A.X)⁻¹).left ≫ ((𝟙 A.X : A.X ⟶ A.X)⁻¹).left = 𝟙 A.X.left := by
  rw [← Over.comp_left, GrpObj.comp_inv, Category.comp_id, inv_inv, Over.id_left]

/-- Degree-zero vanishing for a nontrivial line bundle `L` on an abelian scheme over a field,
given an isomorphism `L ⊗ i^*L ≅ 𝒪` for the inversion `i`. -/
theorem relativeCohomology_zero_isZero_of_inversion_tensor_iso {K : Type u} [Field K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (L : LineBundle A.X.left)
    (φ : tensorObj L.obj ((Scheme.Modules.pullback ((𝟙 A.X : A.X ⟶ A.X)⁻¹).left).obj L.obj) ≅
      structureSheaf A.X.left)
    (hL : ¬ Nonempty (L ≅ LineBundle.trivial A.X.left)) :
    IsZero ((DerivedSections.relativeCohomology A.X.hom 0).obj L.obj) := by
  have : GeometricallyIntegral A.X.hom :=
    smoothGeometricIntegrality K A.X.left A.X.hom inferInstance inferInstance
  have : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  have : IsIso A.X.hom.appTop :=
    Langlands.AlgebraicGeometry.fieldSmoothProperConnectedGlobalFunctions K A.X.left A.X.hom
      inferInstance inferInstance inferInstance
  have hΓ : IsField Γ(A.X.left, ⊤) := by
    let e : Γ(A.X.left, ⊤) ≅ CommRingCat.of K :=
      (asIso A.X.hom.appTop).symm ≪≫ Scheme.ΓSpecIso (CommRingCat.of K)
    exact e.commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField K)
  let i : A.X.left ⟶ A.X.left := ((𝟙 A.X : A.X ⟶ A.X)⁻¹).left
  have hi : Function.Surjective i := fun x ↦ ⟨i x, by
    rw [← Scheme.Hom.comp_apply, inversion_left_comp_inversion_left]
    rfl⟩
  have hs : ∀ s : GlobalSections L.obj, s = 0 := fun s ↦
    LineBundle.eq_zero_of_tensor_pullback_iso hΓ L i hi φ hL s
  refine IsZero.of_iso ?_ ((DerivedSections.relativeCohomologyZeroIso A.X.hom).app L.obj ≪≫
    ((DerivedSections.relativeGlobalSectionsIso A.X.hom).app L.obj).symm)
  exact @ModuleCat.isZero_of_subsingleton _ _ _ ⟨fun a b ↦ (hs a).trans (hs b).symm⟩

/-- A nontrivial translation-invariant line bundle on an abelian variety over an algebraically
closed field has vanishing degree-zero relative cohomology. -/
theorem algClosedFieldTranslationInvariantH0Vanishing :
    AlgClosedFieldTranslationInvariantH0VanishingStatement.{u} := by
  intro K _ _ A L hinv hL
  obtain ⟨-, ⟨φ⟩⟩ := algClosedFieldTranslationInvariantPullbackIdentities K A L hinv
  exact relativeCohomology_zero_isZero_of_inversion_tensor_iso A L φ hL

end Langlands.AbelianScheme
