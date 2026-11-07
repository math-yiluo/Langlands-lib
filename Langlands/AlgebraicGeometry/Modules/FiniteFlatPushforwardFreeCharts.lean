import Langlands.AlgebraicGeometry.Modules.DirectImageAffineCriterion
import Langlands.AlgebraicGeometry.Modules.AffineCartesianSectionsBaseChange
import Langlands.AlgebraicGeometry.Modules.PullbackUnit
import Langlands.AlgebraicGeometry.Picard.LineBundleQuasicoherent
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.EquationalCriterion

/-! # The pushforward of the structure sheaf along a finite flat morphism of constant degree -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

open Langlands.Scheme.Modules Langlands.AlgebraicGeometry.Picard

/-- A morphism to an affine spectrum factors through the spectrum of its global sections
by the structure ring map. -/
lemma isoSpec_hom_comp_specMap_structureRingHom {R : CommRingCat.{u}} {X : Scheme.{u}}
    [IsAffine X] (f : X ⟶ Spec R) :
    X.isoSpec.hom ≫ Spec.map (structureRingHom f) = f := by
  rw [structureRingHom, Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality,
    Category.assoc, Scheme.isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.comp_id]

variable {Y Y₁ : Scheme.{u}}

/-- The relative global sections of the structure sheaf over an affine spectrum are the global
functions with the module structure given by the structure ring map. -/
def relativeGlobalSectionsStructureSheafLinearEquiv {R : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) :
    letI := (structureRingHom f).hom.toAlgebra
    (relativeGlobalSections f).obj (structureSheaf X) ≃ₗ[R] Γ(X, ⊤) :=
  letI := (structureRingHom f).hom.toAlgebra
  { toFun := fun m => m
    invFun := fun m => m
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- For a finite flat morphism of finite presentation with constant degree `d`, the structure
sheaf satisfies the affine sections data of rank `d`. -/
theorem affineSectionsData_structureSheaf (f : Y₁ ⟶ Y) [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] (d : ℕ) (hd : ∀ y : Y, f.finrank y = d) :
    AffineSectionsData f (structureSheaf Y₁) d := by
  intro R x XR p fR h
  have : IsFinite fR := MorphismProperty.of_isPullback h ‹IsFinite f›
  have : Flat fR := MorphismProperty.of_isPullback h ‹Flat f›
  have : LocallyOfFinitePresentation fR :=
    MorphismProperty.of_isPullback h ‹LocallyOfFinitePresentation f›
  have : IsAffine XR := isAffine_of_isAffineHom fR
  let φ := structureRingHom fR
  have hspec : Spec.map φ = XR.isoSpec.inv ≫ fR := by
    rw [← isoSpec_hom_comp_specMap_structureRingHom fR, Iso.inv_hom_id_assoc]
  have : IsFinite (Spec.map φ) := by rw [hspec]; infer_instance
  have : Flat (Spec.map φ) := by rw [hspec]; infer_instance
  have : LocallyOfFinitePresentation (Spec.map φ) := by rw [hspec]; infer_instance
  have hφfin : φ.hom.Finite := (IsFinite.SpecMap_iff φ).mp inferInstance
  have hφflat : φ.hom.Flat := Flat.SpecMap_iff.mp inferInstance
  have hφfp : φ.hom.FinitePresentation :=
    (LocallyOfFinitePresentation.SpecMap_iff φ).mp inferInstance
  let := φ.hom.toAlgebra
  have : Module.Finite R Γ(XR, ⊤) := hφfin
  have : Module.Flat R Γ(XR, ⊤) := hφflat
  have : Algebra.FinitePresentation R Γ(XR, ⊤) := hφfp
  have : Module.FinitePresentation R Γ(XR, ⊤) :=
    Module.FinitePresentation.of_finite_of_finitePresentation R Γ(XR, ⊤)
  have : Module.Projective R Γ(XR, ⊤) := Module.Flat.projective_of_finitePresentation
  let E : (relativeGlobalSections fR).obj ((Scheme.Modules.pullback p).obj (structureSheaf Y₁))
      ≃ₗ[R] Γ(XR, ⊤) :=
    ((relativeGlobalSections fR).mapIso (pullbackUnitIso p)).toLinearEquiv.trans
      (relativeGlobalSectionsStructureSheafLinearEquiv fR)
  have hrank : ∀ q : PrimeSpectrum R, Module.rankAtStalk Γ(XR, ⊤) q = d := by
    intro q
    have h1 : φ.hom.finrank q = Module.rankAtStalk Γ(XR, ⊤) q := rfl
    rw [← h1, ← Scheme.Hom.finrank_SpecMap_eq_finrank hφfin hφflat,
      ← Scheme.Hom.finrank_comp_left_of_isIso XR.isoSpec.hom (Spec.map φ),
      isoSpec_hom_comp_specMap_structureRingHom fR]
    rw [Scheme.Hom.finrank_of_isPullback p fR f x h q]
    exact hd _
  refine ⟨Module.Finite.equiv E.symm, Module.Projective.of_equiv' E.symm, fun q => ?_, ?_⟩
  · rw [Module.rankAtStalk_eq_of_equiv E]
    exact hrank q
  · intro T φ' XT p' fT h'
    have : IsFinite fT := MorphismProperty.of_isPullback h' ‹IsFinite fR›
    have : IsAffine XT := isAffine_of_isAffineHom fT
    have : ((Scheme.Modules.pullback p).obj (structureSheaf Y₁)).IsQuasicoherent :=
      ((LineBundle.pullback p).obj (LineBundle.trivial Y₁)).isQuasicoherent
    exact isIso_scalarSectionsBaseChangeMap_of_isPullback_affine φ' fR fT p' h'.w h' _

/-- Affine sections data of rank `r` give a free chart of rank `r` of the pushforward around
every point, in the form of an isomorphism of the restriction to an open with the free module. -/
theorem exists_freeChart_of_affineSectionsData {S X : Scheme.{u}} {f : X ⟶ S} {M : X.Modules}
    {r : ℕ} (H : AffineSectionsData f M r) (y : S) :
    ∃ V : S.Opens, y ∈ V ∧
      Nonempty ((Scheme.Modules.restrictFunctor V.ι).obj ((Scheme.Modules.pushforward f).obj M) ≅
        SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin r))) := by
  let P := (Scheme.Modules.pushforward f).obj M
  obtain ⟨U, hU, hyU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ (⊤ : S.Opens) from trivial)
  let R := Γ(S, U)
  let x : Spec R ⟶ S := hU.fromSpec
  let t : Spec R := hU.isoSpec.hom ⟨y, hyU⟩
  have hty : x t = y := by
    change (hU.isoSpec.hom ≫ hU.isoSpec.inv ≫ U.ι) ⟨y, hyU⟩ = y
    simp
  let XR := pullback f x
  let pR : XR ⟶ X := pullback.fst f x
  let fR : XR ⟶ Spec R := pullback.snd f x
  have hR : IsPullback pR fR f x := IsPullback.of_hasPullback f x
  let PR := (Scheme.Modules.pushforward fR).obj ((Scheme.Modules.pullback pR).obj M)
  have : PR.IsQuasicoherent := H.isQuasicoherent R x XR pR fR hR
  have hData := H R x XR pR fR hR
  have : Module.Finite R ((moduleSpecΓFunctor (R := R)).obj PR) := hData.1
  have : Module.Projective R ((moduleSpecΓFunctor (R := R)).obj PR) := hData.2.1
  obtain ⟨W, htW, ⟨eW⟩⟩ :=
    exists_freeNeighborhood_of_finite_projective_rankAtStalk PR r hData.2.2.1 t
  let eR : P.restrict x ≅ PR :=
    (Scheme.Modules.restrictFunctorIsoPullback x).app P ≪≫
      openCartesianBaseChangeIso x f fR pR hR M
  let j : W.toScheme ⟶ S := W.ι ≫ x
  let e : P.restrict j ≅
      SheafOfModules.free (R := W.toScheme.ringCatSheaf) (ULift.{u} (Fin r)) :=
    (Scheme.Modules.restrictFunctorComp W.ι x).app P ≪≫
      (Scheme.Modules.restrictFunctor W.ι).mapIso eR ≪≫ eW
  exact ⟨j.opensRange, ⟨⟨t, htW⟩, hty⟩,
    ⟨freeChartOnOpensRange P j (ULift.{u} (Fin r)) e⟩⟩

/-- For a finite flat morphism of finite presentation with constant degree `d`, the pushforward
of the structure sheaf has a free chart of rank `d` around every point. -/
theorem exists_freeChart_pushforward_structureSheaf (f : Y₁ ⟶ Y) [IsFinite f] [Flat f]
    [LocallyOfFinitePresentation f] (d : ℕ) (hd : ∀ y : Y, f.finrank y = d) (y : Y) :
    ∃ V : Y.Opens, y ∈ V ∧
      Nonempty ((Scheme.Modules.restrictFunctor V.ι).obj
          ((Scheme.Modules.pushforward f).obj (structureSheaf Y₁)) ≅
        SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin d))) :=
  exists_freeChart_of_affineSectionsData (affineSectionsData_structureSheaf f d hd) y

/-- Base change of the pushforward of the structure sheaf along a finite flat morphism of finite
presentation and constant degree: for every cartesian square `φ, q₁, q, f`,
`φ_* 𝒪 ≅ q^* f_* 𝒪`. -/
def pushforwardStructureSheafBaseChangeIso {Z Z₁ : Scheme.{u}} (f : Y₁ ⟶ Y) [IsFinite f]
    [Flat f] [LocallyOfFinitePresentation f] (d : ℕ) (hd : ∀ y : Y, f.finrank y = d)
    (q : Z ⟶ Y) (φ : Z₁ ⟶ Z) (q₁ : Z₁ ⟶ Y₁) (hsq : IsPullback φ q₁ q f) :
    (Scheme.Modules.pushforward φ).obj (structureSheaf Z₁) ≅
      (Scheme.Modules.pullback q).obj ((Scheme.Modules.pushforward f).obj (structureSheaf Y₁)) :=
  have := (affineSectionsData_structureSheaf f d hd).isIso_baseChange q φ q₁ hsq.flip
  (Scheme.Modules.pushforward φ).mapIso (pullbackUnitIso q₁).symm ≪≫
    (asIso (pushforwardBaseChange q f φ q₁ hsq.flip.w (structureSheaf Y₁))).symm

end Langlands.AlgebraicGeometry.Modules.DerivedSections
