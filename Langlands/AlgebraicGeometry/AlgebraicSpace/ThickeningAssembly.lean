import Langlands.AlgebraicGeometry.AlgebraicSpace.OpenChartGluingProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.OpenFamilyLiftingProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteSurjectiveAffineDescentStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.SchemenessOfThickeningStatement

/-! # Assembly helpers for unrestricted thickenings

The input interfaces abbreviate the published propositions.
The final corollary uses the lifting proof and takes affine descent as a hypothesis;
`SchemenessOfThickeningProof` discharges it with the published affine-descent theorem.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.ThickeningAssembly

abbrev openMorphism {S : Scheme.{u}} : MorphismProperty (Presheaf S) :=
  @IsOpenImmersion S

local instance {S : Scheme.{u}} : (@openMorphism S).RespectsIso := by
  change ((SliceOpenGluing.openProperty S).relative (schemeYoneda S)).RespectsIso
  infer_instance

abbrev finiteMorphism {S : Scheme.{u}} : MorphismProperty (Presheaf S) :=
  @IsFinite S

abbrev AffineRepresentation {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop :=
  IsRepresentedByAffineScheme X

/-- The published family-lifting proposition. -/
abbrev OpenFamilyLiftingInput : Prop := OpenFamilyLiftingStatement.{u}

/-- The published finite-surjective affine-descent proposition. -/
abbrev FiniteSurjectiveAffineDescentInput : Prop :=
  FiniteSurjectiveAffineDescentStatement.{u}

variable {S : Scheme.{u}}

lemma thickening_finite {F G : Presheaf S} {f : F ⟶ G} (hf : IsThickening f) :
    finiteMorphism f :=
  hf.finite

/-- The actual affine open charts of a represented scheme, retaining its base map. -/
def affineCharts (W : Over S) (k : W.left.affineCover.I₀) : Over S :=
  Over.mk (W.left.affineCover.f k ≫ W.hom)

def affineChartMap (W : Over S) (k : W.left.affineCover.I₀) :
    affineCharts W k ⟶ W :=
  Over.homMk (W.left.affineCover.f k)

instance (W : Over S) (k : W.left.affineCover.I₀) :
    _root_.AlgebraicGeometry.IsAffine (affineCharts W k).left :=
  Scheme.isAffine_affineCover W.left k

lemma affineChartMap_open (W : Over S) (k : W.left.affineCover.I₀) :
    openMorphism ((schemeYoneda S).map (affineChartMap W k)) := by
  let : (SliceOpenGluing.openProperty S).IsStableUnderBaseChange := {
    of_isPullback := fun sq hg ↦
      MorphismProperty.of_isPullback (P := @_root_.AlgebraicGeometry.IsOpenImmersion.{u})
        (sq.map (Over.forget S)) hg }
  apply MorphismProperty.relative_map
  exact inferInstanceAs
    (_root_.AlgebraicGeometry.IsOpenImmersion (W.left.affineCover.f k))

lemma affineChartMap_cover (W : Over S) :
    CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S)
      (Sigma.desc (fun k ↦ (schemeYoneda S).map (affineChartMap W k))) := by
  apply (GrothendieckTopology.ofArrows_mem_iff_isLocallySurjective_sigmaDesc_uliftYoneda_map
    (fppfTopology S) (affineChartMap W)).mp
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact (Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage) _
    W.left.affineCover.mem_grothendieckTopology

/-- A represented space has actual affine open charts with the required local coverage. -/
theorem exists_affine_open_cover (X : AlgebraicSpace S) (hX : IsRepresentedByScheme X) :
    ∃ (I : Type u) (U : I → Over S)
      (a : ∀ k, (schemeYoneda S).obj (U k) ⟶ X.presheaf),
      (∀ k, _root_.AlgebraicGeometry.IsAffine (U k).left) ∧
      (∀ k, openMorphism (a k)) ∧
      CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S) (Sigma.desc a) := by
  obtain ⟨W, ⟨e⟩⟩ := hX
  let a := fun k ↦ (schemeYoneda S).map (affineChartMap W k) ≫ e.hom
  refine ⟨W.left.affineCover.I₀, affineCharts W, a, fun k ↦ inferInstance, ?_, ?_⟩
  · intro k
    exact MorphismProperty.RespectsIso.postcomp openMorphism e.hom _
      (affineChartMap_open W k)
  · let := affineChartMap_cover W
    have h : Sigma.desc (fun k ↦ (schemeYoneda S).map (affineChartMap W k)) ≫ e.hom =
        Sigma.desc a := by
      apply Sigma.hom_ext
      intro k
      simp [a]
    rw [← h]
    infer_instance

/-- Replacing every chart by an isomorphic presheaf preserves local coverage. -/
lemma coproduct_cover_of_isos {I : Type u} {F G : I → Presheaf S} {H : Presheaf S}
    (a : ∀ k, G k ⟶ H) (e : ∀ k, F k ≅ G k)
    [CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S) (Sigma.desc a)] :
    CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S)
      (Sigma.desc (fun k ↦ (e k).hom ≫ a k)) := by
  have h : Limits.Sigma.map (fun k ↦ (e k).hom) ≫ Sigma.desc a =
      Sigma.desc (fun k ↦ (e k).hom ≫ a k) := by
    apply Sigma.hom_ext
    intro k
    simp
  rw [← h]
  infer_instance

/-- Conditional assembly from the two exact published input propositions. -/
theorem schemeness_of_inputs
    (hLift : OpenFamilyLiftingInput.{u})
    (hDescent : FiniteSurjectiveAffineDescentInput.{u}) :
    SchemenessOfThickeningStatement.{u} := by
  intro S X Y i hi hX
  obtain ⟨I, U, a, hU, ha, hcover⟩ := exists_affine_open_cover X hX
  obtain ⟨V, j, c, hj, hc, _, hVcover⟩ := hLift S X Y i hi I U a ha hcover
  have hAff : ∀ k, AffineRepresentation (V k) := fun k ↦
    hDescent S ((schemeToSpace S).obj (U k)) (V k) (c k)
      (thickening_finite (hc k)) (hc k).surjective
      ⟨U k, hU k, ⟨Iso.refl _⟩⟩
  choose W _ he using hAff
  let e := fun k ↦ Classical.choice (he k)
  let b := fun k ↦ (e k).hom ≫ hom (j k)
  have hb : ∀ k, openMorphism (b k) := fun k ↦
    MorphismProperty.RespectsIso.precomp openMorphism (e k).hom _ (hj k)
  let := hVcover
  let := coproduct_cover_of_isos (fun k ↦ hom (j k)) e
  exact openChartGluing S Y.toSheaf I W b hb (by infer_instance)

/-- The lifting and gluing proofs reduce schemeness to finite-surjective affine descent. -/
theorem schemeness_of_finite_descent
    (hDescent : FiniteSurjectiveAffineDescentInput.{u}) :
    SchemenessOfThickeningStatement.{u} :=
  schemeness_of_inputs openFamilyLifting hDescent

end Langlands.AlgebraicGeometry.AlgebraicSpace.ThickeningAssembly
