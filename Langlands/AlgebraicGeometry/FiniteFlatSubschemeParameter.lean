import Langlands.AbelianScheme.RelativeEndomorphismRepresentabilityOfPieces
import Langlands.AlgebraicGeometry.HilbertSchemeUniversalFamilyProof
import Langlands.AlgebraicGeometry.Picard.ProperAmpleClosedImmersionBySectionsStatement

/-! # Flat closed subschemes of a finite flat scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.FiniteFlatSubschemeParameter

variable {S : Scheme.{u}} (X : Over S) {T P : Over S}

/-- The comparison of the two pullbacks of `X` along a map of tests. -/
def testMap (g : T ⟶ P) :
    ((Over.pullback T.hom).obj X).left ⟶ ((Over.pullback P.hom).obj X).left :=
  pullback.map X.hom T.hom X.hom P.hom (𝟙 _) g.left (𝟙 _) (by simp) (by simp)

@[reassoc (attr := simp)]
theorem testMap_fst (g : T ⟶ P) :
    testMap X g ≫ pullback.fst X.hom P.hom = pullback.fst X.hom T.hom := by
  simp [testMap, Over.pullback_obj_left]

@[reassoc (attr := simp)]
theorem testMap_snd (g : T ⟶ P) :
    testMap X g ≫ pullback.snd X.hom P.hom = pullback.snd X.hom T.hom ≫ g.left := by
  dsimp [testMap]
  simp

/-- The test comparison is a pullback of the map of tests. -/
theorem testMap_isPullback (g : T ⟶ P) :
    IsPullback (testMap X g) (pullback.snd X.hom T.hom) (pullback.snd X.hom P.hom) g.left := by
  refine IsPullback.of_right (h₁₂ := pullback.fst X.hom P.hom) (v₁₃ := X.hom)
    (h₂₂ := P.hom) ?_ (testMap_snd X g) (IsPullback.of_hasPullback X.hom P.hom)
  rw [testMap_fst, Over.w g]
  exact IsPullback.of_hasPullback X.hom T.hom

@[simp]
theorem testMap_id (T : Over S) : testMap X (𝟙 T) = 𝟙 _ := by
  apply pullback.hom_ext <;> simp

@[reassoc]
theorem testMap_comp {U : Over S} (f : U ⟶ T) (g : T ⟶ P) :
    testMap X (f ≫ g) = testMap X f ≫ testMap X g := by
  apply pullback.hom_ext <;> simp

/-- A universal finitely presented flat closed family in a finite scheme. -/
structure Parameter where
  base : Over S
  separated : IsSeparated base.hom
  locallyOfFinitePresentation : LocallyOfFinitePresentation base.hom
  ideal : ((Over.pullback base.hom).obj X).left.IdealSheafData
  flat : Flat (ideal.subschemeι ≫ pullback.snd X.hom base.hom)
  finitelyPresented : LocallyOfFinitePresentation (ideal.subschemeι ≫ pullback.snd X.hom base.hom)
  classifies : ∀ (T : Over S) (I : ((Over.pullback T.hom).obj X).left.IdealSheafData),
    Flat (I.subschemeι ≫ pullback.snd X.hom T.hom) →
    LocallyOfFinitePresentation (I.subschemeι ≫ pullback.snd X.hom T.hom) →
    ∃! g : T ⟶ base, ideal.comap (testMap X g) = I

/-- The actual classified ideal over the given test point. -/
def Parameter.eval (D : Parameter X) (g : T ⟶ D.base) :
    ((Over.pullback T.hom).obj X).left.IdealSheafData :=
  D.ideal.comap (testMap X g)

@[simp]
theorem Parameter.eval_id (D : Parameter X) : D.eval X (𝟙 D.base) = D.ideal := by
  simp [Parameter.eval]

@[simp]
theorem Parameter.eval_comp (D : Parameter X) {U : Over S} (f : U ⟶ T) (g : T ⟶ D.base) :
    D.eval X (f ≫ g) = (D.eval X g).comap (testMap X f) := by
  simp [Parameter.eval, testMap_comp, Scheme.IdealSheafData.comap_comp]

/-- The composite of the closed family inclusion with the finite projection is finite. -/
theorem Parameter.isFinite (D : Parameter X) [IsFinite X.hom] :
    IsFinite (D.ideal.subschemeι ≫ pullback.snd X.hom D.base.hom) := inferInstance

/-- Finite flat, locally finitely presented schemes over an affine base admit a
separated, locally finitely presented parameter for their flat closed subschemes. -/
def FiniteFlatSubschemeParameterStatement : Prop :=
  ∀ (R : CommRingCat.{u}) (X : Over (Spec R)),
    IsFinite X.hom → Flat X.hom → LocallyOfFinitePresentation X.hom → Nonempty (Parameter X)

/-- A finite scheme embeds in finite projective space. Its Hilbert scheme supplies
precisely the flat, locally finitely presented closed subschemes on all tests. -/
theorem finiteFlatSubschemeParameter : FiniteFlatSubschemeParameterStatement.{u} := by
  intro R X hfin hflat hfp
  let := hfin
  obtain ⟨L, hL, hc⟩ := (Picard.exists_closedImmersionBySections_iff_isHProjective X.hom).mpr
    (Langlands.AbelianScheme.isHProjective_of_isFinite X.hom)
  obtain ⟨H, p, W, hp, hs, h, -⟩ := HilbertSchemeUniversalFamily.hilbertSchemeUniversalFamily
    R X.hom L hflat hfp hL hc
  let M : Over (Spec R) := Over.mk p
  have hM := (h H p).1 (𝟙 H) (Category.id_comp p)
  change Flat ((W.comap (testMap X (𝟙 M))).subschemeι ≫ pullback.snd X.hom p) ∧
    LocallyOfFinitePresentation ((W.comap (testMap X (𝟙 M))).subschemeι ≫ pullback.snd X.hom p) at hM
  have hid : testMap X (𝟙 M) = 𝟙 (pullback X.hom p) := testMap_id X M
  rw [hid, Scheme.IdealSheafData.comap_id W] at hM
  refine ⟨⟨M, hs, hp, W, hM.1, hM.2, ?_⟩⟩
  intro T I hI hIfp
  obtain ⟨g, ⟨hg, he⟩, hg'⟩ := (h T.left T.hom).2 I hI hIfp
  let g₀ : T ⟶ M := Over.homMk g hg
  refine ⟨g₀, he, fun g₁ he₁ => ?_⟩
  apply Over.OverMorphism.ext
  exact hg' g₁.left ⟨Over.w g₁, he₁⟩

end Langlands.AlgebraicGeometry.FiniteFlatSubschemeParameter
