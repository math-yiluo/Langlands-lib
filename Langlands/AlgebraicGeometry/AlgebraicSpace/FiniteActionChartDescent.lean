import Langlands.AlgebraicGeometry.AlgebraicSpace.CoproductChart
import Langlands.AlgebraicGeometry.AlgebraicSpace.DiagonalEqualizer
import Langlands.AlgebraicGeometry.AlgebraicSpace.FppfQuotientRepresentability
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTuplePresentation
import Langlands.AlgebraicGeometry.FiniteFreeSchemeActionQuotient

/-! # Descent of invariant scheme charts along quotients by finite free actions

Let `A` be an affine scheme over `S` with a finite free action of `G` over `S`, and let
`q : A → M` be an affine quotient. A map `t : h_A → X` to an fppf sheaf that is invariant
under the action descends uniquely to `h_M → X`. If `t` is étale and `X` has representable
diagonal, then the descended map is étale.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

open CoproductChart in
/-- Two sections of an fppf sheaf over a scheme coproduct agree when they agree on every
component. -/
theorem sheaf_ext_sigmaOver {X : Presheaf S} (hX : Presheaf.IsSheaf (fppfTopology S) X)
    {ι : Type u} (V : ι → Over S) {x y : X.obj (op (sigmaOver V))}
    (h : ∀ i, X.map (sigmaOverι V i).op x = X.map (sigmaOverι V i).op y) : x = y := by
  have hcov : Sieve.ofArrows V (sigmaOverι V) ∈ fppfTopology S (sigmaOver V) := by
    let 𝒰 := Scheme.Cover.mkOfCovers (P := @_root_.AlgebraicGeometry.IsOpenImmersion.{u}) ι
      (fun i => (V i).left) (fun i => (sigmaOverι V i).left) (fun z => by
        obtain ⟨⟨i, y⟩, hy⟩ := (sigmaMk (fun i => (V i).left)).surjective z
        refine ⟨i, y, ?_⟩
        change Sigma.ι (fun i => (V i).left) i y = z
        rw [← sigmaMk_mk]
        exact hy)
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact (Precoverage.toGrothendieck_mono
      Scheme.zariskiPrecoverage_le_fppfPrecoverage) _ 𝒰.mem_grothendieckTopology
  have hsh := (isSheaf_iff_isSheaf_of_type (fppfTopology S) X).mp hX _ hcov
  apply hsh.isSeparatedFor.ext
  rintro T f ⟨W, g, _, ⟨i⟩, rfl⟩
  rw [op_comp, X.map_comp, types_comp_apply, types_comp_apply, h i]

/-- Descent of a map to an fppf sheaf along a represented fppf cover, assuming that the map
identifies points with equal images. -/
theorem exists_desc_of_fppf_cover {X : FppfSheaf S} {A M : Over S} (q : A ⟶ M)
    [Flat q.left] [LocallyOfFinitePresentation q.left] [Surjective q.left]
    (t : (schemeYoneda S).obj A ⟶ X.obj)
    (ht : ∀ (T : Over S) (w₁ w₂ : T ⟶ A), w₁ ≫ q = w₂ ≫ q →
      t.app (op T) ⟨w₁⟩ = t.app (op T) ⟨w₂⟩) :
    ∃ t' : (schemeYoneda S).obj M ⟶ X.obj, (schemeYoneda S).map q ≫ t' = t := by
  let a' : (schemeSheaf S).obj A ⟶ X := ObjectProperty.homMk t
  let q' : (schemeSheaf S).obj A ⟶ (schemeSheaf S).obj M := (schemeSheaf S).map q
  have : Sheaf.IsLocallySurjective q' := isLocallySurjective_schemeYoneda_map q
  have : Epi q' := inferInstance
  have : IsRegularEpi q' := IsRegularEpiCategory.regularEpiOfEpi q'
  have hqa : ∀ {Z : FppfSheaf S} (g₁ g₂ : Z ⟶ (schemeSheaf S).obj A),
      g₁ ≫ q' = g₂ ≫ q' → g₁ ≫ a' = g₂ ≫ a' := by
    intro Z g₁ g₂ h
    apply ObjectProperty.hom_ext
    ext T x
    apply ht T.unop (g₁.hom.app T x).down (g₂.hom.app T x).down
    exact congrArg ULift.down
      (ConcreteCategory.congr_hom (NatTrans.congr_app
        ((sheafToPresheaf (fppfTopology S) (Type (u + 1))).congr_map h) T) x)
  exact ⟨(sheafToPresheaf (fppfTopology S) (Type (u + 1))).map (EffectiveEpi.desc q' a' hqa),
    (sheafToPresheaf (fppfTopology S) (Type (u + 1))).congr_map (EffectiveEpi.fac q' a' hqa)⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- A map from a scheme to a presheaf with representable diagonal is étale if its composite
with a finite étale surjective scheme map is étale. -/
theorem isEtale_of_finiteEtale_comp {X : Presheaf S} (hX : HasRepresentableDiagonal X)
    {A M : Over S} (q : A ⟶ M) [IsFinite q.left] [Etale q.left] [Surjective q.left]
    (t : (schemeYoneda S).obj M ⟶ X) (ht : IsEtale ((schemeYoneda S).map q ≫ t)) :
    IsEtale t := by
  refine ⟨Functor.relativelyRepresentable.of_diag hX t, ?_⟩
  intro T W g b p h
  obtain ⟨β, rfl⟩ := (schemeYoneda S).map_surjective b
  have hpb := IsPullback.of_hasPullback β q
  have hpaste := (hpb.flip.map (schemeYoneda S)).paste_vert h
  have he : Etale (pullback.fst β q ≫ p).left :=
    ht.projection g _ _ (by simpa only [Functor.map_comp] using hpaste)
  have hbc : IsPullback (pullback.fst β q).left (pullback.snd β q).left β.left q.left :=
    hpb.map (Over.forget S)
  have : IsFinite (pullback.fst β q).left := MorphismProperty.of_isPullback hbc.flip ‹_›
  have : Etale (pullback.fst β q).left := MorphismProperty.of_isPullback hbc.flip ‹_›
  have : Surjective (pullback.fst β q).left := MorphismProperty.of_isPullback hbc.flip ‹_›
  have : Etale ((pullback.fst β q).left ≫ p.left) := he
  exact etale_of_finiteEtale_surjective_comp (pullback.fst β q).left p.left

namespace FiniteActionChart

variable {G : Type u} [Group G] {A : Over S} (α : FiniteFreeSchemeAction G A.left)
  (hα : ∀ g, (α.act g).hom ≫ A.hom = A.hom)

/-- An element of the group acting by a morphism over the base. -/
def actOver (g : G) : A ⟶ A := Over.homMk (α.act g).hom (hα g)

@[simp] theorem actOver_left (g : G) : (actOver α hα g).left = (α.act g).hom := rfl

variable (Q : α.AffineQuotient)

/-- The quotient, as a scheme over the base. -/
def quotientOver : Over S := Over.mk (Q.desc A.hom hα)

/-- The quotient map, as a morphism over the base. -/
def quotientMapOver : A ⟶ quotientOver α hα Q := Over.homMk Q.map (Q.map_desc A.hom hα)

@[simp] theorem quotientMapOver_left : (quotientMapOver α hα Q).left = Q.map := rfl

instance : IsAffine (quotientOver α hα Q).left := Q.isAffine

instance : IsFinite (quotientMapOver α hα Q).left := Q.finite

instance : Etale (quotientMapOver α hα Q).left := Q.etale

instance : Surjective (quotientMapOver α hα Q).left := Q.surjective

/-- The element of `X(A)` classifying a map from the functor of points of `A` is invariant
when the map is. -/
theorem map_actOver_uliftYonedaEquiv {X : Presheaf S} (t : (schemeYoneda S).obj A ⟶ X)
    (ht : ∀ g, (schemeYoneda S).map (actOver α hα g) ≫ t = t) (g : G) :
    X.map (actOver α hα g).op (uliftYonedaEquiv t) = uliftYonedaEquiv t := by
  rw [uliftYonedaEquiv_naturality]
  exact congrArg _ (ht g)

open CoproductChart in
/-- An invariant map from `A` to an fppf sheaf identifies points of `A` with equal images in
the quotient. -/
theorem app_eq_of_map_eq {X : Presheaf S} (hX : Presheaf.IsSheaf (fppfTopology S) X)
    (t : (schemeYoneda S).obj A ⟶ X)
    (ht : ∀ g, (schemeYoneda S).map (actOver α hα g) ≫ t = t)
    {T : Over S} (w₁ w₂ : T ⟶ A) (h : w₁.left ≫ Q.map = w₂.left ≫ Q.map) :
    t.app (op T) ⟨w₁⟩ = t.app (op T) ⟨w₂⟩ := by
  let r : T.left ⟶ α.relationScheme := Q.isPullback.lift w₁.left w₂.left h
  have hsrc : (sigmaOver (fun _ : G => A)).hom = α.source ≫ A.hom := by
    apply Sigma.hom_ext
    intro g
    change Sigma.ι _ g ≫ Sigma.desc (fun _ => A.hom) = _
    rw [Sigma.ι_comp_desc]
    exact (α.ι_source_assoc g A.hom).symm
  have hr : r ≫ (sigmaOver (fun _ : G => A)).hom = T.hom := by
    rw [hsrc, ← Category.assoc, Q.isPullback.lift_snd]
    exact Over.w w₂
  let r' : T ⟶ sigmaOver (fun _ : G => A) := Over.homMk r hr
  have h₁ : r' ≫ sigmaOverDesc (fun _ : G => A) (actOver α hα) = w₁ :=
    Over.OverMorphism.ext (Q.isPullback.lift_fst _ _ _)
  have h₂ : r' ≫ sigmaOverDesc (fun _ : G => A) (fun _ => 𝟙 A) = w₂ :=
    Over.OverMorphism.ext (Q.isPullback.lift_snd _ _ _)
  have key : X.map (sigmaOverDesc (fun _ : G => A) (actOver α hα)).op (uliftYonedaEquiv t) =
      X.map (sigmaOverDesc (fun _ : G => A) (fun _ => 𝟙 A)).op (uliftYonedaEquiv t) := by
    apply sheaf_ext_sigmaOver hX
    intro g
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, ι_desc,
      ι_desc, map_actOver_uliftYonedaEquiv α hα t ht g, op_id, Functor.map_id_apply]
  rw [schemeYoneda_app_up, schemeYoneda_app_up, ← h₁, ← h₂, op_comp, op_comp,
    Functor.map_comp_apply, Functor.map_comp_apply, key]

/-- An invariant map from `A` to an fppf sheaf descends to the quotient. -/
theorem exists_desc (X : FppfSheaf S) (t : (schemeYoneda S).obj A ⟶ X.obj)
    (ht : ∀ g, (schemeYoneda S).map (actOver α hα g) ≫ t = t) :
    ∃ t' : (schemeYoneda S).obj (quotientOver α hα Q) ⟶ X.obj,
      (schemeYoneda S).map (quotientMapOver α hα Q) ≫ t' = t :=
  exists_desc_of_fppf_cover (quotientMapOver α hα Q) t fun _ w₁ w₂ h =>
    app_eq_of_map_eq α hα Q X.property t ht w₁ w₂ (by
      have h' := congrArg CommaMorphism.left h
      exact h')

end FiniteActionChart

end Langlands.AlgebraicGeometry.AlgebraicSpace
