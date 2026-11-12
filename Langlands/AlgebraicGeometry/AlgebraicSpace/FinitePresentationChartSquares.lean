import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitFlatnessDimensionDescentStatement
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationPresentation
import Mathlib.AlgebraicGeometry.Cover.Sigma
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-! # Affine finite-presentation chart squares for morphisms of spaces -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- A compact scheme has a surjective etale cover by one affine scheme. -/
theorem exists_affine_etale_surjective_cover (W : Scheme.{u}) [CompactSpace W] :
    ∃ (A : Scheme.{u}) (_ : IsAffine A) (p : A ⟶ W), Etale p ∧ Surjective p := by
  let C := W.affineCover.finiteSubcover
  let p : (∐ C.X) ⟶ W := Sigma.desc C.f
  have : IsZariskiLocalAtSource @Etale.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale.{u})
  have hp : Etale p := IsZariskiLocalAtSource.sigmaDesc (fun _ => inferInstance)
  have hs : Surjective p := by
    constructor
    intro w
    obtain ⟨i, x, rfl⟩ := C.exists_eq w
    exact ⟨Sigma.ι C.X i x, by simp [p, ← Scheme.Hom.comp_apply]⟩
  exact ⟨∐ C.X, inferInstance, p, hp, hs⟩

variable {S : Scheme.{u}}

/-- Finite-presentation atlas data over an affine base admit an affine atlas
whose structure map is still locally of finite presentation. -/
theorem exists_affine_finitePresentation_atlas [IsAffine S] (X : AlgebraicSpace S)
    (hX : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X) :
    ∃ (U : Over S) (a : (schemeYoneda S).obj U ⟶ X.presheaf),
      IsAffine U.left ∧ IsEtale a ∧ IsSurjective a ∧ LocallyOfFinitePresentation U.hom := by
  obtain ⟨W, a, ha, hs, hl, hq⟩ := hX
  have : QuasiCompact W.hom := hq
  have : LocallyOfFinitePresentation W.hom := hl
  have : CompactSpace W.left := QuasiCompact.compactSpace_of_compactSpace W.hom
  obtain ⟨A, hA, p, hp, hps⟩ := exists_affine_etale_surjective_cover W.left
  have : IsAffine A := hA
  have : Etale p := hp
  let U : Over S := Over.mk (p ≫ W.hom)
  let j : U ⟶ W := Over.homMk p
  have hj : IsSurjective ((schemeYoneda S).map j) := by
    have : (MorphismProperty.inverseImage (@Surjective.{u})
        (Over.forget S)).IsStableUnderBaseChange := isStableUnderBaseChange_inverseImage_forget
    exact MorphismProperty.relative_map (P := MorphismProperty.inverseImage
      (@Surjective.{u}) (Over.forget S)) hps
  refine ⟨U, (schemeYoneda S).map j ≫ a, hA, (isEtale_map j hp).comp ha,
    ?_, inferInstanceAs (LocallyOfFinitePresentation (p ≫ W.hom))⟩
  exact MorphismProperty.comp_mem (W := (MorphismProperty.inverseImage (@Surjective.{u})
    (Over.forget S)).relative (schemeYoneda S)) _ _ hj hs

private theorem diagonal_square_of_pullback
    {C : Type*} [Category C] [HasBinaryProducts C] {T U V X : C}
    {p : T ⟶ U} {q : T ⟶ V} {a : U ⟶ X} {b : V ⟶ X}
    (h : IsPullback p q a b) :
    IsPullback (p ≫ a) (prod.lift p q) (diag X) (prod.map a b) := by
  have hw : (p ≫ a) ≫ diag X = prod.lift p q ≫ prod.map a b := by
    apply prod.hom_ext <;> simp [h.w]
  apply IsPullback.of_isLimit (c := PullbackCone.mk _ _ hw)
  refine PullbackCone.IsLimit.mk _ (fun s => h.lift
    (s.snd ≫ prod.fst) (s.snd ≫ prod.snd) ?_) ?_ ?_ ?_
  · have h₁ := congrArg (fun k => k ≫ prod.fst) s.condition
    have h₂ := congrArg (fun k => k ≫ prod.snd) s.condition
    simp only [Category.assoc, prod.map_fst, prod.map_snd, diag, prod.lift_fst,
      prod.lift_snd, Category.comp_id] at h₁ h₂
    simpa only [Category.assoc] using h₁.symm.trans h₂
  · intro s
    simp only [← Category.assoc, h.lift_fst]
    have h₁ := congrArg (fun k => k ≫ prod.fst) s.condition
    simpa using h₁.symm
  · intro s
    apply prod.hom_ext <;> simp
  · intro s m hm₁ hm₂
    apply h.hom_ext
    · simpa using congrArg (fun k => k ≫ prod.fst) hm₂
    · simpa using congrArg (fun k => k ≫ prod.snd) hm₂

/-- Pulling back two scheme charts of a space pulls back its diagonal to
their pairing into the product over the base. -/
theorem relative_diagonal_property_chart_pairing
    (P : MorphismProperty Scheme.{u}) {X : AlgebraicSpace S}
    (hX : (MorphismProperty.inverseImage P (Over.forget S)).relative
      (schemeYoneda S) (diag X.presheaf))
    {T U V : Over S} (p : T ⟶ U) (q : T ⟶ V)
    (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    (b : (schemeYoneda S).obj V ⟶ X.presheaf)
    (h : IsPullback ((schemeYoneda S).map p) ((schemeYoneda S).map q) a b) :
    P (prod.lift p q).left := by
  let F := schemeYoneda S
  let m : T ⟶ U ⨯ V := prod.lift p q
  let e := prodComparison F U V
  have he : F.map m ≫ e = prod.lift (F.map p) (F.map q) := by
    apply prod.hom_ext <;> simp [e, prodComparison, m, ← F.map_comp]
  have h₁ : IsPullback (𝟙 (F.obj T)) (F.map m)
      (prod.lift (F.map p) (F.map q)) e :=
    IsPullback.of_horiz_isIso ⟨by simpa using he.symm⟩
  have h₂ := diagonal_square_of_pullback h
  change P m.left
  exact hX.2 (e ≫ prod.map a b) (F.map p ≫ a) m (by
      simpa only [Category.id_comp] using h₁.paste_horiz h₂)

/-- Over an affine base, every morphism between spaces with finite-presentation
atlases and quasi-separated target has a commuting chart square with affine
source and target schemes, both locally of finite presentation over the base. -/
theorem exists_affine_finitePresentation_chart_square [IsAffine S]
    {X Y : AlgebraicSpace S}
    (hX : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X)
    (hY : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) Y)
    (hYqs : IsQuasiSeparated Y) (f : X ⟶ Y) :
    ∃ (W V : Over S) (a : (schemeYoneda S).obj W ⟶ X.presheaf)
      (b : (schemeYoneda S).obj V ⟶ Y.presheaf) (φ : W ⟶ V),
      IsAffine W.left ∧ IsAffine V.left ∧ IsEtale a ∧ IsSurjective a ∧
      IsEtale b ∧ IsSurjective b ∧ LocallyOfFinitePresentation W.hom ∧
      LocallyOfFinitePresentation V.hom ∧
      a ≫ hom f = (schemeYoneda S).map φ ≫ b := by
  obtain ⟨U, a, hUa, ha, has, hUl⟩ := exists_affine_finitePresentation_atlas X hX
  obtain ⟨V, b, hVa, hb, hbs, hVl⟩ := exists_affine_finitePresentation_atlas Y hY
  have : IsAffine U.left := hUa
  have : IsAffine V.left := hVa
  have : LocallyOfFinitePresentation U.hom := hUl
  let F := schemeYoneda S
  let T := hb.representable.pullback (a ≫ hom f)
  let q : T ⟶ V := Functor.relativelyRepresentable.fst' hb.representable (a ≫ hom f)
  let p : T ⟶ U := hb.representable.snd (a ≫ hom f)
  have hT : IsPullback (F.map p) (F.map q) (a ≫ hom f) b :=
    (Functor.relativelyRepresentable.isPullback' hb.representable (a ≫ hom f)).flip
  have hp : Etale p.left := hb.projection (a ≫ hom f) (F.map q) p hT.flip
  have hps : Surjective p.left := hbs.projection (a ≫ hom f) (F.map q) p hT.flip
  have : Etale p.left := hp
  have : LocallyOfFinitePresentation T.hom := by
    rw [← Over.w p]
    infer_instance
  have : IsAffine (U ⨯ V).left := by
    exact IsAffine.of_isIso (Over.prodLeftIsoPullback U V).hom
  have : QuasiCompact (prod.lift p q).left :=
    relative_diagonal_property_chart_pairing @QuasiCompact hYqs p q (a ≫ hom f) b hT
  have : CompactSpace T.left :=
    QuasiCompact.compactSpace_of_compactSpace (prod.lift p q).left
  have : QuasiCompact T.hom := inferInstance
  obtain ⟨W, aW, hWa, haW, hsW, hWl⟩ := exists_affine_finitePresentation_atlas
    ((schemeToSpace S).obj T) (HasAtlasProperty.of_scheme T ⟨inferInstance, inferInstance⟩)
  obtain ⟨j, hj⟩ := F.map_surjective aW
  have hjE : Etale j.left := MorphismProperty.of_relative_map
    (P := MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S)) (hj ▸ haW)
  have hjS : Surjective j.left := MorphismProperty.of_relative_map
    (P := MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)) (hj ▸ hsW)
  have : Etale j.left := hjE
  have : Surjective j.left := hjS
  have : Surjective p.left := hps
  have hja : IsSurjective (F.map (j ≫ p)) := by
    have : (MorphismProperty.inverseImage (@Surjective.{u})
        (Over.forget S)).IsStableUnderBaseChange := isStableUnderBaseChange_inverseImage_forget
    exact MorphismProperty.relative_map (P := MorphismProperty.inverseImage
      (@Surjective.{u}) (Over.forget S)) (inferInstanceAs (Surjective (j.left ≫ p.left)))
  refine ⟨W, V, F.map (j ≫ p) ≫ a, b, j ≫ q, hWa, hVa,
    (isEtale_map (j ≫ p) (inferInstanceAs (Etale (j.left ≫ p.left)))).comp ha,
    ?_, hb, hbs, hWl, hVl, ?_⟩
  · exact MorphismProperty.comp_mem (W := (MorphismProperty.inverseImage (@Surjective.{u})
      (Over.forget S)).relative F) _ _ hja has
  · simpa only [Functor.map_comp, Category.assoc] using congrArg (fun k => F.map j ≫ k) hT.w

/-- Fixed affine finite-presentation chart squares for all morphisms covered
by the finite-presentation atlas hypotheses over an affine base. -/
def FinitePresentationChartSquaresStatement : Prop :=
  ∀ (S : Scheme.{u}) [IsAffine S] (X Y : AlgebraicSpace S),
    HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X →
    HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) Y →
    IsQuasiSeparated Y → ∀ f : X ⟶ Y,
    ∃ (W V : Over S) (a : (schemeYoneda S).obj W ⟶ X.presheaf)
      (b : (schemeYoneda S).obj V ⟶ Y.presheaf) (φ : W ⟶ V),
      IsAffine W.left ∧ IsAffine V.left ∧ IsEtale a ∧ IsSurjective a ∧
      IsEtale b ∧ IsSurjective b ∧ LocallyOfFinitePresentation W.hom ∧
      LocallyOfFinitePresentation V.hom ∧
      a ≫ hom f = (schemeYoneda S).map φ ≫ b

/-- The fixed-chart existence theorem with all scheme and space quantifiers. -/
theorem finitePresentationChartSquares : FinitePresentationChartSquaresStatement.{u} := by
  intro S _ X Y hX hY hYqs f
  exact exists_affine_finitePresentation_chart_square hX hY hYqs f

end Langlands.AlgebraicGeometry.AlgebraicSpace
