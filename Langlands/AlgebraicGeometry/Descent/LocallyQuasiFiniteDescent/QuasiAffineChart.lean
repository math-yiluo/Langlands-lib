import Langlands.AlgebraicGeometry.Descent.LocallyQuasiFiniteDescent.Core
import Langlands.AlgebraicGeometry.Descent.LocallyQuasiFiniteDescent.FlatImage
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Quasi-affine open charts of a locally quasi-finite base change -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.LocallyQuasiFiniteDescent

open AlgebraicSpace AlgebraicSpace.OpenSubfunctorImages

/-- Zariski's main theorem, quasi-affine form: a quasi-compact scheme which is separated,
locally quasi-finite and locally of finite type over an affine scheme is quasi-affine. -/
theorem isQuasiAffine_of_locallyQuasiFinite {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y]
    [CompactSpace X] [IsSeparated f] [LocallyQuasiFinite f] [LocallyOfFiniteType f] :
    X.IsQuasiAffine := by
  have : IsAffine f.normalization := isAffine_of_isAffineHom f.fromNormalization
  exact Scheme.IsQuasiAffine.of_isImmersion f.toNormalization

variable {S : Scheme.{u}}

/-- An open subscheme of a scheme over `S`, as a scheme over `S`. -/
abbrev openOver (X : Over S) (U : X.left.Opens) : Over S :=
  Over.mk (U.ι ≫ X.hom)

/-- The inclusion of an open subscheme, as a morphism over `S`. -/
abbrev openOverι (X : Over S) (U : X.left.Opens) : openOver X U ⟶ X :=
  Over.homMk U.ι

/-- Quasi-affine chart step. Let `G` be an fppf sheaf over `S` with a map `p` to `T`, and let
`x' : X' ⟶ V` represent the base change of `p` along `g : V ⟶ T` by `a'`, with `x'` separated,
locally quasi-finite and locally of finite type. Suppose that `g` factors through an affine
open `ι : D ⟶ T` by a flat morphism `g' : V ⟶ D` of finite presentation with `V` affine.
Then the image in `G` of any affine open `U` of `X'` lies in a represented open subfunctor
of `G`. -/
theorem exists_openChart {G : FppfSheaf S} {T V X' : Over S}
    {p : G.obj ⟶ (schemeYoneda S).obj T} {g : V ⟶ T} {x' : X' ⟶ V}
    {a' : (schemeYoneda S).obj X' ⟶ G.obj}
    (hpb : IsPullback a' ((schemeYoneda S).map x') p ((schemeYoneda S).map g))
    [IsSeparated x'.left] [LocallyQuasiFinite x'.left] [LocallyOfFiniteType x'.left]
    {D : Scheme.{u}} [IsAffine D] (ι : D ⟶ T.left) [_root_.AlgebraicGeometry.IsOpenImmersion ι]
    (g' : V.left ⟶ D) (hg : g' ≫ ι = g.left) [IsAffine V.left] [Flat g']
    [LocallyOfFinitePresentation g'] (U : X'.left.Opens) (hU : IsAffineOpen U) :
    ∃ (Y : Over S) (b : (schemeYoneda S).obj Y ⟶ G.obj) (z : openOver X' U ⟶ Y),
      AlgebraicSpace.IsOpenImmersion b ∧
        (schemeYoneda S).map z ≫ b = (schemeYoneda S).map (openOverι X' U) ≫ a' := by
  classical
  let u : openOver X' U ⟶ X' := openOverι X' U
  let b₀ : (schemeYoneda S).obj (openOver X' U) ⟶ G.obj := (schemeYoneda S).map u ≫ a'
  have : _root_.AlgebraicGeometry.IsOpenImmersion u.left :=
    inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion U.ι)
  have : Flat g.left := by rw [← hg]; infer_instance
  have : LocallyOfFinitePresentation g.left := by rw [← hg]; infer_instance
  -- The map `b₀ : U ⟶ G` is flat and locally of finite presentation relative to schemes.
  have : ((flatLFP S).relative (schemeYoneda S)).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange (flatLFP S) (F := schemeYoneda S)
  have ha' : (flatLFP S).relative (schemeYoneda S) a' :=
    MorphismProperty.of_isPullback hpb.flip (flatLFP_relative_map g)
  have hb₀ : (flatLFP S).relative (schemeYoneda S) b₀ :=
    MorphismProperty.comp_mem _ _ _ (flatLFP_relative_map u) ha'
  -- The base change `σ : U ×_T V ⟶ X'` of `b₀` along `a'`.
  have hσ : ((schemeYoneda S).map (pullback.fst (u ≫ x' ≫ g) g) ≫ b₀) ≫ p =
      (schemeYoneda S).map (pullback.snd (u ≫ x' ≫ g) g) ≫ (schemeYoneda S).map g := by
    simp only [b₀, Category.assoc, hpb.w, ← Functor.map_comp, pullback.condition]
  let σ : pullback (u ≫ x' ≫ g) g ⟶ X' := (schemeYoneda S).preimage (hpb.lift _ _ hσ)
  have hσa : (schemeYoneda S).map σ ≫ a' =
      (schemeYoneda S).map (pullback.fst (u ≫ x' ≫ g) g) ≫ b₀ := by
    simp [σ]
  have hσx : σ ≫ x' = pullback.snd (u ≫ x' ≫ g) g := by
    apply (schemeYoneda S).map_injective
    simp [σ]
  have hsq : IsPullback ((schemeYoneda S).map σ)
      ((schemeYoneda S).map (pullback.fst (u ≫ x' ≫ g) g)) a' b₀ := by
    have hout := ((IsPullback.of_hasPullback (u ≫ x' ≫ g) g).map (schemeYoneda S)).flip
    have e₁ : (schemeYoneda S).map σ ≫ (schemeYoneda S).map x' =
        (schemeYoneda S).map (pullback.snd (u ≫ x' ≫ g) g) := by
      rw [← Functor.map_comp, hσx]
    have e₂ : b₀ ≫ p = (schemeYoneda S).map (u ≫ x' ≫ g) := by
      simp only [b₀, Category.assoc, hpb.w, Functor.map_comp]
    refine IsPullback.of_right ?_ hσa hpb.flip
    rw [e₁, e₂]
    exact hout
  have hσP : flatLFP S σ := hb₀.property a' _ σ hsq.flip
  have : Flat σ.left := hσP.1
  have : LocallyOfFinitePresentation σ.left := hσP.2
  -- The sheafified image `Q` of `b₀` is an open subsheaf of `G`.
  let Q := (Subfunctor.range b₀).sheafify (fppfTopology S)
  have hQopen : AlgebraicSpace.IsOpenImmersion Q.ι := sheafify_range_open_of_flat b₀ hb₀
  have hQ : CategoryTheory.Presheaf.IsSheaf (fppfTopology S) Q.toFunctor :=
    isSheaf_of_open G.property hQopen
  -- Its base change along `a'` is the open image `W` of `σ`.
  let W := flatImage σ
  let w₀ : W ⟶ X' := flatImageι σ
  let c₀ : (schemeYoneda S).obj W ⟶ Q.toFunctor := toSheafifyRange a' σ hsq.flip
  have hc₀ι : c₀ ≫ Q.ι = (schemeYoneda S).map w₀ ≫ a' := toSheafifyRange_ι a' σ hsq.flip
  have hc₀ : IsPullback c₀ ((schemeYoneda S).map w₀) Q.ι a' :=
    isPullback_toSheafifyRange a' σ hsq.flip
  have hpb' : IsPullback c₀ ((schemeYoneda S).map (w₀ ≫ x')) (Q.ι ≫ p)
      ((schemeYoneda S).map g) := by
    rw [Functor.map_comp]
    exact hc₀.paste_vert hpb
  -- The open `U` lies in `W`.
  let δ : openOver X' U ⟶ pullback (u ≫ x' ≫ g) g := pullback.lift (𝟙 _) (u ≫ x') (by simp)
  have hδσ : δ ≫ σ = u := by
    apply eq_of_isPullback hpb
    · rw [Functor.map_comp, Category.assoc, hσa, ← Category.assoc, ← Functor.map_comp,
        pullback.lift_fst, CategoryTheory.Functor.map_id, Category.id_comp]
    · rw [Category.assoc, hσx, pullback.lift_snd]
  let j : openOver X' U ⟶ W := δ ≫ toFlatImage σ
  have hj : j ≫ w₀ = u := by
    simp only [j, w₀, Category.assoc, toFlatImage_fac, hδσ]
  -- `c₀` is locally surjective.
  have hρ : (schemeYoneda S).map j ≫ c₀ = Subfunctor.toRangeSheafify (fppfTopology S) b₀ := by
    rw [← cancel_mono Q.ι, Category.assoc, hc₀ι, ← Functor.map_comp_assoc, hj]
    rfl
  have hc : CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S) c₀ := by
    have : CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S)
        ((schemeYoneda S).map j ≫ c₀) := by
      rw [hρ]
      infer_instance
    exact CategoryTheory.Presheaf.isLocallySurjective_of_isLocallySurjective _
      ((schemeYoneda S).map j) c₀
  -- `W` is quasi-affine.
  have : IsAffine (openOver X' U).left := hU
  have hK : IsPullback (pullback.fst (u ≫ x' ≫ g) g).left (pullback.snd (u ≫ x' ≫ g) g).left
      ((u ≫ x').left ≫ g') g' :=
    isPullback_left_of_factor _ _ ι _ _
      (by rw [Category.assoc, hg]; simp only [Over.comp_left, Category.assoc]) hg
  have : IsAffineHom (pullback.fst (u ≫ x' ≫ g) g).left :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) hK.flip inferInstance
  have : IsAffine (pullback (u ≫ x' ≫ g) g).left :=
    isAffine_of_isAffineHom (pullback.fst (u ≫ x' ≫ g) g).left
  have : CompactSpace W.left := by
    constructor
    rw [← Set.range_eq_univ.mpr (toFlatImage σ).left.surjective]
    exact isCompact_range (toFlatImage σ).left.continuous
  have : IsSeparated (w₀ ≫ x').left := by rw [Over.comp_left]; infer_instance
  have : LocallyQuasiFinite (w₀ ≫ x').left := by rw [Over.comp_left]; infer_instance
  have : LocallyOfFiniteType (w₀ ≫ x').left := by rw [Over.comp_left]; infer_instance
  have : W.left.IsQuasiAffine := isQuasiAffine_of_locallyQuasiFinite (w₀ ≫ x').left
  -- Descend `W` to a scheme representing `Q`.
  obtain ⟨Y, q, e, he⟩ := exists_iso_of_quasiAffine (F := ⟨Q.toFunctor, hQ⟩) hpb' hc ι g' hg
  refine ⟨Y, e.hom ≫ Q.ι, j ≫ q, ?_, ?_⟩
  · exact (MorphismProperty.cancel_left_of_respectsIso
      ((MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsOpenImmersion.{u})
        (Over.forget S)).relative (schemeYoneda S)) _ _).mpr hQopen
  · rw [Functor.map_comp, Category.assoc, ← Category.assoc ((schemeYoneda S).map q), he, hc₀ι,
      ← Functor.map_comp_assoc, hj]

end Langlands.AlgebraicGeometry.LocallyQuasiFiniteDescent
