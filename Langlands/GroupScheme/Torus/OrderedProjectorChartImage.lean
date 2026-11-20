import Langlands.GroupScheme.Torus.OrderedProjectorChartCover
import Langlands.GroupScheme.Torus.OrderedProjectorChartOverlap
import Langlands.GroupScheme.AffineQuotientReduction
import Langlands.AlgebraicGeometry.SchemeFlatPropertyDescent

/-! # Finiteness and affine images of ordered projector charts -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.OrderedProjectorScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

private theorem of_etale_cover_pullback_snd (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [IsZariskiLocalAtTarget P]
    [P.DescendsAlong (@Surjective.{u} ⊓ @Flat.{u} ⊓ @QuasiCompact.{u})]
    {I : Type u} {X Y : Scheme.{u}} {V : I → Scheme.{u}} (f : X ⟶ Y)
    (q : ∀ i, V i ⟶ Y) (hq : ∀ i, Etale (q i))
    (hcov : ⋃ i, Set.range (q i) = Set.univ)
    (h : ∀ i, P (pullback.snd f (q i))) : P f := by
  let p : (∐ V) ⟶ Y := Sigma.desc q
  have hp : Etale p := IsZariskiLocalAtSource.sigmaDesc (P := @Etale) hq
  have hps : Surjective p := Surjective.sigmaDesc_of_union_range_eq_univ hcov
  let : P.DescendsAlong (@Etale.{u} ⊓ @Surjective.{u}) :=
    Langlands.AlgebraicGeometry.SchemeFlatPropertyDescent.descendsAlong_etale_surjective P
  apply MorphismProperty.of_pullback_snd_of_descendsAlong (P := P) (g := p)
    (Q := @Etale ⊓ @Surjective) ⟨hp, hps⟩
  apply IsZariskiLocalAtTarget.of_openCover (P := P) (sigmaOpenCover V)
  intro i
  let a := Sigma.ι V i
  change P (pullback.snd (pullback.snd f p) a)
  have hpb := (IsPullback.of_hasPullback (pullback.snd f p) a).paste_horiz
    (IsPullback.of_hasPullback f p)
  have ha : a ≫ p = q i := Sigma.ι_comp_desc q i
  rw [ha] at hpb
  rw [← hpb.isoPullback_hom_snd, P.cancel_left_of_respectsIso]
  exact h i

variable {R : CommRingCat.{u}} {n : Type} [Fintype n] [DecidableEq n]
variable {M : Over (Spec R)} {K : GroupScheme M.left}
variable (j : K ⟶ (baseChange M.hom).obj (GeneralLinear.groupScheme n R))
  (hj : IsClosedSubgroup j) (hK : RelativeTorus.IsTorus K)
  (hu : TorusSubgroupModuli.IsUniversal j)

include hj hK

/-- For two split charts, the second projection from their overlap is finite étale. -/
theorem SplitChart.finiteEtale_overlap (C D : SplitChart.{u}) :
    IsFinite (pullback.snd (C.map j hu).left (D.map j hu).left) ∧
      Etale (pullback.snd (C.map j hu).left (D.map j hu).left) := by
  classical
  let : Fintype C.index := Fintype.ofFinite C.index
  let : Fintype D.index := Fintype.ofFinite D.index
  exact finiteEtale_secondProjection hj hK hu C.generates D.generates
    (Diagonalizable.isSplitTorus R (AddEquiv.refl (C.index → ℤ)))
    (Diagonalizable.isSplitTorus R (AddEquiv.refl (D.index → ℤ))) C.injective D.injective

/-- Every split chart map is finite étale. After an étale cover of the moduli which factors
through split charts, its pullback is the base change of a projection from a chart overlap. -/
theorem SplitChart.finiteEtale_map (C : SplitChart.{u}) :
    IsFinite (C.map j hu).left ∧ Etale (C.map j hu).left := by
  classical
  let P : MorphismProperty Scheme.{u} := @IsFinite ⊓ @Etale
  change P (C.map j hu).left
  choose D V p hEt hmem using exists_etale_factorization_through_splitChart j hj hK hu
  let q (x : M.left) : (V x).left ⟶ M.left := (p x).left ≫ ((D x).map j hu).left
  have hcov : ⋃ x, Set.range (q x) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    exact fun x => Set.mem_iUnion.mpr ⟨x, hmem x⟩
  refine of_etale_cover_pullback_snd P (C.map j hu).left q hEt hcov fun x => ?_
  apply MorphismProperty.of_isPullback (P := P) (IsPullback.of_right'
    (IsPullback.of_hasPullback (C.map j hu).left (q x))
    (IsPullback.of_hasPullback (C.map j hu).left ((D x).map j hu).left))
  exact C.finiteEtale_overlap j hj hK hu (D x)

/-- The open image of a split chart. -/
def SplitChart.image (C : SplitChart.{u}) : M.left.Opens :=
  have : Etale (C.map j hu).left := (C.finiteEtale_map j hj hK hu).2
  ⟨Set.range (C.map j hu).left, (C.map j hu).left.isOpenMap.isOpen_range⟩

/-- The image of each split chart is affine. The map from the affine projector scheme to its
image is a finite surjective map, so affineness descends along it. -/
theorem SplitChart.isAffineOpen_image (C : SplitChart.{u}) :
    IsAffineOpen (C.image j hj hK hu) := by
  let U := C.image j hj hK hu
  let f := C.map j hu
  have hsubset : Set.range f.left ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    exact Set.Subset.rfl
  let g := IsOpenImmersion.lift U.ι f.left hsubset
  have hg : g ≫ U.ι = f.left := IsOpenImmersion.lift_fac _ _ _
  have hpb : IsPullback (𝟙 _) g f.left U.ι :=
    IsPullback.of_horiz_isIso_mono ⟨(Category.id_comp _).trans hg.symm⟩
  have hfin : IsFinite g := MorphismProperty.of_isPullback (P := @IsFinite) hpb
    (C.finiteEtale_map j hj hK hu).1
  have hsurj : Surjective g := ⟨fun y => by
    have hy : U.ι y ∈ Set.range f.left := y.2
    obtain ⟨x, hx⟩ := hy
    refine ⟨x, U.ι.isOpenEmbedding.injective ?_⟩
    rwa [← Scheme.Hom.comp_apply, hg]⟩
  let W : Over (Spec R) := Over.mk (U.ι ≫ M.hom)
  let p : C.scheme n R ⟶ W := Over.homMk g (by
    change g ≫ U.ι ≫ M.hom = (C.scheme n R).hom
    rw [← Category.assoc, hg, Over.w f])
  exact AffineQuotient.isAffine_of_finite_surjective p hfin hsurj

end Langlands.GroupScheme.OrderedProjectorScheme
