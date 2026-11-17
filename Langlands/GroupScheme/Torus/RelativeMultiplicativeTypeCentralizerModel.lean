import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeCentralizerSmooth
import Langlands.GroupScheme.Torus.RelativeCentralizerDescent

/-! # Actual smooth closed centralizers of multiplicative-type homomorphisms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

variable {S : Scheme.{u}} {G : GroupScheme S} {H : CommGroupScheme S}

/-- Equality of the two products defining commutation is detected on any
fppf covering family of the base, on all relative test schemes. -/
theorem torusCentralizer_eq_fppfCoverDescent
    (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage S) (i : H.toGrp ⟶ G) :
    torusCentralizer i = SubgroupFunctor.CoverDescent.subgroup 𝒰
      (fun k => (torusCentralizer i).baseChange (𝒰.f k)) := by
  apply le_antisymm (SubgroupFunctor.CoverDescent.le_subgroup_baseChange 𝒰 _) ?_
  intro U x hx V a s
  let 𝒱 := 𝒰.pullback₁ V.hom
  let : EffectiveEpiFamily 𝒱.X 𝒱.f := by
    rw [← Sieve.effectiveEpimorphic_family,
      Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda]
    intro Y
    exact (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      (J := Scheme.fppfTopology) _).isSheafFor _
        (Precoverage.generate_mem_toGrothendieck 𝒱.mem₀)
  apply Over.OverMorphism.ext
  apply EffectiveEpiFamily.hom_ext 𝒱.X 𝒱.f
  intro k
  let W : Over (𝒰.X k) := Over.mk (pullback.snd V.hom (𝒰.f k))
  let q : (Over.map (𝒰.f k)).obj W ⟶ V :=
    Over.homMk (pullback.fst V.hom (𝒰.f k)) pullback.condition
  have hm := hx k W (q ≫ a)
  rw [SubgroupFunctor.mem_baseChange, MulEquiv.apply_symm_apply] at hm
  have hc := hm _ (𝟙 _) (q ≫ s)
  simp only [Category.id_comp, Category.assoc] at hc
  have he := congrArg (fun f => f.left) hc.eq
  change (q ≫ ((a ≫ x) * (s ≫ i.hom.hom))).left =
    (q ≫ ((s ≫ i.hom.hom) * (a ≫ x))).left
  simpa only [MonObj.comp_mul, Category.assoc] using he

/-- Closed representability of the all-test centralizer descends along any
fppf cover; no immersion assumption on the original homomorphism is needed. -/
theorem torusCentralizer_isClosedRepresentable_of_fppfCover
    (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage S) (i : H.toGrp ⟶ G)
    (h : ∀ k, ((torusCentralizer i).baseChange (𝒰.f k)).IsClosedRepresentable) :
    (torusCentralizer i).IsClosedRepresentable := by
  rw [torusCentralizer_eq_fppfCoverDescent 𝒰 i]
  exact SubgroupFunctor.CoverDescent.isClosedRepresentable_subgroup_fppf 𝒰 _
    (SubgroupFunctor.CoverDescent.isMatching_baseChange 𝒰 _) h

/-- Closed representability of a diagonalizable centralizer over an arbitrary
base follows from the actual smooth ring-level centralizer models. -/
theorem diagonalizableCentralizer_isClosedRepresentable
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : H.toGrp ⟶ G) (hH : RelativeMultiplicativeType.IsDiagonalizable H.toGrp) :
    (torusCentralizer i).IsClosedRepresentable := by
  let 𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage S :=
    S.affineOpenCover.openCover.changeProp (Q := @Flat ⊓ @LocallyOfFinitePresentation)
      (fun _ => ⟨inferInstance, inferInstance⟩)
  apply torusCentralizer_isClosedRepresentable_of_fppfCover 𝒰 i
  intro k
  let b := S.affineOpenCover.f k
  let B := GroupScheme.baseChange b
  let : Smooth (B.obj G).X.hom := MorphismProperty.pullback_snd G.X.hom b inferInstance
  let : IsAffineHom (B.obj G).X.hom := MorphismProperty.pullback_snd G.X.hom b inferInstance
  obtain ⟨C, c, hc, _, hrep⟩ := diagonalizableSmoothCentralizerModelOverSpec
    (H := (CommGroupScheme.baseChange b).obj H) (B.map i) (hH.baseChange b)
  rw [torusCentralizer_baseChange] at hrep
  exact ⟨C, c, hrep, hc⟩

/-- The centralizer of any multiplicative-type homomorphism into a smooth
affine group has an actual closed representative over its original base. -/
theorem relativeMultiplicativeTypeCentralizer_isClosedRepresentable
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : H.toGrp ⟶ G) (hH : RelativeMultiplicativeType.IsMultiplicativeType H.toGrp) :
    (torusCentralizer i).IsClosedRepresentable := by
  obtain ⟨𝒰, h𝒰⟩ := hH
  apply torusCentralizer_isClosedRepresentable_of_fppfCover 𝒰 i
  intro k
  let b := 𝒰.f k
  let B := GroupScheme.baseChange b
  let : Smooth (B.obj G).X.hom := MorphismProperty.pullback_snd G.X.hom b inferInstance
  let : IsAffineHom (B.obj G).X.hom := MorphismProperty.pullback_snd G.X.hom b inferInstance
  have h := diagonalizableCentralizer_isClosedRepresentable
    (H := (CommGroupScheme.baseChange b).obj H) (B.map i) (h𝒰 k)
  rwa [torusCentralizer_baseChange] at h

/-- Choose the actual smooth closed centralizer of a multiplicative-type
homomorphism on the original arbitrary scheme base. -/
def relativeMultiplicativeTypeCentralizerModel
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (i : H.toGrp ⟶ G) (hH : RelativeMultiplicativeType.IsMultiplicativeType H.toGrp) :
    Σ C : GroupScheme S, {c : C ⟶ G // IsClosedSubgroup c ∧ Smooth C.X.hom ∧
      (torusCentralizer i).IsRepresentedBy c} := by
  let h := relativeMultiplicativeTypeCentralizer_isClosedRepresentable i hH
  let C := SubgroupFunctor.ClosedRepresentative.ofIsClosedRepresentable h
  exact ⟨C.group, C.hom, C.closed,
    relativeMultiplicativeTypeCentralizer_smooth i hH C.hom C.represents, C.represents⟩

end Langlands.GroupScheme
