import Langlands.GroupScheme.HomEqualityOpenLocus
import Langlands.AlgebraicGeometry.ReducedSubscheme
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Equality after schematically dense base change -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace Langlands.GroupScheme.SchematicHomEquality

variable {S T Z : Scheme.{u}}

/-- Morphisms into a separated scheme over the base are determined by restriction
along a schematically dominant morphism, even when their source is nonreduced. -/
theorem over_hom_ext {X Y : Over S} [IsSeparated Y.hom]
    (f g : X ⟶ Y) (i : Z ⟶ X.left) [IsSchemeTheoreticallyDominant i]
    (he : i ≫ f.left = i ≫ g.left) : f = g := by
  let Z' : Over S := Over.mk (i ≫ X.hom)
  let i' : Z' ⟶ X := Over.homMk i rfl
  have he' : i' ≫ f = i' ≫ g := Over.OverMorphism.ext he
  let j := equalizer.ι f g
  let l := equalizer.lift i' he'
  have hj : j.left.ker = ⊥ := by
    apply le_antisymm _ bot_le
    calc
      j.left.ker ≤ (l.left ≫ j.left).ker := Scheme.Hom.le_ker_comp _ _
      _ = i.ker := by
        congr 1
        exact congrArg (fun a => a.left) (equalizer.lift_ι i' he')
      _ = ⊥ := i.ker_eq_bot
  have : IsIso j.left := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hj
  apply Over.OverMorphism.ext
  apply (cancel_epi j.left).mp
  exact congrArg (fun a => a.left) (equalizer.condition f g)

variable {H G : GroupScheme S}

/-- A quasi-compact schematically dominant base change detects equality from a flat
source into a separated target. -/
theorem baseChange_hom_ext (b : T ⟶ S)
    [IsSchemeTheoreticallyDominant b] [QuasiCompact b]
    [Flat H.X.hom] [IsSeparated G.X.hom] {f g : H ⟶ G}
    (he : (baseChange b).map f = (baseChange b).map g) : f = g := by
  apply Grp.hom_ext
  apply over_hom_ext f.hom.hom g.hom.hom (pullback.fst H.X.hom b)
  have he' : (Over.pullback b).map f.hom.hom =
      (Over.pullback b).map g.hom.hom := congrArg (fun a => a.hom.hom) he
  have h := congrArg (fun a => a.left ≫ pullback.fst G.X.hom b) he'
  simpa only [Over.pullback_map_left, pullback.lift_fst] using h

/-- On a reduced base, equality on a quasi-compact dense open detects equality
from any flat group scheme into any separated group scheme. -/
theorem hom_ext_of_dense_open [IsReduced S] [Flat H.X.hom] [IsSeparated G.X.hom]
    (U : S.Opens) [QuasiCompact U.ι] (hU : Dense (U : Set S))
    {f g : H ⟶ G} (he : (baseChange U.ι).map f = (baseChange U.ι).map g) :
    f = g := by
  have : IsDominant U.ι :=
    ⟨by simpa only [DenseRange, Scheme.Opens.range_ι] using hU⟩
  have : IsSchemeTheoreticallyDominant U.ι :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  exact baseChange_hom_ext U.ι he

/-- Over a base with Noetherian underlying space, equality on an open extends
to equality on every residue-field fibre over its closure. -/
theorem fibre_eq_on_closure_of_open_eq [NoetherianSpace S]
    [Flat H.X.hom] [IsSeparated G.X.hom]
    (U : S.Opens) {f g : H ⟶ G}
    (he : (baseChange U.ι).map f = (baseChange U.ι).map g)
    (s : S) (hs : s ∈ closure (U : Set S)) :
    (baseChange (S.fromSpecResidueField s)).map f =
      (baseChange (S.fromSpecResidueField s)).map g := by
  let C : Closeds S := ⟨closure (U : Set S), isClosed_closure⟩
  let I := Scheme.IdealSheafData.vanishingIdeal C
  let B := I.subscheme
  let j : B ⟶ S := I.subschemeι
  have hrange : Set.range j = closure (U : Set S) :=
    Langlands.AlgebraicGeometry.ReducedSubscheme.range_subschemeι_vanishingIdeal C
  let : IsReduced B :=
    Langlands.AlgebraicGeometry.ReducedSubscheme.isReduced_vanishingIdeal_subscheme C
  let : NoetherianSpace B := j.isClosedEmbedding.isEmbedding.isInducing.noetherianSpace
  let V : B.Opens := j ⁻¹ᵁ U
  have : NoetherianSpace V.toScheme :=
    V.ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  have hV : Dense (V : Set B) := by
    intro x
    rw [j.isClosedEmbedding.isEmbedding.closure_eq_preimage_closure_image]
    change j x ∈ closure (j '' (j ⁻¹' (U : Set S)))
    rw [Set.image_preimage_eq_inter_range, hrange,
      Set.inter_eq_left.mpr subset_closure]
    exact hrange ▸ Set.mem_range_self x
  have heV : (baseChange V.ι).map ((baseChange j).map f) =
      (baseChange V.ι).map ((baseChange j).map g) := by
    apply (HomEqualityOpenLocus.iterated_baseChange_eq_iff j V.ι
      (V.ι ≫ j) rfl f g).mpr
    have hr : Set.range (V.ι ≫ j) ⊆ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      exact x.property
    exact HomEqualityOpenLocus.baseChange_eq_of_factor U.ι
      (IsOpenImmersion.lift U.ι (V.ι ≫ j) hr) (V.ι ≫ j)
      (IsOpenImmersion.lift_fac _ _ _) he
  have hej : (baseChange j).map f = (baseChange j).map g := by
    have : Flat ((baseChange j).obj H).X.hom := by
      change Flat (pullback.snd H.X.hom j)
      infer_instance
    have : IsSeparated ((baseChange j).obj G).X.hom := by
      change IsSeparated (pullback.snd G.X.hom j)
      infer_instance
    exact hom_ext_of_dense_open V hV heV
  have hfactor : Set.range (S.fromSpecResidueField s) ⊆ C := by
    rw [Scheme.range_fromSpecResidueField]
    exact Set.singleton_subset_iff.mpr hs
  obtain ⟨c, hc⟩ :=
    Langlands.AlgebraicGeometry.ReducedSubscheme.exists_lift_vanishingIdeal
      (S.fromSpecResidueField s) C hfactor
  exact HomEqualityOpenLocus.baseChange_eq_of_factor j c
    (S.fromSpecResidueField s) hc hej

/-- Local extension of fibre equality gives a closed equality locus over a base
with Noetherian underlying space, provided the source is flat and the target separated. -/
theorem isClosed_fibre_eq_set_of_locally_eq [NoetherianSpace S]
    [Flat H.X.hom] [IsSeparated G.X.hom] (f g : H ⟶ G)
    (hloc : ∀ s : S,
      (baseChange (S.fromSpecResidueField s)).map f =
          (baseChange (S.fromSpecResidueField s)).map g →
      ∃ W : S.Opens, s ∈ W ∧
        (baseChange W.ι).map f = (baseChange W.ι).map g) :
    IsClosed {s : S | (baseChange (S.fromSpecResidueField s)).map f =
      (baseChange (S.fromSpecResidueField s)).map g} := by
  obtain ⟨U, hU, he⟩ := HomEqualityOpenLocus.exists_open_fibre_eq_locus f g hloc
  have hclosed : IsClosed (U : Set S) := by
    apply isClosed_of_closure_subset
    intro s hs
    exact (hU s).mpr (fibre_eq_on_closure_of_open_eq U he s hs)
  have hset : (U : Set S) =
      {s : S | (baseChange (S.fromSpecResidueField s)).map f =
        (baseChange (S.fromSpecResidueField s)).map g} := Set.ext hU
  exact hset ▸ hclosed

/-- The actual clopen fibre equality locus over a base with Noetherian
underlying space, under local extension of equality. -/
def clopenLocus [NoetherianSpace S] [Flat H.X.hom] [IsSeparated G.X.hom]
    (f g : H ⟶ G)
    (hloc : ∀ s : S,
      (baseChange (S.fromSpecResidueField s)).map f =
          (baseChange (S.fromSpecResidueField s)).map g →
      ∃ W : S.Opens, s ∈ W ∧
        (baseChange W.ι).map f = (baseChange W.ι).map g) : Clopens S :=
  ⟨_, ⟨isClosed_fibre_eq_set_of_locally_eq f g hloc,
    HomEqualityOpenLocus.isOpen_fibre_eq_set f g hloc⟩⟩

/-- Membership in the constructed clopen is exactly equality of the residue-field fibres. -/
theorem mem_clopenLocus_iff [NoetherianSpace S] [Flat H.X.hom] [IsSeparated G.X.hom]
    (f g : H ⟶ G)
    (hloc : ∀ s : S,
      (baseChange (S.fromSpecResidueField s)).map f =
          (baseChange (S.fromSpecResidueField s)).map g →
      ∃ W : S.Opens, s ∈ W ∧
        (baseChange W.ι).map f = (baseChange W.ι).map g) (s : S) :
    s ∈ clopenLocus f g hloc ↔
      (baseChange (S.fromSpecResidueField s)).map f =
        (baseChange (S.fromSpecResidueField s)).map g := Iff.rfl

/-- The two homomorphisms agree over the actual clopen fibre equality locus. -/
theorem eq_on_clopenLocus [NoetherianSpace S] [Flat H.X.hom] [IsSeparated G.X.hom]
    (f g : H ⟶ G)
    (hloc : ∀ s : S,
      (baseChange (S.fromSpecResidueField s)).map f =
          (baseChange (S.fromSpecResidueField s)).map g →
      ∃ W : S.Opens, s ∈ W ∧
        (baseChange W.ι).map f = (baseChange W.ι).map g) :
    (baseChange (Scheme.Opens.ι (X := S) (clopenLocus f g hloc).toOpens)).map f =
      (baseChange (Scheme.Opens.ι (X := S) (clopenLocus f g hloc).toOpens)).map g := by
  apply HomEqualityOpenLocus.eq_on_open_of_locally_eq
  intro s
  exact hloc s.val s.property

end Langlands.GroupScheme.SchematicHomEquality
