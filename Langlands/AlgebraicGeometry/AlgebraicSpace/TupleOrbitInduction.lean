import Langlands.AlgebraicGeometry.AlgebraicSpace.TupleOrbitCover
import Langlands.AlgebraicGeometry.ReducedSubscheme
import Langlands.AlgebraicGeometry.OrbitSaturatedAffineOpen
import Langlands.AlgebraicGeometry.AlgebraicSpace.SaturatedAffineOpensRepresentation
import Langlands.AlgebraicGeometry.AlgebraicSpace.ReducedClosedSubspaceStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.NoetherianSchemeQuasiAffineSourceAFStatement
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationPresentation
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # The Noetherian case by induction over tuple-orbit covers -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : Presheaf S}

section SameImageLemmas

/-- Points of `U'` have the same image under `h_φ ≫ a` iff their images in `U` have the same
image under `a`. -/
theorem sameImage_map_comp_iff {U' U : Over S} (φ : U' ⟶ U) (a : (schemeYoneda S).obj U ⟶ X)
    (w w' : U'.left) :
    SameImage ((schemeYoneda S).map φ ≫ a) w w' ↔ SameImage a (φ.left w) (φ.left w') := by
  rw [sameImage_iff, sameImage_iff, SameImage₂.of_comp_iff φ w w']
  constructor
  · intro h
    exact ((SameImage₂.of_comp_iff φ w' (φ.left w)).mp h.symm).symm
  · intro h
    exact ((SameImage₂.of_comp_iff φ w' (φ.left w)).mpr h.symm).symm

/-- Composing with an isomorphism of presheaves does not change which points have the same
image. -/
theorem sameImage_comp_iso_iff {U : Over S} {X' : Presheaf S} (a : (schemeYoneda S).obj U ⟶ X)
    (e : X ≅ X') (u u' : U.left) : SameImage (a ≫ e.hom) u u' ↔ SameImage a u u' := by
  constructor
  · rintro ⟨T, g, g', t, h, hg, hg'⟩
    refine ⟨T, g, g', t, ?_, hg, hg'⟩
    rw [← cancel_mono e.hom]
    simpa only [Category.assoc] using h
  · rintro ⟨T, g, g', t, h, hg, hg'⟩
    refine ⟨T, g, g', t, ?_, hg, hg'⟩
    rw [← Category.assoc, h, Category.assoc]

/-- For a morphism of schemes, two points have the same image in the represented presheaf iff
they have the same image point. -/
theorem sameImage_map_iff {U V : Over S} (φ : U ⟶ V) (x x' : U.left) :
    SameImage ((schemeYoneda S).map φ) x x' ↔ φ.left x = φ.left x' := by
  constructor
  · rintro ⟨T, g, g', t, h, rfl, rfl⟩
    have h' : g ≫ φ = g' ≫ φ :=
      (schemeYoneda S).map_injective (by simpa only [Functor.map_comp] using h)
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left, ← Over.comp_left, h']
  · intro h
    obtain ⟨t, ht1, ht2⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := φ.left) (g := φ.left) x x' h
    refine ⟨overPullback φ φ, overPullbackFst φ φ, overPullbackSnd φ φ, t, ?_, ht1, ht2⟩
    rw [← Functor.map_comp, ← Functor.map_comp, overPullback_condition]

end SameImageLemmas

section Finiteness

variable {F G H : Presheaf S}

set_option backward.isDefEq.respectTransparency.types false in
/-- Composing a finite transformation with a presheaf isomorphism keeps it finite. -/
theorem IsFinite.comp_iso {f : F ⟶ G} (hf : IsFinite f) (e : G ≅ H) : IsFinite (f ≫ e.hom) := by
  let := MorphismProperty.RespectsIso.inverseImage
    (@_root_.AlgebraicGeometry.IsFinite.{u}) (Over.forget S)
  exact (MorphismProperty.cancel_right_of_respectsIso
    ((MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsFinite.{u})
      (Over.forget S)).relative (schemeYoneda S)) _ _).mpr hf

/-- A morphism of schemes whose represented transformation is finite is finite. -/
theorem isFinite_left_of_isFinite_map {U V : Over S} (φ : U ⟶ V)
    (h : IsFinite ((schemeYoneda S).map φ)) : _root_.AlgebraicGeometry.IsFinite φ.left :=
  h.projection (𝟙 _) (𝟙 _) φ IsPullback.of_id_fst

end Finiteness

section Reduced

open ReducedSubscheme

/-- The reduced induced closed subscheme on a closed set, as a scheme over `S`. -/
def reducedOver (U : Over S) (Z : Closeds U.left) : Over S :=
  Over.mk ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ U.hom)

/-- The inclusion of the reduced induced closed subscheme. -/
def reducedOverι (U : Over S) (Z : Closeds U.left) : reducedOver U Z ⟶ U :=
  Over.homMk (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι

theorem reducedOverι_left (U : Over S) (Z : Closeds U.left) :
    (reducedOverι U Z).left = (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι :=
  rfl

instance (U : Over S) (Z : Closeds U.left) :
    _root_.AlgebraicGeometry.IsClosedImmersion (reducedOverι U Z).left :=
  inferInstanceAs (_root_.AlgebraicGeometry.IsClosedImmersion
    (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι)

instance (U : Over S) (Z : Closeds U.left) :
    _root_.AlgebraicGeometry.IsReduced (reducedOver U Z).left :=
  isReduced_vanishingIdeal_subscheme Z

theorem range_reducedOverι (U : Over S) (Z : Closeds U.left) :
    Set.range (reducedOverι U Z).left = Z :=
  range_subschemeι_vanishingIdeal Z

end Reduced

section Step

open ReducedSubscheme OrbitSaturatedAffineOpen SaturatedAffineOpensRepresentation

set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1000000 in
/-- One step of the induction: a tuple-orbit cover whose closed part maps to a scheme with
finite affine neighborhoods, compatibly with the identifications of points, gives an AF
representation of the target. -/
theorem exists_af_of_tupleOrbitCover {U : Over S} [U.left.IsQuasiAffine] {Y : AlgebraicSpace S}
    {f : (schemeYoneda S).obj U ⟶ Y.presheaf} (hf : IsFinite f) (hfs : IsSurjective f)
    (T : TupleOrbitCover f) {PC : Over S}
    (hPC : PointTopology.HasFiniteAffineNeighborhoods PC.left)
    (q₀ : reducedOver U ⟨T.C, T.isClosed_C⟩ ⟶ PC) (hq₀ : IsClosedMap q₀.left)
    (hq₀rel : ∀ x x', SameImage f ((reducedOverι U ⟨T.C, T.isClosed_C⟩).left x)
      ((reducedOverι U ⟨T.C, T.isClosed_C⟩).left x') ↔ q₀.left x = q₀.left x') :
    ∃ P : Over S, PointTopology.HasFiniteAffineNeighborhoods P.left ∧
      Nonempty ((schemeYoneda S).obj P ≅ Y.presheaf) := by
  classical
  have hP0 : _root_.AlgebraicGeometry.IsFinite (T.P.pr 0).left := T.pr_isFinite 0
  have : T.P.obj.left.IsQuasiAffine := Scheme.IsQuasiAffine.of_isAffineHom (T.P.pr 0).left
  set f₀ : (schemeYoneda S).obj T.P.obj ⟶ Y.presheaf := (schemeYoneda S).map (T.P.pr 0) ≫ f
    with hf₀_def
  have hf₀ : IsFinite f₀ := IsFinite.map_comp _ hP0 hf
  -- the permutation action on points
  have hpp : ∀ (g h : Equiv.Perm (Fin (T.k + 1))) (w : T.P.obj.left),
      (T.P.perm h).left ((T.P.perm g).left w) = (T.P.perm (g * h)).left w := by
    intro g h w
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, ChartFibrePower.perm_mul]
  have hp1 : ∀ w : T.P.obj.left, (T.P.perm 1).left w = w := by
    intro w
    rw [ChartFibrePower.perm_one]
    rfl
  have hpinv : ∀ (g : Equiv.Perm (Fin (T.k + 1))) (w : T.P.obj.left),
      (T.P.perm g⁻¹).left ((T.P.perm g).left w) = w := by
    intro g w
    rw [hpp, mul_inv_cancel, hp1]
  have hpW : ∀ (g : Equiv.Perm (Fin (T.k + 1))) (w : T.P.obj.left),
      (T.P.perm g).left w ∈ T.Wset ↔ w ∈ T.Wset := by
    intro g w
    refine ⟨fun h => ?_, T.perm_mem g w⟩
    have := T.perm_mem g⁻¹ _ h
    rwa [hpinv] at this
  have hpS : ∀ (g : Equiv.Perm (Fin (T.k + 1))) (w : T.P.obj.left),
      SameImage f₀ w ((T.P.perm g).left w) := by
    intro g w
    refine ⟨T.P.obj, 𝟙 _, T.P.perm g, w, ?_, rfl, rfl⟩
    rw [CategoryTheory.Functor.map_id, Category.id_comp, ← Functor.map_comp_assoc,
      ChartFibrePower.perm_pr, T.P.w (g 0) 0]
  -- the relation on points of the fibre power
  let rel : T.P.obj.left → T.P.obj.left → Prop := fun w w' =>
    (w ∈ T.Wset ∧ w' ∈ T.Wset ∧ SameImage f₀ w w') ∨
      (w ∉ T.Wset ∧ w' ∉ T.Wset ∧ ∃ g, (T.P.perm g).left w = w')
  have hrel : Equivalence rel := by
    refine ⟨fun w => ?_, fun {w w'} h => ?_, fun {w w' w''} h h' => ?_⟩
    · by_cases hw : w ∈ T.Wset
      · exact Or.inl ⟨hw, hw, SameImage.refl f₀ w⟩
      · exact Or.inr ⟨hw, hw, 1, hp1 w⟩
    · rcases h with ⟨hw, hw', hs⟩ | ⟨hw, hw', g, hg⟩
      · exact Or.inl ⟨hw', hw, hs.symm⟩
      · exact Or.inr ⟨hw', hw, g⁻¹, by rw [← hg, hpinv]⟩
    · rcases h with ⟨hw, hw', hs⟩ | ⟨hw, hw', g, hg⟩
      · rcases h' with ⟨-, hw'', hs'⟩ | ⟨hn, -, -⟩
        · exact Or.inl ⟨hw, hw'', hs.trans hs'⟩
        · exact absurd hw' hn
      · rcases h' with ⟨hn, -, -⟩ | ⟨-, hw'', g', hg'⟩
        · exact absurd hn hw'
        · exact Or.inr ⟨hw, hw'', g * g', by rw [← hpp, hg, hg']⟩
  have hfin : ∀ w, {w' | rel w w'}.Finite := by
    intro w
    refine ((SameImage.finite_class hf₀ w).union
      (Set.finite_range fun g : Equiv.Perm (Fin (T.k + 1)) => (T.P.perm g).left w)).subset ?_
    rintro w' (⟨-, -, hs⟩ | ⟨-, -, g, hg⟩)
    · exact Or.inl hs
    · exact Or.inr ⟨g, hg⟩
  have hσrel : ∀ (g : Equiv.Perm (Fin (T.k + 1))) w, rel w ((T.P.perm g).left w) := by
    intro g w
    by_cases hw : w ∈ T.Wset
    · exact Or.inl ⟨hw, T.perm_mem g w hw, hpS g w⟩
    · exact Or.inr ⟨hw, fun h => hw ((hpW g w).mp h), g, rfl⟩
  -- the closed part
  let CC : Closeds U.left := ⟨T.C, T.isClosed_C⟩
  let Zset : Closeds T.P.obj.left := ⟨T.Wset ∩ (T.P.pr 0).left ⁻¹' T.C,
    T.isClosed_Wset.inter (T.isClosed_C.preimage (T.P.pr 0).left.continuous)⟩
  let i := (Scheme.IdealSheafData.vanishingIdeal Zset).subschemeι
  have : _root_.AlgebraicGeometry.IsReduced (Scheme.IdealSheafData.vanishingIdeal Zset).subscheme :=
    isReduced_vanishingIdeal_subscheme Zset
  have hri : Set.range i = (Zset : Set T.P.obj.left) := range_subschemeι_vanishingIdeal Zset
  have hmem_i : ∀ w, w ∈ Set.range i ↔ w ∈ T.Wset ∧ (T.P.pr 0).left w ∈ T.C := by
    intro w
    rw [hri]
    rfl
  have hlift : Set.range (i ≫ (T.P.pr 0).left) ⊆ (CC : Set U.left) := by
    rintro _ ⟨z, rfl⟩
    exact ((hmem_i (i z)).mp ⟨z, rfl⟩).2
  obtain ⟨l, hl⟩ := exists_lift_vanishingIdeal (i ≫ (T.P.pr 0).left) CC hlift
  let ιC := (Scheme.IdealSheafData.vanishingIdeal CC).subschemeι
  have hlz : ∀ z, ιC (l z) = (T.P.pr 0).left (i z) := by
    intro z
    rw [← Scheme.Hom.comp_apply, hl, Scheme.Hom.comp_apply]
  have hιCinj : Function.Injective ιC := ιC.isClosedEmbedding.injective
  have hl_closed : IsClosedMap l := by
    intro K hK
    have h1 : l '' K = ιC ⁻¹' ((T.P.pr 0).left '' (i '' K)) := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨i z, ⟨z, hz, rfl⟩, (hlz z).symm⟩
      · rintro ⟨_, ⟨z, hz, rfl⟩, hzx⟩
        exact ⟨z, hz, hιCinj ((hlz z).trans hzx)⟩
    rw [h1]
    exact ((T.P.pr 0).left.isClosedMap _ (i.isClosedEmbedding.isClosedMap _ hK)).preimage
      ιC.continuous
  let q := l ≫ q₀.left
  have hq : IsClosedMap q := hq₀.comp hl_closed
  have hsat : ∀ z w, rel (i z) w → w ∈ Set.range i := by
    intro z w h
    have hz := (hmem_i (i z)).mp ⟨z, rfl⟩
    rcases h with ⟨-, hw, hs⟩ | ⟨hn, -, -⟩
    · refine (hmem_i w).mpr ⟨hw, T.saturated_C _ _ ?_ hz.2⟩
      exact (sameImage_map_comp_iff (T.P.pr 0) f _ _).mp hs
    · exact absurd hz.1 hn
  have hqrel : ∀ z z', rel (i z) (i z') ↔ q z = q z' := by
    intro z z'
    have hz := (hmem_i (i z)).mp ⟨z, rfl⟩
    have hz' := (hmem_i (i z')).mp ⟨z', rfl⟩
    have h1 : rel (i z) (i z') ↔ SameImage f₀ (i z) (i z') := by
      constructor
      · rintro (⟨-, -, hs⟩ | ⟨hn, -, -⟩)
        · exact hs
        · exact absurd hz.1 hn
      · intro hs
        exact Or.inl ⟨hz.1, hz'.1, hs⟩
    rw [h1, sameImage_map_comp_iff (T.P.pr 0) f, ← hlz, ← hlz]
    exact hq₀rel (l z) (l z')
  have horbit : ∀ w w', w ∉ Set.range i → rel w w' →
      ∃ g, (T.P.perm g).left w = w' := by
    intro w w' hw h
    rcases h with ⟨hW, hW', hs⟩ | ⟨-, -, g, hg⟩
    · refine T.orbit w hW w' hW' (fun hC => hw ((hmem_i w).mpr ⟨hW, hC⟩)) hs
    · exact ⟨g, hg⟩
  have core := fun (F : Set T.P.obj.left) (hF : F.Finite) =>
    exists_saturated_isAffineOpen (fun g => (T.P.perm g).left)
      (by rw [ChartFibrePower.perm_one]; rfl)
      (fun g h => by rw [← Over.comp_left, ChartFibrePower.perm_mul])
      rel hrel hfin hσrel i q hq hPC hsat hqrel horbit F hF
  -- the finite cover by the reduced subscheme on `Wset`
  let WW : Closeds T.P.obj.left := ⟨T.Wset, T.isClosed_Wset⟩
  let ιW := reducedOverι T.P.obj WW
  have hιW : ∀ w, w ∈ Set.range ιW.left ↔ w ∈ T.Wset := by
    intro w
    rw [range_reducedOverι]
    rfl
  let g : (schemeYoneda S).obj (reducedOver T.P.obj WW) ⟶ Y.presheaf :=
    (schemeYoneda S).map ιW ≫ f₀
  have hιWfin : _root_.AlgebraicGeometry.IsFinite ιW.left := inferInstance
  have hg : IsFinite g := IsFinite.map_comp _ hιWfin hf₀
  have hgs : IsSurjective g := by
    let hr := hg.representable
    refine isSurjective_of_isPullback hr hfs (hr.isPullback f) ⟨fun u => ?_⟩
    obtain ⟨w, hw, hwu⟩ := T.surj u
    obtain ⟨wB, rfl⟩ := (hιW w).mpr hw
    have h₁ : SameImage₂ f f u ((T.P.pr 0).left (ιW.left wB)) := hwu
    have h₂ : SameImage₂ g f wB ((T.P.pr 0).left (ιW.left wB)) := by
      have := SameImage₂.map (ιW ≫ T.P.pr 0) f wB
      rw [Functor.map_comp, Category.assoc] at this
      exact this
    obtain ⟨p, hp, -⟩ := SameImage₂.exists_pullback hr (h₁.trans h₂.symm)
    exact ⟨p, hp⟩
  have hClaim : HasSaturatedAffineNeighborhoods g := by
    intro F hF
    obtain ⟨V, hV, hFV, hVsat⟩ := core (ιW.left '' F) (hF.image _)
    refine ⟨ιW.left ⁻¹ᵁ V, hV.preimage ιW.left, fun x hx => hFV ⟨x, hx, rfl⟩, ?_⟩
    intro w w' h hw
    have hs : SameImage f₀ (ιW.left w) (ιW.left w') := (sameImage_map_comp_iff ιW f₀ w w').mp h
    exact hVsat _ _ (Or.inl ⟨(hιW _).mp ⟨w, rfl⟩, (hιW _).mp ⟨w', rfl⟩, hs⟩) hw
  exact exists_AF_representation_of_saturated_affine_opens g hg hgs hClaim

end Step

section Induction

open SaturatedAffineOpensRepresentation

set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1000000 in
/-- The Noetherian case, assuming the reduced-closed-subspace statement. -/
theorem noetherianSchemeQuasiAffineSourceAF_of_reducedClosedSubspace
    (hCS : ReducedClosedSubspaceStatement.{u}) :
    NoetherianSchemeQuasiAffineSourceAFStatement.{u} := by
  intro S U₀ Y₀ f₀ hY₀ hY₀s hqa hnoeth hf₀ hf₀s
  suffices key : ∀ Z : Closeds U₀.left, ∀ (U : Over S) (j : U ⟶ U₀),
      _root_.AlgebraicGeometry.IsClosedImmersion j.left → Set.range j.left ⊆ Z →
      ∀ (Y : AlgebraicSpace S) (f : (schemeToSpace S).obj U ⟶ Y), IsQuasiCompact Y →
        IsQuasiSeparated Y → IsFinite (hom f) → IsSurjective (hom f) →
        ∃ P : Over S, PointTopology.HasFiniteAffineNeighborhoods P.left ∧
          Nonempty ((schemeYoneda S).obj P ≅ Y.presheaf) by
    refine key ⊤ U₀ (𝟙 U₀) ?_ (fun _ _ => trivial) Y₀ f₀ hY₀ hY₀s hf₀ hf₀s
    rw [Over.id_left]
    infer_instance
  intro Z
  induction Z using WellFoundedLT.induction with
  | _ Z ih => ?_
  intro U j hj hjZ Y f hY hYs hf hfs
  have : U.left.IsQuasiAffine := Scheme.IsQuasiAffine.of_isAffineHom j.left
  have : _root_.AlgebraicGeometry.IsNoetherian U.left := isNoetherian_of_isFinite j.left
  have : QuasiSeparatedSpace U.left :=
    (quasiSeparatedSpace_iff_quasiSeparated U.left).mpr inferInstance
  by_cases hne : Nonempty U.left
  swap
  · refine exists_AF_representation_of_saturated_affine_opens (hom f) hf hfs ?_
    intro F _
    exact ⟨⊥, isAffineOpen_bot _, fun x _ => (hne ⟨x⟩).elim, fun w _ _ _ => (hne ⟨w⟩).elim⟩
  obtain ⟨T⟩ := exists_tupleOrbitCover hf hfs hY hne
  let CC : Closeds U.left := ⟨T.C, T.isClosed_C⟩
  let jC := reducedOverι U CC
  obtain ⟨YT, fT, hYT, hYTs, hfT, hfTs, hfTrel⟩ := hCS S U Y f hY hYs hf hfs
    (reducedOver U CC) jC inferInstance inferInstance (by
      intro u u' h hu
      rw [range_reducedOverι] at hu ⊢
      exact T.saturated_C u u' h hu)
  -- the induction hypothesis on the image of `C`
  have hjj : _root_.AlgebraicGeometry.IsClosedImmersion (jC ≫ j).left := by
    rw [Over.comp_left]
    infer_instance
  let Z' : Closeds U₀.left := ⟨Set.range (jC ≫ j).left,
    (jC ≫ j).left.isClosedEmbedding.isClosed_range⟩
  have hrange : Set.range (jC ≫ j).left = j.left '' T.C := by
    ext y
    constructor
    · rintro ⟨c, rfl⟩
      have hc : jC.left c ∈ Set.range jC.left := ⟨c, rfl⟩
      rw [range_reducedOverι] at hc
      exact ⟨jC.left c, hc, by rw [Over.comp_left, Scheme.Hom.comp_apply]⟩
    · rintro ⟨u, hu, rfl⟩
      have hu' : u ∈ Set.range jC.left := by
        rw [range_reducedOverι]
        exact hu
      obtain ⟨c, rfl⟩ := hu'
      exact ⟨c, by rw [Over.comp_left, Scheme.Hom.comp_apply]⟩
  have hlt : Z' < Z := by
    rw [SetLike.lt_iff_le_and_exists]
    obtain ⟨u, hu⟩ := T.exists_notMem
    refine ⟨fun x hx => ?_, j.left u, hjZ ⟨u, rfl⟩, fun hx => ?_⟩
    · change x ∈ Set.range (jC ≫ j).left at hx
      rw [hrange] at hx
      obtain ⟨c, -, rfl⟩ := hx
      exact hjZ ⟨c, rfl⟩
    · change j.left u ∈ Set.range (jC ≫ j).left at hx
      rw [hrange] at hx
      obtain ⟨c, hc, hcu⟩ := hx
      exact hu (j.left.isClosedEmbedding.injective hcu ▸ hc)
  obtain ⟨PC, hPC, ⟨eC⟩⟩ := ih Z' hlt (reducedOver U CC) (jC ≫ j) hjj le_rfl YT fT hYT hYTs
    hfT hfTs
  -- the morphism from the closed part to its AF representative
  let q₀ : reducedOver U CC ⟶ PC := (schemeYoneda S).preimage (hom fT ≫ eC.inv)
  have hq₀ : (schemeYoneda S).map q₀ = hom fT ≫ eC.inv := Functor.map_preimage _ _
  have hq₀fin : _root_.AlgebraicGeometry.IsFinite q₀.left := by
    refine isFinite_left_of_isFinite_map q₀ ?_
    rw [hq₀]
    exact IsFinite.comp_iso hfT eC.symm
  refine exists_af_of_tupleOrbitCover hf hfs T hPC q₀ q₀.left.isClosedMap ?_
  intro x x'
  rw [← hfTrel x x', ← sameImage_comp_iso_iff (hom fT) eC.symm x x', Iso.symm_hom]
  have h := sameImage_map_iff q₀ x x'
  rw [hq₀] at h
  exact h

end Induction

end Langlands.AlgebraicGeometry.AlgebraicSpace
