import Langlands.AlgebraicGeometry.AlgebraicSpace.AFDescentOpenCharts
import Mathlib.AlgebraicGeometry.Properties

/-! # Finite-set AF descent conditional on quasi-affine-source AF descent -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.AFDescentFiniteSets

open OpenSubfunctorLifting OpenSubspaceGeometry FiniteAffineUniversalNeighborhoods
  AFDescentOpenCharts

/-- A chosen compact open neighborhood of a finite point set inside a specified
scheme open, without an AF hypothesis on the scheme. -/
def compactNeighborhood {X : Scheme.{u}} (E : Set X) (hE : E.Finite)
    (W : X.Opens) (hEW : E ⊆ W) :
    {V : X.Opens // IsCompact (V : Set X) ∧ E ⊆ V ∧ V ≤ W} :=
  let h := PrespectralSpace.exists_isCompact_and_isOpen_between hE.isCompact W.2 hEW
  ⟨⟨h.choose, h.choose_spec.2.1⟩,
    h.choose_spec.1, h.choose_spec.2.2.1, h.choose_spec.2.2.2⟩

variable {R : Type u} [CommRing R]
variable {U P : Over (Spec (CommRingCat.of R))}
  {Y : AlgebraicSpace (Spec (CommRingCat.of R))}

/-- Any representing scheme has AF, conditional on the explicit
quasi-affine-source descent proposition. -/
theorem hasFiniteAffineNeighborhoods_of_representation
    (hcore : FiniteSurjectiveQuasiAffineSourceAFStatement.{u})
    (π : (schemeYoneda _).obj U ⟶ Y.presheaf)
    (hπ : IsFinite π) (hs : IsSurjective π)
    (hU : PointTopology.HasFiniteAffineNeighborhoods U.left)
    (hY : IsQuasiSeparated Y) (e : (schemeYoneda _).obj P ≅ Y.presheaf) :
    PointTopology.HasFiniteAffineNeighborhoods P.left := by
  let f : U ⟶ P := (schemeYoneda _).preimage (π ≫ e.inv)
  have hf : (schemeYoneda _).map f = π ≫ e.inv :=
    Functor.map_preimage _ _
  have hfe : (schemeYoneda _).map f ≫ e.hom = π := by
    rw [hf]
    simp
  have hfr : IsFinite ((schemeYoneda _).map f) := by
    rw [hf]
    exact (MorphismProperty.cancel_right_of_respectsIso
      ((MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsFinite.{u})
        (Over.forget _)).relative (schemeYoneda _)) π e.inv).mpr hπ
  let : _root_.AlgebraicGeometry.IsFinite f.left :=
    MorphismProperty.of_relative_map
      (P := MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsFinite.{u})
        (Over.forget _)) (F := schemeYoneda _) hfr
  intro E hE
  obtain ⟨V, hV⟩ := hU (f.left ⁻¹' E) (f.left.finite_preimage hE)
  let W₀ := OpenSubfunctorDescent.universalOpen f (affineOpenInclusion V)
    f.left.isClosedMap
  have hEW₀ : E ⊆ W₀ := by
    intro x hx
    change x ∉ f.left '' (Set.range (affineOpenInclusion V).left)ᶜ
    rintro ⟨z, hz, hzx⟩
    apply hz
    change z ∈ Set.range V.val.ι
    rw [Scheme.Opens.range_ι]
    apply hV
    change f.left z ∈ E
    rwa [hzx]
  let N := compactNeighborhood E hE W₀ hEW₀
  let W : P.left.Opens := N.val
  have hWc : IsCompact (W : Set P.left) := N.property.1
  have hEW : E ⊆ W := N.property.2.1
  have hWW₀ : W ≤ W₀ := N.property.2.2
  have hWsource : f.left ⁻¹' (W : Set P.left) ⊆ V.val := by
    intro z hz
    by_contra hzV
    have hn := hWW₀ hz
    change f.left z ∉ f.left '' (Set.range (affineOpenInclusion V).left)ᶜ at hn
    apply hn
    refine ⟨z, ?_, rfl⟩
    change z ∉ Set.range V.val.ι
    rw [Scheme.Opens.range_ι]
    exact hzV
  let Q : Over (Spec (CommRingCat.of R)) := Over.mk (W.ι ≫ P.hom)
  let i : Q ⟶ P := Over.homMk W.ι
  let b := (schemeYoneda _).map i ≫ e.hom
  have hb : IsOpenImmersion b :=
    (AffineOpenSubfunctors.isOpenImmersion_schemeYoneda_map i
      (inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion W.ι))).comp_iso e
  let : Mono b := SliceOpenGluing.open_mono hb
  let A := Subfunctor.range b
  have hA : IsOpenImmersion A.ι := range_open b hb
  let eQ : (schemeYoneda _).obj Q ≅ A.toFunctor := asIso (Subfunctor.toRange b)
  let : CompactSpace Q.left := isCompact_iff_compactSpace.mp hWc
  have hAc : IsQuasiCompact (openSubspace Y A hA) :=
    (IsQuasiCompact.of_scheme Q).of_iso eQ
  have hAV : A ≤ universalAffineOpen π V := by
    apply (universalImage_le_iff π _ A).mpr
    change (Subfunctor.range b).preimage π ≤
      Subfunctor.range ((schemeYoneda _).map (affineOpenInclusion V))
    rintro Z ⟨g⟩ ⟨⟨t⟩, ht⟩
    have hti : t ≫ i = g ≫ f := by
      apply ULift.up_injective
      apply (CategoryTheory.mono_iff_injective (e.hom.app Z)).mp inferInstance
      change b.app Z (ULift.up t) =
        ((schemeYoneda _).map f ≫ e.hom).app Z (ULift.up g)
      rw [hfe]
      exact ht
    have hg : Set.range g.left ⊆ Set.range (affineOpenInclusion V).left := by
      change Set.range g.left ⊆ Set.range V.val.ι
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨z, rfl⟩
      apply hWsource
      change (g ≫ f).left z ∈ W
      rw [← hti]
      exact (t.left z).property
    obtain ⟨l, hl⟩ := (factors_through_open_iff (affineOpenInclusion V) g).mpr hg
    exact ⟨ULift.up l, congrArg ULift.up hl⟩
  let M := openAFModel hcore π hπ hs hY A hA hAc V hAV
  let qIso : M.1.val ≅ Q := (schemeYoneda _).preimageIso (M.2 ≪≫ eQ.symm)
  let : IsIso qIso.hom.left := by
    change IsIso ((Over.forget _).map qIso.hom)
    infer_instance
  let c := qIso.hom ≫ i
  let : _root_.AlgebraicGeometry.IsOpenImmersion c.left := by
    change _root_.AlgebraicGeometry.IsOpenImmersion (qIso.hom.left ≫ W.ι)
    infer_instance
  have hEc : E ⊆ Set.range c.left := by
    intro x hx
    obtain ⟨z, hz⟩ := qIso.hom.left.surjective (show Q.left from ⟨x, hEW hx⟩)
    refine ⟨z, ?_⟩
    change i.left (qIso.hom.left z) = x
    rw [hz]
    rfl
  have hEcfinite : (c.left ⁻¹' E).Finite :=
    hE.preimage c.left.isOpenEmbedding.injective.injOn
  obtain ⟨V', hV'⟩ := M.1.property (c.left ⁻¹' E) hEcfinite
  refine ⟨⟨c.left ''ᵁ V'.val, V'.property.image_of_isOpenImmersion c.left⟩, ?_⟩
  intro x hx
  obtain ⟨z, hz⟩ := hEc hx
  refine ⟨z, hV' ?_, hz⟩
  change c.left z ∈ E
  rwa [hz]

/-- Reduction of the exact full AF-descent proposition to the explicit
quasi-affine-source AF-descent proposition. -/
theorem finiteAffineNeighborhoodsDescent_of_quasiAffineSourceAF
    (hcore : FiniteSurjectiveQuasiAffineSourceAFStatement.{u}) :
    FiniteSurjectiveFiniteAffineNeighborhoodsDescentStatement.{u} := by
  intro R _ U Y f _ hY hU hπ hs
  obtain ⟨P, ⟨e⟩⟩ := AFDescentOpenCharts.exists_representation
    hcore (hom f) hπ hs hU hY
  exact ⟨P, hasFiniteAffineNeighborhoods_of_representation
    hcore (hom f) hπ hs hU hY e, ⟨e⟩⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace.AFDescentFiniteSets
