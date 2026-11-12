import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianExtensionLocalReduction
import Langlands.AlgebraicGeometry.PointTopology.FiniteExtensionCompletion

/-! # Reducing extension-image closedness through completions -/
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite Topology Filter
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
  (RingPoint ringTest ringTestMap schemePointTopology IsHenselianValuedField
    AlgPoint affineSchemePointEquiv AffineCoordinateRing)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace
namespace ExtensionCompletionReduction

/-- Chart lifts over a field separably closed in an extension descend to that field,
with the chart and space allowed to be defined over a smaller coefficient ring. -/
theorem exists_chart_lift_to_subfield
    {C k L : Type u} [CommRing C] [Field k] [Field L]
    [Algebra C k] [Algebra C L] [Algebra k L] [IsScalarTower C k L]
    (hsep : separableClosure k L = ⊥)
    {X : AlgebraicSpace (Spec (CommRingCat.of C))}
    {U : Over (Spec (CommRingCat.of C))}
    (a : (schemeYoneda _).obj U ⟶ X.presheaf) (ha : IsEtale a)
    (η : RingPoint C U L) (y : RingPoints C X k)
    (h : RingPoints.map (homMk a) ((schemeRingPointsEquiv C U L).symm η) =
      RingPoints.changeRing (IsScalarTower.toAlgHom C k L) y) :
    ∃ v : RingPoint C U k,
      PointTopology.RingPoint.changeRing (IsScalarTower.toAlgHom C k L) v = η := by
  obtain ⟨V, b, -, hb, v, hv⟩ := FieldPointEtaleLift.exists_affine_etale_point X y
  have h' : a.app (op (ringTest C L)) (ULift.up η) =
      (hom b).app (op (ringTest C L))
        (ULift.up (PointTopology.RingPoint.changeRing (IsScalarTower.toAlgHom C k L) v)) := by
    change RingPoints.map (homMk a) ((schemeRingPointsEquiv C U L).symm η) = RingPoints.map b _
    rw [h, ← hv, RingPoints.changeRing_map]
    rfl
  let hr := X.representable_from_scheme a
  let W := hr.pullback (hom b)
  let q : W ⟶ U := Functor.relativelyRepresentable.fst' hr (hom b)
  let p : W ⟶ V := hr.snd (hom b)
  have hsq : IsPullback ((schemeYoneda _).map q) ((schemeYoneda _).map p) a (hom b) :=
    Functor.relativelyRepresentable.isPullback' hr (hom b)
  obtain ⟨w, hw₁, hw₂⟩ := exists_app_of_isPullback hsq
    (ringTest C L) (ULift.up η) (ULift.up _) h'
  let w' : RingPoint C W L := w.down
  have he₁ : w' ≫ q = η := congrArg ULift.down hw₁
  have he₂ : w' ≫ p =
      PointTopology.RingPoint.changeRing (IsScalarTower.toAlgHom C k L) v :=
    congrArg ULift.down hw₂
  have : Etale p.left := ha.projection (hom b) _ p hsq
  have hleft : w'.left ≫ p.left =
      Spec.algebraMap k L ≫ v.left := congrArg Over.Hom.left he₂
  obtain ⟨l, hl⟩ := PointTopology.exists_lift_of_formallyUnramified
    p.left k L hsep w'.left v.left hleft
  let f := l ≫ q.left
  have hf : Spec.algebraMap k L ≫ f = η.left := by
    dsimp only [f]
    rw [← Category.assoc, hl]
    exact congrArg Over.Hom.left he₁
  have : Flat (Spec.algebraMap k L) := inferInstanceAs (Flat (specOver k L).hom)
  have : Surjective (Spec.algebraMap k L) := inferInstanceAs (Surjective (specOver k L).hom)
  have : Epi (Spec.algebraMap k L) := Flat.epi_of_flat_of_surjective _
  have hbase : f ≫ U.hom = Spec.algebraMap C k := by
    apply (cancel_epi (Spec.algebraMap k L)).mp
    rw [← Category.assoc, hf]
    exact (Over.w η).trans (specAlgebraMap_comp C k L).symm
  refine ⟨Over.homMk f hbase, Over.OverMorphism.ext hf⟩

/-- A point of L whose completed image lies in the completed base field lies in K,
provided K is closed in L. -/
theorem mem_range_of_completion_eq
    {K L : Type u} [NontriviallyNormedField K] [NontriviallyNormedField L]
    [NormedAlgebra K L] (hclosed : IsClosed (Set.range (algebraMap K L)))
    (a : UniformSpace.Completion K) (b : L)
    (h : PointTopology.FiniteExtensionCompletion.map K L a =
      (b : UniformSpace.Completion L)) : b ∈ Set.range (algebraMap K L) := by
  have hmem := mem_closure_image
    (PointTopology.FiniteExtensionCompletion.isometry_map K L).continuous.continuousAt
    (UniformSpace.Completion.denseRange_coe a)
  have heq : PointTopology.FiniteExtensionCompletion.map K L ''
        Set.range ((↑) : K → UniformSpace.Completion K) =
      ((↑) : L → UniformSpace.Completion L) '' Set.range (algebraMap K L) := by
    ext z
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨algebraMap K L x, ⟨x, rfl⟩, (PointTopology.FiniteExtensionCompletion.map_coe K L x).symm⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨(x : UniformSpace.Completion K), ⟨x, rfl⟩,
        PointTopology.FiniteExtensionCompletion.map_coe K L x⟩
  rw [h, heq] at hmem
  have hb : b ∈ closure (Set.range (algebraMap K L)) := by
    rw [(UniformSpace.Completion.isUniformEmbedding_coe L).isEmbedding.isInducing.closure_eq_preimage_closure_image]
    exact hmem
  rwa [hclosed.closure_eq] at hb

/-- The completed base-field inclusion, as an algebra map over the original base. -/
def completedBaseAlgHom (K L : Type u) [NontriviallyNormedField K]
    [NontriviallyNormedField L] [NormedAlgebra K L] :
    UniformSpace.Completion K →ₐ[K] UniformSpace.Completion L where
  __ := PointTopology.FiniteExtensionCompletion.map K L
  commutes' c := PointTopology.FiniteExtensionCompletion.map_coe K L c

/-- Affine points in both the completed base and the original extension descend to the
closed base field, coordinate by coordinate. -/
theorem exists_affine_point_of_completion_eq
    {K L A : Type u} [NontriviallyNormedField K] [NontriviallyNormedField L]
    [NormedAlgebra K L] [CommRing A] [Algebra K A]
    (hclosed : IsClosed (Set.range (algebraMap K L)))
    (p : AlgPoint K A (UniformSpace.Completion K)) (q : AlgPoint K A L)
    (h : ∀ a : A, PointTopology.FiniteExtensionCompletion.map K L (p a) =
      (q a : UniformSpace.Completion L)) :
    ∃ r : AlgPoint K A K, AlgPoint.mapCoefficients (Algebra.ofId K L) r = q := by
  have hq : q ∈ ⋂ a : A, {p : AlgPoint K A L | p a ∈ Set.range (Algebra.ofId K L)} := by
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact fun a => mem_range_of_completion_eq hclosed (p a) (q a) (h a)
  rw [← AlgPoint.range_mapCoefficients (Algebra.ofId K L) (algebraMap K L).injective] at hq
  exact hq

/-- The intersection of the completed-base rational locus and the original-extension
rational locus is the original-base rational locus when the base is closed. -/
theorem exists_point_of_completion_eq
    {K L : Type u} [NontriviallyNormedField K] [NontriviallyNormedField L]
    [NormedAlgebra K L] (hL : IsHenselianValuedField L)
    (hclosed : IsClosed (Set.range (algebraMap K L)))
    {X : AlgebraicSpace (Spec (CommRingCat.of K))} (hs : IsSeparated X)
    (x : RingPoints K X (UniformSpace.Completion K)) (z : RingPoints K X L)
    (h : RingPoints.changeRing (completedBaseAlgHom K L) x =
      RingPoints.changeRing (PointTopology.FiniteExtensionCompletion.coeAlgHom K L) z) :
    ∃ y : RingPoints K X K, RingPoints.changeRing (Algebra.ofId K L) y = z := by
  let Lc := UniformSpace.Completion L
  let Kc := UniformSpace.Completion K
  obtain ⟨U, a, hU, ha, v, hv⟩ := FieldPointEtaleLift.exists_affine_etale_point X x
  let := hU
  let v' := PointTopology.RingPoint.changeRing (completedBaseAlgHom K L) v
  have hv' : RingPoints.map a ((schemeRingPointsEquiv K U Lc).symm v') =
      RingPoints.changeRing (PointTopology.FiniteExtensionCompletion.coeAlgHom K L) z := by
    rw [← h, ← hv, RingPoints.changeRing_map]
    rfl
  obtain ⟨w, hw⟩ := exists_chart_lift_to_subfield
    (PointTopology.separableClosure_completion_eq_bot L hL) (hom a) ha v' z hv'
  change PointTopology.RingPoint.changeRing
    (PointTopology.FiniteExtensionCompletion.coeAlgHom K L) w = v' at hw
  have heq := congrArg (affineSchemePointEquiv K U Lc) hw
  change affineSchemePointEquiv K U Lc
      (PointTopology.RingPoint.changeRing (PointTopology.FiniteExtensionCompletion.coeAlgHom K L) w) =
    affineSchemePointEquiv K U Lc
      (PointTopology.RingPoint.changeRing (completedBaseAlgHom K L) v) at heq
  rw [PointTopology.affineSchemePointEquiv_changeRing,
    PointTopology.affineSchemePointEquiv_changeRing] at heq
  obtain ⟨r, hr⟩ := exists_affine_point_of_completion_eq hclosed
    (affineSchemePointEquiv K U Kc v) (affineSchemePointEquiv K U L w)
    (fun b => (congrArg (fun p : AlgPoint K (AffineCoordinateRing K U) Lc => p b) heq).symm)
  let u : RingPoint K U K := (affineSchemePointEquiv K U K).symm r
  have huw : PointTopology.RingPoint.changeRing (Algebra.ofId K L) u = w := by
    apply (affineSchemePointEquiv K U L).injective
    rw [PointTopology.affineSchemePointEquiv_changeRing, Equiv.apply_symm_apply]
    exact hr
  have hwz : RingPoints.map a ((schemeRingPointsEquiv K U L).symm w) = z := by
    apply RelativeIntegralPoints.changeRing_injective hs
      (PointTopology.FiniteExtensionCompletion.coeAlgHom K L)
      (UniformSpace.Completion.coe_injective L)
    rw [RingPoints.changeRing_map]
    change RingPoints.map a ((schemeRingPointsEquiv K U Lc).symm
      (PointTopology.RingPoint.changeRing (PointTopology.FiniteExtensionCompletion.coeAlgHom K L) w)) = _
    rw [hw]
    exact hv'
  refine ⟨RingPoints.map a ((schemeRingPointsEquiv K U K).symm u), ?_⟩
  rw [RingPoints.changeRing_map]
  change RingPoints.map a ((schemeRingPointsEquiv K U L).symm
    (PointTopology.RingPoint.changeRing (Algebra.ofId K L) u)) = _
  rw [huw, hwz]

end ExtensionCompletionReduction
end Langlands.AlgebraicGeometry.AlgebraicSpace
