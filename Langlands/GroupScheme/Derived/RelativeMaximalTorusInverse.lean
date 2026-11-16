import Langlands.GroupScheme.Torus.RelativeCentralizerDescent
import Langlands.GroupScheme.Torus.CommutativeReductive
import Langlands.GroupScheme.Torus.RelativeReductive
import Langlands.GroupScheme.Torus.RelativeCommutativity
import Langlands.GroupScheme.Torus.MaximalSelfCentralizing
import Langlands.GroupScheme.Torus.SplitOfDomination
import Langlands.GroupScheme.Torus.Products
import Langlands.GroupScheme.SimplyConnected.CoverPreimageToolkit
import Langlands.GroupScheme.Reductive.CentralProductParabolicInverse
import Langlands.AbelianScheme.IsogenyInverse

/-! # Extending relative maximal tori through a central product -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

/-- An isogeny from a commutative group scheme has commutative target. -/
theorem IsIsogeny.isCommMonObj_of_source
    {S : Scheme.{u}} {A H : GroupScheme S} [IsCommMonObj A.X]
    {f : A ⟶ H} (hf : IsIsogeny f) : IsCommMonObj H.X := by
  let : Epi (f.hom.hom ⊗ₘ f.hom.hom) := hf.epi_tensorHom
  refine ⟨?_⟩
  apply (cancel_epi (f.hom.hom ⊗ₘ f.hom.hom)).mp
  rw [BraidedCategory.braiding_naturality_assoc, ← IsMonHom.mul_hom,
    IsCommMonObj.mul_comm_assoc]

/-- A smooth affine isogeny image of a torus over a field is a torus. -/
theorem IsTorus.of_isogeny_from_torus
    {k : Type u} [Field k]
    {A H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] (hA : IsTorus A) (hH : Smooth H.X.hom)
    (f : A ⟶ H) (hf : IsIsogeny f) : IsTorus H := by
  obtain ⟨K, hK, aK, hsplit⟩ := hA
  let : Field K := hK
  let : Algebra k K := aK
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let B := GroupScheme.baseChange b
  let : IsAffineHom (B.obj H).X.hom :=
    MorphismProperty.pullback_snd H.X.hom b inferInstance
  let : Smooth (B.obj H).X.hom := MorphismProperty.pullback_snd H.X.hom b hH
  let : IsReduced (B.obj H).X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      K (B.obj H).X.left (B.obj H).X.hom
  have hfB : IsIsogeny (B.map f) := hf.baseChange b
  let : IsFinite (B.map f).hom.hom.left := hfB.1
  let : Surjective (B.map f).hom.hom.left := hfB.2.2
  have hd : IsSchemeTheoreticallyDominant (B.map f).hom.hom.left :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  exact ⟨K, hK, aK, hsplit.of_schematicallyDominant_hom (B.map f) hd⟩

/-- A smooth relatively affine isogeny image of a product of two relative
 tori is a relative torus. -/
theorem relativeTorus_of_smooth_isogeny_from_product
    {S : Scheme.{u}} {A B H : GroupScheme S}
    (hA : RelativeTorus.IsTorus A) (hB : RelativeTorus.IsTorus B)
    [IsAffineHom H.X.hom] (hH : Smooth H.X.hom)
    (f : A ⊗ B ⟶ H) (hf : IsIsogeny f) : RelativeTorus.IsTorus H := by
  let : IsCommMonObj A.X := hA.isCommMonObj
  let : IsCommMonObj B.X := hB.isCommMonObj
  let : IsCommMonObj (A ⊗ B).X := by
    apply (isCommMonObj_iff_isMulCommutative _).2
    intro U
    refine ⟨⟨fun x y => ?_⟩⟩
    apply (productPointsEquiv A B U).injective
    simp only [map_mul]
    exact mul_comm _ _
  let Hc : CommGroupScheme S := { H with comm := hf.isCommMonObj_of_source }
  apply relativeTorus_of_commutative_reductive Hc
  refine ⟨hH, inferInstance, fun s => ?_⟩
  let b := geometricPoint S s
  let F := GroupScheme.baseChange b
  let : IsAffineHom (F.obj H).X.hom :=
    MorphismProperty.pullback_snd H.X.hom b inferInstance
  have hAB : IsTorus (F.obj (A ⊗ B)) :=
    IsTorus.of_iso (baseChangeTensorIso b A B)
      ((hA.baseChange b).isTorus.tensor (hB.baseChange b).isTorus)
  have hHT := hAB.of_isogeny_from_torus
    (MorphismProperty.pullback_snd H.X.hom b hH) (F.map f) (hf.baseChange b)
  exact hHT.isConnectedReductive_of_fieldSplitting.isPseudoReductive

namespace RelativeDerivedTorus

/-- Under a supplied central-product isogeny, every relative maximal torus
of the closed reductive factor extends to a relative maximal torus of the
ambient reductive group, with the prescribed product and full intersection. -/
theorem exists_extension
    {S : Scheme.{u}} {G D Z : GroupScheme S}
    (hG : IsReductive G) (hD : IsReductive D)
    (z : Z ⟶ G) (hz : IsCentral z) (hZ : RelativeTorus.IsTorus Z)
    (d : D ⟶ G) (hd : IsClosedSubgroup d)
    (hprod : IsCentralIsogeny (prodHom z d (hz.commute_values _)))
    {A : CommGroupScheme S} (a : A.toGrp ⟶ D)
    (hA : RelativeTorus.IsTorus A.toGrp) (ha : IsClosedSubgroup a)
    (hmax : IsFibrewiseMaximalTorus a) :
    ∃ (T : CommGroupScheme S) (t : T.toGrp ⟶ G) (e : Z ⊗ A.toGrp ⟶ T.toGrp),
      RelativeTorus.IsTorus T.toGrp ∧ IsClosedSubgroup t ∧
      IsFibrewiseMaximalTorus t ∧ IsIsogeny e ∧
      e ≫ t = prodHom z (a ≫ d) (hz.commute_values _) ∧
      SubgroupFunctor.range (subgroupIntersectionFst d t) = SubgroupFunctor.range a := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsClosedImmersion d.hom.hom.left := hd
  let : Mono d.hom.hom := Over.mono_of_mono_left _
  let : IsClosedImmersion a.hom.hom.left := ha
  let : Mono a.hom.hom := Over.mono_of_mono_left _
  obtain ⟨C, c, hc, hC, hrep⟩ :=
    relativeTorusCentralizer_hasSmoothClosedRepresentative (a ≫ d) hA hG.smooth
  let : Mono c.hom.hom := hrep.1
  let : IsClosedImmersion c.hom.hom.left := hc
  let : IsAffineHom C.X.hom := by
    have : IsAffineHom c.hom.hom.left := inferInstance
    rw [← Over.w c.hom.hom]
    infer_instance
  have hZi : SubgroupFunctor.range z ≤ SubgroupFunctor.range c := by
    rw [hrep.2]
    exact ((isCentral_iff_range_le_center z).mp hz).trans
      (center_le_torusCentralizer (a ≫ d))
  have hInt : SubgroupFunctor.range (subgroupIntersectionFst d c) =
      SubgroupFunctor.range a := by
    rw [range_subgroupIntersectionFst_eq_comap, hrep.2,
      torusCentralizer_comp_comap_of_mono]
    exact relativeTorusCentralizer_eq_range_of_fibrewiseMaximal hD hA a ha hmax
  obtain ⟨e, he, hec⟩ := exists_centralIsogeny_of_intersection_range_eq
    z hz d hprod c hZi a hInt
  have hCT : RelativeTorus.IsTorus C :=
    relativeTorus_of_smooth_isogeny_from_product hZ hA hC e he.isIsogeny
  let T : CommGroupScheme S := { C with comm := hCT.isCommMonObj }
  let f : A.toGrp ⟶ T.toGrp := hrep.factorHom (a ≫ d) (range_le_torusCentralizer (a ≫ d))
  have hf : f ≫ c = a ≫ d := hrep.factorHom_comp _ _
  have hf' : f.hom.hom ≫ c.hom.hom = a.hom.hom ≫ d.hom.hom :=
    congrArg (fun g : A.toGrp ⟶ G => g.hom.hom) hf
  have hself : torusCentralizer (T := T) c = SubgroupFunctor.range c := by
    apply le_antisymm ?_ (range_le_torusCentralizer (T := T) c)
    rw [hrep.2]
    intro U x hx V b s
    have hh := hx V b (s ≫ f.hom.hom)
    simpa only [Grp.comp_hom_hom, Category.assoc, hf'] using hh
  have hCmax : IsFibrewiseMaximalTorus (T := T) c := by
    intro s
    let b := S.fromSpecResidueField s
    apply isMaximalTorus_of_torusCentralizer_eq
      (T := (CommGroupScheme.baseChange b).obj T)
      (hCT.baseChange b).isTorus (hc.baseChange b)
    rw [torusCentralizer_baseChange b (T := T) c, hself,
      SubgroupFunctor.range_baseChangeHom]
  exact ⟨T, c, e, hCT, hc, hCmax, he.isIsogeny, hec, hInt⟩

/-- A chosen extension torus, inclusion, and product isogeny, together with
the full intersection and maximality properties. -/
def extensionModel
    {S : Scheme.{u}} {G D Z : GroupScheme S}
    (hG : IsReductive G) (hD : IsReductive D)
    (z : Z ⟶ G) (hz : IsCentral z) (hZ : RelativeTorus.IsTorus Z)
    (d : D ⟶ G) (hd : IsClosedSubgroup d)
    (hprod : IsCentralIsogeny (prodHom z d (hz.commute_values _)))
    {A : CommGroupScheme S} (a : A.toGrp ⟶ D)
    (hA : RelativeTorus.IsTorus A.toGrp) (ha : IsClosedSubgroup a)
    (hmax : IsFibrewiseMaximalTorus a) :
    Σ (T : CommGroupScheme S), Σ t : T.toGrp ⟶ G,
      {e : Z ⊗ A.toGrp ⟶ T.toGrp //
        RelativeTorus.IsTorus T.toGrp ∧ IsClosedSubgroup t ∧
        IsFibrewiseMaximalTorus t ∧ IsIsogeny e ∧
        e ≫ t = prodHom z (a ≫ d) (hz.commute_values _) ∧
        SubgroupFunctor.range (subgroupIntersectionFst d t) = SubgroupFunctor.range a} := by
  let h := exists_extension hG hD z hz hZ d hd hprod a hA ha hmax
  exact ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec⟩

end RelativeDerivedTorus

end Langlands.GroupScheme
