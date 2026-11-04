import Langlands.GroupScheme.CentralIsogeny.Uniqueness
import Langlands.GroupScheme.ConjugacyBaseChange
import Langlands.GroupScheme.Torus.Geometry
import Langlands.GroupScheme.Torus.SplittingAssembly
import Langlands.GroupScheme.Torus.MaximalBaseChangeForwardReduction
import Langlands.GroupScheme.Absolute.QuotientNormalizer
import Langlands.GroupScheme.Absolute.RationalSubgroupContainment
import Langlands.GroupScheme.ImageGenerationDominant

/-! # Closed containment of torus centralizers under finite surjective maps -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k]

/-- A base-field point centralizes a torus if its image under a finite
homomorphism centralizes the composite torus homomorphism. -/
theorem mem_torusCentralizer_of_finiteHom
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (q : G ⟶ H) [IsFinite q.hom.hom.left]
    (hT : IsTorus T.toGrp) (t : T.toGrp ⟶ G)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (hg : g ≫ q.hom.hom ∈ (torusCentralizer (t ≫ q)).carrier _) :
    g ∈ (torusCentralizer t).carrier _ := by
  have : Smooth T.toGrp.X.hom := hT.smooth
  have : IsAffine T.toGrp.X.left := SplittingAssembly.isAffine_of_isTorus T.toGrp hT
  have : IsAffineHom T.toGrp.X.hom := inferInstance
  have : ConnectedSpace T.toGrp.X.left := hT.connectedSpace
  apply (mem_torusCentralizer_base_iff t g).mpr
  apply finiteHom_cancel q
  rw [Category.assoc, innerIso_hom_comp, ← Category.assoc]
  exact (mem_torusCentralizer_base_iff (t ≫ q) (g ≫ q.hom.hom)).mp hg

namespace SubgroupFunctor

/-- Closed containment of group homomorphisms is reflected by a field extension,
including for nonreduced sources and closed targets. -/
theorem range_le_of_fieldExtension
    (K : Type u) [Field K] [Algebra k K]
    {A D G : GroupScheme (Spec (CommRingCat.of k))}
    (a : A ⟶ G) (d : D ⟶ G) (hd : IsClosedSubgroup d)
    (h : range ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map a) ≤
      range ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map d)) :
    range a ≤ range d := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let B := GroupScheme.baseChange b
  let V := (Over.map b).obj (B.obj A).X
  let p : V ⟶ A.X := baseChangePointsEquiv b A (B.obj A).X (𝟙 _)
  have : Surjective b := (fieldExtension_fpqc k K).1
  have : IsSchemeTheoreticallyDominant b :=
    IsSchemeTheoreticallyDominant.of_isDominant b
  have : IsSchemeTheoreticallyDominant p.left := by
    change IsSchemeTheoreticallyDominant (pullback.fst A.X.hom b)
    infer_instance
  have : IsClosedImmersion d.hom.hom.left := hd
  have hid : (B.map a).hom.hom ∈ (range (B.map a)).carrier (B.obj A).X :=
    mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨v, hv⟩ := mem_range.mp (h _ hid)
  let v' : V ⟶ D.X := baseChangePointsEquiv b D (B.obj A).X v
  have he : p ≫ a.hom.hom = v' ≫ d.hom.hom := by
    have hh := congrArg (baseChangePointsEquiv b G (B.obj A).X) hv
    rw [baseChangePointsEquiv_comp] at hh
    have hp := baseChangePointsEquiv_comp b a (B.obj A).X (𝟙 _)
    simpa only [Category.id_comp] using (hh.trans hp).symm
  obtain ⟨s, hs⟩ := exists_over_factor_of_schematic_precomp
    d.hom.hom p a.hom.hom v' he
  intro U x hx
  obtain ⟨y, rfl⟩ := mem_range.mp hx
  exact mem_range.mpr ⟨y ≫ s, by rw [Category.assoc, hs]⟩

end SubgroupFunctor

section AlgebraicallyClosed

variable [IsAlgClosed k]
    {G H C C' D : GroupScheme (Spec (CommRingCat.of k))}
    {T S : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Over an algebraically closed field, every closed subgroup containing the
image of the source torus centralizer also contains the smooth target torus
centralizer, provided the ambient finite surjection lifts the torus map. -/
theorem range_torusCentralizer_le_of_finiteSurjective_algClosed
    (q : G ⟶ H) [IsFinite q.hom.hom.left] [Surjective q.hom.hom.left]
    (hT : IsTorus T.toGrp) (t : T.toGrp ⟶ G) (s : S.toGrp ⟶ H)
    (f : T.toGrp ⟶ S.toGrp) (hcomm : t ≫ q = f ≫ s)
    (c : C ⟶ G) (hc : (torusCentralizer t).IsRepresentedBy c)
    (c' : C' ⟶ H) (hc' : (torusCentralizer s).IsRepresentedBy c')
    [IsReduced C'.X.left] [LocallyOfFiniteType C'.X.hom]
    (d : D ⟶ H) (hd : IsClosedSubgroup d)
    (hle : SubgroupFunctor.range (c ≫ q) ≤ SubgroupFunctor.range d) :
    SubgroupFunctor.range c' ≤ SubgroupFunctor.range d := by
  apply SubgroupFunctor.range_le_of_algClosed_points hd
  intro x hx
  have hxcent : x ∈ (torusCentralizer s).carrier _ := by
    rw [← hc'.2]
    exact hx
  obtain ⟨g, hg⟩ := exists_rationalPointLift q x
  have hgcent : g ∈ (torusCentralizer t).carrier _ := by
    apply mem_torusCentralizer_of_finiteHom q hT t g
    rw [hg, hcomm]
    intro V a y
    simpa only [Grp.comp_hom_hom, Category.assoc] using
      hxcent V a (y ≫ f.hom.hom)
  rw [← hc.2] at hgcent
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hgcent
  apply hle
  apply SubgroupFunctor.mem_range.mpr
  refine ⟨y, ?_⟩
  rw [Grp.comp_hom_hom, ← Category.assoc, hy, hg]

end AlgebraicallyClosed

section ArbitraryField

variable {G H C C' D : GroupScheme (Spec (CommRingCat.of k))}
    {T S : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Closed containment of torus centralizers under a finite surjective ambient
homomorphism, over an arbitrary field. Only the target centralizer must be smooth. -/
theorem range_torusCentralizer_le_of_finiteSurjective
    (q : G ⟶ H) [IsFinite q.hom.hom.left] [Surjective q.hom.hom.left]
    (hT : IsTorus T.toGrp) (t : T.toGrp ⟶ G) (s : S.toGrp ⟶ H)
    (f : T.toGrp ⟶ S.toGrp) (hcomm : t ≫ q = f ≫ s)
    (c : C ⟶ G) (hc : (torusCentralizer t).IsRepresentedBy c)
    (c' : C' ⟶ H) (hc' : (torusCentralizer s).IsRepresentedBy c')
    [Smooth C'.X.hom]
    (d : D ⟶ H) (hd : IsClosedSubgroup d)
    (hle : SubgroupFunctor.range (c ≫ q) ≤ SubgroupFunctor.range d) :
    SubgroupFunctor.range c' ≤ SubgroupFunctor.range d := by
  let b := toAlgebraicClosure k
  let B := GroupScheme.baseChange b
  have : IsFinite (B.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @IsFinite) b q.hom.hom inferInstance
  have : Surjective (B.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Surjective) b q.hom.hom inferInstance
  have : Smooth (B.obj C').X.hom :=
    MorphismProperty.pullback_snd C'.X.hom b inferInstance
  have : IsReduced (B.obj C').X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      (AlgebraicClosure k) (B.obj C').X.left (B.obj C').X.hom
  have hcK := hc.baseChange b
  rw [← torusCentralizer_baseChange b t] at hcK
  have hcK' := hc'.baseChange b
  rw [← torusCentralizer_baseChange b s] at hcK'
  apply SubgroupFunctor.range_le_of_fieldExtension (AlgebraicClosure k) c' d hd
  apply range_torusCentralizer_le_of_finiteSurjective_algClosed
    (k := AlgebraicClosure k) (G := B.obj G) (H := B.obj H)
    (C := B.obj C) (C' := B.obj C') (D := B.obj D)
    (T := (CommGroupScheme.baseChange b).obj T)
    (S := (CommGroupScheme.baseChange b).obj S)
    (B.map q) (hT.baseChange (K := AlgebraicClosure k)) (B.map t) (B.map s) (B.map f)
    (by rw [← B.map_comp, ← B.map_comp, hcomm])
    (B.map c) hcK (B.map c') hcK' (B.map d) (hd.baseChange b)
  rw [← B.map_comp, SubgroupFunctor.range_baseChangeHom,
    SubgroupFunctor.range_baseChangeHom]
  exact fun U x hx => hle _ hx

/-- Factor the smooth target torus centralizer through any closed subgroup
containing the image of the source torus centralizer. -/
def torusCentralizerImageFactor
    (q : G ⟶ H) [IsFinite q.hom.hom.left] [Surjective q.hom.hom.left]
    (hT : IsTorus T.toGrp) (t : T.toGrp ⟶ G) (s : S.toGrp ⟶ H)
    (f : T.toGrp ⟶ S.toGrp) (hcomm : t ≫ q = f ≫ s)
    (c : C ⟶ G) (hc : (torusCentralizer t).IsRepresentedBy c)
    (c' : C' ⟶ H) (hc' : (torusCentralizer s).IsRepresentedBy c')
    [Smooth C'.X.hom]
    (d : D ⟶ H) (hd : IsClosedSubgroup d)
    (hle : SubgroupFunctor.range (c ≫ q) ≤ SubgroupFunctor.range d) : C' ⟶ D := by
  have : IsClosedImmersion d.hom.hom.left := hd
  have hr : (SubgroupFunctor.range d).IsRepresentedBy d :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  exact hr.factorHom c'
    (range_torusCentralizer_le_of_finiteSurjective q hT t s f hcomm c hc c' hc' d hd hle)

/-- The centralizer factor has the prescribed composite with the closed inclusion. -/
theorem torusCentralizerImageFactor_comp
    (q : G ⟶ H) [IsFinite q.hom.hom.left] [Surjective q.hom.hom.left]
    (hT : IsTorus T.toGrp) (t : T.toGrp ⟶ G) (s : S.toGrp ⟶ H)
    (f : T.toGrp ⟶ S.toGrp) (hcomm : t ≫ q = f ≫ s)
    (c : C ⟶ G) (hc : (torusCentralizer t).IsRepresentedBy c)
    (c' : C' ⟶ H) (hc' : (torusCentralizer s).IsRepresentedBy c')
    [Smooth C'.X.hom]
    (d : D ⟶ H) (hd : IsClosedSubgroup d)
    (hle : SubgroupFunctor.range (c ≫ q) ≤ SubgroupFunctor.range d) :
    torusCentralizerImageFactor q hT t s f hcomm c hc c' hc' d hd hle ≫ d = c' := by
  exact SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

end ArbitraryField

end Langlands.GroupScheme
