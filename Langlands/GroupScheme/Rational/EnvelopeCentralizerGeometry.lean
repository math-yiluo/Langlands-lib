import Langlands.GroupScheme.Rational.EnvelopeKernelGeometry
import Langlands.GroupScheme.Torus.CentralizerConnected
import Langlands.GroupScheme.Rational.TorusCentralizerFactorization
import Langlands.GroupScheme.Rational.SemigroupIntersectionGeometry
import Langlands.GroupScheme.SubgroupIntersection

/-! # The centralizer inside an actual sectioned quotient kernel -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Whole-torus centralizers reflect through every monomorphic ambient map. -/
theorem torusCentralizer_eq_comap_of_mono
    {S : Scheme.{u}} {H G : GroupScheme S} {T : CommGroupScheme S}
    (s : T.toGrp ⟶ H) (h : H ⟶ G) [Mono h.hom.hom] :
    torusCentralizer s = (torusCentralizer (s ≫ h)).comap h := by
  ext U x
  change (∀ (V : Over S) (a : V ⟶ U) (t : V ⟶ T.X),
      Commute (a ≫ x) (t ≫ s.hom.hom)) ↔
    ∀ (V : Over S) (a : V ⟶ U) (t : V ⟶ T.X),
      Commute (a ≫ (x ≫ h.hom.hom)) (t ≫ (s ≫ h).hom.hom)
  constructor
  · intro hx V a t
    apply (commute_iff_eq _ _).mpr
    simpa only [MonObj.mul_comp, Category.assoc, Grp.comp_hom_hom] using
      congrArg (fun f => f ≫ h.hom.hom) (hx V a t).eq
  · intro hx V a t
    apply (commute_iff_eq _ _).mpr
    apply (cancel_mono h.hom.hom).mp
    simpa only [MonObj.mul_comp, Category.assoc, Grp.comp_hom_hom] using
      (hx V a t).eq

/-- An actual smooth connected unipotent representative of the torus centralizer
inside the specified full quotient kernel. -/
structure TorusKernelCentralizerData
    {k : Type u} [Field k]
    {G N : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (s : T.toGrp ⟶ G) (n : N ⟶ G) where
  group : GroupScheme (Spec (CommRingCat.of k))
  inclusion : group ⟶ N
  isClosedSubgroup : IsClosedSubgroup inclusion
  represents : ((torusCentralizer s).comap n).IsRepresentedBy inclusion
  smooth : Smooth group.X.hom
  isAffineHom : IsAffineHom group.X.hom
  connectedSpace : ConnectedSpace group.X.left
  isUnipotent : IsUnipotent group

attribute [instance] TorusKernelCentralizerData.smooth
  TorusKernelCentralizerData.isAffineHom TorusKernelCentralizerData.connectedSpace

/-- Build the centralizer inside the same actual full kernel, using the full
centralizer of the torus section and its sectioned quotient. -/
def torusKernelCentralizerData
    {k : Type u} [Field k]
    {G N : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [IsAffineHom N.X.hom] [LocallyOfFiniteType N.X.hom]
    [IsAffineHom T.X.hom]
    (q : G ⟶ T.toGrp) (s : T.toGrp ⟶ G)
    (hT : IsTorus T.toGrp) (hsclosed : IsClosedSubgroup s)
    (hs : s ≫ q = 𝟙 T.toGrp)
    (n : N ⟶ G) [Mono n.hom.hom]
    (hker : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range n)
    (hn : IsClosedSubgroup n) (hN : IsUnipotent N) :
    TorusKernelCentralizerData s n := by
  apply Classical.choice
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hrep := (hasClosedRepresentative_normalizer_centralizer_range s hsclosed).2
  rw [← torusCentralizer_eq_centralizer_range] at hrep
  obtain ⟨Z, z, hzclosed, hzrep⟩ := hrep
  have : IsClosedImmersion z.hom.hom.left := hzclosed
  have : IsAffineHom Z.X.hom := by
    rw [← z.hom.hom.w]
    infer_instance
  have : Smooth Z.X.hom := torusCentralizerSmooth k G T s hT hsclosed Z z hzrep hzclosed
  have : ConnectedSpace Z.X.left := hT.connectedSpace_centralizer s hzrep
  have hsection : torusCentralizerFactor s hzrep ≫ (z ≫ q) = 𝟙 T.toGrp := by
    rw [← Category.assoc, torusCentralizerFactor_comp, hs]
  have hgeom := SectionedSubgroupKernel.smooth_connected z q
    (torusCentralizerFactor s hzrep) hsection
  have hclosed := SectionedSubgroupKernel.closed_toAmbientKernel z n q hker hzclosed hn
  refine ⟨{
    group := kernel (z ≫ q)
    inclusion := SectionedSubgroupKernel.toAmbientKernel z n q hker
    isClosedSubgroup := hclosed
    represents := ⟨?_, ?_⟩
    smooth := hgeom.1
    isAffineHom := SectionedSubgroupKernel.isAffineHom z q
    connectedSpace := hgeom.2
    isUnipotent := SectionedSubgroupKernel.isUnipotent z n q hker hzclosed hn hN }⟩
  · have : IsClosedImmersion
        (SectionedSubgroupKernel.toAmbientKernel z n q hker).hom.hom.left := hclosed
    exact Over.mono_of_mono_left _
  · rw [SectionedSubgroupKernel.range_toAmbientKernel, hzrep.2]

/-- Over a perfect field the constructed centralizer has a finite split series. -/
theorem TorusKernelCentralizerData.isSplitUnipotent
    {k : Type u} [Field k] [PerfectField k]
    {G N : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {s : T.toGrp ⟶ G} {n : N ⟶ G} (d : TorusKernelCentralizerData s n) :
    RelativeRoot.IsSplitUnipotent d.group :=
  perfectFieldUnipotentSplit k d.group d.connectedSpace d.isUnipotent

namespace TorusKernelCentralizerData

section Intersection

variable {k : Type u} [Field k]
    {H G V N : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (sH : T.toGrp ⟶ H) (h : H ⟶ G) [Mono h.hom.hom]
    (v : V ⟶ H) (m : V ⟶ N) (n : N ⟶ G)
    (hm : m ≫ n = v ≫ h)
    (dG : TorusKernelCentralizerData (sH ≫ h) n)

include hm in
/-- The actual intersection with the ambient kernel centralizer represents
the internal kernel centralizer on every test scheme. -/
theorem represents_intersectionFst :
    ((torusCentralizer sH).comap v).IsRepresentedBy
      (subgroupIntersectionFst m dG.inclusion) := by
  have hp := dG.represents.comap_subgroupIntersectionFst dG.isClosedSubgroup m
  have heq : (((torusCentralizer (sH ≫ h)).comap n).comap m) =
      (torusCentralizer sH).comap v := by
    rw [← SubgroupFunctor.comap_comp, hm, SubgroupFunctor.comap_comp,
      ← torusCentralizer_eq_comap_of_mono sH h]
  rwa [heq] at hp

/-- Compare the internal centralizer with the actual scheme-theoretic
intersection in the original ambient kernel. -/
def intersectionIso (dH : TorusKernelCentralizerData sH v) :
    dH.group ≅ subgroupIntersection m dG.inclusion :=
  dH.represents.isoOfIsRepresentedBy
    (represents_intersectionFst sH h v m n hm dG)

/-- The comparison retains the actual inclusion into the restricted kernel. -/
theorem intersectionIso_hom_fst (dH : TorusKernelCentralizerData sH v) :
    (intersectionIso sH h v m n hm dG dH).hom ≫
      subgroupIntersectionFst m dG.inclusion = dH.inclusion :=
  dH.represents.isoOfIsRepresentedBy_hom_comp _

include hm

/-- Smoothness, affineness, connectedness and unipotence concern the actual
scheme-theoretic intersection, not merely an isomorphic chosen subgroup. -/
theorem intersection_geometry (dH : TorusKernelCentralizerData sH v) :
    Smooth (subgroupIntersection m dG.inclusion).X.hom ∧
      IsAffineHom (subgroupIntersection m dG.inclusion).X.hom ∧
      ConnectedSpace (subgroupIntersection m dG.inclusion).X.left ∧
      IsUnipotent (subgroupIntersection m dG.inclusion) := by
  let e := intersectionIso sH h v m n hm dG dH
  exact ⟨smooth_of_over_iso ((Grp.forget _).mapIso e.symm) dH.smooth,
    isAffineHom_of_over_iso ((Grp.forget _).mapIso e.symm) dH.isAffineHom,
    connectedSpace_of_over_iso ((Grp.forget _).mapIso e.symm) dH.connectedSpace,
    IsUnipotent.of_iso e.symm dH.isUnipotent⟩

/-- Over a perfect field the actual intersection has a finite represented
split series over that same field. -/
theorem intersection_isSplitUnipotent [PerfectField k]
    (dH : TorusKernelCentralizerData sH v) :
    RelativeRoot.IsSplitUnipotent (subgroupIntersection m dG.inclusion) := by
  obtain ⟨hs, ha, hc, hu⟩ := intersection_geometry sH h v m n hm dG dH
  have : Smooth (subgroupIntersection m dG.inclusion).X.hom := hs
  have : IsAffineHom (subgroupIntersection m dG.inclusion).X.hom := ha
  exact perfectFieldUnipotentSplit k (subgroupIntersection m dG.inclusion) hc hu

end Intersection

end TorusKernelCentralizerData

end Langlands.GroupScheme
