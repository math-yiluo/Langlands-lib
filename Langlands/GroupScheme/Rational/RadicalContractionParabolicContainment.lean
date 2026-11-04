import Langlands.GroupScheme.Rational.RootSignUnipotentLie
import Langlands.GroupScheme.Rational.RelativeRootStandardCocharacter
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalReduction
import Langlands.GroupScheme.Rational.LeviContractionCentralizer

/-! # Ambient containment from contraction of the original radical -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Dynamic

section RootSigns

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hT : IsSplitTorus T.toGrp) (t : T.toGrp ⟶ G)
    (eta nu : cocharacterLattice T)

include hT

/-- For a common split torus with negation-stable actual roots, inclusion of
identity-limit subgroups reverses inclusion of dynamic parabolics. -/
theorem parabolic_le_of_unipotent_le_of_root_negation
    (hneg : ∀ α ∈ relativeRoots t, -α ∈ relativeRoots t)
    (hU : unipotent (CommGroupScheme.groupHom eta ≫ t) ≤
      unipotent (CommGroupScheme.groupHom nu ≫ t)) :
    parabolic (CommGroupScheme.groupHom nu ≫ t) ≤
      parabolic (CommGroupScheme.groupHom eta ≫ t) := by
  apply (RelativeRoot.parabolic_le_iff_nonnegative_rootSupport
    dynamicConnected hT t nu eta).mpr
  intro α hα hαnu
  by_contra! hαeta
  have hpos : 0 < latticePairing T (-α) eta := by
    simpa using neg_pos.mpr hαeta
  have h := RelativeRoot.positive_rootSupport_of_unipotent_le
    hT t eta nu hU (-α) (hneg α hα) hpos
  have hn : 0 < -(latticePairing T α nu) := by simpa using h
  omega

/-- A supplied realization of the actual relative roots discharges the
negation premise, without assuming a universal root-system theorem. -/
theorem parabolic_le_of_unipotent_le_of_relativeRootSystem
    [Mono t.hom.hom.left] (hroot : HasRelativeRootSystem t)
    (hU : unipotent (CommGroupScheme.groupHom eta ≫ t) ≤
      unipotent (CommGroupScheme.groupHom nu ≫ t)) :
    parabolic (CommGroupScheme.groupHom nu ≫ t) ≤
      parabolic (CommGroupScheme.groupHom eta ≫ t) :=
  parabolic_le_of_unipotent_le_of_root_negation hT t eta nu
    (fun _ hα => HasRelativeRootSystem.neg_mem_relativeRoots
      (k := k) (G := G) (T := T) (i := t) hroot hT hα) hU

end RootSigns

section Radical

variable {k : Type u} [Field k]
    {G P U H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (chi : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (p : P ⟶ G) (hP : (parabolic chi).IsRepresentedBy p)
    (r : U ⟶ P) (hr : IsUnipotentRadical r)

include hP hr

/-- The actual dynamic identity-limit subgroup lies in every supplied
unipotent radical of its represented dynamic parabolic. -/
theorem unipotent_le_range_of_isUnipotentRadical :
    unipotent chi ≤ SubgroupFunctor.range (r ≫ p) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let H := Affine.unipotentScheme chi
  let i := Affine.unipotentHom chi
  have hi : (unipotent chi).IsRepresentedBy i := Affine.isRepresentedBy_unipotentHom chi
  let f := hP.factorHom i (hi.2.le.trans (unipotent_le_parabolic chi))
  have hf : f ≫ p = i := hP.factorHom_comp i _
  have hif : (unipotent chi).IsRepresentedBy (f ≫ p) := by rw [hf]; exact hi
  have hc : IsClosedSubgroup f := IsClosedSubgroup.of_comp
    (Affine.isClosedSubgroup_of_isRepresentedBy_parabolic chi hP)
    (Affine.isClosedSubgroup_of_isRepresentedBy_unipotent chi hif)
  have hs : Smooth H.X.hom := (dynamicSmooth k G chi H i).2.2 hi
  have hconn : ConnectedSpace H.X.left :=
    DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent G chi hi
  have hu : IsUnipotent H := isUnipotent_unipotentRepresentative chi hi
  have hn : (SubgroupFunctor.range f).IsNormal :=
    range_unipotentRepresentative_isNormal chi p f hP hif
  have hle := hr.greatest H f hc hs hconn hu hn
  intro V x hx
  rw [← hi.2] at hx
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hx
  have hyf : y ≫ f.hom.hom ∈ (SubgroupFunctor.range r).carrier V :=
    hle V (SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩)
  obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp hyf
  refine SubgroupFunctor.mem_range.mpr ⟨z, ?_⟩
  have hfp := congrArg (fun q : H ⟶ G => q.hom.hom) hf
  change f.hom.hom ≫ p.hom.hom = i.hom.hom at hfp
  rw [Grp.comp_hom_hom, ← Category.assoc, hz, Category.assoc, hfp, hy]

/-- Factor any supplied representative of the dynamic identity-limit subgroup
through the original unipotent radical. -/
def unipotentRepresentativeToRadical (i : H ⟶ G)
    (hi : (unipotent chi).IsRepresentedBy i) : H ⟶ U := by
  let : IsClosedImmersion r.hom.hom.left := hr.isClosedSubgroup
  let : Mono r.hom.hom := Over.mono_of_mono_left _
  let : Mono p.hom.hom := hP.1
  let hrep : (SubgroupFunctor.range (r ≫ p)).IsRepresentedBy (r ≫ p) :=
    ⟨by change Mono (r.hom.hom ≫ p.hom.hom); infer_instance, rfl⟩
  exact hrep.factorHom i
    (hi.2.le.trans (unipotent_le_range_of_isUnipotentRadical chi p hP r hr))

/-- The factor keeps the exact original ambient inclusion. -/
theorem unipotentRepresentativeToRadical_comp (i : H ⟶ G)
    (hi : (unipotent chi).IsRepresentedBy i) :
    unipotentRepresentativeToRadical chi p hP r hr i hi ≫ r ≫ p = i := by
  unfold unipotentRepresentativeToRadical
  exact SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

end Radical

section Containment

variable {k : Type u} [Field k]
    {G P U : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hT : IsSplitTorus T.toGrp) (t : T.toGrp ⟶ G)
    (eta nu : cocharacterLattice T)
    (hneg : ∀ α ∈ relativeRoots t, -α ∈ relativeRoots t)
    (p : P ⟶ G)
    (hP : (parabolic (CommGroupScheme.groupHom eta ≫ t)).IsRepresentedBy p)
    (r : U ⟶ P) (hr : IsUnipotentRadical r)
    (hcontract : SubgroupFunctor.range (r ≫ p) ≤
      unipotent (CommGroupScheme.groupHom nu ≫ t))

include hT eta hneg hP r hr hcontract

/-- Contraction of the supplied radical gives ambient parabolic containment
when the original parabolic has a presentation through the same split torus. -/
theorem parabolic_le_range_of_radical_contraction :
    parabolic (CommGroupScheme.groupHom nu ≫ t) ≤ SubgroupFunctor.range p := by
  rw [hP.2]
  exact parabolic_le_of_unipotent_le_of_root_negation hT t eta nu hneg
    ((unipotent_le_range_of_isUnipotentRadical _ p hP r hr).trans hcontract)

/-- The whole ambient cocharacter centralizer is consequently contained in
the original represented parabolic. -/
theorem centralizer_le_range_of_radical_contraction :
    centralizer (CommGroupScheme.groupHom nu ≫ t) ≤ SubgroupFunctor.range p :=
  (centralizer_le_parabolic _).trans
    (parabolic_le_range_of_radical_contraction hT t eta nu hneg p hP r hr hcontract)

/-- If the first multiplication factor is fixed, the new dynamic parabolic
is exactly the original image, and its centralizer is the original first factor. -/
theorem parabolic_and_centralizer_eq_of_radical_contraction
    {L : GroupScheme (Spec (CommRingCat.of k))} (l : L ⟶ P)
    [IsIso (subgroupMultiplication l r)]
    (hfixed : SubgroupFunctor.range (l ≫ p) ≤
      centralizer (CommGroupScheme.groupHom nu ≫ t)) :
    parabolic (CommGroupScheme.groupHom nu ≫ t) = SubgroupFunctor.range p ∧
      centralizer (CommGroupScheme.groupHom nu ≫ t) = SubgroupFunctor.range (l ≫ p) := by
  have hpar := parabolic_le_range_of_radical_contraction hT t eta nu hneg p hP r hr hcontract
  have hcen := centralizer_le_range_of_radical_contraction hT t eta nu hneg p hP r hr hcontract
  exact ⟨le_antisymm hpar
    (range_le_parabolic_of_subgroupMultiplication l r p _ hfixed hcontract),
    centralizer_eq_of_subgroupMultiplication l r p _ hfixed hcontract hcen⟩

end Containment

end Dynamic

end Langlands.GroupScheme
