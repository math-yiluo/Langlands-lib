import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Adjoint.QuasiSplitProof
import Langlands.GroupScheme.Absolute.AlgClosedMaximalTorusCentralizerAssembly
import Langlands.GroupScheme.Absolute.SolvableSubgroupBorelContainmentProof
import Langlands.GroupScheme.Absolute.BorelConjugacyProof
import Langlands.GroupScheme.Absolute.QuotientNormalizer
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.Torus.NoTorusUnipotent
import Langlands.GroupScheme.Torus.ExistenceProof
import Langlands.GroupScheme.SubgroupFunctor.FppfImagePullback
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicRangeReduction
import Langlands.GroupScheme.Rational.CentralTorusFixedness
import Langlands.GroupScheme.ConjugacyBaseChange

/-! # Preimages of Borel subgroups under central isogenies over an algebraically closed field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme
namespace CentralIsogenyBorelPreimage

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A subgroup of the source mapping to a solvable group has solvable rational points when the
kernel of the ambient map is central. -/
theorem isSolvable_of_central_kernel
    {C G A J : GroupScheme (Spec (CommRingCat.of k))}
    (q : G ⟶ A) (hq : IsCentral (kernelι q))
    (a : C ⟶ G) [Mono a.hom.hom] (r : C ⟶ J) (j : J ⟶ A)
    (hcomm : a ≫ q = r ≫ j) (hJ : IsSolvableGroupScheme J) :
    IsSolvableGroupScheme C := by
  apply (isSolvableGroupScheme_iff_isSolvable_points C).mpr
  have : Group.IsSolvable (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ J.X) :=
    (isSolvableGroupScheme_iff_isSolvable_points J).mp hJ
  let R : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ C.X) →*
      (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ J.X) :=
    ((yonedaGrp.map r).app (op (Over.mk (𝟙 (Spec (CommRingCat.of k)))))).hom
  have hcomm' : a.hom.hom ≫ q.hom.hom = r.hom.hom ≫ j.hom.hom :=
    congrArg (fun f : C ⟶ A => f.hom.hom) hcomm
  have hc (x : R.ker) : (x.val ≫ a.hom.hom) ∈
      (center G).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
    apply (isCentral_kernelι_iff q).mp hq
    have hx : x.val ≫ r.hom.hom = 1 := x.property
    rw [Category.assoc, hcomm', ← Category.assoc, hx, MonObj.one_comp]
  have : Group.IsSolvable R.ker := Group.isSolvable_of_comm (by
    intro x y
    apply Subtype.ext
    apply (cancel_mono a.hom.hom).mp
    change (x.val * y.val) ≫ a.hom.hom = (y.val * x.val) ≫ a.hom.hom
    rw [MonObj.mul_comp, MonObj.mul_comp]
    exact (commute_of_mem_center (hc x) (y.val ≫ a.hom.hom)).eq)
  exact Group.isSolvable_of_ker_le_range R.ker.subtype R (by simp)

/-- Over an algebraically closed field, the smooth connected image of a Borel subgroup under a
flat homomorphism of finite presentation with central kernel is a Borel subgroup. -/
theorem isBorelSubgroup_image
    {B G I A : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [IsAffineHom A.X.hom]
    (i : B ⟶ G) (hi : IsBorelSubgroup i)
    (q : G ⟶ A) (hq : IsCentral (kernelι q)) [Flat q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]
    (p : B ⟶ I) [Surjective p.hom.hom.left] [LocallyOfFiniteType p.hom.hom.left]
    (j : I ⟶ A) (hj : IsClosedSubgroup j)
    [Smooth I.X.hom] [ConnectedSpace I.X.left]
    (hcomm : i ≫ q = p ≫ j) : IsBorelSubgroup j := by
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : Smooth B.X.hom := hi.smooth
  have : ConnectedSpace B.X.left := hi.connectedSpace
  have : Group.IsSolvable (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ B.X) :=
    (isSolvableGroupScheme_iff_isSolvable_points B).mp hi.isSolvableGroupScheme
  let pPoints : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ B.X) →*
      (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ I.X) :=
    ((yonedaGrp.map p).app (op (Over.mk (𝟙 (Spec (CommRingCat.of k)))))).hom
  refine ⟨hj, inferInstance, inferInstance,
    (isSolvableGroupScheme_iff_isSolvable_points I).mpr
      (Group.isSolvable_of_surjective (f := pPoints) (rationalPoints_surjective p)), ?_⟩
  intro J j' f hj' hJs hJc hJv hf
  have : Smooth J.X.hom := hJs
  have : ConnectedSpace J.X.left := hJc
  have : IsClosedImmersion j'.hom.hom.left := hj'
  have : IsAffineHom J.X.hom := by
    rw [← Over.w j'.hom.hom]
    infer_instance
  let P := SubgroupPreimage.groupScheme q j'
  let a : P ⟶ G := SubgroupPreimage.inclusion q j'
  let r : P ⟶ J := SubgroupPreimage.projection q j'
  have ha : IsClosedSubgroup a := SubgroupPreimage.isClosedSubgroup q j' hj'
  have : IsClosedImmersion a.hom.hom.left := ha
  have : IsAffineHom P.X.hom := SubgroupPreimage.isAffineHom q j' hj'
  have : LocallyOfFiniteType P.X.hom := by
    rw [← Over.w a.hom.hom]
    infer_instance
  let C := ReducedSubgroup.identityCore P
  let c : C ⟶ G := ReducedSubgroup.identityCoreι P ≫ a
  let s : C ⟶ J := ReducedSubgroup.identityCoreι P ≫ r
  have hc : IsClosedSubgroup c := by
    change IsClosedImmersion
      ((ReducedSubgroup.identityCoreι P).hom.hom.left ≫ a.hom.hom.left)
    infer_instance
  have : IsClosedImmersion c.hom.hom.left := hc
  have : Mono c.hom.hom := Over.mono_of_mono_left _
  have hpre : a ≫ q = r ≫ j' := by
    apply Grp.hom_ext
    exact (SubgroupPreimage.isPullback q j').w
  have hcs : c ≫ q = s ≫ j' := by
    dsimp only [c, s]
    rw [Category.assoc, hpre, Category.assoc]
  have hCv : IsSolvableGroupScheme C :=
    isSolvable_of_central_kernel q hq c s j' hcs hJv
  let b : B ⟶ P := quotientOvergroupHom i q p j hcomm j' f hf
  let bC : B ⟶ C := ReducedSubgroup.factorIdentityCore b
  have hbC : bC ≫ c = i := by
    dsimp only [bC, c]
    rw [← Category.assoc, ReducedSubgroup.factorIdentityCore_comp]
    exact quotientOvergroupHom_inclusion i q p j hcomm j' f hf
  have : IsIso bC := hi.maximal C c bC hc inferInstance inferInstance hCv hbC
  have : IsIso bC.hom := inferInstanceAs (IsIso ((Grp.forget₂Mon _).map bC))
  have : IsIso bC.hom.hom := inferInstanceAs (IsIso ((Mon.forget _).map bC.hom))
  have : IsIso bC.hom.hom.left := inferInstanceAs (IsIso ((Over.forget _).map bC.hom.hom))
  have : Flat r.hom.hom.left := SubgroupPreimage.flat_projection q j'
  have : LocallyOfFinitePresentation r.hom.hom.left :=
    MorphismProperty.of_isPullback (SubgroupPreimage.isPullback_scheme q j') inferInstance
  have : Surjective s.hom.hom.left :=
    AdjointQuotientBorelImage.surjective_identityCore_comp r
  have hproj : bC ≫ s = p ≫ f := by
    dsimp only [bC, s]
    rw [← Category.assoc, ReducedSubgroup.factorIdentityCore_comp]
    exact quotientOvergroupHom_projection i q p j hcomm j' f hf
  have : Surjective (p.hom.hom.left ≫ f.hom.hom.left) := by
    change Surjective (p ≫ f).hom.hom.left
    rw [← hproj]
    change Surjective (bC.hom.hom.left ≫ s.hom.hom.left)
    infer_instance
  have : Surjective f.hom.hom.left := Surjective.of_comp p.hom.hom.left _
  have hfclosed : IsClosedSubgroup f := IsClosedSubgroup.of_comp hj' (by rw [hf]; exact hj)
  have : IsClosedImmersion f.hom.hom.left := hfclosed
  have : IsReduced J.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k _ J.X.hom
  have : IsIso f.hom.hom.left := isIso_of_isClosedImmersion_of_surjective _
  have : IsIso ((Over.forget _).map f.hom.hom) := ‹IsIso f.hom.hom.left›
  have : IsIso f.hom.hom := isIso_of_reflects_iso _ (Over.forget _)
  have : IsIso ((Mon.forget _).map f.hom) := ‹IsIso f.hom.hom›
  have : IsIso f.hom := isIso_of_reflects_iso _ (Mon.forget _)
  have : IsIso ((Grp.forget₂Mon _).map f) := ‹IsIso f.hom›
  exact isIso_of_reflects_iso f (Grp.forget₂Mon _)

/-- Over an algebraically closed field, the full scheme-theoretic centre of a connected
reductive group lies in some Borel subgroup, on every test scheme. The centralizer of a maximal
torus is a smooth connected solvable closed subgroup containing the centre. -/
theorem exists_isBorelSubgroup_center_le
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G) :
    ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G),
      IsBorelSubgroup i ∧ center G ≤ SubgroupFunctor.range i := by
  have := hG.smooth
  have := hG.isAffineHom
  have := hG.connectedSpace
  obtain ⟨T, j, hj⟩ := maximalTorusExistence k G
  have hTs : IsSplitTorus T.toGrp :=
    hj.1.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  obtain ⟨ν, hν⟩ := hTs.exists_genericCocharacter j
  have hZ := genericCentralizer k G hG T j (hj.isMaximalSplitTorus hTs) ν hν
  obtain ⟨C, c, hc, hcc⟩ :=
    fieldCentralizerRepresentability k T G (hj.2.1.isAffineHom : IsAffineHom T.toGrp.X.hom) j
  have hcD : (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ j)).IsRepresentedBy c := by
    rw [hZ]
    exact hc
  have : Smooth C.X.hom := (dynamicSmooth k G _ C c).2.1 hcD
  have : ConnectedSpace C.X.left := ((dynamicConnected k G _ C c).2 inferInstance).2 hcD
  have : IsAffineHom C.X.hom := hcc.isAffineHom
  -- The torus `T` is a central maximal torus of its centralizer `C`.
  set t := torusCentralizerFactor j hc
  have ht : t ≫ c = j := torusCentralizerFactor_comp j hc
  have htm : IsMaximalTorus t := by
    refine ⟨hj.1, isClosedSubgroup_torusCentralizerFactor j hc hcc hj.2.1, ?_⟩
    intro T' i' f hT' hi' hf
    exact hj.2.2 T' (i' ≫ c) f hT' (hi'.comp hcc) (by rw [← Category.assoc, hf, ht])
  have htc : IsCentral t := isCentral_torusCentralizerFactor j hc
  -- So `C/T` has no tori, hence is unipotent, and `C` is solvable.
  obtain ⟨Q, q, hQs, hQa, hq⟩ :=
    normalSubgroupQuotient k C T.toGrp t htm.2.1 htc.range_isNormal
  have : Smooth Q.X.hom := hQs
  have : IsAffineHom Q.X.hom := hQa
  have : Surjective q.hom.hom.left := hq.2.1
  have : ConnectedSpace Q.X.left :=
    Function.Surjective.connectedSpace q.hom.hom.left.surjective q.hom.hom.left.continuous
  have hQ : IsUnipotent Q :=
    noTorusUnipotent k Q (centralMaximalTorusQuotientStatement k C T t htc htm Q q hq)
  have : Group.IsSolvable (algebraicClosurePoint k ⟶ Q.X) :=
    isSolvable_points_of_isUnipotent hQ _
  have hsolv : IsSolvableGroupScheme C :=
    isSolvableGroupScheme_of_isSolvable_points (isSolvable_points_of_isFppfQuotient hq _)
  -- The smooth connected solvable closed subgroup `C` lies in a Borel subgroup.
  obtain ⟨B, i, f, hi, hf⟩ := solvableSubgroupBorelContainment k G C c hcc hsolv
  refine ⟨B, i, hi, ?_⟩
  intro U x hx
  have hx' : x ∈ (SubgroupFunctor.range c).carrier U := by
    rw [hc.2]
    exact center_le_torusCentralizer j U hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx'
  refine SubgroupFunctor.mem_range.mpr ⟨y ≫ f.hom.hom, ?_⟩
  rw [Category.assoc, ← Grp.comp_hom_hom, hf]

/-- **Preimages of Borel subgroups under central isogenies.** Over an algebraically closed
field, let `π : G ⟶ A` be a central isogeny of connected reductive groups and `j : B ⟶ A` a
Borel subgroup. A closed subgroup `i : P ⟶ G` whose points are exactly those mapping into `B`
on every test scheme is a Borel subgroup. -/
theorem isBorelSubgroup_of_range_eq_comap
    {G A B P : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (hA : IsConnectedReductive A)
    (π : G ⟶ A) (hπ : IsCentralIsogeny π)
    (j : B ⟶ A) (hj : IsBorelSubgroup j)
    (i : P ⟶ G) (hi : IsClosedSubgroup i)
    (hrange : SubgroupFunctor.range i = (SubgroupFunctor.range j).comap π) :
    IsBorelSubgroup i := by
  have := hG.smooth
  have := hG.isAffineHom
  have := hG.connectedSpace
  have := hA.smooth
  have := hA.isAffineHom
  have := hA.connectedSpace
  have : Flat π.hom.hom.left := hπ.flat
  have : Surjective π.hom.hom.left := hπ.surjective
  have : LocallyOfFinitePresentation π.hom.hom.left := hπ.locallyOfFinitePresentation
  -- A Borel subgroup `B₁` of `G` containing the full kernel.
  obtain ⟨B₁, i₁, hi₁, hcen⟩ := exists_isBorelSubgroup_center_le hG
  have hker : SubgroupFunctor.range (kernelι π) ≤ SubgroupFunctor.range i₁ :=
    hπ.kernel_range_le_center.trans hcen
  -- Its image `I` in `A` is a Borel subgroup.
  have : IsClosedImmersion i₁.hom.hom.left := hi₁.isClosedSubgroup
  have : Smooth B₁.X.hom := hi₁.smooth
  have : ConnectedSpace B₁.X.left := hi₁.connectedSpace
  have : IsAffineHom B₁.X.hom := hi₁.isClosedSubgroup.isAffineHom
  obtain ⟨I, jI, p, hjI, hfac, hpf, hps, hpq, hpl, hIs, hIc, hIa⟩ :=
    HomImage.exists_image (i₁ ≫ π)
  have : Flat p.hom.hom.left := hpf
  have : Surjective p.hom.hom.left := hps
  have : QuasiCompact p.hom.hom.left := hpq
  have : LocallyOfFinitePresentation p.hom.hom.left := hpl
  have : Smooth I.X.hom := hIs
  have : ConnectedSpace I.X.left := hIc
  have hjIB : IsBorelSubgroup jI :=
    isBorelSubgroup_image i₁ hi₁ π hπ.isCentral_kernelι p jI hjI hfac.symm
  -- Conjugate `I` onto `B` by a rational point of `A`, lifted to `G`.
  obtain ⟨a, φ, ha⟩ := (borelConjugacy k A).2 I B jI j hjIB hj
  let g := rationalPointLift π a
  have hg : g ≫ π.hom.hom = a := rationalPointLift_comp π a
  let i₀ := i₁ ≫ (G.innerIso g).hom
  have hi₀ : IsBorelSubgroup i₀ := hi₁.comp_iso (G.innerIso g)
  let p₀ := p ≫ φ.hom
  have hsq : i₀ ≫ π = p₀ ≫ j := by
    calc i₀ ≫ π = i₁ ≫ ((G.innerIso g).hom ≫ π) := Category.assoc _ _ _
      _ = i₁ ≫ (π ≫ (A.innerIso (g ≫ π.hom.hom)).hom) := by rw [innerIso_hom_comp]
      _ = (p ≫ jI) ≫ (A.innerIso a).hom := by rw [hg, ← Category.assoc, hfac]
      _ = p₀ ≫ j := by rw [Category.assoc, ha, ← Category.assoc]
  -- The conjugate Borel subgroup still contains the central kernel.
  have hker₀ : SubgroupFunctor.range (kernelι π) ≤ SubgroupFunctor.range i₀ := by
    intro U x hx
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp (hker U hx)
    obtain ⟨z, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    refine SubgroupFunctor.mem_range.mpr ⟨y, ?_⟩
    change y ≫ i₁.hom.hom ≫ (G.innerIso g).hom.hom.hom = z ≫ (kernelι π).hom.hom
    rw [← Category.assoc, hy, Category.assoc, ← Grp.comp_hom_hom,
      hπ.isCentral_kernelι.comp_innerIso_hom]
  -- The fppf image criterion identifies the preimage of `B` with `B₁`.
  have : IsIso φ.hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso φ)).hom)
  have hp₀f : Flat p₀.hom.hom.left := by
    change Flat (p.hom.hom.left ≫ φ.hom.hom.hom.left)
    infer_instance
  have hp₀s : Surjective p₀.hom.hom.left := by
    change Surjective (p.hom.hom.left ≫ φ.hom.hom.hom.left)
    infer_instance
  have hp₀l : LocallyOfFinitePresentation p₀.hom.hom.left := by
    change LocallyOfFinitePresentation (p.hom.hom.left ≫ φ.hom.hom.hom.left)
    infer_instance
  have : IsClosedImmersion i₀.hom.hom.left := hi₀.isClosedSubgroup
  have : IsClosedImmersion j.hom.hom.left := hj.isClosedSubgroup
  have hr₀ : (SubgroupFunctor.range i₀).IsRepresentedBy i₀ :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  have hrj : (SubgroupFunctor.range j).IsRepresentedBy j :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  have himg : SubgroupFunctor.IsFppfImage (SubgroupFunctor.range i₀)
      (SubgroupFunctor.range j) π :=
    ⟨B₁, B, i₀, j, p₀, hr₀, hrj, hsq, hp₀f, hp₀s, hp₀l⟩
  have heq : SubgroupFunctor.range i = SubgroupFunctor.range i₀ :=
    hrange.trans (himg.comap_eq_of_kernel_le hker₀)
  have h := hi₀.iso_comp (hi.sourceIsoOfRangeEq hi₀.isClosedSubgroup heq)
  rwa [IsClosedSubgroup.sourceIsoOfRangeEq_hom_comp] at h

end CentralIsogenyBorelPreimage
end Langlands.GroupScheme
