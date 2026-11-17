import Langlands.GroupScheme.Reductive.AdjointParabolicCorrespondenceStatement
import Langlands.GroupScheme.Adjoint.RelativeReductivity
import Langlands.GroupScheme.RelativeLevi.ParabolicClosedProof
import Langlands.GroupScheme.Rational.UnipotentRadicalProperties
import Langlands.GroupScheme.CentralIsogeny.BorelPreimage
import Langlands.GroupScheme.Absolute.UnipotentQuotientParabolics
import Langlands.BruhatTits.MaximalProP.FacetBorelImage
import Langlands.GroupScheme.Absolute.GeometricBorelBaseChange

/-! # Preimages of parabolic subgroups of the adjoint quotient

Clauses 3 and 5 of `AdjointParabolicCorrespondenceStatement`: inverse images of parabolic
subgroups of an fppf quotient by the centre are parabolic, and the correspondence matches
Borel subgroups. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AdjointParabolicPreimage

section AlgClosed

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Over an algebraically closed field, let `π : G ⟶ A` be a flat surjective homomorphism
locally of finite presentation with central kernel from a connected reductive group to a
smooth connected affine group. A closed subgroup of `G` whose points are exactly those mapping
into a Borel subgroup of `A` is a Borel subgroup of `G`. -/
theorem isBorelSubgroup_of_range_eq_comap
    {G A B P : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G)
    [Smooth A.X.hom] [IsAffineHom A.X.hom] [ConnectedSpace A.X.left]
    (π : G ⟶ A) [Flat π.hom.hom.left] [Surjective π.hom.hom.left]
    [LocallyOfFinitePresentation π.hom.hom.left] (hπ : IsCentral (kernelι π))
    (j : B ⟶ A) (hj : IsBorelSubgroup j)
    (i : P ⟶ G) (hi : IsClosedSubgroup i)
    (hrange : SubgroupFunctor.range i = (SubgroupFunctor.range j).comap π) :
    IsBorelSubgroup i := by
  have := hG.smooth
  have := hG.isAffineHom
  have := hG.connectedSpace
  -- A Borel subgroup `B₁` of `G` containing the full kernel.
  obtain ⟨B₁, i₁, hi₁, hcen⟩ := CentralIsogenyBorelPreimage.exists_isBorelSubgroup_center_le hG
  have hker : SubgroupFunctor.range (kernelι π) ≤ SubgroupFunctor.range i₁ :=
    ((isCentral_iff_range_le_center _).mp hπ).trans hcen
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
    CentralIsogenyBorelPreimage.isBorelSubgroup_image i₁ hi₁ π hπ p jI hjI hfac.symm
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
      hπ.comp_innerIso_hom]
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

/-- Over an algebraically closed field, with `π` as in `isBorelSubgroup_of_range_eq_comap`,
the full inverse image of a smooth connected closed subgroup `J` of `A` containing a Borel
subgroup is smooth. It is the reduced identity component of the scheme-theoretic preimage. -/
theorem smooth_of_range_eq_comap
    {G A B J H : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G)
    [Smooth A.X.hom] [IsAffineHom A.X.hom] [ConnectedSpace A.X.left]
    (π : G ⟶ A) [Flat π.hom.hom.left] [Surjective π.hom.hom.left]
    [LocallyOfFinitePresentation π.hom.hom.left] (hπ : IsCentral (kernelι π))
    (jJ : J ⟶ A) (hjJ : IsClosedSubgroup jJ) [Smooth J.X.hom] [ConnectedSpace J.X.left]
    (jB : B ⟶ A) (hjB : IsBorelSubgroup jB) (a : B ⟶ J) (ha : a ≫ jJ = jB)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hrange : SubgroupFunctor.range i = (SubgroupFunctor.range jJ).comap π) :
    Smooth H.X.hom := by
  have := hG.smooth
  have := hG.isAffineHom
  have : IsClosedImmersion jJ.hom.hom.left := hjJ
  have : IsAffineHom J.X.hom := by
    rw [← Over.w jJ.hom.hom]
    infer_instance
  let P := SubgroupPreimage.groupScheme π jJ
  let aP : P ⟶ G := SubgroupPreimage.inclusion π jJ
  let r : P ⟶ J := SubgroupPreimage.projection π jJ
  have haP : IsClosedSubgroup aP := SubgroupPreimage.isClosedSubgroup π jJ hjJ
  have : IsClosedImmersion aP.hom.hom.left := haP
  have : IsAffineHom P.X.hom := SubgroupPreimage.isAffineHom π jJ hjJ
  have : LocallyOfFiniteType P.X.hom := by
    rw [← Over.w aP.hom.hom]
    infer_instance
  have : Flat r.hom.hom.left := SubgroupPreimage.flat_projection π jJ
  have : LocallyOfFinitePresentation r.hom.hom.left :=
    MorphismProperty.of_isPullback (SubgroupPreimage.isPullback_scheme π jJ) inferInstance
  let C := ReducedSubgroup.identityCore P
  let c : C ⟶ G := ReducedSubgroup.identityCoreι P ≫ aP
  let s : C ⟶ J := ReducedSubgroup.identityCoreι P ≫ r
  have hc : IsClosedSubgroup c := by
    change IsClosedImmersion
      ((ReducedSubgroup.identityCoreι P).hom.hom.left ≫ aP.hom.hom.left)
    infer_instance
  have : IsClosedImmersion c.hom.hom.left := hc
  have : Mono c.hom.hom := Over.mono_of_mono_left _
  have : Mono jJ.hom.hom := Over.mono_of_mono_left _
  have hpre : aP ≫ π = r ≫ jJ := by
    apply Grp.hom_ext
    exact (SubgroupPreimage.isPullback π jJ).w
  have hcs : c ≫ π = s ≫ jJ := by
    dsimp only [c, s]
    rw [Category.assoc, hpre, Category.assoc]
  -- `s` is surjective, and it is flat because it factors through its schematic image.
  have : Surjective s.hom.hom.left :=
    AdjointQuotientBorelImage.surjective_identityCore_comp r
  obtain ⟨D, inc, fac, hinc, hfac, hff, hfs, -, hfl, -, -, -⟩ := HomImage.exists_image s
  have : IsClosedImmersion inc.hom.hom.left := hinc
  have : Flat fac.hom.hom.left := hff
  have : LocallyOfFinitePresentation fac.hom.hom.left := hfl
  have hsl : s.hom.hom.left = fac.hom.hom.left ≫ inc.hom.hom.left := by
    rw [← hfac]
    rfl
  have : Surjective (fac.hom.hom.left ≫ inc.hom.hom.left) := by
    rw [← hsl]
    infer_instance
  have : Surjective inc.hom.hom.left := Surjective.of_comp fac.hom.hom.left _
  have : IsReduced J.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k _ J.X.hom
  have : IsIso inc.hom.hom.left := isIso_of_isClosedImmersion_of_surjective _
  have hsf : Flat s.hom.hom.left := by
    rw [hsl]
    infer_instance
  have hslp : LocallyOfFinitePresentation s.hom.hom.left := by
    rw [hsl]
    infer_instance
  -- The preimage of the Borel subgroup is a Borel subgroup inside the reduced core.
  let n := SubgroupPreimage.inclusion π jB
  have hn : IsBorelSubgroup n :=
    isBorelSubgroup_of_range_eq_comap hG π hπ jB hjB n
      (SubgroupPreimage.isClosedSubgroup π jB hjB.isClosedSubgroup)
      (SubgroupPreimage.range_inclusion π jB)
  have : Mono n.hom.hom := hn.isClosedSubgroup.mono_overHom
  have : Mono aP.hom.hom := haP.mono_overHom
  have hnP : SubgroupFunctor.range n ≤ SubgroupFunctor.range aP := by
    rw [SubgroupPreimage.range_inclusion, SubgroupPreimage.range_inclusion]
    exact SubgroupFunctor.comap_mono (SubgroupFunctor.range_le_of_factor a ha)
  obtain ⟨b, hb⟩ := SubgroupFunctor.exists_factor_of_range_le hnP
  have : Smooth (SubgroupPreimage.groupScheme π jB).X.hom := hn.smooth
  have : ConnectedSpace (SubgroupPreimage.groupScheme π jB).X.left := hn.connectedSpace
  let bC := ReducedSubgroup.factorIdentityCore b
  have hbC : bC ≫ c = n := by
    dsimp only [bC, c]
    rw [← Category.assoc, ReducedSubgroup.factorIdentityCore_comp, hb]
  have hker : SubgroupFunctor.range (kernelι π) ≤ SubgroupFunctor.range c := by
    refine le_trans ?_ (SubgroupFunctor.range_le_of_factor bC hbC)
    rw [SubgroupPreimage.range_inclusion]
    intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    change (y ≫ (kernelι π).hom.hom) ≫ π.hom.hom ∈ (SubgroupFunctor.range jB).carrier T
    have h1 : (y ≫ (kernelι π).hom.hom) ≫ π.hom.hom = 1 :=
      (mem_range_kernelι_iff π _).mp (SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩)
    rw [h1]
    exact ((SubgroupFunctor.range jB).carrier T).one_mem
  have himg : SubgroupFunctor.IsFppfImage (SubgroupFunctor.range c)
      (SubgroupFunctor.range jJ) π :=
    ⟨C, J, c, jJ, s, ⟨inferInstance, rfl⟩, ⟨inferInstance, rfl⟩, hcs, hsf, inferInstance, hslp⟩
  have heq : SubgroupFunctor.range i = SubgroupFunctor.range c :=
    hrange.trans (himg.comap_eq_of_kernel_le hker)
  let e := hi.sourceIsoOfRangeEq hc heq
  have : IsIso e.hom.hom.hom.left := by
    have : IsIso e.hom.hom.hom := (Grp.forget _).map_isIso e.hom
    exact (Over.forget _).map_isIso e.hom.hom.hom
  rw [← Over.w e.hom.hom.hom]
  infer_instance

end AlgClosed

section Field

variable {k : Type u} [Field k]

/-- The kernel of the base change to the algebraic closure of an fppf quotient by the centre is
central. -/
theorem isCentral_kernelι_baseChange
    {G A : GroupScheme (Spec (CommRingCat.of k))}
    (q : G ⟶ A) (hq : RelativeRoot.IsFppfQuotient (center G) q) :
    IsCentral (kernelι ((GroupScheme.baseChange (toAlgebraicClosure k)).map q)) :=
  (isCentral_iff_range_le_center _).mpr
    (hq.baseChange_center (toAlgebraicClosure k)).2.2.2.le

/-- Over any field, let `q : G ⟶ A` be an fppf quotient of a connected reductive group by its
centre, with `A` smooth, affine and connected. A closed subgroup of `G` whose points are exactly
those mapping into a parabolic subgroup of `A` is a parabolic subgroup of `G`. -/
theorem isParabolicSubgroup_of_range_eq_comap
    {G A P H : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G)
    [Smooth A.X.hom] [IsAffineHom A.X.hom] [ConnectedSpace A.X.left]
    (q : G ⟶ A) (hq : RelativeRoot.IsFppfQuotient (center G) q)
    (j : P ⟶ A) (hj : IsParabolicSubgroup j)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hrange : SubgroupFunctor.range i = (SubgroupFunctor.range j).comap q) :
    IsParabolicSubgroup i := by
  let b := toAlgebraicClosure k
  let F := GroupScheme.baseChange b
  have hGK : IsConnectedReductive (F.obj G) := hG.baseChange_toAlgebraicClosure
  have hqK := hq.baseChange_center b
  have : Flat (F.map q).hom.hom.left := hqK.1
  have : Surjective (F.map q).hom.hom.left := hqK.2.1
  have : LocallyOfFinitePresentation (F.map q).hom.hom.left := hqK.2.2.1
  have hπ : IsCentral (kernelι (F.map q)) := isCentral_kernelι_baseChange q hq
  have : Smooth (F.obj A).X.hom := inferInstanceAs (Smooth (pullback.snd A.X.hom b))
  have : IsAffineHom (F.obj A).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd A.X.hom b))
  have : ConnectedSpace (F.obj A).X.left := A.connectedSpace_baseChange_of_smooth_affine b
  have : Smooth P.X.hom := hj.smooth
  have : ConnectedSpace P.X.left := hj.connectedSpace
  have : IsAffineHom P.X.hom := hj.isClosedSubgroup.isAffineHom
  have : Smooth (F.obj P).X.hom := inferInstanceAs (Smooth (pullback.snd P.X.hom b))
  have : ConnectedSpace (F.obj P).X.left := P.connectedSpace_baseChange_of_smooth_affine b
  have heq : SubgroupFunctor.range (F.map i) =
      (SubgroupFunctor.range (F.map j)).comap (F.map q) := by
    rw [SubgroupFunctor.range_baseChangeHom, hrange, SubgroupFunctor.comap_baseChange,
      ← SubgroupFunctor.range_baseChangeHom]
  obtain ⟨B, jB, a, hjB, ha⟩ := hj.exists_isBorelSubgroup
  have hsm : Smooth (F.obj H).X.hom :=
    smooth_of_range_eq_comap hGK (F.map q) hπ (F.map j) (hj.isClosedSubgroup.baseChange b)
      jB hjB a ha (F.map i) (hi.baseChange b) heq
  have hb := fieldExtension_fpqc k (AlgebraicClosure k)
  have : Surjective b := hb.1
  have : Flat b := hb.2.1
  have : QuasiCompact b := hb.2.2
  refine ⟨hi, smooth_of_baseChange b H hsm, ?_⟩
  let n := SubgroupPreimage.inclusion (F.map q) jB
  have hn : IsBorelSubgroup n :=
    isBorelSubgroup_of_range_eq_comap hGK (F.map q) hπ jB hjB n
      (SubgroupPreimage.isClosedSubgroup (F.map q) jB hjB.isClosedSubgroup)
      (SubgroupPreimage.range_inclusion (F.map q) jB)
  have hle : SubgroupFunctor.range n ≤ SubgroupFunctor.range (F.map i) := by
    rw [heq, SubgroupPreimage.range_inclusion]
    exact SubgroupFunctor.comap_mono (SubgroupFunctor.range_le_of_factor a ha)
  have : Mono n.hom.hom := hn.isClosedSubgroup.mono_overHom
  have : Mono (F.map i).hom.hom := (hi.baseChange b).mono_overHom
  obtain ⟨f, hf⟩ := SubgroupFunctor.exists_factor_of_range_le hle
  exact ⟨_, n, f, hn, hf⟩

/-- Over any field, with `q` as in `isParabolicSubgroup_of_range_eq_comap`, let `i` and `j` be
parabolic subgroups of `G` and `A` such that the points of `i` are exactly those mapping into
`j`. Then `i` is a geometric Borel subgroup if and only if `j` is. -/
theorem isGeometricBorelSubgroup_iff_of_range_eq_comap
    {G A P H : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G)
    [Smooth A.X.hom] [IsAffineHom A.X.hom] [ConnectedSpace A.X.left]
    (q : G ⟶ A) (hq : RelativeRoot.IsFppfQuotient (center G) q)
    (j : P ⟶ A) (hj : IsParabolicSubgroup j)
    (i : H ⟶ G) (hi : IsParabolicSubgroup i)
    (hrange : SubgroupFunctor.range i = (SubgroupFunctor.range j).comap q) :
    IsGeometricBorelSubgroup i ↔ IsGeometricBorelSubgroup j := by
  have := hG.smooth
  have := hG.isAffineHom
  have := hG.connectedSpace
  have : Flat q.hom.hom.left := hq.1
  have : Surjective q.hom.hom.left := hq.2.1
  have : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  have : Mono i.hom.hom := hi.isClosedSubgroup.mono_overHom
  have : Mono j.hom.hom := hj.isClosedSubgroup.mono_overHom
  let hiR : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨inferInstance, rfl⟩
  let hjR : (SubgroupFunctor.range j).IsRepresentedBy j := ⟨inferInstance, rfl⟩
  let p := hiR.restrictionHom hjR q hrange.le
  have hsq : i ≫ q = p ≫ j := (hiR.restrictionHom_comp hjR q hrange.le).symm
  have hpb := (hiR.isPullback_of_comap_eq hjR q p hsq hrange.symm).map (Over.forget _)
  have : Surjective p.hom.hom.left :=
    MorphismProperty.of_isPullback hpb (inferInstance : Surjective q.hom.hom.left)
  have : LocallyOfFinitePresentation p.hom.hom.left :=
    MorphismProperty.of_isPullback hpb
      (inferInstance : LocallyOfFinitePresentation q.hom.hom.left)
  constructor
  · intro hB
    exact hj.isGeometricBorelSubgroup_of_isSolvable
      (hB.1.isSolvableGroupScheme.map_of_surjective p)
  · intro hB
    refine hi.isGeometricBorelSubgroup_of_isSolvable ?_
    let b := toAlgebraicClosure k
    let F := GroupScheme.baseChange b
    have hb := fieldExtension_fpqc k (AlgebraicClosure k)
    have : Surjective b := hb.1
    have : Flat b := hb.2.1
    have : Smooth H.X.hom := hi.smooth
    have : IsAffineHom H.X.hom := hi.isClosedSubgroup.isAffineHom
    have : Mono (F.map i).hom.hom := (hi.isClosedSubgroup.baseChange b).mono_overHom
    refine IsSolvableGroupScheme.of_baseChange b
      (inferInstanceAs (Smooth (pullback.snd H.X.hom b)))
      (inferInstanceAs (IsAffineHom (pullback.snd H.X.hom b))) ?_
    exact CentralIsogenyBorelPreimage.isSolvable_of_central_kernel (F.map q)
      (isCentral_kernelι_baseChange q hq) (F.map i) (F.map p) (F.map j)
      (by rw [← F.map_comp, hsq, F.map_comp])
      hB.1.isSolvableGroupScheme.baseChange_toAlgebraicClosure

end Field

section Relative

open RelativeLevi

variable {S : Scheme.{u}}

/-- Over a base scheme `S`, let `q : G ⟶ Gad` be an fppf quotient of a reductive group scheme
by its centre, with `Gad` affine over `S`. The inverse image under `q` of a parabolic subgroup
of `Gad` is a parabolic subgroup of `G`. -/
theorem isRelativeParabolicSubgroup_preimage
    {G Gad P' : GroupScheme S} (hG : IsReductive G) [IsAffineHom Gad.X.hom]
    {q : G ⟶ Gad} (hq : RelativeRoot.IsFppfQuotient (center G) q)
    {i' : P' ⟶ Gad} (hi' : IsRelativeParabolicSubgroup i') :
    IsRelativeParabolicSubgroup (SubgroupPreimage.inclusion q i') := by
  have hGad : IsReductive Gad := hq.isReductive_target hG
  have hi'c : IsClosedSubgroup i' := relativeParabolicClosed S Gad P' i' hGad hi'
  have := hG.isAffineHom
  have : Flat q.hom.hom.left := hq.1
  have : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  have : Smooth P'.X.hom := hi'.smooth
  let i := SubgroupPreimage.inclusion q i'
  let r := SubgroupPreimage.projection q i'
  have hic : IsClosedSubgroup i := SubgroupPreimage.isClosedSubgroup q i' hi'c
  have : Flat r.hom.hom.left := SubgroupPreimage.flat_projection q i'
  have : LocallyOfFinitePresentation r.hom.hom.left :=
    MorphismProperty.of_isPullback (SubgroupPreimage.isPullback_scheme q i') inferInstance
  have : Flat (SubgroupPreimage.groupScheme q i').X.hom := by
    rw [← Over.w r.hom.hom]
    infer_instance
  have : LocallyOfFinitePresentation (SubgroupPreimage.groupScheme q i').X.hom := by
    rw [← Over.w r.hom.hom]
    infer_instance
  have hfib : ∀ s : S, IsParabolicSubgroup (residueFiberHom i s) := by
    intro s
    let b : Spec (CommRingCat.of (S.residueField s)) ⟶ S := S.fromSpecResidueField s
    let F := GroupScheme.baseChange b
    have hAs : IsConnectedReductive (F.obj Gad) := hGad.isConnectedReductive_baseChange b
    have : Smooth (F.obj Gad).X.hom := hAs.smooth
    have : IsAffineHom (F.obj Gad).X.hom := hAs.isAffineHom
    have : ConnectedSpace (F.obj Gad).X.left := hAs.connectedSpace
    exact isParabolicSubgroup_of_range_eq_comap (hG.isConnectedReductive_baseChange b)
      (F.map q) (hq.baseChange_center b) (F.map i') (hi'.residueFiber s) (F.map i)
      (hic.baseChange b)
      (by rw [SubgroupFunctor.range_baseChangeHom, SubgroupPreimage.range_inclusion,
        SubgroupFunctor.comap_baseChange, ← SubgroupFunctor.range_baseChangeHom])
  refine ⟨?_, SubgroupPreimage.isAffineHom q i' hi'c, hic.mono_overHom, hfib⟩
  apply Smooth.of_smooth_fiberToSpecResidueField
  intro s
  exact (hfib s).smooth

/-- Clause 3 of `AdjointParabolicCorrespondenceStatement`: every parabolic subgroup of `Gad`
has a parabolic inverse image in `G`. -/
theorem exists_relativeParabolic_preimage
    {G Gad P' : GroupScheme S} (hG : IsReductive G) [IsAffineHom Gad.X.hom]
    {q : G ⟶ Gad} (hq : RelativeRoot.IsFppfQuotient (center G) q)
    {i' : P' ⟶ Gad} (hi' : IsRelativeParabolicSubgroup i') :
    ∃ (P : GroupScheme S) (i : P ⟶ G), IsRelativeParabolicSubgroup i ∧
      (SubgroupFunctor.range i').comap q = SubgroupFunctor.range i :=
  ⟨_, _, isRelativeParabolicSubgroup_preimage hG hq hi',
    (SubgroupPreimage.range_inclusion q i').symm⟩

/-- Clause 5 of `AdjointParabolicCorrespondenceStatement`: if a parabolic subgroup `i` of `G`
is the inverse image of a parabolic subgroup `i'` of `Gad`, then `i` is a Borel subgroup if and
only if `i'` is. -/
theorem isRelativeBorelSubgroup_iff_of_comap_eq
    {G Gad P P' : GroupScheme S} (hG : IsReductive G) [IsAffineHom Gad.X.hom]
    {q : G ⟶ Gad} (hq : RelativeRoot.IsFppfQuotient (center G) q)
    {i : P ⟶ G} {i' : P' ⟶ Gad}
    (hi : IsRelativeParabolicSubgroup i) (hi' : IsRelativeParabolicSubgroup i')
    (hrange : (SubgroupFunctor.range i').comap q = SubgroupFunctor.range i) :
    IsRelativeBorelSubgroup i ↔ IsRelativeBorelSubgroup i' := by
  have hGad : IsReductive Gad := hq.isReductive_target hG
  have hfib : ∀ s : S, IsGeometricBorelSubgroup (residueFiberHom i s) ↔
      IsGeometricBorelSubgroup (residueFiberHom i' s) := by
    intro s
    let b : Spec (CommRingCat.of (S.residueField s)) ⟶ S := S.fromSpecResidueField s
    let F := GroupScheme.baseChange b
    have hAs : IsConnectedReductive (F.obj Gad) := hGad.isConnectedReductive_baseChange b
    have : Smooth (F.obj Gad).X.hom := hAs.smooth
    have : IsAffineHom (F.obj Gad).X.hom := hAs.isAffineHom
    have : ConnectedSpace (F.obj Gad).X.left := hAs.connectedSpace
    exact isGeometricBorelSubgroup_iff_of_range_eq_comap (hG.isConnectedReductive_baseChange b)
      (F.map q) (hq.baseChange_center b) (F.map i') (hi'.residueFiber s) (F.map i)
      (hi.residueFiber s)
      (by rw [SubgroupFunctor.range_baseChangeHom, ← hrange,
        SubgroupFunctor.comap_baseChange, ← SubgroupFunctor.range_baseChangeHom])
  exact ⟨fun h => ⟨hi', fun s => (hfib s).mp (h.residueFiber s)⟩,
    fun h => ⟨hi, fun s => (hfib s).mpr (h.residueFiber s)⟩⟩

end Relative

end AdjointParabolicPreimage

end Langlands.GroupScheme
