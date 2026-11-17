import Langlands.GroupScheme.Reductive.ParabolicContainsCenter
import Langlands.GroupScheme.RelativeCentralMultiplicativeTypeQuotientStatement
import Langlands.GroupScheme.FppfQuotientComparison
import Langlands.GroupScheme.SubgroupFunctor.QuotientEmbedding
import Langlands.GroupScheme.Torus.RelativeQuotient
import Langlands.GroupScheme.CentralIsogeny.BorelPreimage
import Langlands.GroupScheme.HomImage
import Langlands.GroupScheme.RelativeLevi.Reductivity
import Langlands.GroupScheme.RelativeLevi.ParabolicClosedProof
import Langlands.GroupScheme.Absolute.ParabolicTransport
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.ClosedSubgroupMonomorphism
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-! # Images of parabolic subgroups in a quotient by the centre -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace AdjointParabolicCorrespondence

/-- Centrality of the actual kernel is preserved by every change of base. -/
theorem isCentral_kernelι_baseChange {S S' : Scheme.{u}} (b : S' ⟶ S)
    {G Q : GroupScheme S} (q : G ⟶ Q) (hq : IsCentral (kernelι q)) :
    IsCentral (kernelι ((GroupScheme.baseChange b).map q)) := by
  rw [isCentral_iff_range_le_center, kernel_range_baseChange,
    ← SubgroupFunctor.range_baseChangeHom]
  exact (isCentral_iff_range_le_center _).mp (hq.baseChange b)

section Field

variable {k : Type u} [Field k]
    {G A : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [IsAffineHom A.X.hom]
    (q : G ⟶ A) [Flat q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]
    (hq : IsCentral (kernelι q))

include hq in
/-- Over a field, a smooth closed image of a parabolic subgroup under a
homomorphism with central kernel is parabolic. -/
theorem isParabolicSubgroup_image_of_centralKernel
    {P I : GroupScheme (Spec (CommRingCat.of k))}
    (i : P ⟶ G) (hi : IsParabolicSubgroup i)
    (p : P ⟶ I) [Surjective p.hom.hom.left]
    (j : I ⟶ A) (hj : IsClosedSubgroup j) [Smooth I.X.hom]
    (hsq : i ≫ q = p ≫ j) : IsParabolicSubgroup j := by
  have : IsAffineHom I.X.hom := hj.isAffineHom
  refine ⟨hj, inferInstance, ?_⟩
  let b := toAlgebraicClosure k
  let F := GroupScheme.baseChange b
  have : Smooth (F.obj G).X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.X.hom b))
  have : IsAffineHom (F.obj G).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom b))
  have : IsAffineHom (F.obj A).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd A.X.hom b))
  have : IsAffineHom (F.obj I).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd I.X.hom b))
  have : LocallyOfFiniteType (F.obj I).X.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd I.X.hom b))
  have : Flat (F.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Flat) b q.hom.hom inferInstance
  have : LocallyOfFinitePresentation (F.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFinitePresentation) b q.hom.hom
      inferInstance
  have hqF : IsCentral (kernelι (F.map q)) := isCentral_kernelι_baseChange b q hq
  obtain ⟨B, jB, a, hjB, ha⟩ := hi.exists_isBorelSubgroup
  have : Smooth B.X.hom := hjB.smooth
  have : ConnectedSpace B.X.left := hjB.connectedSpace
  have : IsAffineHom B.X.hom := hjB.isClosedSubgroup.isAffineHom
  obtain ⟨J, c, d, hc, hd, _, hds, _, hdl, hJs, hJc, _⟩ :=
    HomImage.exists_image (a ≫ F.map p)
  have : Surjective d.hom.hom.left := hds
  have : LocallyOfFinitePresentation d.hom.hom.left := hdl
  have : Smooth J.X.hom := hJs
  have : ConnectedSpace J.X.left := hJc
  have hcs : IsClosedSubgroup (c ≫ F.map j) := hc.comp (hj.baseChange b)
  have hsqB : jB ≫ F.map q = d ≫ (c ≫ F.map j) := by
    calc
      jB ≫ F.map q = (a ≫ F.map i) ≫ F.map q := by rw [ha]
      _ = a ≫ F.map (i ≫ q) := by rw [F.map_comp, Category.assoc]
      _ = (a ≫ F.map p) ≫ F.map j := by rw [hsq, F.map_comp, Category.assoc]
      _ = d ≫ (c ≫ F.map j) := by rw [← hd, Category.assoc]
  have hB := CentralIsogenyBorelPreimage.isBorelSubgroup_image jB hjB (F.map q) hqF
    d (c ≫ F.map j) hcs hsqB
  exact ⟨J, c ≫ F.map j, c, hB, rfl⟩

end Field

section Base

variable {S : Scheme.{u}}

/-- A homomorphism between groups affine over the base is quasi-compact. -/
theorem quasiCompact_of_isAffineHom {G Q : GroupScheme S} (q : G ⟶ Q)
    [IsAffineHom G.X.hom] [IsAffineHom Q.X.hom] : QuasiCompact q.hom.hom.left := by
  have : IsAffineHom (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  have : IsAffineHom q.hom.hom.left := IsAffineHom.of_comp q.hom.hom.left Q.X.hom
  infer_instance

/-- An fppf quotient that receives a comparison map from a quasi-compact fppf
quotient of the same subgroup is isomorphic to it. -/
theorem isIso_comparison {G Q R : GroupScheme S} {F : SubgroupFunctor G}
    {q : G ⟶ Q} {r : G ⟶ R}
    (hq : RelativeRoot.IsFppfQuotient F q) (hr : RelativeRoot.IsFppfQuotient F r)
    [QuasiCompact q.hom.hom.left] :
    IsIso (FppfQuotientComparison.hom hq hr).hom.hom.left := by
  have : Flat q.hom.hom.left := hq.1
  have : Surjective q.hom.hom.left := hq.2.1
  have : Flat r.hom.hom.left := hr.1
  have : Surjective r.hom.hom.left := hr.2.1
  have : LocallyOfFinitePresentation r.hom.hom.left := hr.2.2.1
  have hkernel : SubgroupFunctor.range (kernelι q) ≤
      (SubgroupFunctor.range (kernelι r)).comap (𝟙 G) := by
    intro T x hx
    change x ≫ 𝟙 G.X ∈ (SubgroupFunctor.range (kernelι r)).carrier T
    rw [Category.comp_id, hr.2.2.2, ← hq.2.2.2]
    exact hx
  have hkernel' : (SubgroupFunctor.range (kernelι r)).comap (𝟙 G) ≤
      SubgroupFunctor.range (kernelι q) := by
    intro T x hx
    change x ≫ 𝟙 G.X ∈ (SubgroupFunctor.range (kernelι r)).carrier T at hx
    rw [Category.comp_id, hr.2.2.2, ← hq.2.2.2] at hx
    exact hx
  have hcontain : SubgroupFunctor.range (kernelι r) ≤ SubgroupFunctor.range (𝟙 G) := by
    intro T x _
    exact SubgroupFunctor.mem_range.mpr ⟨x, Category.comp_id _⟩
  have he : FppfQuotientComparison.hom hq hr =
      SubgroupFunctor.quotientSubgroupHom (𝟙 G) r q hkernel :=
    SubgroupFunctor.quotientSubgroupHom_unique (𝟙 G) r q hkernel _
      (by rw [Category.id_comp, FppfQuotientComparison.fac])
  have hpb := (SubgroupFunctor.quotientSubgroupHom_isPullback (𝟙 G) r q hkernel
    hkernel' hcontain).map (Over.forget S)
  rw [he]
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := MorphismProperty.isomorphisms Scheme)
    (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
    hpb ⟨⟨(hr.2.1 : Surjective r.hom.hom.left), (hr.1 : Flat r.hom.hom.left)⟩,
      (hr.2.2.1 : LocallyOfFinitePresentation r.hom.hom.left)⟩
    (inferInstanceAs (IsIso (𝟙 G.X.left)))

/-- Given the central multiplicative-type quotient construction, every fppf
quotient of a reductive group by its centre is affine over the base. -/
theorem isAffineHom_of_isFppfQuotient_center
    (hquot : RelativeCentralMultiplicativeTypeQuotientStatement.{u})
    {G Gad : GroupScheme S} (hG : IsReductive G) {q : G ⟶ Gad}
    (hq : RelativeRoot.IsFppfQuotient (center G) q) : IsAffineHom Gad.X.hom := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨Z, z, hz, hZ, -⟩ := reductiveRelativeCenter S G hG
  obtain ⟨Q₀, q₀, hQ₀, hq₀⟩ := hquot S G hG.smooth hG.isAffineHom
    (fun s => (hG.geometricFiber s).connectedSpace) Z z hz.1 hz.isCentral hZ
  rw [hz.2] at hq₀
  have : IsAffineHom Q₀.X.hom := hQ₀
  have : QuasiCompact q₀.hom.hom.left := quasiCompact_of_isAffineHom q₀
  have : IsIso (FppfQuotientComparison.hom hq₀ hq).hom.hom.left := isIso_comparison hq₀ hq
  have hw : Gad.X.hom = inv (FppfQuotientComparison.hom hq₀ hq).hom.hom.left ≫ Q₀.X.hom := by
    rw [IsIso.eq_inv_comp, Over.w (FppfQuotientComparison.hom hq₀ hq).hom.hom]
  rw [hw]
  infer_instance

/-- Given the central multiplicative-type quotient construction, every relative
parabolic subgroup of a reductive group is the full inverse image of a relative
parabolic subgroup of any fppf quotient by the centre. -/
theorem exists_parabolic_image
    (hquot : RelativeCentralMultiplicativeTypeQuotientStatement.{u})
    {G Gad : GroupScheme S} (hG : IsReductive G) {q : G ⟶ Gad}
    (hq : RelativeRoot.IsFppfQuotient (center G) q)
    {P : GroupScheme S} {i : P ⟶ G} (hi : IsRelativeParabolicSubgroup i) :
    ∃ (P' : GroupScheme S) (i' : P' ⟶ Gad), IsRelativeParabolicSubgroup i' ∧
      (SubgroupFunctor.range i').comap q = SubgroupFunctor.range i := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffineHom Gad.X.hom := isAffineHom_of_isFppfQuotient_center hquot hG hq
  have : Smooth P.X.hom := hi.smooth
  have : IsAffineHom P.X.hom := hi.isAffineHom
  have : Mono i.hom.hom := hi.mono
  have : Flat q.hom.hom.left := hq.1
  have : Surjective q.hom.hom.left := hq.2.1
  have : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  have : QuasiCompact q.hom.hom.left := quasiCompact_of_isAffineHom q
  have hic : IsClosedSubgroup i := relativeParabolicClosed S G P i hG hi
  have hcenter := hi.center_le_range hG
  obtain ⟨Z, z, hz, hZ, -⟩ := reductiveRelativeCenter S G hG
  have : Mono z.hom.hom := hz.1.mono_overHom
  have hle : SubgroupFunctor.range z ≤ SubgroupFunctor.range i := hz.2 ▸ hcenter
  let zP : Z ⟶ P := SubgroupFunctor.factorOfRangeLE hle
  have hzP : zP ≫ i = z := SubgroupFunctor.factorOfRangeLE_comp hle
  have hzPc : IsClosedSubgroup zP := IsClosedSubgroup.of_comp hic (hzP ▸ hz.1)
  have hzPcen : IsCentral zP := IsCentral.of_comp hi.mono (hzP ▸ hz.isCentral)
  obtain ⟨Q, π, hQ, hπ⟩ := hquot S P hi.smooth hi.isAffineHom
    (hi.connectedSpace_geometricFiber hG) Z zP hzPc hzPcen hZ
  have : IsAffineHom Q.X.hom := hQ
  have : Flat π.hom.hom.left := hπ.1
  have : Surjective π.hom.hom.left := hπ.2.1
  have : LocallyOfFinitePresentation π.hom.hom.left := hπ.2.2.1
  have : QuasiCompact π.hom.hom.left := quasiCompact_of_isAffineHom π
  have : Smooth Q.X.hom := smooth_target_of_surjective_flat_hom_overBase π
  have hzPi : zP.hom.hom ≫ i.hom.hom = z.hom.hom := by
    rw [← Grp.comp_hom_hom, hzP]
  have hkernel : SubgroupFunctor.range (kernelι π) ≤
      (SubgroupFunctor.range (kernelι q)).comap i := by
    rw [hπ.2.2.2, hq.2.2.2, ← hz.2]
    intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    change (y ≫ zP.hom.hom) ≫ i.hom.hom ∈ (SubgroupFunctor.range z).carrier T
    exact SubgroupFunctor.mem_range.mpr ⟨y, by rw [Category.assoc, hzPi]⟩
  have hkernel' : (SubgroupFunctor.range (kernelι q)).comap i ≤
      SubgroupFunctor.range (kernelι π) := by
    rw [hπ.2.2.2, hq.2.2.2, ← hz.2]
    intro T x hx
    change x ≫ i.hom.hom ∈ (SubgroupFunctor.range z).carrier T at hx
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hx
    refine SubgroupFunctor.mem_range.mpr ⟨y, ?_⟩
    apply (cancel_mono i.hom.hom).mp
    rw [Category.assoc, hzPi, hy]
  have hcontain : SubgroupFunctor.range (kernelι q) ≤ SubgroupFunctor.range i := by
    rw [hq.2.2.2]
    exact hcenter
  let i' := SubgroupFunctor.quotientSubgroupHom i q π hkernel
  have : Mono i'.hom.hom :=
    SubgroupFunctor.quotientSubgroupHom_mono i q π hkernel hkernel'
  have hi'c : IsClosedSubgroup i' :=
    SubgroupFunctor.quotientSubgroupHom_isClosedSubgroup i q π hkernel hkernel'
      hcontain hic
  have hsq : i ≫ q = π ≫ i' := SubgroupFunctor.quotientSubgroupHom_square i q π hkernel
  have hqc : IsCentral (kernelι q) := by
    rw [isCentral_iff_range_le_center, hq.2.2.2]
  refine ⟨Q, i', ⟨inferInstance, hQ, inferInstance, fun s => ?_⟩,
    SubgroupFunctor.quotientSubgroupHom_comap_range i q π hkernel hcontain⟩
  let b : Spec (CommRingCat.of (S.residueField s)) ⟶ S := S.fromSpecResidueField s
  let F := GroupScheme.baseChange b
  have hGs := hG.isConnectedReductive_residueFiber s
  have : Smooth (F.obj G).X.hom := hGs.smooth
  have : IsAffineHom (F.obj G).X.hom := hGs.isAffineHom
  have : IsAffineHom (F.obj Gad).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd Gad.X.hom b))
  have : Smooth (F.obj Q).X.hom := inferInstanceAs (Smooth (pullback.snd Q.X.hom b))
  have : Flat (F.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Flat) b q.hom.hom inferInstance
  have : LocallyOfFinitePresentation (F.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFinitePresentation) b q.hom.hom
      inferInstance
  have : Surjective (F.map π).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Surjective) b π.hom.hom inferInstance
  exact isParabolicSubgroup_image_of_centralKernel (F.map q)
    (isCentral_kernelι_baseChange b q hqc) (F.map i) (hi.residueFiber s) (F.map π)
    (F.map i') (hi'c.baseChange (b := b))
    (by rw [← F.map_comp, ← F.map_comp, hsq])

end Base

end AdjointParabolicCorrespondence

end Langlands.GroupScheme
