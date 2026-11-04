import Langlands.GroupScheme.Rational.AlgClosedNormalSolvableTorusStatement
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientStatement
import Langlands.GroupScheme.Rational.NormalSplitTorusCentrality
import Langlands.GroupScheme.Absolute.RationalSubgroupContainment
import Langlands.GroupScheme.NormalizerRepresentability
import Langlands.GroupScheme.Derived.NormalityTransfer
import Langlands.GroupScheme.InnerAutomorphismHom
import Langlands.GroupScheme.Torus.UnipotentHom
import Langlands.GroupScheme.Rational.RootSubgroupVectorTransport
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Rational.LeviSplitComponentFactorization
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.SubgroupRangeTransport
import Langlands.GroupScheme.Torus.Lattice
import Langlands.GroupScheme.Torus.MaximalAmbient
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Normal solvable subgroups of reductive groups from split torus quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AlgClosedNormalSolvableTorus

variable {k : Type u} [Field k]
variable {G H U D : GroupScheme (Spec (CommRingCat.of k))}

/-- Conjugation by a rational point of `G` maps a closed subgroup with normal range
into itself. -/
theorem range_comp_innerIso_le (h : H ⟶ G) (hn : (SubgroupFunctor.range h).IsNormal)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    SubgroupFunctor.range (h ≫ (G.innerIso g).hom) ≤ SubgroupFunctor.range h := by
  intro V x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  rw [Grp.comp_hom_hom, ← Category.assoc, G.comp_innerIso_hom g V _]
  exact hn V _ _ (Subgroup.mem_top _) (SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩)

/-- The restriction of conjugation by a rational point to a closed subgroup with
normal range. -/
def conjRestrict (h : H ⟶ G) (hh : IsClosedSubgroup h)
    (hn : (SubgroupFunctor.range h).IsNormal)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) : H ⟶ H :=
  haveI : IsClosedImmersion h.hom.hom.left := hh
  SubgroupFunctor.IsRepresentedBy.factorHom
    (show (SubgroupFunctor.range h).IsRepresentedBy h from ⟨Over.mono_of_mono_left _, rfl⟩)
    (h ≫ (G.innerIso g).hom) (range_comp_innerIso_le h hn g)

theorem conjRestrict_comp (h : H ⟶ G) (hh : IsClosedSubgroup h)
    (hn : (SubgroupFunctor.range h).IsNormal)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    conjRestrict h hh hn g ≫ h = h ≫ (G.innerIso g).hom :=
  SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

/-- Conjugation by a rational point of `G` preserves the unipotent kernel `U` of a
split torus quotient `q` of a closed subgroup `H` with normal range. -/
theorem conj_mem_range_comp (h : H ⟶ G) (hh : IsClosedSubgroup h)
    (hn : (SubgroupFunctor.range h).IsNormal) (i : U ⟶ H) (hU : IsUnipotent U)
    (q : H ⟶ D) (hq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range i)
    (hD : IsSplitTorus D) (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    {V : Over (Spec (CommRingCat.of k))} {x : V ⟶ G.X}
    (hx : x ∈ (SubgroupFunctor.range (i ≫ h)).carrier V) :
    G.constantPoint g V * x * (G.constantPoint g V)⁻¹ ∈
      (SubgroupFunctor.range (i ≫ h)).carrier V := by
  obtain ⟨u, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  have h1 : u ≫ (i ≫ conjRestrict h hh hn g ≫ q).hom.hom = 1 :=
    hU.comp_eq_one_of_isSplitTorus hD (i ≫ conjRestrict h hh hn g ≫ q) V u
  have h2 : u ≫ (i ≫ conjRestrict h hh hn g).hom.hom ∈
      (SubgroupFunctor.range (kernelι q)).carrier V := by
    rw [mem_range_kernelι_iff]
    simp only [Grp.comp_hom_hom, Category.assoc] at h1 ⊢
    exact h1
  rw [hq] at h2
  obtain ⟨v, hv⟩ := SubgroupFunctor.mem_range.mp h2
  refine SubgroupFunctor.mem_range.mpr ⟨v, ?_⟩
  calc v ≫ (i ≫ h).hom.hom = (u ≫ (i ≫ conjRestrict h hh hn g).hom.hom) ≫ h.hom.hom := by
        rw [← hv, Grp.comp_hom_hom, Category.assoc]
    _ = (u ≫ (i ≫ h).hom.hom) ≫ (G.innerIso g).hom.hom.hom := by
        have := congrArg (fun f => u ≫ i.hom.hom ≫ f.hom.hom) (conjRestrict_comp h hh hn g)
        simp only [Grp.comp_hom_hom, Category.assoc] at this ⊢
        exact this
    _ = _ := G.comp_innerIso_hom g V _

/-- Over an algebraically closed field, the unipotent kernel of a split torus
quotient of a closed subgroup with normal range of a smooth affine group has normal
range in the ambient group. -/
theorem isNormal_range_comp [IsAlgClosed k] [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (h : H ⟶ G) (hh : IsClosedSubgroup h) (hn : (SubgroupFunctor.range h).IsNormal)
    (i : U ⟶ H) (hi : IsClosedSubgroup i) (hU : IsUnipotent U)
    (q : H ⟶ D) (hq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range i)
    (hD : IsSplitTorus D) :
    (SubgroupFunctor.range (i ≫ h)).IsNormal := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsReduced G.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k G.X.left G.X.hom
  obtain ⟨N, n, hnc, hr⟩ :=
    (hasClosedRepresentative_normalizer_centralizer_range (i ≫ h) (hi.comp hh)).1
  have hle : SubgroupFunctor.range (𝟙 G) ≤ SubgroupFunctor.range n := by
    apply SubgroupFunctor.range_le_of_algClosed_points hnc
    intro g _
    rw [hr.2]
    intro V a x hx
    rw [comp_eq_constantPoint a g]
    constructor
    · exact conj_mem_range_comp h hh hn i hU q hq hD g hx
    · have := conj_mem_range_comp h hh hn i hU q hq hD g⁻¹ hx
      simpa only [constantPoint_inv, inv_inv] using this
  apply SubgroupFunctor.isNormal_of_normalizer_eq_top
  apply le_antisymm
  · intro V g _
    exact Subgroup.mem_top _
  intro V g _
  rw [← hr.2]
  exact hle V (SubgroupFunctor.mem_range.mpr ⟨g, by
    simp only [Grp.id_hom_hom, Category.comp_id]⟩)

/-- A smooth connected solvable closed subgroup with normal range of a
pseudo-reductive group over an algebraically closed field is a central torus, given
split torus quotients of smooth connected solvable groups. -/
theorem isTorus_isCentral_of_solvableTorusQuotient
    (hquot : SolvableTorusQuotientStatement.{u}) [IsAlgClosed k]
    (hG : IsPseudoReductive G) (h : H ⟶ G) (hh : IsClosedSubgroup h)
    [Smooth H.X.hom] [ConnectedSpace H.X.left] (hsol : IsSolvableGroupScheme H)
    (hn : (SubgroupFunctor.range h).IsNormal) : IsTorus H ∧ IsCentral h := by
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : ConnectedSpace G.X.left := hG.connectedSpace
  have : IsAffineHom H.X.hom := hh.isAffineHom_source
  obtain ⟨U, D, i, q, hi, hUs, hUc, hU, -, hq, hD⟩ := hquot k H hsol
  have hnorm := isNormal_range_comp h hh hn i hi hU q hq.2.2.2 hD
  have hbot : SubgroupFunctor.range (i ≫ h) = ⊥ :=
    hG.hasTrivialUnipotentRadical U (i ≫ h) (hi.comp hh) hUs hUc hU hnorm
  have : IsClosedImmersion h.hom.hom.left := hh
  have : Mono h.hom.hom := Over.mono_of_mono_left _
  have hibot : SubgroupFunctor.range i = ⊥ :=
    (SubgroupFunctor.range_comp_eq_bot_iff i h).mp hbot
  have hq' : RelativeRoot.IsFppfQuotient ⊥ q := by
    rw [← hibot]
    exact hq
  have hHs : IsSplitTorus H := hD.of_iso hq'.isoOfBot
  have hHt : IsTorus H := hHs.isTorus
  refine ⟨hHt, ?_⟩
  let T : CommGroupScheme (Spec (CommRingCat.of k)) := { toGrp := H, comm := hHt.isCommMonObj }
  have : Mono h.hom.hom.left := hh.mono
  exact isCentral_of_isNormal_of_isSplitTorus (T := T) h hHs hn

end AlgClosedNormalSolvableTorus

/-- Normal solvable subgroups of reductive groups over algebraically closed fields
are central tori, given split torus quotients of smooth connected solvable groups. -/
def AlgClosedNormalSolvableTorusFromQuotientStatement : Prop :=
  SolvableTorusQuotientStatement.{u} → AlgClosedReductiveNormalSolvableTorusStatement.{u}

/-- The split torus quotient statement implies that normal solvable subgroups of
reductive groups over algebraically closed fields are central tori. -/
theorem algClosedReductiveNormalSolvableTorus_of_quotient :
    AlgClosedNormalSolvableTorusFromQuotientStatement.{u} := by
  intro hquot k _ _ G hG H h hh hs hc hsol hn
  exact AlgClosedNormalSolvableTorus.isTorus_isCentral_of_solvableTorusQuotient
    hquot hG h hh hsol hn

end Langlands.GroupScheme
