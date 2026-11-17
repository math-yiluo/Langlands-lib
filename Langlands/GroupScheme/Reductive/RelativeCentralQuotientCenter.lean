import Langlands.GroupScheme.Reductive.MultiplicativeTypeNormalCentralStatement
import Langlands.GroupScheme.Reductive.RelativeCenterProof
import Langlands.GroupScheme.Reductive.UnipotentRadicalQuotientReduction
import Langlands.GroupScheme.Reductive.BaseChange

/-! # Centre comparison for relative central quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G Q Z : GroupScheme S}

/-- The all-test centre maps into the all-test centre under a flat surjective
homomorphism of group schemes. -/
theorem center_le_comap_of_flat_surjective_hom (q : G ⟶ Q)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left] :
    center G ≤ (center Q).comap q := by
  intro U x hx
  change x ≫ q.hom.hom ∈ (center Q).carrier U
  intro V a y
  let W : Over S := Over.mk (pullback.fst y.left q.hom.hom.left ≫ V.hom)
  let v : W ⟶ V := Over.homMk (pullback.fst y.left q.hom.hom.left) rfl
  let g : W ⟶ G.X := Over.homMk (pullback.snd y.left q.hom.hom.left) (by
    rw [← Over.w q.hom.hom, ← Category.assoc, ← pullback.condition,
      Category.assoc, Over.w y]
    rfl)
  let : Flat v.left := show Flat (pullback.fst y.left q.hom.hom.left) from inferInstance
  let : Surjective v.left :=
    show Surjective (pullback.fst y.left q.hom.hom.left) from inferInstance
  let : Epi v.left := Flat.epi_of_flat_of_surjective v.left
  let : Epi v := Over.epi_of_epi_left _
  have he : v ≫ y = g ≫ q.hom.hom := Over.OverMorphism.ext pullback.condition
  have hc := (hx W (v ≫ a) g).map ((yonedaGrp.map q).app (Opposite.op W)).hom
  change Commute (((v ≫ a) ≫ x) ≫ q.hom.hom) (g ≫ q.hom.hom) at hc
  rw [← he] at hc
  apply (cancel_epi v).mp
  simpa only [MonObj.comp_mul, Category.assoc] using hc.eq

/-- The centre-preimage clause for a supplied central quotient follows from
the normal multiplicative-type centrality theorem. The latter remains an
explicit assumption. -/
theorem RelativeRoot.IsFppfQuotient.center_comap_eq_of_multiplicativeTypeNormalCentral
    (h : MultiplicativeTypeNormalCentralStatement.{u})
    (hG : IsReductive G) (hQ : IsReductive Q)
    (z : Z ⟶ G) (hz : IsClosedSubgroup z) (hc : IsCentral z)
    (hZ : RelativeMultiplicativeType.IsMultiplicativeType Z)
    (q : G ⟶ Q) (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range z) q) :
    (center Q).comap q = center G := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Flat q.hom.hom.left := hq.1
  let : Surjective q.hom.hom.left := hq.2.1
  have hn : (SubgroupFunctor.range z).IsNormal := by
    intro U g x _ hx
    have hxcent := (isCentral_iff_range_le_center z).mp hc U hx
    have he : g * x * g⁻¹ = x := by
      rw [(commute_of_mem_center hxcent g).symm.eq, mul_inv_cancel_right]
    rwa [he]
  obtain ⟨C, c, hcenter, hC, _⟩ := reductiveRelativeCenter S Q hQ
  let P := SubgroupPreimage.groupScheme q c
  let p : P ⟶ G := SubgroupPreimage.inclusion q c
  have hpclosed : IsClosedSubgroup p := SubgroupPreimage.isClosedSubgroup q c hcenter.1
  let : IsClosedImmersion p.hom.hom.left := hpclosed
  have hprep : ((SubgroupFunctor.range c).comap q).IsRepresentedBy p :=
    ⟨Over.mono_of_mono_left _, SubgroupPreimage.range_inclusion q c⟩
  have hpcentral : IsCentral p :=
    ((h S G (fun s => (hG.isConnectedReductive_residueFiber s).connectedSpace)
      Z z hz hZ hn).2 Q q hq C c hcenter.1 hC hcenter.isCentral P p hprep).2
  apply le_antisymm
  · rw [← hcenter.2, ← SubgroupPreimage.range_inclusion q c]
    exact (isCentral_iff_range_le_center p).mp hpcentral
  · exact center_le_comap_of_flat_surjective_hom q


/-- The complete proposition proved by the supplied helper, with every hypothesis explicit. -/
def RelativeCentralQuotientCenterReductionStatement : Prop :=
  ∀
    {S : Scheme.{u}} {G Q Z : GroupScheme S}

    (_h : MultiplicativeTypeNormalCentralStatement.{u})
    (_hG : IsReductive G) (_hQ : IsReductive Q)
    (z : Z ⟶ G) (_hz : IsClosedSubgroup z) (_hc : IsCentral z)
    (_hZ : RelativeMultiplicativeType.IsMultiplicativeType Z)
    (q : G ⟶ Q) (_hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range z) q),
    (center Q).comap q = center G

/-- The retained helper proof establishes the named proposition. -/
theorem relativeCentralQuotientCenterReduction : RelativeCentralQuotientCenterReductionStatement.{u} := by
  unfold RelativeCentralQuotientCenterReductionStatement
  exact @RelativeRoot.IsFppfQuotient.center_comap_eq_of_multiplicativeTypeNormalCentral.{u}

end Langlands.GroupScheme
