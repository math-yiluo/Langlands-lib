import Langlands.GroupScheme.SimplyConnected.FactorRootDatum
import Langlands.GroupScheme.Reductive.PinningConstruction
import Langlands.GroupScheme.Reductive.SplitBorelCell
import Langlands.GroupScheme.Reductive.RootDatumGaloisSimpleRoots
import Langlands.GroupScheme.Reductive.RegularCocharacterPinning
import Langlands.LinearAlgebra.RootDatumCoweightFace

/-! # The ambient simple base induces an actual base on each product factor -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.SimplyConnectedAlmostSimpleProduct
namespace FactorMaximalTorus

section Projection

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {D : SimplyConnectedAlmostSimpleProduct G}
  {T : CommGroupScheme (Spec (CommRingCat.of k))} {t : T.toGrp ⟶ G}
  {i j : D.Index} (F : D.FactorMaximalTorus t i) (F' : D.FactorMaximalTorus t j)

omit [IsAffineHom G.X.hom] in
/-- Distinct actual factor-torus blocks have zero cross projection. -/
theorem torusHom_projectionHom_ne (hij : i ≠ j) : F.torusHom ≫ F'.projectionHom = 0 := by
  apply CommGroupScheme.hom_ext_points
  intro U x
  rw [comp_groupHom_comp, comp_groupHom_zero]
  have : IsClosedImmersion F'.subgroupHom.hom.hom.left := F'.isMaximalTorus.2.1
  have : Mono F'.subgroupHom.hom.hom := Over.mono_of_mono_left _
  apply (cancel_mono F'.subgroupHom.hom.hom).mp
  rw [MonObj.one_comp]
  calc
    _ = (x ≫ (CommGroupScheme.groupHom F.torusHom).hom.hom) ≫
        (t ≫ D.projection j).hom.hom := by
      rw [Category.assoc, ← Grp.comp_hom_hom]
      change (x ≫ (CommGroupScheme.groupHom F.torusHom).hom.hom) ≫
        (F'.projection ≫ F'.subgroupHom).hom.hom = _
      rw [F'.projection_comp]
    _ = ((x ≫ F.subgroupHom.hom.hom) ≫ (D.inclusion i).hom.hom) ≫
        (D.projection j).hom.hom := by
      simpa only [Grp.comp_hom_hom, Category.assoc] using
        congrArg (fun f : F.torus.toGrp ⟶ G =>
          (x ≫ f.hom.hom) ≫ (D.projection j).hom.hom) F.comp_eq
    _ = 1 := D.inclusion_projection_points_ne i j hij _

variable (hG : IsSemisimple G) (hT : IsSplitTorus T.toGrp) (ht : IsMaximalTorus t)

/-- An ambient root in another actual factor restricts to zero on this
factor's compatible torus. -/
theorem root_restrict_eq_zero_of_other {α : characterLattice T} (hα : α ∈ roots t)
    (hne : D.rootFactorIndex hG hT t ht hα ≠ i) : F.torusHom ≫ α = 0 := by
  let j := D.rootFactorIndex hG hT t ht hα
  let F' := D.factorMaximalTorus hG.isConnectedReductive t hT ht j
  obtain ⟨β, _hβ, hβα⟩ := F'.root_restriction hG hT ht hα rfl
  rw [← hβα, ← Category.assoc,
    F.torusHom_projectionHom_ne F' (Ne.symm hne), Limits.zero_comp]

end Projection

section Base

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (D : SimplyConnectedAlmostSimpleProduct G) (hG : IsSemisimple G) (p : SplitPinning G)
  {i : D.Index} (F : D.FactorMaximalTorus p.inclusion i)

private instance factorRootBase_factorAffine : IsAffineHom (D.factor i).X.hom :=
  (D.isSimplyConnected i).isSemisimple.isConnectedReductive.isAffineHom

variable {K : Type u} [Finite K]
  {Q : RootDatum K (characterLattice F.torus) (cocharacterLattice F.torus)}
  (hQ : IsRootDatumOf F.subgroupHom Q) [Q.IsReduced]

local notation "idx" => F.rootIndex D hG p.isSplitTorus p.inclusion p.isMaximalTorus p.isRootDatum hQ

omit [Finite K] [Q.IsReduced] in
/-- Restriction to the factor torus is inverse to literal root inflation. -/
theorem rootIndex_restrict (b : K) : F.torusHom ≫ p.rootDatum.root (idx b) = Q.root b := by
  rw [F.rootIndex_root D hG p.isSplitTorus p.inclusion p.isMaximalTorus p.isRootDatum hQ,
    ← Category.assoc, F.torusHom_projectionHom, Category.id_comp]

/-- The ambient positive cocharacter projected to the actual factor torus. -/
def factorPositiveCocharacter : cocharacterLattice F.torus :=
  p.positiveCocharacter ≫ F.projectionHom

omit [Finite K] [Q.IsReduced] in
/-- Every factor-root pairing is the original positive scale times the
height of its ambient root. -/
theorem pairing_factorPositiveCocharacter (b : K) :
    Q.root' b (F.factorPositiveCocharacter D p) = p.positiveScale * p.base.height (idx b) := by
  change Q.toLinearMap (Q.root b) (p.positiveCocharacter ≫ F.projectionHom) = _
  rw [hQ.1]
  change gmEndEquiv k ((p.positiveCocharacter ≫ F.projectionHom) ≫ Q.root b) = _
  rw [Category.assoc, ← F.rootIndex_root D hG p.isSplitTorus p.inclusion
    p.isMaximalTorus p.isRootDatum hQ]
  exact p.latticePairing_root_positiveCocharacter (idx b)

include hG hQ in
omit [Finite K] [Q.IsReduced] in
/-- The projected cocharacter is regular on all actual factor roots. -/
theorem factorPositiveCocharacter_regular (b : K) :
    Q.root' b (F.factorPositiveCocharacter D p) ≠ 0 := by
  rw [F.pairing_factorPositiveCocharacter D hG p hQ]
  have h := p.latticePairing_root_positiveCocharacter_ne_zero (idx b)
  rwa [p.latticePairing_root_positiveCocharacter] at h

/-- A genuine integral base on the original factor lattices selected by
the projected ambient positive cocharacter. -/
def inducedBase : Q.Base := by
  let := Fintype.ofFinite K
  exact (Langlands.LinearAlgebra.RootDatumCoweightFace.exists_base_support Q
    (F.factorPositiveCocharacter D p) (F.factorPositiveCocharacter_regular D hG p hQ)).choose

theorem inducedBase_support :
    ((F.inducedBase D hG p hQ).support : Set K) =
      IsAddIndecomposable.baseOf Q.root
        ((Q.flip.toLinearMap (F.factorPositiveCocharacter D p)) : _ →+ ℤ) := by
  let := Fintype.ofFinite K
  exact (Langlands.LinearAlgebra.RootDatumCoweightFace.exists_base_support Q
    (F.factorPositiveCocharacter D p) (F.factorPositiveCocharacter_regular D hG p hQ)).choose_spec

/-- Factor positivity is exactly positivity of the corresponding ambient root. -/
theorem inducedBase_isPos (b : K) :
    (F.inducedBase D hG p hQ).IsPos b ↔ p.base.IsPos (idx b) := by
  have hsign : (F.inducedBase D hG p hQ).IsPos b ↔
      0 < Q.root' b (F.factorPositiveCocharacter D p) := by
    apply RootPairing.Base.isPos_iff_positive_functional Q _
      (Q.flip.toLinearMap (F.factorPositiveCocharacter D p))
    intro c hc
    have hmem : c ∈ IsAddIndecomposable.baseOf Q.root
        ((Q.flip.toLinearMap (F.factorPositiveCocharacter D p)) : _ →+ ℤ) := by
      rw [← F.inducedBase_support D hG p hQ]
      exact hc
    exact hmem.1
  rw [hsign, F.pairing_factorPositiveCocharacter D hG p hQ,
    RootPairing.Base.isPos_iff]
  exact ⟨fun h => pos_of_mul_pos_right h p.positiveScale_pos.le,
    fun h => mul_pos p.positiveScale_pos h⟩

/-- Any ambient simple root carried by the factor is simple in the induced base. -/
theorem mem_inducedBase_of_mem_ambient {b : K} (hb : idx b ∈ p.base.support) :
    b ∈ (F.inducedBase D hG p hQ).support := by
  rw [RootPairing.Base.mem_support_iff_positive_indecomposable]
  refine ⟨(F.inducedBase_isPos D hG p hQ b).mpr (p.base.isPos_of_mem_support hb), ?_⟩
  intro a c ha hc heq
  have hmem := (RootPairing.Base.mem_support_iff_positive_indecomposable
    p.rootDatum p.base (idx b)).mp hb
  apply hmem.2 (idx a) (idx c)
    ((F.inducedBase_isPos D hG p hQ a).mp ha)
    ((F.inducedBase_isPos D hG p hQ c).mp hc)
  rw [F.rootIndex_root D hG p.isSplitTorus p.inclusion p.isMaximalTorus p.isRootDatum hQ,
    heq, Preadditive.comp_add,
    ← F.rootIndex_root D hG p.isSplitTorus p.inclusion p.isMaximalTorus p.isRootDatum hQ,
    ← F.rootIndex_root D hG p.isSplitTorus p.inclusion p.isMaximalTorus p.isRootDatum hQ]

omit [Finite K] [Q.IsReduced] in
/-- The factor roots are integrally spanned by precisely the ambient simple
roots lying in that factor, restricted to its actual torus. -/
theorem root_mem_span_ambient_simples (b : K) :
    Q.root b ∈ Submodule.span ℤ (Q.root '' {c : K | idx c ∈ p.base.support}) := by
  let M := Submodule.span ℤ (Q.root '' {c : K | idx c ∈ p.base.support})
  have hmem : p.rootDatum.root (idx b) ∈
      Submodule.span ℤ (p.rootDatum.root '' (p.base.support : Set p.rootIndex)) :=
    p.base.root_mem_span_int (idx b)
  have haux : ∀ a ∈ Submodule.span ℤ
      (p.rootDatum.root '' (p.base.support : Set p.rootIndex)), F.torusHom ≫ a ∈ M := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨r, hr, rfl⟩ := ha
      have hroot : p.rootDatum.root r ∈ roots p.inclusion := by
        rw [← p.isRootDatum.2.1]
        exact Set.mem_range_self r
      by_cases hi : D.rootDatumFactorIndex hG p.isSplitTorus p.inclusion
          p.isMaximalTorus p.isRootDatum r = i
      · obtain ⟨c, hc⟩ := F.rootIndex_surjective D hG p.isSplitTorus p.inclusion
          p.isMaximalTorus p.isRootDatum hQ hi
        have hcroot := F.rootIndex_restrict D hG p hQ c
        rw [hc] at hcroot
        rw [hcroot]
        exact Submodule.subset_span ⟨c, by
          change idx c ∈ p.base.support
          rw [hc]
          exact hr, rfl⟩
      · have hz := F.root_restrict_eq_zero_of_other hG p.isSplitTorus p.isMaximalTorus hroot hi
        rw [hz]
        exact M.zero_mem
    | zero => simpa only [Limits.comp_zero] using M.zero_mem
    | add a c _ _ ha hc =>
      simpa only [Preadditive.comp_add] using M.add_mem ha hc
    | smul n a _ ha =>
      simpa only [Preadditive.comp_zsmul] using M.smul_mem n ha
  have hrestrict := haux _ hmem
  rw [F.rootIndex_restrict D hG p hQ] at hrestrict
  exact hrestrict

/-- The induced genuine base has exactly the prescribed ambient simple roots;
no simple roots are lost or added inside the actual factor. -/
theorem mem_inducedBase_iff (b : K) :
    b ∈ (F.inducedBase D hG p hQ).support ↔ idx b ∈ p.base.support := by
  constructor
  · intro hb
    by_contra hn
    have hsub : insert b {c : K | idx c ∈ p.base.support} ⊆
        ((F.inducedBase D hG p hQ).support : Set K) := by
      intro c hc
      rcases hc with rfl | hc
      · exact hb
      · exact F.mem_inducedBase_of_mem_ambient D hG p hQ hc
    have hli := (F.inducedBase D hG p hQ).linearIndepOn_root.mono hsub
    exact hli.notMem_span_of_insert hn (F.root_mem_span_ambient_simples D hG p hQ b)
  · exact F.mem_inducedBase_of_mem_ambient D hG p hQ

/-- The exact simple-vertex equivalence with the ambient actual factor fibre. -/
def simpleRootIndexEquiv :
    (F.inducedBase D hG p hQ).support ≃
      {r : p.base.support // D.rootDatumFactorIndex hG p.isSplitTorus p.inclusion
        p.isMaximalTorus p.isRootDatum r.val = i} :=
  Equiv.ofBijective
    (fun b => ⟨⟨idx b.val, (F.mem_inducedBase_iff D hG p hQ b.val).mp b.property⟩,
      F.rootIndex_factor D hG p.isSplitTorus p.inclusion p.isMaximalTorus p.isRootDatum hQ
        b.val⟩)
    ⟨by
      intro b c h
      apply Subtype.ext
      exact F.rootIndex_injective D hG p.isSplitTorus p.inclusion p.isMaximalTorus
        p.isRootDatum hQ (congrArg (fun r => r.val.val) h),
      by
        intro r
        obtain ⟨b, hb⟩ := F.rootIndex_surjective D hG p.isSplitTorus p.inclusion
          p.isMaximalTorus p.isRootDatum hQ r.property
        have hs : b ∈ (F.inducedBase D hG p hQ).support :=
          (F.mem_inducedBase_iff D hG p hQ b).mpr (by rw [hb]; exact r.val.property)
        exact ⟨⟨b, hs⟩, Subtype.ext (Subtype.ext hb)⟩⟩

/-- The simple-vertex equivalence retains every ordered integral Cartan entry. -/
theorem pairing_simpleRootIndexEquiv
    (b c : (F.inducedBase D hG p hQ).support) :
    p.rootDatum.pairing (F.simpleRootIndexEquiv D hG p hQ b).val.val
        (F.simpleRootIndexEquiv D hG p hQ c).val.val = Q.pairing b.val c.val :=
  F.pairing_rootIndex D hG p.isSplitTorus p.inclusion p.isMaximalTorus p.isRootDatum hQ
    b.val c.val

end Base
end FactorMaximalTorus
end Langlands.GroupScheme.SimplyConnectedAlmostSimpleProduct
