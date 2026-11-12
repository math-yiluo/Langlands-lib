import Langlands.GroupScheme.SimplyConnected.AlmostSimpleProductUniqueness
import Langlands.GroupScheme.SimplyConnected.BaseIsoTransport
import Langlands.GroupScheme.Descent.GaloisSubgroupTransport

/-! # Canonical Galois action on actual almost-simple factors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {S S' : Scheme.{u}} {G : GroupScheme S}

/-- Membership is unchanged when a test scheme is replaced by an isomorphic one. -/
theorem precomp_iso_mem_iff (F : SubgroupFunctor G)
    {T T' : Over S} (e : T' ≅ T) (x : T ⟶ G.X) :
    e.hom ≫ x ∈ F.carrier T' ↔ x ∈ F.carrier T := by
  constructor
  · intro hx
    simpa only [Iso.inv_hom_id_assoc] using F.comp_mem e.inv hx
  · exact F.comp_mem e.hom

/-- Pullback along a base isomorphism is injective on all subgroup functors. -/
theorem baseChange_injective_of_isIso (b : S' ⟶ S) [IsIso b] :
    Function.Injective (fun F : SubgroupFunctor G => F.baseChange b) := by
  intro F F' h
  change F.baseChange b = F'.baseChange b at h
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  let T' := (Over.map (inv b)).obj T
  let e := overMapRetractionIso (IsIso.inv_hom_id b) T
  let z := (baseChangePointsEquiv b G T').symm (e.hom ≫ x)
  have hz : z ∈ (F.baseChange b).carrier T' ↔
      z ∈ (F'.baseChange b).carrier T' := by rw [h]
  change baseChangePointsEquiv b G T' z ∈ F.carrier _ ↔
    baseChangePointsEquiv b G T' z ∈ F'.carrier _ at hz
  simpa only [z, MulEquiv.apply_symm_apply, precomp_iso_mem_iff] using hz

end SubgroupFunctor

section AlmostSimpleTransport

variable {k K : Type u} [Field k] [Field K]
    {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- Almost-simplicity transports through an actual group-scheme isomorphism. -/
theorem IsAlmostSimple.of_iso (e : G ≅ H) (hH : IsAlmostSimple H) :
    IsAlmostSimple G := by
  refine ⟨hH.isSemisimple.of_iso e, ?_, ?_⟩
  · intro hc
    apply hH.noncommutative
    intro T x y
    apply (commute_iff_eq _ _).2
    apply (cancel_mono e.inv.hom.hom).1
    simpa only [MonObj.mul_comp] using
      (hc T (x ≫ e.inv.hom.hom) (y ≫ e.inv.hom.hom)).eq
  · intro A j hj hs hc hn
    have hn' : (SubgroupFunctor.range (j ≫ e.hom)).IsNormal := by
      rw [SubgroupFunctor.range_comp_iso]
      exact hn.comap e.inv
    rcases hH.normalSubgroup_trivial_or_full A (j ≫ e.hom)
        (hj.comp_iso e) hs hc hn' with hb | ht
    · left
      apply SubgroupFunctor.ext
      intro T
      apply Subgroup.ext
      intro x
      constructor
      · rintro ⟨y, rfl⟩
        have hy : y ≫ (j ≫ e.hom).hom.hom ∈
            (SubgroupFunctor.range (j ≫ e.hom)).carrier T :=
          SubgroupFunctor.mem_range.2 ⟨y, rfl⟩
        rw [hb, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hy
        change y ≫ j.hom.hom = 1
        apply (cancel_mono e.hom.hom.hom).1
        simpa only [Grp.comp_hom_hom, Category.assoc, MonObj.one_comp] using hy
      · intro hx
        have hx' : x = 1 := hx
        rw [hx']
        exact (SubgroupFunctor.range j).carrier T |>.one_mem
    · right
      apply SubgroupFunctor.ext
      intro T
      apply top_unique
      intro x _
      have hx : x ≫ e.hom.hom.hom ∈
          (SubgroupFunctor.range (j ≫ e.hom)).carrier T := by
        rw [ht]
        exact Subgroup.mem_top _
      obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.1 hx
      refine SubgroupFunctor.mem_range.2 ⟨y, ?_⟩
      apply (cancel_mono e.hom.hom.hom).1
      simpa only [Grp.comp_hom_hom, Category.assoc] using hy

private theorem commute_baseChange_of_commute
    {S S' : Scheme.{u}} (b : S' ⟶ S) (G : GroupScheme S)
    (h : ∀ (T : Over S) (x y : T ⟶ G.X), Commute x y)
    (T : Over S') (x y : T ⟶ ((GroupScheme.baseChange b).obj G).X) :
    Commute x y := by
  apply (commute_iff_eq _ _).2
  apply (baseChangePointsEquiv b G T).injective
  simpa only [map_mul] using
    (h _ (baseChangePointsEquiv b G T x) (baseChangePointsEquiv b G T y)).eq

/-- Almost-simplicity transports along an isomorphism of base fields,
including automorphisms of imperfect fields. -/
theorem IsAlmostSimple.baseChange_of_isIso (hG : IsAlmostSimple G)
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) [IsIso b] :
    IsAlmostSimple ((GroupScheme.baseChange b).obj G) := by
  let F := GroupScheme.baseChange b
  let R := GroupScheme.baseChange (inv b)
  let e := baseChangeSectionNatIso b (inv b) (IsIso.inv_hom_id b)
  refine ⟨hG.isSemisimple.baseChange_of_isIso b, ?_, ?_⟩
  · intro hc
    apply hG.noncommutative
    intro T x y
    apply (commute_iff_eq _ _).2
    apply (cancel_mono (e.app G).inv.hom.hom).1
    simpa only [MonObj.mul_comp] using
      (commute_baseChange_of_commute (inv b) (F.obj G) hc T
        (x ≫ (e.app G).inv.hom.hom) (y ≫ (e.app G).inv.hom.hom)).eq
  · intro A j hj hs hc hn
    let : Smooth A.X.hom := hs
    let : ConnectedSpace A.X.left := hc
    have hR : IsAlmostSimple (R.obj (F.obj G)) := hG.of_iso (e.app G)
    have hRn : (SubgroupFunctor.range (R.map j)).IsNormal := by
      rw [SubgroupFunctor.range_baseChangeHom]
      exact hn.baseChange (inv b)
    rcases hR.normalSubgroup_trivial_or_full (R.obj A) (R.map j)
        (hj.baseChange (inv b)) (inferInstanceAs (Smooth
          (pullback.snd A.X.hom (inv b))))
        (connectedSpace_baseChange_of_isIso (inv b) A) hRn with hb | ht
    · left
      apply SubgroupFunctor.baseChange_injective_of_isIso (inv b)
      change SubgroupFunctor.range ((GroupScheme.baseChange (inv b)).map j) = ⊥ at hb
      simpa only [SubgroupFunctor.range_baseChangeHom,
        SubgroupFunctor.bot_baseChange] using hb
    · right
      apply SubgroupFunctor.baseChange_injective_of_isIso (inv b)
      change SubgroupFunctor.range ((GroupScheme.baseChange (inv b)).map j) = ⊤ at ht
      simpa only [SubgroupFunctor.range_baseChangeHom,
        SubgroupFunctor.top_baseChange] using ht

end AlmostSimpleTransport

namespace SimplyConnectedAlmostSimpleProduct

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom]
    [IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom]
    (D : SimplyConnectedAlmostSimpleProduct
      ((GroupScheme.baseChange (algebraBaseMap k L)).obj G))

/-- The actual inclusion of a semilinearly transported product factor. -/
def galoisFactorInclusion (σ : L ≃ₐ[k] L) (i : D.Index) :
    (GroupScheme.baseChange (galoisBaseMap k L σ)).obj (D.factor i) ⟶
      (GroupScheme.baseChange (algebraBaseMap k L)).obj G :=
  (GroupScheme.baseChange (galoisBaseMap k L σ)).map (D.inclusion i) ≫
    (descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
      (galoisBaseMap_over k L σ) G).hom

omit [Smooth ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom]
  [IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom] in
theorem galoisFactor_isAlmostSimple (σ : L ≃ₐ[k] L) (i : D.Index) :
    IsAlmostSimple
      ((GroupScheme.baseChange (galoisBaseMap k L σ)).obj (D.factor i)) := by
  let : IsIso (galoisBaseMap k L σ) :=
    isIso_SpecMap_iff.mpr σ.bijective
  exact (D.isAlmostSimple i).baseChange_of_isIso _

omit [Smooth ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom] in
theorem isClosedSubgroup_galoisFactorInclusion (σ : L ≃ₐ[k] L) (i : D.Index) :
    IsClosedSubgroup (D.galoisFactorInclusion σ i) :=
  ((D.isClosedSubgroup_inclusion i).baseChange _).comp_iso _

omit [Smooth ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom]
  [IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom] in
theorem isNormal_range_galoisFactorInclusion (σ : L ≃ₐ[k] L) (i : D.Index) :
    (SubgroupFunctor.range (D.galoisFactorInclusion σ i)).IsNormal := by
  rw [galoisFactorInclusion, SubgroupFunctor.range_comp_iso,
    SubgroupFunctor.range_baseChangeHom]
  exact ((D.isNormal_range_inclusion i).baseChange _).comap _

/-- The unique index selected by canonical Galois transport of a factor. -/
def galoisFactorIndex (σ : L ≃ₐ[k] L) (i : D.Index) : D.Index :=
  D.indexOfNormalAlmostSimple (D.galoisFactor_isAlmostSimple σ i)
    (D.galoisFactorInclusion σ i) (D.isClosedSubgroup_galoisFactorInclusion σ i)
    (D.isNormal_range_galoisFactorInclusion σ i)

/-- The factor-index map has exactly the canonical all-test Galois transport. -/
theorem range_inclusion_galoisFactorIndex (σ : L ≃ₐ[k] L) (i : D.Index) :
    SubgroupFunctor.range (D.inclusion (D.galoisFactorIndex σ i)) =
      SubgroupFunctor.galoisTransport k L G σ
        (SubgroupFunctor.range (D.inclusion i)) := by
  have h := D.range_eq_indexOfNormalAlmostSimple
    (D.galoisFactor_isAlmostSimple σ i) (D.galoisFactorInclusion σ i)
    (D.isClosedSubgroup_galoisFactorInclusion σ i)
    (D.isNormal_range_galoisFactorInclusion σ i)
  change SubgroupFunctor.range (D.galoisFactorInclusion σ i) =
    SubgroupFunctor.range (D.inclusion (D.galoisFactorIndex σ i)) at h
  rw [← h]
  exact (SubgroupFunctor.descentTransport_range _ _ _ _ _).symm

@[simp] theorem galoisFactorIndex_one (i : D.Index) :
    D.galoisFactorIndex 1 i = i := by
  apply D.range_inclusion_injective
  change SubgroupFunctor.range (D.inclusion (D.galoisFactorIndex 1 i)) =
    SubgroupFunctor.range (D.inclusion i)
  rw [range_inclusion_galoisFactorIndex, map_one]
  rfl

theorem galoisFactorIndex_mul (σ τ : L ≃ₐ[k] L) (i : D.Index) :
    D.galoisFactorIndex (σ * τ) i =
      D.galoisFactorIndex σ (D.galoisFactorIndex τ i) := by
  apply D.range_inclusion_injective
  change SubgroupFunctor.range (D.inclusion (D.galoisFactorIndex (σ * τ) i)) =
    SubgroupFunctor.range (D.inclusion (D.galoisFactorIndex σ (D.galoisFactorIndex τ i)))
  rw [range_inclusion_galoisFactorIndex, range_inclusion_galoisFactorIndex,
    range_inclusion_galoisFactorIndex, map_mul]
  rfl

/-- The actual canonical Galois action on the finite index type of factors.
No finite-degree or perfectness hypothesis is needed for this action. -/
@[instance_reducible] def galoisFactorAction : MulAction (L ≃ₐ[k] L) D.Index where
  smul := D.galoisFactorIndex
  one_smul := D.galoisFactorIndex_one
  mul_smul := D.galoisFactorIndex_mul

end SimplyConnectedAlmostSimpleProduct

end Langlands.GroupScheme
