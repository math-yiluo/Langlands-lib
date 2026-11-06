import Langlands.ClassFieldTheory.Local.TateTransfers
import Langlands.ClassFieldTheory.Local.TateAbelianization
import Langlands.Cohomology.Tate.AbelianizationCorestriction
import Langlands.Cohomology.Tate.ReindexNaturality

/-! # Actual low-degree norm transfer comparisons -/

noncomputable section

open CategoryTheory

namespace Langlands.Tate

universe u

set_option backward.isDefEq.respectTransparency false

variable {R G J : Type u} [CommRing R] [Group G] [Group J]
  [Fintype G] [Fintype J]

/-- Change of group coordinates on a degree-minus-two single-chain class. -/
lemma reindex_minusTwoClass (e : G ≃* J) {A : Rep.{u} R G} {B : Rep.{u} R J}
    [A.IsTrivial] [B.IsTrivial] (φ : Rep.res e.symm.toMonoidHom A ⟶ B)
    (g : G) (a : A) :
    reindex e φ (-2) (minusTwoClass A g a) = minusTwoClass B (e g) (φ.hom a) := by
  have h := ConcreteCategory.congr_hom (reindex_groupHomology e φ 1)
    (minusTwoClass A g a)
  change reindex e φ (-2) (minusTwoClass A g a) =
    ((TateCohomology.isoGroupHomology (-2) 1 (by norm_num)).app B).inv
      (groupHomology.map e.toMonoidHom (reindexCoefficient e φ) 1
        (((TateCohomology.isoGroupHomology (-2) 1 (by norm_num)).app A).hom
          (((TateCohomology.isoGroupHomology (-2) 1 (by norm_num)).app A).inv
            (groupHomology.H1π A
              ((groupHomology.cycles₁IsoOfIsTrivial A).inv (Finsupp.single g a)))))) at h
  rw [Iso.inv_hom_id_apply] at h
  exact h.trans (congrArg
    ((TateCohomology.isoGroupHomology (-2) 1 (by norm_num)).app B).inv
    (groupHomology_map_single e.toMonoidHom (reindexCoefficient e φ) g a))

end Langlands.Tate

namespace Langlands.ClassFieldTheory.Local

universe u

variable (K L M : Type u)
  [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/-- Actual scalar restriction on Galois abelianizations. -/
def relativeAbelianizationInclusion :
    Additive (Abelianization Gal(M/L)) →+ Additive (Abelianization Gal(M/K)) :=
  (Abelianization.map (AlgEquiv.restrictScalarsHom K)).toAdditive

/-- The subgroup of automorphisms over the middle field is the restriction kernel. -/
lemma relativeGaloisSubgroup_eq_ker [Normal K L] :
    relativeGaloisSubgroup K L M =
      (AlgEquiv.restrictNormalHom L : Gal(M/K) →* Gal(L/K)).ker := by
  ext σ
  constructor
  · rintro ⟨τ, rfl⟩
    apply AlgEquiv.ext
    intro x
    apply (algebraMap L M).injective
    change algebraMap L M (AlgEquiv.restrictNormal (τ.restrictScalars K) L x) =
      algebraMap L M x
    rw [AlgEquiv.restrictNormal_commutes]
    exact τ.commutes x
  · intro h
    have hs : ∀ x : L, σ (algebraMap L M x) = algebraMap L M x := by
      intro x
      rw [← AlgEquiv.restrictNormal_commutes σ L x]
      exact congrArg (algebraMap L M) (AlgEquiv.congr_fun h x)
    refine ⟨{ toRingEquiv := σ.toRingEquiv, commutes' := hs }, ?_⟩
    rfl

instance relativeGaloisSubgroup_normal [Normal K L] :
    (relativeGaloisSubgroup K L M).Normal := by
  rw [relativeGaloisSubgroup_eq_ker K L M]
  infer_instance

/-- Left Galois cosets are the actual automorphisms of a normal intermediate field. -/
def relativeGaloisCosetEquiv [Normal K L] [Normal K M] :
    Gal(M/K) ⧸ relativeGaloisSubgroup K L M ≃* Gal(L/K) :=
  QuotientGroup.liftEquiv _ (AlgEquiv.restrictNormalHom_surjective (F := K) M)
    (relativeGaloisSubgroup_eq_ker K L M)

variable [FiniteDimensional K M] [FiniteDimensional L M]

local instance :
    (Rep.res (relativeGaloisSubgroup K L M).subtype
      (Langlands.Tate.integralTrivial Gal(M/K))).IsTrivial where
  out _ := rfl

/-- The source coordinate change is literal scalar restriction on single chains. -/
lemma integralSubgroupTateIso_minusTwoClass (σ : Gal(M/L)) :
    letI := Fintype.ofFinite Gal(M/L)
    letI := Fintype.ofFinite (relativeGaloisSubgroup K L M)
    (integralSubgroupTateIso K L M (-2)).hom
      (Langlands.Tate.minusTwoClass (Langlands.Tate.integralTrivial Gal(M/L)) σ 1) =
    Langlands.Tate.minusTwoClass
      (Rep.res (relativeGaloisSubgroup K L M).subtype
        (Langlands.Tate.integralTrivial Gal(M/K)))
      (relativeGaloisSubgroupEquiv K L M σ) 1 := by
  let := Fintype.ofFinite Gal(M/L)
  let := Fintype.ofFinite (relativeGaloisSubgroup K L M)
  exact Langlands.Tate.reindex_minusTwoClass (relativeGaloisSubgroupEquiv K L M)
    (integralSubgroupCoefficientsIso K L M).hom σ 1

/-- Integral degree-minus-two corestriction is actual inclusion on Galois abelianizations. -/
lemma integralTateMinusTwoEquiv_corestriction
    (x : integralTateCohomology L M (-2)) :
    integralTateMinusTwoEquiv K M (integralTateCorestriction K L M (-2) x) =
      relativeAbelianizationInclusion K L M (integralTateMinusTwoEquiv L M x) := by
  let := Fintype.ofFinite Gal(M/K)
  let := Fintype.ofFinite Gal(M/L)
  let := Fintype.ofFinite (relativeGaloisSubgroup K L M)
  let := Fintype.ofFinite (Gal(M/K) ⧸ relativeGaloisSubgroup K L M)
  obtain ⟨σ, rfl⟩ := Langlands.Tate.integralMinusTwoClass_surjective x
  change Langlands.Tate.integralMinusTwoEquiv Gal(M/K)
    (Langlands.Tate.corestriction (relativeGaloisSubgroup K L M)
      (Langlands.Tate.integralTrivial Gal(M/K)) (-2)
      ((integralSubgroupTateIso K L M (-2)).hom
        (Langlands.Tate.minusTwoClass (Langlands.Tate.integralTrivial Gal(M/L)) σ 1))) = _
  rw [integralSubgroupTateIso_minusTwoClass,
    Langlands.Tate.corestriction_minusTwoClass,
    Langlands.Tate.integralMinusTwoEquiv_class, integralTateMinusTwoEquiv_class]
  rfl

end Langlands.ClassFieldTheory.Local
