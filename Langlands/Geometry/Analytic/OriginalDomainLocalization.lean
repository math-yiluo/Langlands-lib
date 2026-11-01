import Langlands.Geometry.Analytic.OriginalDomainTopology
import Langlands.Geometry.Analytic.AtlasTopology.NestedRestriction

/-! # Localization of fixed-original-chart domains and their covering families -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open Set CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- A domain of the constructed subspace atlas is exactly an ambient
original-chart domain, regarded as a subset of that subspace. -/
theorem isOriginalChartDomain_subspaceAtlas_iff (S : Set X)
    (hS : a.IsOriginalChartDomain S) (U : Set S) :
    (a.subspaceAtlas S hS).IsOriginalChartDomain U ↔
      a.IsOriginalChartDomain (Subtype.val '' U) := by
  change AtlasTopology.IsQuasinet
    (AtlasTopology.restrictedFamily
      (Set.range (fun c => Set.range (a.subspaceChart S c))) U) ↔ _
  rw [a.subspaceChartFamily_eq S]
  exact AtlasTopology.isQuasinet_restrictedFamily_subtype_iff _ S U

namespace OriginalChartDomain

variable {a}

/-- The ambient image of an actual domain of the constructed subspace atlas. -/
def subspaceExtend (S : OriginalChartDomain a)
    (U : OriginalChartDomain (a.subspaceAtlas S.carrier S.is_domain)) :
    OriginalChartDomain a where
  carrier := Subtype.val '' U.carrier
  is_domain := (a.isOriginalChartDomain_subspaceAtlas_iff
    S.carrier S.is_domain U.carrier).mp U.is_domain

@[simp]
theorem coe_subspaceExtend (S : OriginalChartDomain a)
    (U : OriginalChartDomain (a.subspaceAtlas S.carrier S.is_domain)) :
    (S.subspaceExtend U : Set X) = Subtype.val '' U.carrier := rfl

theorem subspaceExtend_le (S : OriginalChartDomain a)
    (U : OriginalChartDomain (a.subspaceAtlas S.carrier S.is_domain)) :
    S.subspaceExtend U ≤ S := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

theorem subspaceExtend_le_iff (S : OriginalChartDomain a)
    (U V : OriginalChartDomain (a.subspaceAtlas S.carrier S.is_domain)) :
    S.subspaceExtend U ≤ S.subspaceExtend V ↔ U ≤ V :=
  Set.image_subset_image_iff Subtype.val_injective

theorem subspaceExtend_mono (S : OriginalChartDomain a) :
    Monotone S.subspaceExtend :=
  fun _ _ h => Set.image_mono h

/-- Restrict an actual ambient domain contained in `S` to the subspace atlas. -/
def subspaceRestrict (S : OriginalChartDomain a)
    (T : Set.Iic S) :
    OriginalChartDomain (a.subspaceAtlas S.carrier S.is_domain) where
  carrier := Subtype.val ⁻¹' T.val.carrier
  is_domain := by
    apply (a.isOriginalChartDomain_subspaceAtlas_iff
      S.carrier S.is_domain _).mpr
    rw [Subtype.image_preimage_val,
      inter_eq_right.mpr (show T.val.carrier ⊆ S.carrier from T.property)]
    exact T.val.is_domain

@[simp]
theorem coe_subspaceRestrict (S : OriginalChartDomain a) (T : Set.Iic S) :
    ((S.subspaceRestrict T) : Set S.carrier) = Subtype.val ⁻¹' T.val.carrier := rfl

@[simp]
theorem subspaceRestrict_subspaceExtend (S : OriginalChartDomain a)
    (U : OriginalChartDomain (a.subspaceAtlas S.carrier S.is_domain)) :
    S.subspaceRestrict ⟨S.subspaceExtend U, S.subspaceExtend_le U⟩ = U := by
  apply SetLike.coe_injective
  exact Set.preimage_image_eq U.carrier Subtype.val_injective

@[simp]
theorem subspaceExtend_subspaceRestrict (S : OriginalChartDomain a)
    (T : Set.Iic S) :
    S.subspaceExtend (S.subspaceRestrict T) = T.val := by
  apply SetLike.coe_injective
  exact (Subtype.image_preimage_val S.carrier T.val.carrier).trans
    (inter_eq_right.mpr T.property)

/-- Domains of the actual subspace atlas identify with ambient domains
contained in `S`, preserving and reflecting literal subset inclusion. -/
def localizationOrderIso (S : OriginalChartDomain a) :
    OriginalChartDomain (a.subspaceAtlas S.carrier S.is_domain) ≃o Set.Iic S where
  toFun U := ⟨S.subspaceExtend U, S.subspaceExtend_le U⟩
  invFun := S.subspaceRestrict
  left_inv := S.subspaceRestrict_subspaceExtend
  right_inv T := Subtype.ext (S.subspaceExtend_subspaceRestrict T)
  map_rel_iff' := fun {U V} => S.subspaceExtend_le_iff U V

/-- The same identification as an equivalence of inclusion categories. -/
def localizationEquivalence (S : OriginalChartDomain a) :
    OriginalChartDomain (a.subspaceAtlas S.carrier S.is_domain) ≌ Set.Iic S :=
  S.localizationOrderIso.equivalence

/-- Extension gives an actual inclusion functor into ambient domains. -/
def subspaceExtensionFunctor (S : OriginalChartDomain a) :
    OriginalChartDomain (a.subspaceAtlas S.carrier S.is_domain) ⥤
      OriginalChartDomain a :=
  S.subspaceExtend_mono.functor

/-- A family covers a domain of the subspace atlas exactly when its ambient
images cover the corresponding ambient domain. The full quasinet condition
is preserved, including arbitrary index universes and empty domains. -/
theorem ofArrows_subspaceExtend_mem_iff (S : OriginalChartDomain a)
    {ι : Type*}
    {U : OriginalChartDomain (a.subspaceAtlas S.carrier S.is_domain)}
    (D : ι → OriginalChartDomain (a.subspaceAtlas S.carrier S.is_domain))
    (f : ∀ i, D i ⟶ U) :
    Sieve.ofArrows D f ∈ quasinetTopology (a.subspaceAtlas S.carrier S.is_domain) U ↔
      Sieve.ofArrows (fun i => S.subspaceExtend (D i))
        (fun i => homOfLE (S.subspaceExtend_mono (leOfHom (f i)))) ∈
          quasinetTopology a (S.subspaceExtend U) := by
  rw [ofArrows_mem_iff_isQuasinet, ofArrows_mem_iff_isQuasinet]
  change AtlasTopology.IsQuasinet
    (AtlasTopology.restrictedFamily (Set.range (fun i => (D i).carrier)) U.carrier) ↔
      AtlasTopology.IsQuasinet (AtlasTopology.restrictedFamily
        (Set.range (fun i => Subtype.val '' (D i).carrier)) (Subtype.val '' U.carrier))
  simpa only [← Set.range_comp'] using
    AtlasTopology.isQuasinet_restrictedFamily_subtype_images_iff
      S.carrier (Set.range (fun i => (D i).carrier)) U.carrier

end OriginalChartDomain

end Langlands.Analytic.IndexedAffinoidAtlas
