import Langlands.Geometry.Analytic.OriginalDomainTopology
import Langlands.Geometry.Analytic.AtlasSubatlas
import Mathlib.CategoryTheory.Sites.Equivalence

/-! # Invariance of original-chart domain sites under local refinement -/

noncomputable section

universe u v w w' t s

namespace Langlands.Analytic.IndexedAffinoidAtlas

open Set CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X]
  {a : IndexedAffinoidAtlas.{u, v, w} K X}
  {b : IndexedAffinoidAtlas.{u, v, w'} K X}

/-- Replacing the charts by finite relative local refinements preserves
the original-chart-domain condition. -/
theorem IsOriginalChartDomain.of_locallyRefines {S : Set X}
    (hS : a.IsOriginalChartDomain S)
    (hba : AtlasTopology.LocallyRefines
      (Set.range (fun i => Set.range (b.chart i)))
      (Set.range (fun i => Set.range (a.chart i)))) :
    b.IsOriginalChartDomain S :=
  hS.refine (hba.restrict S)

namespace OriginalChartDomain

/-- Change the supplied atlas while retaining the literal domain subset. -/
def transport
    (hba : AtlasTopology.LocallyRefines
      (Set.range (fun i => Set.range (b.chart i)))
      (Set.range (fun i => Set.range (a.chart i))))
    (S : OriginalChartDomain a) : OriginalChartDomain b :=
  ⟨S.carrier, S.is_domain.of_locallyRefines hba⟩

@[simp]
theorem coe_transport
    (hba : AtlasTopology.LocallyRefines
      (Set.range (fun i => Set.range (b.chart i)))
      (Set.range (fun i => Set.range (a.chart i))))
    (S : OriginalChartDomain a) :
    (transport hba S : Set X) = S := rfl

/-- Mutual finite relative local refinement identifies the actual domains,
preserving and reflecting their subset order. -/
def refinementOrderIso
    (hab : AtlasTopology.LocallyRefines
      (Set.range (fun i => Set.range (a.chart i)))
      (Set.range (fun i => Set.range (b.chart i))))
    (hba : AtlasTopology.LocallyRefines
      (Set.range (fun i => Set.range (b.chart i)))
      (Set.range (fun i => Set.range (a.chart i)))) :
    OriginalChartDomain a ≃o OriginalChartDomain b where
  toFun := transport hba
  invFun := transport hab
  left_inv _ := SetLike.coe_injective rfl
  right_inv _ := SetLike.coe_injective rfl
  map_rel_iff' := Iff.rfl

/-- The same comparison as an equivalence of actual inclusion categories. -/
def refinementEquivalence
    (hab : AtlasTopology.LocallyRefines
      (Set.range (fun i => Set.range (a.chart i)))
      (Set.range (fun i => Set.range (b.chart i))))
    (hba : AtlasTopology.LocallyRefines
      (Set.range (fun i => Set.range (b.chart i)))
      (Set.range (fun i => Set.range (a.chart i)))) :
    OriginalChartDomain a ≌ OriginalChartDomain b :=
  (refinementOrderIso hab hba).equivalence

section

variable
  (hab : AtlasTopology.LocallyRefines
    (Set.range (fun i => Set.range (a.chart i)))
    (Set.range (fun i => Set.range (b.chart i))))
  (hba : AtlasTopology.LocallyRefines
    (Set.range (fun i => Set.range (b.chart i)))
    (Set.range (fun i => Set.range (a.chart i))))

/-- Pulling a sieve back along the comparison retains exactly its family
of actual subsets, rather than merely its covered points. -/
theorem sieveFamily_functorPullback_refinement
    (S : OriginalChartDomain a)
    (R : Sieve ((refinementEquivalence hab hba).functor.obj S)) :
    sieveFamily (R.functorPullback (refinementEquivalence hab hba).functor) =
      sieveFamily R := by
  ext U
  constructor
  · rintro ⟨V, hVS, hR, rfl⟩
    exact ⟨transport hba V, hVS, hR, rfl⟩
  · rintro ⟨V, hVS, hR, rfl⟩
    refine ⟨transport hab V, hVS, ?_, rfl⟩
    have hV : transport hba (transport hab V) = V := SetLike.coe_injective rfl
    cases hV
    exact hR

/-- The comparison preserves and reflects all quasinet-covering sieves. -/
theorem functorPullback_mem_quasinetTopology_iff
    (S : OriginalChartDomain a)
    (R : Sieve ((refinementEquivalence hab hba).functor.obj S)) :
    R.functorPullback (refinementEquivalence hab hba).functor ∈ quasinetTopology a S ↔
      R ∈ quasinetTopology b ((refinementEquivalence hab hba).functor.obj S) := by
  change AtlasTopology.LocallyRefines _ {S.carrier} ↔
    AtlasTopology.LocallyRefines _ {S.carrier}
  rw [sieveFamily_functorPullback_refinement]

instance refinementFunctor_isCocontinuous :
    (refinementEquivalence hab hba).functor.IsCocontinuous
      (quasinetTopology a) (quasinetTopology b) where
  cover_lift {U} {R} hR :=
    (functorPullback_mem_quasinetTopology_iff hab hba U R).mpr hR

instance refinementInverse_isCocontinuous :
    (refinementEquivalence hab hba).inverse.IsCocontinuous
      (quasinetTopology b) (quasinetTopology a) where
  cover_lift {U} {R} hR :=
    (functorPullback_mem_quasinetTopology_iff hba hab U R).mpr hR

instance refinementInverse_isDenseSubsite :
    (refinementEquivalence hab hba).inverse.IsDenseSubsite
      (quasinetTopology b) (quasinetTopology a) :=
  Equivalence.isDenseSubsite_inverse_of_isCocontinuous
    (quasinetTopology a) (quasinetTopology b) (refinementEquivalence hab hba)

/-- Actual sheaves on the two constructed quasinet sites correspond by
restriction along the inverse subset-preserving comparison. -/
def refinementSheafEquivalence (C : Type t) [Category.{s} C] :
    Sheaf (quasinetTopology a) C ≌ Sheaf (quasinetTopology b) C :=
  (refinementEquivalence hab hba).sheafCongr
    (quasinetTopology a) (quasinetTopology b) C

/-- The comparison of sheaves retains the given value at the same actual
domain subset, with only its atlas-domain proof changed. -/
@[simp]
theorem refinementSheafEquivalence_obj_obj
    {C : Type t} [Category.{s} C] (F : Sheaf (quasinetTopology a) C)
    (S : OriginalChartDomain b) :
    ((refinementSheafEquivalence hab hba C).functor.obj F).obj.obj
        (Opposite.op S) =
      F.obj.obj (Opposite.op (transport hab S)) := rfl

/-- Arbitrarily indexed generated covering families are also unchanged. -/
theorem ofArrows_refinement_mem_iff {ι : Type*}
    (S : OriginalChartDomain a) (D : ι → OriginalChartDomain a)
    (f : ∀ i, D i ⟶ S) :
    Sieve.ofArrows D f ∈ quasinetTopology a S ↔
      Sieve.ofArrows (fun i => transport hba (D i))
        (fun i => homOfLE (show transport hba (D i) ≤ transport hba S
          from leOfHom (f i))) ∈ quasinetTopology b (transport hba S) := by
  rw [ofArrows_mem_iff_locallyRefines, ofArrows_mem_iff_locallyRefines]
  rfl

end

end OriginalChartDomain

variable (a)

/-- Deleting locally redundant original charts does not change which actual
subsets are domains. Neither downward closure nor upper cofinality is needed. -/
theorem isOriginalChartDomain_subatlas_iff (P : a.Index → Prop)
    (hP : a.IsLocallyRefiningSelection P) (S : Set X) :
    (a.subatlas P hP).IsOriginalChartDomain S ↔ a.IsOriginalChartDomain S := by
  constructor
  · intro hS
    apply hS.of_locallyRefines
    exact (AtlasTopology.LocallyRefines.refl (a.selectedChartFamily P)).mono
      (a.selectedChartFamily_subset P) Subset.rfl
  · intro hS
    exact hS.of_locallyRefines hP

/-- The actual domain orders before and after selecting a locally refining
subatlas agree on literal subsets. -/
def originalDomainSubatlasOrderIso (P : a.Index → Prop)
    (hP : a.IsLocallyRefiningSelection P) :
    OriginalChartDomain a ≃o OriginalChartDomain (a.subatlas P hP) :=
  OriginalChartDomain.refinementOrderIso
    ((AtlasTopology.LocallyRefines.refl (a.selectedChartFamily P)).mono
      (a.selectedChartFamily_subset P) Subset.rfl) hP

/-- Sheaves on the actual quasinet domain site are invariant under deletion
of locally redundant original charts. -/
def originalDomainSubatlasSheafEquivalence (P : a.Index → Prop)
    (hP : a.IsLocallyRefiningSelection P) (C : Type t) [Category.{s} C] :
    Sheaf (OriginalChartDomain.quasinetTopology a) C ≌
      Sheaf (OriginalChartDomain.quasinetTopology (a.subatlas P hP)) C :=
  OriginalChartDomain.refinementSheafEquivalence
    (b := a.subatlas P hP)
    ((AtlasTopology.LocallyRefines.refl (a.selectedChartFamily P)).mono
      (a.selectedChartFamily_subset P) Subset.rfl) hP C

end Langlands.Analytic.IndexedAffinoidAtlas
