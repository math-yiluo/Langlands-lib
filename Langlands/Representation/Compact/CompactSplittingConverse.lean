import Langlands.Representation.Compact.CompactPartExhaustion
import Langlands.Representation.Category.IdempotentDecomposition
import Langlands.Representation.CompactCoefficient.Subquotients
import Langlands.Representation.Jacquet.SmallFixedVectorGenerator
import Langlands.CategoryTheory.Renard.DecompositionCenterIdempotent
import Mathlib.Topology.Compactness.Lindelof

/-! # A compact/noncompact category decomposition forces finite fixed-level strata -/

noncomputable section
universe u v

namespace Langlands.Renard.CompactRepresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits CompactCoefficientClass SmoothRep

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] in
/-- A finite-type object exhausted by its compact isotypic parts has only finitely
many compact irreducible quotient classes. -/
theorem finite_compact_quotient_classes
    (A : SmoothRep.{0, u, v} ℂ G)
    [Module.Finite (MonoidAlgebra ℂ G) A.representation.asModule]
    (htop : totalIsotypicSubrepresentation.{u, v} A = ⊤) :
    {c : CompactCoefficientClass.{u, v} G | ∃ f : A ⟶ c.out.obj, f ≠ 0}.Finite := by
  classical
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := A.representation)
  have hcompact : IsCompactElement (⊤ : Submodule (MonoidAlgebra ℂ G) A.representation.asModule) :=
    (Submodule.fg_iff_compact ⊤).mp Module.Finite.fg_top
  obtain ⟨t, ht⟩ := hcompact.exists_finset_of_le_iSup
    (fun c : CompactCoefficientClass.{u, v} G => e (isotypicSubrepresentation c A)) (by
      rw [← e.map_iSup]
      change ⊤ ≤ e (totalIsotypicSubrepresentation.{u, v} A)
      rw [htop, e.map_top])
  have hcover : (⨆ c ∈ t, isotypicSubrepresentation c A) = ⊤ := by
    apply e.injective
    simp only [e.map_iSup, e.map_top]
    exact top_unique ht
  apply t.finite_toSet.subset
  rintro c ⟨f, hf⟩
  by_contra hc
  have hle : (⊤ : Subrepresentation A.representation) ≤ annihilatorSubrepresentation c A := by
    rw [← hcover]
    exact iSup₂_le fun d hd => isotypicSubrepresentation_le_annihilator_of_ne
      (fun heq : d = c => hc (heq ▸ hd)) A
  apply hf
  ext x
  exact annihilatorSubrepresentation_le_ker c.out (Quotient.out_eq c) (hom f) (hle (by trivial))

/-- The converse of Renard IV.1.7. The sigma-compact quotient by an open subgroup
is countable, allowing the compact permutation generator in every carrier universe. -/
theorem finite_strata_of_compactCategoryDecomposition
    [SigmaCompactSpace G]
    (hdec : Renard.IsCategoryDecomposition
      (irreducibleSubquotientProperties
        (fun A : SmoothRep.{0, u, v} ℂ G => HasCompactSmoothDualCoefficients A.representation)))
    (K : OpenSubgroup G) : (fixedStratum.{u, v} K.toSubgroup).Finite := by
  classical
  let : DiscreteTopology (G ⧸ K.toSubgroup) := QuotientGroup.discreteTopology K.isOpen
  let : LindelofSpace (G ⧸ K.toSubgroup) := LindelofSpace.of_continuous_surjective
    (QuotientGroup.continuous_mk : Continuous (QuotientGroup.mk : G → G ⧸ K.toSubgroup))
    QuotientGroup.mk_surjective
  let : Countable (G ⧸ K.toSubgroup) := countable_of_Lindelof_of_discrete
  let : Small.{v} (G ⧸ K.toSubgroup) := inferInstance
  let E := Jacquet.smallFixedVectorGenerator.{u, v} K
  obtain ⟨Y, ι, hY, ⟨hcol⟩⟩ := hdec.1 E
  let A := Y true
  let r : E ⟶ A := Renard.decompositionProj hcol true
  have hret : ι true ≫ r = 𝟙 A := Renard.inj_decompositionProj_self hcol true
  have hsurj : Function.Surjective (hom r) := by
    intro y
    exact ⟨hom (ι true) y, congrArg (fun f => hom f y) hret⟩
  let : Module.Finite (MonoidAlgebra ℂ G) A.representation.asModule :=
    Module.Finite.of_surjective
      (Representation.IntertwiningMap.equivLinearMapAsModule _ _ (hom r)) hsurj
  have hA : ∀ D : SmoothRep.{0, u, v} ℂ G, D.IsIrreducible → IsSubquotient D A →
      HasCompactSmoothDualCoefficients D.representation := hY true
  have hfinite := finite_compact_quotient_classes A
    (totalIsotypic_eq_top_of_compact_irreducible_subquotients A hA)
  apply hfinite.subset
  intro c hc
  have hDfix : fixedVectors c.out.obj.representation K.toSubgroup ≠ ⊥ := by
    apply (hasFixedVector_ofRep K.toSubgroup c.out).mp
    have hout : ofRep c.out = c := Quotient.out_eq c
    rw [hout]
    exact hc
  obtain ⟨x, hxK, hx⟩ := (Submodule.ne_bot_iff _).mp hDfix
  let f : E ⟶ c.out.obj := ofHom
    (Jacquet.smallFixedVectorLift K c.out.obj.representation ⟨x, hxK⟩)
  have hf : f ≠ 0 := by
    intro hz
    have hzero := congrArg (fun q => hom q (Jacquet.smallFixedVectorUnit K)) hz
    have heval : hom f (Jacquet.smallFixedVectorUnit K) = x :=
      Jacquet.smallFixedVectorLift_unit K c.out.obj.representation ⟨x, hxK⟩
    exact hx (heval.symm.trans hzero)
  have hcof : ∀ U : OpenSubgroup G,
      ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ U := by
    intro U
    obtain ⟨L, hLU, hL, _⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G ∅ U
    exact ⟨L, hL, hLU⟩
  have hDtrue : irreducibleSubquotientProperties
      (fun B : SmoothRep.{0, u, v} ℂ G => HasCompactSmoothDualCoefficients B.representation)
      true c.out.obj := by
    intro D hD hDC
    exact hasCompactSmoothDualCoefficients_of_isSubquotient hcof c.out.property.2 hDC
  refine ⟨ι true ≫ f, ?_⟩
  intro hzero
  apply hf
  apply Cofan.IsColimit.hom_ext hcol
  intro b
  change ι b ≫ f = ι b ≫ 0
  rw [comp_zero]
  cases b
  · exact hdec.2 false true (by decide) (Y false) c.out.obj (hY false) hDtrue (ι false ≫ f)
  · exact hzero

end Langlands.Renard.CompactRepresentation
