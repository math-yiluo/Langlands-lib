/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

import WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit
import WeilConjectures.AlgebraicGeometry.EtaleSectionsFilteredColimit
import WeilConjectures.AlgebraicGeometry.EtaleCechVanishingCriterion
import WeilConjectures.CategoryTheory.InjectiveSheafCechAcyclic
import WeilConjectures.AlgebraicGeometry.FiniteEtaleCechFilteredColimit

/-!
# Acyclicity of filtered colimits of injective étale sheaves

Source: Stacks Project, Cohomology on Sites, Tag 0739, the final claim and its proof,
applied to the qcqs objects of the small étale site as in Tag 073E.
(blueprint: lem-weil-pbc-etale-filtered-injective-acyclic).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem abelianSectionsColimit (Y : Scheme.{u}) (V : Y.Etale)
    [CompactSpace V.left] [QuasiSeparatedSpace V.left]
    {I : Type u} [SmallCategory I] [IsFiltered I]
    {F : I ⥤ Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}} {c : Cocone F}
    (hc : IsColimit c) :
    Nonempty (IsColimit
      (((sheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (Opposite.op V)).mapCocone c)) := by
  let R := ULift.{u + 1} ℤ
  let U := ModuleCat.restrictScalars (ULift.ringEquiv (R := ℤ)).symm.toRingHom ⋙
    forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  let e := U.asEquivalence
  let S := sheafCompose Y.smallEtaleTopology U
  have : S.EssSurj := ⟨fun P ↦ by
    let Q := (sheafCompose Y.smallEtaleTopology e.inverse).obj P
    refine ⟨Q, ⟨?_⟩⟩
    exact ObjectProperty.isoMk _ (Functor.isoWhiskerLeft P.obj e.counitIso)⟩
  have : S.IsEquivalence := {}
  let T := S.asEquivalence.inverse
  let G := F ⋙ T
  let d := T.mapCocone c
  have hd : IsColimit d := isColimitOfPreserves T hc
  let E := (sheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} R)).obj (Opposite.op V)
  have hbij := AlgebraicGeometry.etale_sections_filtered_colimit Y R V I G d hd
  have hE : IsColimit (E.mapCocone d) := by
    exact (colimit.isColimit (G ⋙ E)).ofPointIso (t := E.mapCocone d)
      (i := (ConcreteCategory.isIso_iff_bijective _).2 hbij)
  let Eab := (sheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (Opposite.op V)
  have hEU := isColimitOfPreserves U hE
  change IsColimit ((T ⋙ S ⋙ Eab).mapCocone c) at hEU
  exact ⟨IsColimit.mapCoconeEquiv
    (Functor.isoWhiskerRight S.asEquivalence.counitIso Eab) hEU⟩

/-- Filtered colimits of injective abelian étale sheaves are global-sections acyclic
on a qcqs scheme. The colimit need not itself be injective.
Source: Stacks Project, Tag 0739, final paragraph; Tag 073E, proof.
(blueprint: lem-weil-pbc-etale-filtered-injective-acyclic).

Proof:
1. Take `B` to consist of the qcqs objects of the small étale site, and take the
finite coverings with source and members in `B`. Finite affine refinements are
cofinal. All their iterated fibre products are qcqs: maps from qcqs schemes to
qcqs schemes are qcqs, and these properties persist under base change and composition.
2. Sections on objects of `B` commute with filtered colimits. For abelian sheaves
this follows from the module-valued sections result with the ring of integers.
A term of a finite-cover Čech complex is a finite product of sections on these
fibre products. Finite products of abelian groups are finite biproducts, so they
commute with colimits. Compatibility with restriction maps identifies the whole
Čech complex of `colim J` with the filtered colimit of the Čech complexes of `J i`.
3. Each `J i` is injective, hence its positive Čech cohomology vanishes. Exactness
of filtered colimits of abelian groups implies that the colimit Čech complex is
exact in every positive degree.
4. Apply the Čech vanishing criterion to `B` and these cofinal finite coverings.
It gives vanishing of positive derived sections on each object of `B`. The identity
of `Y` is a terminal étale object in `B`; sections there are naturally global
sections. Transport derived sections along this natural isomorphism to obtain
vanishing of the stated positive right derived global sections. -/
theorem isZero_rightDerived_globalSections_colimit_of_injective
    (Y : Scheme.{u}) [CompactSpace Y] [QuasiSeparatedSpace Y]
    (I : Type u) [SmallCategory I] [IsFiltered I]
    (J : I ⥤ Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hJ : ∀ i : I, Injective (J.obj i)) (n : ℕ) :
    IsZero (((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived
      (n + 1)).obj (colimit J)) := by
  classical
  let (U : Y.Etale) : HasFiniteProducts (Over U) :=
    Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks
  let B : Set Y.Etale := {U | CompactSpace U.left ∧ QuasiSeparatedSpace U.left}
  let Cov (U : Y.Etale) (K : Type (u + 1)) (V : K → Y.Etale)
      (f : ∀ k : K, V k ⟶ U) : Prop :=
    Finite K ∧ U ∈ B ∧ (∀ k, V k ∈ B) ∧
      Sieve.ofArrows V f ∈ Y.smallEtaleTopology U
  have hcover (U K V f) (h : Cov U K V f) := h.2.2.2
  have hB (U K V f) (h : Cov U K V f) :
      U ∈ B ∧ (∀ k : K, V k ∈ B) ∧
      ∀ (p : ℕ) (a : Fin (p + 1) → K),
        (piObj (fun j : Fin (p + 1) ↦ Over.mk (f (a j)))).left ∈ B := by
    obtain ⟨hfin, hU, hV, _⟩ := h
    let := hfin
    let := hU.1
    let := hU.2
    refine ⟨hU, hV, fun p a ↦ ?_⟩
    exact compactSpace_and_quasiSeparatedSpace_piObj _ (fun j ↦ hV (a j))
  have hcofinal (U : Y.Etale) (hU : U ∈ B) (K : Type (u + 1))
      (V : K → Y.Etale) (f : ∀ k : K, V k ⟶ U)
      (hf : Sieve.ofArrows V f ∈ Y.smallEtaleTopology U) :
      ∃ (L : Type (u + 1)) (W : L → Y.Etale) (g : ∀ l : L, W l ⟶ U),
        Cov U L W g ∧ ∀ l : L, ∃ (k : K) (t : W l ⟶ V k), t ≫ f k = g l := by
    let := hU.1
    obtain ⟨m, W, g, hR, hW, hg⟩ := (AlgebraicGeometry.Etale.exists_affine_refinement _) hf
    refine ⟨ULift.{u + 1} (Fin m), fun l ↦ W l.down, fun l ↦ g l.down,
      ⟨inferInstance, hU, ?_, ?_⟩, ?_⟩
    · intro l
      have := hW l.down
      exact ⟨inferInstance, inferInstance⟩
    · apply (ofArrows_mem_smallEtaleTopology_iff _).2
      apply Set.eq_univ_of_forall
      intro x
      obtain ⟨l, y, rfl⟩ := Set.mem_iUnion.mp (hg.symm ▸ Set.mem_univ x)
      exact Set.mem_iUnion.mpr ⟨⟨l⟩, y, rfl⟩
    · intro l
      obtain ⟨k, t, ht⟩ := Sieve.ofArrows.exists (hR l.down)
      exact ⟨k, t, ht.symm⟩
  have hcech (U K V f) (h : Cov U K V f) (p : ℕ) (hp : 0 < p) :
      IsZero (((cechComplexFunctor fun k : K ↦ Over.mk (f k)).obj
        ((Over.forget U).op ⋙ (colimit J).obj)).homology p) := by
    let := h.1
    have hs (q : ℕ) (a : Fin (q + 1) → K) :
        PreservesColimitsOfShape I
          ((sheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
            (Opposite.op (piObj (fun j : Fin (q + 1) ↦ Over.mk (f (a j)))).left)) := by
      obtain ⟨hcomp, hqs⟩ := (hB U K V f h).2.2 q a
      let := hcomp
      let := hqs
      exact ⟨fun {G} ↦ ⟨fun {d} hd ↦ abelianSectionsColimit Y _ hd⟩⟩
    let H := sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (Functor.whiskeringLeft (Over U)ᵒᵖ Y.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
        (Over.forget U).op ⋙
      cechComplexFunctor (fun k : K ↦ Over.mk (f k)) ⋙
      HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℕ) p
    have : PreservesColimitsOfShape I H :=
      preservesColimitsOfShape_finiteEtaleCechHomology Y U K V f I hs p
    have hzero : IsZero (J ⋙ H) := Functor.isZero _ (fun i ↦ by
      let := hJ i
      exact injective_sheaf_cech_acyclic Y (J.obj i) U K V f (hcover U K V f h) p hp)
    exact (isColimitOfPreserves H (colimit.isColimit J)).isZero_pt hzero
  let T : Y.Etale := Etale.mk (𝟙 Y)
  have hT : T ∈ B := ⟨‹CompactSpace Y›, ‹QuasiSeparatedSpace Y›⟩
  have hz := isZero_rightDerived_etale_of_cech_vanishing Y B Cov (colimit J)
    hcover hB hcofinal hcech T hT (n + 1) (Nat.succ_pos n)
  have : ((sheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (Opposite.op T)).Additive :=
    inferInstanceAs ((sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (CategoryTheory.evaluation _ _).obj (Opposite.op T)).Additive)
  have hterminal : IsTerminal T := MorphismProperty.Over.mkIdTerminal @Etale Y
  let e : Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1} ≅
      (sheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (Opposite.op T) :=
    Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1} hterminal
  let d : (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived (n + 1) ≅
      ((sheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (Opposite.op T)).rightDerived (n + 1) :=
    { hom := NatTrans.rightDerived e.hom (n + 1)
      inv := NatTrans.rightDerived e.inv (n + 1)
      hom_inv_id := by rw [← NatTrans.rightDerived_comp, e.hom_inv_id]; simp
      inv_hom_id := by rw [← NatTrans.rightDerived_comp, e.inv_hom_id]; simp }
  exact hz.of_iso (d.app (colimit J))

end AlgebraicGeometry.Scheme
