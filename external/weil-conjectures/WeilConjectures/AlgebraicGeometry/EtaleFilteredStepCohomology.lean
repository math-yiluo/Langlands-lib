/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.EtaleTermwiseHypercohomology
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.StupidTrunc
public import WeilConjectures.AlgebraicGeometry.EtaleRestrictedTotalResolution
public import WeilConjectures.AlgebraicGeometry.EtaleRestrictedSectionsComparison
import WeilConjectures.AlgebraicGeometry.EtaleRestrictedSectionsComparisonMap

/-! # Computing one filtered Cartan--Eilenberg step

Source: Stacks Project, Tags 015J and 0133, applied to the columns in degrees at least q.
(blueprint: lem-weil-pbc-etale-filtered-step-cohomology).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The canonical filtered-step cohomology comparison. Its first factor is the
inverse of the sections lift through the monic step inclusion; its second is
cohomology of the specified restricted K-injective augmentation.
Source: Stacks, Tag 015J, proof remark (3), and Tag 0133.
(blueprint: def-weil-pbc-etale-filtered-step-cohomology-iso). -/
noncomputable def etaleFilteredStepCohomologyIso
    (X : Scheme.{u})
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (T : EtaleTermwiseHypercohomology X K) (p q : ℤ) :
    ((T.L.step q : CochainComplex AddCommGrpCat.{u + 1} ℤ).homology p) ≅
      (cohomology AddCommGrpCat.{u + 1} X p).obj
        (DerivedCategory.Q.obj (K.obj.stupidTrunc (ComplexShape.embeddingUpIntGE q))) := by
  letI := (etaleRestrictedTotal_resolution X K T q).1
  letI := (etaleRestrictedTotal_resolution X K T q).2
  letI := etaleRestrictedSectionsLift_isIso X K T q
  exact (HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℤ)
    p).mapIso (asIso (etaleRestrictedSectionsLift X K T q)).symm ≪≫
      resolutionEtaleCohomologyIso X
        (K.obj.stupidTrunc (ComplexShape.embeddingUpIntGE q))
        (etaleRestrictedTotal X K T q) (etaleRestrictedAugmentation X K T q) p

/-- The cohomology of one filtered total step computes derived global sections of
one fixed stupid truncation, compatibly with its inclusion in the full complex.
Source: Stacks Project, Tag 015J, proof remark (3), and Tag 0133.

Proof: Restrict the augmented bicomplex to complex degrees s >= q and extend by zero.
Its rows remain injective resolutions of the corresponding terms of the stupid
truncation; the other rows are zero. The row augmentations commute with the complex
differential, so their degree-zero summand maps assemble into an augmentation of
K.stupidTrunc(embeddingUpIntGE q) into the restricted total. In total degree n its
only possibly nonzero summands have resolution degree r >= 0 and complex degree
s >= q with r+s=n. There are finitely many, and none when n<q. The total therefore
has injective terms and is bounded below, hence is K-injective. The exact augmented
rows and the finite diagonal filtration give an acyclic augmentation cone (0133),
so this augmentation is a quasi-isomorphism. Apply global sections termwise. Its
restricted total identifies with (T.L.step q): T.filtration_formula identifies the
subobjects degreewise, and their canonical inclusions commute with differentials.
This gives the displayed cohomology isomorphism by the K-injective computation of
RΓ. The inclusion of the restricted resolution into the full total, followed by
T.comparison, is a resolution comparison for the stupid-truncation inclusion:
T.aug_formula fixes the augmentation, and T.over_K makes its composite agree with
T.ρ.map up to homotopy. Naturality of the K-injective derived-functor computation
and T.w_formula then identify the induced map with the map of the truncation
inclusion. Finally T.c_formula fixes the full-total identification, giving the
stated commutative equation. Empty diagonals, the zero complex and negative q
satisfy the same finite-diagonal calculation; no positivity of q is required.
(blueprint: lem-weil-pbc-etale-filtered-step-cohomology-iso). -/
theorem etale_filtered_step_cohomology_iso
    (X : Scheme.{u})
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (T : EtaleTermwiseHypercohomology X K) (p q : ℤ) :
    Nonempty (((T.L.step q : CochainComplex AddCommGrpCat.{u + 1} ℤ).homology p) ≅
        (cohomology AddCommGrpCat.{u + 1} X p).obj
          (DerivedCategory.Q.obj (K.obj.stupidTrunc (ComplexShape.embeddingUpIntGE q)))) := by
  exact ⟨etaleFilteredStepCohomologyIso X K T p q⟩


set_option backward.isDefEq.respectTransparency false in
private theorem resolutionObjQIso_naturality
    (X : Scheme.{u})
    (I J : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    [I.IsKInjective] [J.IsKInjective] (g : I ⟶ J) :
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctor.map
        (DerivedCategory.Q.map g) ≫
      ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorObjQIso
        J).hom =
    ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorObjQIso
        I).hom ≫ DerivedCategory.Q.map
      (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).map g) := by
  let F := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}
  have hn := F.rightDerivedFunctorUnit.naturality
    ((HomotopyCategory.quotient _ (.up ℤ)).map g)
  dsimp only [Functor.comp_map] at hn
  simp only [Functor.rightDerivedFunctorObjQIso, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_hom,
    Quotient.lift.isLift_inv, asIso_inv]
  repeat erw [Category.comp_id]
  change F.rightDerivedFunctor.map
    (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map g)) ≫
      F.rightDerivedFunctor.map (𝟙 _) ≫ inv (F.rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj J)) =
    (F.rightDerivedFunctor.map (𝟙 _) ≫ inv (F.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj I))) ≫
      DerivedCategory.Qh.map ((F.mapHomotopyCategory (.up ℤ)).map
        ((HomotopyCategory.quotient _ (.up ℤ)).map g))
  erw [F.rightDerivedFunctor.map_id, F.rightDerivedFunctor.map_id]
  simp only [Category.id_comp]
  apply (cancel_epi (F.rightDerivedFunctorUnit.app
    ((HomotopyCategory.quotient _ (.up ℤ)).obj I))).mp
  change _ ≫ F.rightDerivedFunctor.map
    (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map g)) ≫ _ = _
  rw [← Category.assoc, ← hn]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc, IsIso.hom_inv_id,
    Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem resolutionEtaleCohomologyIso_naturality
    (X : Scheme.{u})
    (A B I J : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (a : A ⟶ I) (b : B ⟶ J) [QuasiIso a] [QuasiIso b]
    [I.IsKInjective] [J.IsKInjective] (f : A ⟶ B) (g : I ⟶ J)
    (h : Nonempty (Homotopy (a ≫ g) (f ≫ b))) (p : ℤ) :
    HomologicalComplex.homologyMap
        (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
          (.up ℤ)).map g) p ≫ (resolutionEtaleCohomologyIso X B J b p).hom =
      (resolutionEtaleCohomologyIso X A I a p).hom ≫
        (cohomology AddCommGrpCat.{u + 1} X p).map (DerivedCategory.Q.map f) := by
  let F := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let H := DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} p
  let G := F.mapHomologicalComplex (.up ℤ)
  let e := F.rightDerivedFunctor.mapIso (asIso (DerivedCategory.Q.map a)) ≪≫
    F.rightDerivedFunctorObjQIso I
  let e' := F.rightDerivedFunctor.mapIso (asIso (DerivedCategory.Q.map b)) ≪≫
    F.rightDerivedFunctorObjQIso J
  have hq := DerivedCategory.Q_map_eq_of_homotopy _ h.some
  have hn := resolutionObjQIso_naturality X I J g
  have he : e.hom ≫ DerivedCategory.Q.map (G.map g) =
      F.rightDerivedFunctor.map (DerivedCategory.Q.map f) ≫ e'.hom := by
    dsimp only [e, e', Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
    rw [Category.assoc, ← hn, ← Functor.map_comp_assoc,
      ← Functor.map_comp, hq, Functor.map_comp, Functor.map_comp]
    simp only [Category.assoc]
    rfl
  let c := (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u + 1} p).app (G.obj I)
  let d := (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u + 1} p).app (G.obj J)
  have hh := DerivedCategory.homologyFunctorFactors_hom_naturality (G.map g) p
  change H.map (DerivedCategory.Q.map (G.map g)) ≫ d.hom =
    c.hom ≫ HomologicalComplex.homologyMap (G.map g) p at hh
  change HomologicalComplex.homologyMap (G.map g) p ≫
      (H.mapIso e' ≪≫ d).inv = (H.mapIso e ≪≫ c).inv ≫ _
  simp only [Iso.trans_inv, Functor.mapIso_inv, Category.assoc]
  apply (cancel_epi c.hom).mp
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [← hh]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  apply (cancel_epi (H.map e.hom)).mp
  rw [← Functor.map_comp_assoc, he]
  rw [H.map_comp]
  simp only [Category.assoc, ← H.map_comp, Iso.hom_inv_id,
    Category.comp_id]
  rw [← H.map_comp_assoc, e.hom_inv_id, H.map_id, Category.id_comp]
  rfl

/-- Compatibility of the canonical filtered-step isomorphism with truncation inclusion.
Source: Stacks Project, Tags 015J and 0133; restricted augmented-total comparison.

Proof: Use the explicit restricted augmentation and total from
`etaleRestrictedAugmentation`. The diagonal description of the mapped total
identifies its inclusion into the full mapped total with `(T.L.step q).arrow`.
The named augmentation-inclusion equation and `T.over_K` give the homotopy
between augmentation composites. Naturality of the derived unit on K-injectives
and of the homology comparison proves resolutionEtaleCohomologyIso naturality
(the two private helpers below). The named chain-level sections equation and
`T.c_formula` then identify the full comparison. Precompose by homology of the
canonical sections lift, use its inclusion equation, and cancel its inverse in
the definition of etaleFilteredStepCohomologyIso to obtain the displayed equality. The argument is
degreewise and also covers empty diagonals, zero terms, and arbitrary integers p,q.
(blueprint: lem-weil-pbc-etale-filtered-step-cohomology-compatibility). -/
theorem etale_filtered_step_cohomology_compatibility
    (X : Scheme.{u})
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (T : EtaleTermwiseHypercohomology X K) (p q : ℤ) :
    HomologicalComplex.homologyMap (T.L.step q).arrow p ≫ (T.c p).hom =
      (etaleFilteredStepCohomologyIso X K T p q).hom ≫
        (cohomology AddCommGrpCat.{u + 1} X p).map
          (DerivedCategory.Q.map (K.obj.ιStupidTrunc (ComplexShape.embeddingUpIntGE q))) := by
  have : QuasiIso (etaleRestrictedAugmentation X K T q) :=
    (etaleRestrictedTotal_resolution X K T q).1
  have : CochainComplex.IsKInjective (etaleRestrictedTotal X K T q) :=
    (etaleRestrictedTotal_resolution X K T q).2
  have : IsIso (etaleRestrictedSectionsLift X K T q) :=
    etaleRestrictedSectionsLift_isIso X K T q
  have : QuasiIso T.ρ.map := T.ρ.quasiIso
  have : T.ρ.complex.IsKInjective := T.ρ.isKInjective
  let g := etaleRestrictedTotalInclusion X K T q ≫ T.comparison
  have hg : Nonempty (Homotopy
      (etaleRestrictedAugmentation X K T q ≫ g)
      (K.obj.ιStupidTrunc (ComplexShape.embeddingUpIntGE q) ≫ T.ρ.map)) := by
    dsimp only [g]
    rw [← Category.assoc, etaleRestrictedAugmentation_inclusion, Category.assoc]
    exact ⟨T.over_K.some.compLeft _⟩
  have hn := resolutionEtaleCohomologyIso_naturality X _ _ _ _
    (etaleRestrictedAugmentation X K T q) T.ρ.map
    (K.obj.ιStupidTrunc (ComplexShape.embeddingUpIntGE q)) g hg p
  apply (cancel_epi
    (HomologicalComplex.homologyMap (etaleRestrictedSectionsLift X K T q) p)).mp
  rw [← HomologicalComplex.homologyMap_comp_assoc,
    etaleRestrictedSectionsLift_arrow, T.c_formula]
  rw [← HomologicalComplex.homologyMap_comp_assoc,
    ← etaleRestrictedSections_comparison_map]
  rw [hn]
  simp only [etaleFilteredStepCohomologyIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, asIso_inv, HomologicalComplex.homologyFunctor_map, Category.assoc]
  rw [← HomologicalComplex.homologyMap_comp_assoc]
  simp

/-- (blueprint: lem-weil-pbc-etale-filtered-step-cohomology) -/
theorem etale_filtered_step_cohomology
    (X : Scheme.{u})
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (T : EtaleTermwiseHypercohomology X K) (p q : ℤ) :
    ∃ e : ((T.L.step q : CochainComplex AddCommGrpCat.{u + 1} ℤ).homology p) ≅
        (cohomology AddCommGrpCat.{u + 1} X p).obj
          (DerivedCategory.Q.obj (K.obj.stupidTrunc (ComplexShape.embeddingUpIntGE q))),
      HomologicalComplex.homologyMap (T.L.step q).arrow p ≫ (T.c p).hom =
        e.hom ≫ (cohomology AddCommGrpCat.{u + 1} X p).map
          (DerivedCategory.Q.map (K.obj.ιStupidTrunc (ComplexShape.embeddingUpIntGE q))) := by
  let e := etaleFilteredStepCohomologyIso X K T p q
  refine ⟨e, ?_⟩
  exact etale_filtered_step_cohomology_compatibility X K T p q


end AlgebraicGeometry.Etale
