/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineAcyclicHypercover
import WeilConjectures.CategoryTheory.DerivedCategory.BoundedBelowSectionModel
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianHypercoverQuasiIso
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianHypercoverRowComparison
import WeilConjectures.AlgebraicGeometry.CondensedHypercoverInjectiveRow
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.CondensedQcqsPushforwardLocalComparison
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Category.Grp.EpiMono
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-!
# Continuity of ordinary condensed-coefficient pushforward

Source: Hemo--Richarz--Scholbach, Constructible sheaves, Lemma 5.3(1)
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v w x y z

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

noncomputable local instance
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] (X : Scheme.{u}) :
    HasZeroMorphisms (Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
      (condensedRingObj Λ X)) := inferInstance

/-- The cocone obtained from good truncation, retaining the original complexes as its
source. Source: Hemo--Richarz--Scholbach, Lemma 5.3(1)
(auxiliary; not a blueprint node). -/
noncomputable def condensedContinuityCocone
    {A : Type v} [Category.{w} A] [Abelian A]
    {I : Type x} [Category.{y} I] (D : I ⥤ CochainComplex A ℤ) (a : ℤ)
    [HasColimit (D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A)] : Cocone D :=
  (Cocone.precompose (Functor.whiskerLeft D
    ((ComplexShape.embeddingUpIntGE a).πTruncGENatTrans A))).obj
      (colimit.cocone (D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A))

/-- The canonical comparison induced by the maps to the termwise truncated colimit.
Source: Hemo--Richarz--Scholbach, Lemma 5.3(1)
(auxiliary; not a blueprint node). -/
noncomputable def condensedContinuityComparison
    {A : Type v} [Category.{w} A] [Abelian A]
    {B : Type u} [Category.{z} B]
    {I : Type x} [Category.{y} I] (D : I ⥤ CochainComplex A ℤ) (a : ℤ)
    (T : CochainComplex A ℤ ⥤ B)
    [HasColimit (D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A)]
    [HasColimit (D ⋙ T)] :
    colimit (D ⋙ T) ⟶ T.obj (condensedContinuityCocone D a).pt :=
  colimit.desc (D ⋙ T) (T.mapCocone (condensedContinuityCocone D a))

/-- Evaluation of the underlying abelian sheaf at the terminal pro-etale object.
Its right derived functor is ordinary uncompleted derived global sections of modules.
Source: Hemo--Richarz--Scholbach, proof of Lemma 5.3(1)
(auxiliary; not a blueprint node). -/
noncomputable abbrev condensedModuleSections
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] (X : Scheme.{u}) :
    Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) (condensedRingObj Λ X) ⥤
      AddCommGrpCat.{u + 1} :=
  Mod.forget (condensedRingObj Λ X) ⋙
    sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} ⋙
      (evaluation X.ProEtᵒᵖ AddCommGrpCat.{u + 1}).obj
        (Opposite.op (Scheme.ProEt.mk (𝟙 X)))

private theorem isIso_of_weaklyContractible_sections (X : Scheme.{u})
    {M N : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}} (f : M ⟶ N)
    (hf : ∀ (V : X.ProEt), IsAffine V.left →
      (∀ (F G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) (g : F ⟶ G),
        Epi g → Function.Surjective (g.hom.app (Opposite.op V))) →
      IsIso (f.hom.app (Opposite.op V))) : IsIso f := by
  have hinj (V : X.ProEtᵒᵖ) : Function.Injective (f.hom.app V) := by
    intro x y hxy
    obtain ⟨I, W, g, hcov, haff, hweak⟩ :=
      Scheme.ProEt.exists_affine_weaklyContractible_covering_family X V.unop
    have hcover : Sieve.ofArrows W g ∈ Scheme.ProEt.topology X V.unop :=
      Precoverage.generate_mem_toGrothendieck hcov
    apply Sheaf.isSeparated M V.unop _ hcover x y
    rintro Z h ⟨_, b, _, ⟨i⟩, rfl⟩
    have := hf (W i) (haff i) (hweak i)
    have hi : Function.Injective (f.hom.app (Opposite.op (W i))) :=
      (AddCommGrpCat.mono_iff_injective _).1 inferInstance
    have heq : M.obj.map (g i).op x = M.obj.map (g i).op y := by
      apply hi
      rw [f.hom.naturality_apply, f.hom.naturality_apply, hxy]
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply, heq]
  have hsurj : Presheaf.IsLocallySurjective (Scheme.ProEt.topology X) f.hom := by
    constructor
    intro V x
    obtain ⟨I, W, g, hcov, haff, hweak⟩ :=
      Scheme.ProEt.exists_affine_weaklyContractible_covering_family X V
    apply (Scheme.ProEt.topology X).superset_covering _
      (Precoverage.generate_mem_toGrothendieck hcov)
    rintro Z h ⟨_, b, _, ⟨i⟩, rfl⟩
    have := hf (W i) (haff i) (hweak i)
    have hs : Function.Surjective (f.hom.app (Opposite.op (W i))) :=
      (AddCommGrpCat.epi_iff_surjective _).1 inferInstance
    obtain ⟨y, hy⟩ := hs (N.obj.map (g i).op x)
    refine ⟨M.obj.map b.op y, ?_⟩
    rw [f.hom.naturality_apply, hy, op_comp, Functor.map_comp]
    rfl
  apply (Sheaf.isLocallyBijective_iff_isIso f).1
  exact ⟨(Sheaf.isLocallyInjective_iff_injective f).2 hinj, hsurj⟩

set_option synthInstance.maxHeartbeats 100000 in
-- Colimit inference for the internal module category needs a larger search budget.
set_option synthInstance.maxSize 4096 in
/-- The ordinary uncompleted derived pushforward commutes with uniformly bounded-below
filtered colimits on cohomology. There is no torsion, completeness, or constructibility
condition on the coefficient ring or its modules.

Source: Hemo--Richarz--Scholbach, Lemma 5.3(1)
(auxiliary; not a blueprint node).

Proof: replace each complex by its good truncation at the common lower bound. Exactness
of filtered colimits in module sheaves identifies cohomology of their termwise colimit
with the colimit of cohomology. Cover every object of the target site by affine weakly
contractible objects V. Their inverse images W are qcqs because f is qcqs. Resolve W
by an acyclic hypercover whose terms are finite disjoint unions of weakly contractible
affines. On each component, evaluation is exact and preserves filtered colimits
(lem-weil-pbc-proetale-wcontractible-affine-evaluation-colimits). The hypercover
computes derived sections (lem-weil-pbc-proetale-hypercover-computes-bounded-complex).
In total degree r only the finitely many hypercover degrees 0 through r-a occur.
Evaluation commutes with the filtered colimit in each of these degrees; finite products
and finite sums commute with filtered colimits of modules. Thus the total complexes
are canonically identified, including both differential summands. Exact filtered
colimits then commute with cycles, boundaries and their quotient. On K-injective
resolutions, the formula (f_*J)(V)=J(W) identifies this with precisely the cohomology
comparison induced by the original cocone legs. The comparison is invertible on every
V. A sheaf map invertible on this covering basis is invertible: injectivity follows
from separation and surjectivity follows by lifting locally and gluing. -/
theorem condensed_qcqs_pushforward_continuity
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
        (condensedRingObj Λ X)) ℤ)
    (a : ℤ) (ha : ∀ (i : I) (n : ℤ), n < a → IsZero ((D.obj i).homology n))
    (q : ℤ) :
    IsIso (condensedContinuityComparison D a
      (DerivedCategory.Q ⋙ (CondensedRing.lowerStar Λ f).rightDerivedFunctor ⋙
        DerivedCategory.homologyFunctor _ q)) := by
  have : IsIso ((Mod.forget (condensedRingObj Λ Y)).map
      (condensedContinuityComparison D a
        (DerivedCategory.Q ⋙ (CondensedRing.lowerStar Λ f).rightDerivedFunctor ⋙
          DerivedCategory.homologyFunctor _ q))) := by
    apply isIso_of_weaklyContractible_sections Y
    intro V hV hweak
    exact condensed_qcqs_pushforward_local_comparison Λ f D a ha q V hV hweak
  exact isIso_of_reflects_iso _ (Mod.forget (condensedRingObj Λ Y))

set_option backward.isDefEq.respectTransparency false in
private theorem comparison_isIso_of_bounded_model
    {A : Type v} [Category.{w} A] [Abelian A]
    {B : Type u} [Category.{z} B]
    {I : Type x} [Category.{y} I]
    (D : I ⥤ CochainComplex A ℤ) (a : ℤ)
    (T H : CochainComplex A ℤ ⥤ B)
    [HasColimit (D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A)]
    [HasColimit (D ⋙ T)] [HasColimitsOfShape I A]
    [PreservesColimit (D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A) H]
    (hπ : ∀ i, IsIso (T.map ((D.obj i).πTruncGE a)))
    (e : ∀ (K : CochainComplex A ℤ) (_ : K.IsStrictlyGE a), T.obj K ≅ H.obj K)
    (he : ∀ (K L : CochainComplex A ℤ) (hK : K.IsStrictlyGE a)
      (hL : L.IsStrictlyGE a) (f : K ⟶ L),
      T.map f ≫ (e L hL).hom = (e K hK).hom ≫ H.map f) :
    IsIso (condensedContinuityComparison D a T) := by
  let E : I ⥤ CochainComplex A ℤ :=
    D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A
  let c := colimit.cocone E
  have hE (i : I) : (E.obj i).IsStrictlyGE a := by
    change ((D.obj i).truncGE a).IsStrictlyGE a
    infer_instance
  have hc : CochainComplex.IsStrictlyGE c.pt a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    exact (isColimitOfPreserves (HomologicalComplex.eval A (.up ℤ) n)
      (colimit.isColimit E)).isZero_pt
        (Functor.isZero _ fun i ↦ (E.obj i).isZero_of_isStrictlyGE a n hn)
  let η : D ⋙ T ⟶ E ⋙ H :=
    Functor.whiskerRight (Functor.whiskerLeft D
      ((ComplexShape.embeddingUpIntGE a).πTruncGENatTrans A)) T ≫
      { app := fun i ↦ (e (E.obj i) (hE i)).hom
        naturality := fun i j f ↦ by
          change T.map (E.map f) ≫ (e (E.obj j) (hE j)).hom =
            (e (E.obj i) (hE i)).hom ≫ H.map (E.map f)
          exact he (E.obj i) (E.obj j) (hE i) (hE j) (E.map f) }
  have hη (i : I) : IsIso (η.app i) := by
    have := hπ i
    dsimp only [η, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    change IsIso (T.map ((D.obj i).πTruncGE a) ≫ (e (E.obj i) (hE i)).hom)
    infer_instance
  have : IsIso η := NatIso.isIso_of_isIso_app η
  have hcolim : IsColimit (H.mapCocone c) :=
    isColimitOfPreserves H (colimit.isColimit E)
  let k := colimit.desc (D ⋙ T)
    ((Cocone.precompose η).obj (H.mapCocone c))
  have hk : IsIso k := by
    have hcolim' : IsColimit ((Cocone.precompose η).obj (H.mapCocone c)) :=
      (IsColimit.precomposeHomEquiv (asIso η) (H.mapCocone c)).symm hcolim
    exact (colimit.isColimit (D ⋙ T)).coconePointUniqueUpToIso hcolim' |>.isIso_hom
  have heq : condensedContinuityComparison D a T ≫ (e c.pt hc).hom = k := by
    apply colimit.hom_ext
    intro i
    simp only [condensedContinuityComparison, colimit.ι_desc_assoc]
    rw [colimit.ι_desc]
    change T.map ((D.obj i).πTruncGE a ≫ c.ι.app i) ≫ (e c.pt hc).hom =
      (T.map ((D.obj i).πTruncGE a) ≫ (e (E.obj i) (hE i)).hom) ≫ H.map (c.ι.app i)
    rw [T.map_comp, Category.assoc, he _ _ (hE i) hc, Category.assoc]
  have : IsIso (condensedContinuityComparison D a T ≫ (e c.pt hc).hom) := by
    rw [heq]
    exact hk
  exact IsIso.of_isIso_comp_right _ (e c.pt hc).hom

set_option synthInstance.maxHeartbeats 100000 in
-- Colimit inference for the internal module category needs a larger search budget.
set_option synthInstance.maxSize 4096 in
set_option backward.isDefEq.respectTransparency false in
/-- Ordinary derived global sections of a qcqs scheme satisfy the same comparison.
Source: Hemo--Richarz--Scholbach, Lemma 5.3(1)
(auxiliary; not a blueprint node).

Proof: choose an affine weakly contractible hypercover of W=X and form its actual
section total after forgetting the internal module action. The existing proved
internal-module row theorem gives injective row descent. Bounded-below row and column
comparison then identify this total naturally with the actual right derived global-sections functor.
Affine
evaluation and diagonal coproducts commute with filtered colimits; homology does
so because these colimits are exact. Good truncation is a quasi-isomorphism under
the given cohomological bound. Transporting its colimit cocone through the natural
model identifies its universal map with the stated canonical comparison. -/
theorem condensed_qcqs_globalSections_continuity
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
        (condensedRingObj Λ X)) ℤ)
    (a : ℤ) (ha : ∀ (i : I) (n : ℤ), n < a → IsZero ((D.obj i).homology n))
    (q : ℤ) :
    IsIso (condensedContinuityComparison D a
      (DerivedCategory.Q ⋙ (condensedModuleSections Λ X).rightDerivedFunctor ⋙
        DerivedCategory.homologyFunctor _ q)) := by
  let W : X.ProEt := Scheme.ProEt.mk (𝟙 X)
  have : CompactSpace W.left := by change CompactSpace X; infer_instance
  have : QuasiSeparatedSpace W.left := by change QuasiSeparatedSpace X; infer_instance
  obtain ⟨U, haff, hweak, hzero, hone, hhigher⟩ :=
    Scheme.ProEt.exists_affine_weaklyContractible_hypercover X W
  let F := condensedModuleSections Λ X
  let A := Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
    (condensedRingObj Λ X)
  let forget : A ⥤ Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
    Mod.forget (condensedRingObj Λ X)
  let P : CochainComplex.Plus A ⥤
      CochainComplex.Plus (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) :=
    ObjectProperty.lift _
      (CochainComplex.Plus.ι A ⋙ forget.mapHomologicalComplex (.up ℤ)) (fun K ↦ by
        obtain ⟨N, hN⟩ := K.property
        have := hN
        refine ⟨N, ?_⟩
        change CochainComplex.IsStrictlyGE
          ((forget.mapHomologicalComplex (.up ℤ)).obj K.obj) N
        infer_instance)
  let H := forget.mapHomologicalComplex (.up ℤ) ⋙ Scheme.ProEt.abelianHypercoverTotal X W U
  let α : F.mapHomologicalComplex (.up ℤ) ⟶ H :=
    Functor.whiskerLeft (forget.mapHomologicalComplex (.up ℤ))
      (Scheme.ProEt.abelianHypercoverAugmentation X W U)
  have hH (K L : CochainComplex.Plus A) (f : K ⟶ L) (hf : QuasiIso f.hom) :
      QuasiIso (H.map f.hom) := by
    have := hf
    have : QuasiIso (P.map f).hom := by
      change QuasiIso ((forget.mapHomologicalComplex (.up ℤ)).map f.hom)
      infer_instance
    exact Scheme.ProEt.abelianHypercoverTotal_map_quasiIso_of_weaklyContractible
      X W U haff hweak (P.obj K) (P.obj L) (P.map f) inferInstance
  have hα (J : CochainComplex.Plus A) (hJ : ∀ n : ℤ, Injective (J.obj.X n)) :
      QuasiIso (α.app J.obj) := by
    apply Scheme.ProEt.abelianHypercoverAugmentation_quasiIso_of_rows X W U (P.obj J)
    intro n
    have := hJ n
    exact condensedHypercoverInjectiveRow Λ X W U hzero hone hhigher (J.obj.X n)
  obtain ⟨e, he⟩ := CategoryTheory.Functor.boundedBelow_sectionModel F H α hH hα a
  let G := HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) q
  let T := DerivedCategory.Q ⋙ F.rightDerivedFunctor ⋙
    DerivedCategory.homologyFunctor AddCommGrpCat q
  let eqv (K) (hK : CochainComplex.IsStrictlyGE K a) : T.obj K ≅ (H ⋙ G).obj K :=
    (DerivedCategory.homologyFunctor AddCommGrpCat q).mapIso (e K hK) ≪≫
      (DerivedCategory.homologyFunctorFactors AddCommGrpCat q).app (H.obj K)
  have hnat (K L) (hK : CochainComplex.IsStrictlyGE K a)
      (hL : CochainComplex.IsStrictlyGE L a) (f : K ⟶ L) :
      T.map f ≫ (eqv L hL).hom = (eqv K hK).hom ≫ (H ⋙ G).map f := by
    dsimp only [eqv, T, Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom]
    rw [← Category.assoc, ← Functor.map_comp, he K L hK hL f, Functor.map_comp,
      Category.assoc]
    have hn := (DerivedCategory.homologyFunctorFactors AddCommGrpCat q).hom.naturality
      (H.map f)
    change (DerivedCategory.homologyFunctor AddCommGrpCat q).map (e K hK).hom ≫ _ = _
    simpa only [G, Functor.comp_map, Category.assoc, Iso.app_hom] using congrArg
      (fun t ↦ (DerivedCategory.homologyFunctor AddCommGrpCat q).map (e K hK).hom ≫ t) hn
  have : PreservesColimitsOfSize.{u + 1, u + 1}
      (Scheme.ProEt.abelianHypercoverTotal X W U) :=
    Scheme.ProEt.abelianHypercoverTotal_preservesColimits X W U haff hweak
  have : PreservesColimitsOfShape I H := by
    dsimp [H]
    infer_instance
  apply comparison_isIso_of_bounded_model D a T (H ⋙ G) _ eqv hnat
  intro i
  have : (D.obj i).IsGE a := by
    rw [CochainComplex.isGE_iff]
    intro n hn
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact ha i n hn
  have : QuasiIso ((D.obj i).πTruncGE a) := inferInstance
  change IsIso ((DerivedCategory.homologyFunctor AddCommGrpCat q).map
    (F.rightDerivedFunctor.map (DerivedCategory.Q.map ((D.obj i).πTruncGE a))))
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The representative comparison induces the canonical isomorphism on each homology object.
Source: Hemo--Richarz--Scholbach, Constructible sheaves, Lemma 5.3(1), representative
comparison step.
(auxiliary; not a blueprint node)

Proof: apply the homology functor to the leg equation, transport along the componentwise
isomorphism `e`, and identify the target using `ε`. Naturality and the colimit universal
property identify the resulting map with the canonical continuity comparison, which is an
isomorphism by the hypothesis `h`. Exact colimits commute with complex homology;
cancel this invertible homology-colimit comparison and the isomorphism induced by `e`
to obtain the asserted homology map. This is the homology-level statement used to prove
the representative quasi-isomorphism below.
-/
theorem condensedContinuityComparison_representatives_homology
    {A : Type v} [Category.{w} A] [Abelian A] [HasDerivedCategory.{w} A]
    {B : Type u} [Category.{z} B] [Abelian B] [HasDerivedCategory.{z} B]
    {I : Type x} [Category.{y} I] [IsFiltered I]
    [HasColimitsOfShape I B] [HasExactColimitsOfShape I B]
    (D : I ⥤ CochainComplex A ℤ) (a : ℤ)
    [HasColimit (D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A)]
    (F : DerivedCategory A ⥤ DerivedCategory B)
    [∀ q : ℤ, HasColimit (D ⋙ (DerivedCategory.Q ⋙ F ⋙
      DerivedCategory.homologyFunctor B q))]
    (h : ∀ q : ℤ, IsIso (condensedContinuityComparison D a
      (DerivedCategory.Q ⋙ F ⋙ DerivedCategory.homologyFunctor B q)))
    (P : I ⥤ CochainComplex B ℤ) [HasColimit P] (L : CochainComplex B ℤ)
    (e : D ⋙ DerivedCategory.Q ⋙ F ≅ P ⋙ DerivedCategory.Q)
    (ε : F.obj (DerivedCategory.Q.obj (condensedContinuityCocone D a).pt) ≅
      DerivedCategory.Q.obj L)
    (ι : P ⟶ (Functor.const I).obj L)
    (hι : ∀ i : I, e.hom.app i ≫ DerivedCategory.Q.map (ι.app i) =
      F.map (DerivedCategory.Q.map ((condensedContinuityCocone D a).ι.app i)) ≫ ε.hom) :
    ∀ q : ℤ, IsIso (HomologicalComplex.homologyMap (colimit.desc P (Cocone.mk L ι)) q) := by
  intro q
  let H := HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) q
  let H' := DerivedCategory.homologyFunctor B q
  let e' : D ⋙ (DerivedCategory.Q ⋙ F ⋙ H') ≅ P ⋙ H :=
    Functor.isoWhiskerRight e H' ≪≫
      Functor.isoWhiskerLeft P (DerivedCategory.homologyFunctorFactors B q)
  let ε' : H'.obj (F.obj (DerivedCategory.Q.obj (condensedContinuityCocone D a).pt)) ≅
      H.obj L :=
    H'.mapIso ε ≪≫ (DerivedCategory.homologyFunctorFactors B q).app L
  let k := colimit.desc P (Cocone.mk L ι)
  have hk : colimMap e'.hom ≫ colimit.post P H ≫ H.map k =
      condensedContinuityComparison D a (DerivedCategory.Q ⋙ F ⋙ H') ≫ ε'.hom := by
    apply colimit.hom_ext
    intro i
    simp only [ι_colimMap_assoc, colimit.ι_post_assoc, ← H.map_comp,
      condensedContinuityComparison, colimit.ι_desc_assoc]
    rw [show colimit.ι P i ≫ k = ι.app i from colimit.ι_desc _ i]
    dsimp only [e', ε', Iso.trans_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      NatTrans.comp_app, Functor.mapIso_hom, H, H']
    simp only [Category.assoc]
    change H'.map (e.hom.app i) ≫
      (DerivedCategory.homologyFunctorFactors B q).hom.app (P.obj i) ≫
        HomologicalComplex.homologyMap (ι.app i) q =
      H'.map (F.map (DerivedCategory.Q.map
        ((condensedContinuityCocone D a).ι.app i))) ≫ H'.map ε.hom ≫
          (DerivedCategory.homologyFunctorFactors B q).hom.app L
    rw [← DerivedCategory.homologyFunctorFactors_hom_naturality,
      ← Category.assoc, ← Functor.map_comp, hι i, Functor.map_comp, Category.assoc]
    rfl
  have := h q
  have : IsIso (colimMap e'.hom ≫ colimit.post P H ≫ H.map k) := by
    rw [hk]
    infer_instance
  have : IsIso (colimit.post P H ≫ H.map k) :=
    IsIso.of_isIso_comp_left (colimMap e'.hom) _
  exact IsIso.of_isIso_comp_left (colimit.post P H) (H.map k)

/-- The representative form of continuity, independent of the choice of functorial
quasi-isomorphic representatives. The equation on each leg requires the specified
canonical derived map, rather than an arbitrary map of representatives.

Source: Hemo--Richarz--Scholbach, Lemma 5.3(1), hypercover proof
(auxiliary; not a blueprint node).

Proof: exact filtered colimits in B commute with kernels, images, and cokernels,
so cohomology of the termwise colimit P is the colimit of its cohomology.
The natural isomorphism e identifies each term with F(QD_i), and ε identifies the
value at the truncated colimit. The leg equation identifies the cohomology map of
the displayed chain map with precisely the continuity comparison. It is an
isomorphism in every degree by h. Thus the chain map is a quasi-isomorphism.
The argument quantifies over all choices of P,L,e,ε and the normalized cocone, so
objectwise quasi-isomorphic replacements give the same derived comparison under
these identifications. Apply this with F equal to derived pushforward, or to derived
module sections, and h the corresponding continuity theorem above. -/
theorem condensedContinuityComparison_representatives
    {A : Type v} [Category.{w} A] [Abelian A] [HasDerivedCategory.{w} A]
    {B : Type u} [Category.{z} B] [Abelian B] [HasDerivedCategory.{z} B]
    {I : Type x} [Category.{y} I] [IsFiltered I]
    [HasColimitsOfShape I B] [HasExactColimitsOfShape I B]
    (D : I ⥤ CochainComplex A ℤ) (a : ℤ)
    [HasColimit (D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A)]
    (F : DerivedCategory A ⥤ DerivedCategory B)
    [∀ q : ℤ, HasColimit (D ⋙ (DerivedCategory.Q ⋙ F ⋙
      DerivedCategory.homologyFunctor B q))]
    (h : ∀ q : ℤ, IsIso (condensedContinuityComparison D a
      (DerivedCategory.Q ⋙ F ⋙ DerivedCategory.homologyFunctor B q)))
    (P : I ⥤ CochainComplex B ℤ) [HasColimit P] (L : CochainComplex B ℤ)
    (e : D ⋙ DerivedCategory.Q ⋙ F ≅ P ⋙ DerivedCategory.Q)
    (ε : F.obj (DerivedCategory.Q.obj (condensedContinuityCocone D a).pt) ≅
      DerivedCategory.Q.obj L)
    (ι : P ⟶ (Functor.const I).obj L)
    (hι : ∀ i : I, e.hom.app i ≫ DerivedCategory.Q.map (ι.app i) =
      F.map (DerivedCategory.Q.map ((condensedContinuityCocone D a).ι.app i)) ≫ ε.hom) :
    QuasiIso (colimit.desc P (Cocone.mk L ι)) := by
  rw [quasiIso_iff]
  intro q
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact condensedContinuityComparison_representatives_homology D a F h P L e ε ι hι q

end AlgebraicGeometry.ProEtale
