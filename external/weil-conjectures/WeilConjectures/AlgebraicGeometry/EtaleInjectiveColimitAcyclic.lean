/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.EtaleCechVanishingCriterion
import WeilConjectures.AlgebraicGeometry.EtaleSectionsFilteredColimit
import WeilConjectures.CategoryTheory.InjectiveSheafCechAcyclic
import WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence

/-!
# Acyclicity of filtered colimits of injective etale sheaves

Source: Stacks Project, Tag 0739, proof, last paragraph, and Tag 03Q5.
(blueprint: lem-weil-pbc-etale-injective-colimit-acyclic).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private instance overFiniteProducts {X : Scheme.{u}} (U : X.Etale) : HasFiniteProducts (Over U) :=
  Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

-- The finite Čech argument below adapts FiniteEtaleCechFilteredColimit to
-- coefficient-size indexing. All helper proofs are complete.
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem shortComplexHomologyColimit (I : Type (u + 1)) [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I (ShortComplex.homologyFunctor AddCommGrpCat.{u + 1}) := by
  let L := colim (J := I) (C := AddCommGrpCat.{u + 1})
  have : L.PreservesHomology := inferInstance
  refine ⟨fun {D} ↦ ?_⟩
  let S := (ShortComplex.functorEquivalence I AddCommGrpCat.{u + 1}).inverse.obj D
  let c : Cocone D :=
    { pt := S.map L
      ι :=
        { app := fun i ↦ S.mapNatTrans (colim.ι i)
          naturality := by
            intro i j f
            apply ShortComplex.Hom.ext
            · change S.X₁.map f ≫ colimit.ι S.X₁ j = colimit.ι S.X₁ i
              exact colimit.w S.X₁ f
            · change S.X₂.map f ≫ colimit.ι S.X₂ j = colimit.ι S.X₂ i
              exact colimit.w S.X₂ f
            · change S.X₃.map f ≫ colimit.ι S.X₃ j = colimit.ι S.X₃ i
              exact colimit.w S.X₃ f } }
  have hc : IsColimit c := ShortComplex.isColimitOfIsColimitπ c
    (colimit.isColimit _) (colimit.isColimit _) (colimit.isColimit _)
  apply preservesColimit_of_preserves_colimit_cocone hc
  let e : D ⋙ ShortComplex.homologyFunctor _ ≅ S.homology :=
    NatIso.ofComponents (fun i ↦ S.mapHomologyIso ((CategoryTheory.evaluation _ _).obj i)) (by
      intro i j f
      change ShortComplex.homologyMap
        (S.mapNatTrans ((CategoryTheory.evaluation _ _).map f)) ≫ _ = _
      rw [ShortComplex.homologyMap_mapNatTrans]
      simp)
  have h : IsColimit ((Cocone.precompose e.hom).obj (colimit.cocone S.homology)) :=
    (IsColimit.precomposeInvEquiv e.symm _).symm (colimit.isColimit _)
  apply IsColimit.ofIsoColimit h
  refine Cocone.ext (S.mapHomologyIso L).symm ?_
  intro i
  change e.hom.app i ≫ colimit.ι S.homology i ≫ (S.mapHomologyIso L).inv =
    ShortComplex.homologyMap (S.mapNatTrans (colim.ι i))
  rw [ShortComplex.homologyMap_mapNatTrans]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem complexHomologyColimit (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
    (h : PreservesColimitsOfShape I (ShortComplex.homologyFunctor AddCommGrpCat.{u + 1}))
    (p : ℕ) :
    PreservesColimitsOfShape I
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℕ) p) := by
  let H := HomologicalComplex.shortComplexFunctor AddCommGrpCat.{u + 1}
    (ComplexShape.up ℕ) p
  have : PreservesColimitsOfShape I H :=
    ⟨fun {D} ↦ ⟨fun {c} hc ↦ ⟨ShortComplex.isColimitOfIsColimitπ (H.mapCocone c)
      (isColimitOfPreserves
        (HomologicalComplex.eval _ (ComplexShape.up ℕ) ((ComplexShape.up ℕ).prev p)) hc)
      (isColimitOfPreserves (HomologicalComplex.eval _ (ComplexShape.up ℕ) p) hc)
      (isColimitOfPreserves
        (HomologicalComplex.eval _ (ComplexShape.up ℕ) ((ComplexShape.up ℕ).next p)) hc)⟩⟩⟩
  have := h
  change PreservesColimitsOfShape I (H ⋙ ShortComplex.homologyFunctor _)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem finiteEtaleCechComplexColimit (X : Scheme.{u}) (U : X.Etale)
    (K : Type (u + 1)) [Finite K]
    (V : K → X.Etale) (f : ∀ k : K, V k ⟶ U)
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
    (hsections : ∀ (q : ℕ) (a : Fin (q + 1) → K),
      PreservesColimitsOfShape I
        ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (Opposite.op (piObj (fun j : Fin (q + 1) ↦ Over.mk (f (a j)))).left))) :
    PreservesColimitsOfShape I
      (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (Functor.whiskeringLeft (Over U)ᵒᵖ X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
          (Over.forget U).op ⋙
        cechComplexFunctor (fun k : K ↦ Over.mk (f k))) := by
  let C := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (Functor.whiskeringLeft (Over U)ᵒᵖ X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
      (Over.forget U).op ⋙
    cechComplexFunctor (fun k : K ↦ Over.mk (f k))
  apply HomologicalComplex.preservesColimitsOfShape_of_eval C
  intro q
  let A := Fin (q + 1) → K
  let G : Discrete A ⥤ X.Etaleᵒᵖ := Discrete.functor fun a ↦
    Opposite.op (piObj (fun j : Fin (q + 1) ↦ Over.mk (f (a j)))).left
  let E := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (Functor.whiskeringLeft (Discrete A) X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj G
  have : PreservesColimitsOfShape I E :=
    preservesColimitsOfShape_of_evaluation E I (fun a ↦ by
      exact hsections q a.as)
  have : HasFiniteBiproducts AddCommGrpCat.{u + 1} := Abelian.hasFiniteBiproducts
  have : PreservesColimitsOfShape I
      (lim (J := Discrete A) (C := AddCommGrpCat.{u + 1})) :=
    preservesColimitsOfShape_of_natIso (HasBiproductsOfShape.colimIsoLim (J := A))
  let e : C ⋙ HomologicalComplex.eval _ (ComplexShape.up ℕ) q ≅ E ⋙ lim :=
    NatIso.ofComponents (fun F ↦ Pi.isoLimit (E.obj F)) (by
      intro F F' φ
      apply limit.hom_ext
      intro a
      simp only [Functor.comp_obj, HomologicalComplex.eval_obj, lim_obj, Functor.comp_map,
        HomologicalComplex.eval_map, Category.assoc, lim_map, limMap_π]
      change (CategoryTheory.Limits.Pi.map (fun a : A ↦ φ.hom.app (G.obj ⟨a⟩))) ≫ _ = _
      simp [G, E, Pi.isoLimit])
  exact preservesColimitsOfShape_of_natIso e.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- If sections on every member of a finite Čech nerve preserve filtered colimits,
then its Čech cohomology functors preserve coefficient-size colimits in every degree.
Source: Stacks Project, Tag 0739, proof of `lemma-colim-works-over-collection`,
the finite-cover Čech step.
(blueprint: lem-weil-pbc-etale-injective-colimit-acyclic).

Proof:
1. In degree `q`, the Čech complex is the product of evaluation at the objects
   `piObj (fun j : Fin (q + 1) ↦ Over.mk (f (a j)))`, indexed by
   `a : Fin (q + 1) → K`. This index type is finite, including when `K` is empty.
2. The hypothesis identifies each factor of the image cocone with a colimit.
   Filtered colimits in abelian groups commute with finite products (finite products
   are finite biproducts). Thus the image cocone is a colimit in every degree.
   The component comparison maps commute with each restriction along a face map,
   by naturality of the original cocone; hence they commute with the alternating
   sums defining the differential. Degreewise colimits are colimits of complexes.
3. Filtered colimits of abelian groups are exact. Applied to the kernels and images
   of the differentials this identifies the homology of the colimit complex with
   the colimit of the homology groups. Composing with step 2 gives preservation
   by the displayed Čech cohomology functor, with its original cocone legs. -/
private theorem coefficientFiniteEtaleCechHomology
    (X : Scheme.{u}) (U : X.Etale) (K : Type (u + 1)) [Finite K]
    (V : K → X.Etale) (f : ∀ k : K, V k ⟶ U)
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
    (hsections : ∀ (q : ℕ) (a : Fin (q + 1) → K),
      PreservesColimitsOfShape I
        ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (Opposite.op (piObj (fun j : Fin (q + 1) ↦ Over.mk (f (a j)))).left)))
    (p : ℕ) :
    PreservesColimitsOfShape I
      (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (Functor.whiskeringLeft (Over U)ᵒᵖ X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
          (Over.forget U).op ⋙
        cechComplexFunctor (fun k : K ↦ Over.mk (f k)) ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℕ) p) := by
  let C := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (Functor.whiskeringLeft (Over U)ᵒᵖ X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
      (Over.forget U).op ⋙ cechComplexFunctor (fun k : K ↦ Over.mk (f k))
  have : PreservesColimitsOfShape I C :=
    finiteEtaleCechComplexColimit X U K V f I hsections
  have := complexHomologyColimit I (shortComplexHomologyColimit I) p
  have h : PreservesColimitsOfShape I
      (C ⋙ HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) p) := inferInstance
  simpa only [C, Functor.assoc] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Transfer the module-valued sections theorem through the equivalence between abelian
sheaves and sheaves of modules over lifted integers. Both equivalence functors preserve
colimits, so the original evaluation cocone is a colimit. Source: Stacks 0738 (4),
0739, via `etale_sections_filtered_colimit`. -/
private theorem abelianSectionsColimit (Y : Scheme.{u}) (V : Y.Etale)
    [CompactSpace V.left] [QuasiSeparatedSpace V.left]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
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

/-- A filtered colimit of injective etale abelian sheaves is acyclic for global
sections on a quasi-compact quasi-separated scheme.
Source: Stacks Project, Tag 0739, proof, last paragraph, applied to the qcqs
etale basis as in Tag 03Q5.
(blueprint: lem-weil-pbc-etale-injective-colimit-acyclic)

Proof: Let B consist of the qcqs objects in the small etale site. Every covering
of a B-object admits a finite affine etale refinement. Finite fibre products
of objects in these coverings remain qcqs, by base change and composition of
qcqs morphisms. Sections of a filtered colimit commute with evaluation on B:
use finite local representatives and a common upper stage for their finitely
many matching equalities. Apply this also on every covering fibre product.
Thus on a finite B-cover the Cech complex of the colimit is the colimit of
the Cech complexes of the injectives: its products are finite and commute with
filtered colimits. The latter complexes have zero positive cohomology by
injective Cech acyclicity. Exactness of filtered colimits of abelian groups
therefore gives zero positive Cech cohomology for the colimit. The Cech
vanishing criterion on B gives zero positive right derived evaluation on
every B-object. The terminal etale object X belongs to B, and evaluation
there is naturally global sections. Transporting right derived evaluation
along this natural isomorphism yields the stated vanishing. No torsion
hypothesis or bound on the index below the coefficient universe is used;
all covers in this calculation are finite. For the zero diagram and for
empty X the groups vanish as well. -/
theorem isZero_rightDerived_globalSections_colimit_of_injective_coefficientSize
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    {J : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (hinjective : ∀ i, Injective (J.obj i)) {c : Cocone J} (hc : IsColimit c)
    (q : ℕ) (hq : 0 < q) :
    IsZero (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived q).obj
      c.pt) := by
  classical
  let (U : X.Etale) : HasFiniteProducts (Over U) :=
    Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks
  let B : Set X.Etale := {U | CompactSpace U.left ∧ QuasiSeparatedSpace U.left}
  let Cov (U : X.Etale) (K : Type (u + 1)) (V : K → X.Etale)
      (f : ∀ k : K, V k ⟶ U) : Prop :=
    Finite K ∧ U ∈ B ∧ (∀ k, V k ∈ B) ∧
      Sieve.ofArrows V f ∈ X.smallEtaleTopology U
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
  have hcofinal (U : X.Etale) (hU : U ∈ B) (K : Type (u + 1))
      (V : K → X.Etale) (f : ∀ k : K, V k ⟶ U)
      (hf : Sieve.ofArrows V f ∈ X.smallEtaleTopology U) :
      ∃ (L : Type (u + 1)) (W : L → X.Etale) (g : ∀ l : L, W l ⟶ U),
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
        ((Over.forget U).op ⋙ c.pt.obj)).homology p) := by
    let := h.1
    have hs (q : ℕ) (a : Fin (q + 1) → K) :
        PreservesColimitsOfShape I
          ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
            (Opposite.op (piObj (fun j : Fin (q + 1) ↦ Over.mk (f (a j)))).left)) := by
      obtain ⟨hcomp, hqs⟩ := (hB U K V f h).2.2 q a
      let := hcomp
      let := hqs
      exact ⟨fun {G} ↦ ⟨fun {d} hd ↦ abelianSectionsColimit X _ hd⟩⟩
    let H := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (Functor.whiskeringLeft (Over U)ᵒᵖ X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj
        (Over.forget U).op ⋙
      cechComplexFunctor (fun k : K ↦ Over.mk (f k)) ⋙
      HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℕ) p
    have : PreservesColimitsOfShape I H :=
      coefficientFiniteEtaleCechHomology X U K V f I hs p
    have hzero : IsZero (J ⋙ H) := Functor.isZero _ (fun i ↦ by
      let := hinjective i
      exact injective_sheaf_cech_acyclic X (J.obj i) U K V f (hcover U K V f h) p hp)
    exact (isColimitOfPreserves H hc).isZero_pt hzero
  let T : X.Etale := Etale.mk (𝟙 X)
  have hT : T ∈ B := ⟨‹CompactSpace X›, ‹QuasiSeparatedSpace X›⟩
  have hz := isZero_rightDerived_etale_of_cech_vanishing X B Cov c.pt
    hcover hB hcofinal hcech T hT q hq
  have : ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (Opposite.op T)).Additive :=
    inferInstanceAs ((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (CategoryTheory.evaluation _ _).obj (Opposite.op T)).Additive)
  have hterminal : IsTerminal T := MorphismProperty.Over.mkIdTerminal @Etale X
  let e : Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1} ≅
      (sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (Opposite.op T) :=
    Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1} hterminal
  let d : (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived q ≅
      ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (Opposite.op T)).rightDerived q :=
    { hom := NatTrans.rightDerived e.hom q
      inv := NatTrans.rightDerived e.inv q
      hom_inv_id := by rw [← NatTrans.rightDerived_comp, e.hom_inv_id]; simp
      inv_hom_id := by rw [← NatTrans.rightDerived_comp, e.inv_hom_id]; simp }
  exact hz.of_iso (d.app c.pt)


end AlgebraicGeometry.Scheme
