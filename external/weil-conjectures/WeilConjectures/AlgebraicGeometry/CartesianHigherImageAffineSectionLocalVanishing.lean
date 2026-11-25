/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CartesianHigherImageTransitions
import WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit
import all WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
import WeilConjectures.AlgebraicGeometry.CartesianHigherImageFiniteRawClassVanishing

/-! # Local affine-cover glue for cartesian higher-image sections

Source: Stacks Project, Tag 0EYM, second proof, affine section reduction.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

noncomputable local instance cartesianHigherImageAffineSectionHasShift (T : Scheme.{u}) :
    HasShift (DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) ℤ :=
  inferInstance

noncomputable local instance cartesianHigherImageAffineSectionHasZeroMorphisms (T : Scheme.{u}) :
    HasZeroMorphisms (DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) :=
  inferInstance

private noncomputable def rawSectionsComparison
    (S : Scheme.{u}) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (abelianComparisonFree S ⋙ DerivedCategory.Plus.singleFunctor _ 0).op ⋙
      preadditiveYoneda.obj (K⟦q⟧) ⟶
        ((DerivedCategory.Plus.homologyFunctor _ q).obj K).obj :=
  (AbelianComparison.derivedHomToHomology (K⟦q⟧) ≫
    AbelianComparison.freeSheafSections _) ≫
      (((DerivedCategory.Plus.homologyFunctor _ 0).shiftIso q 0 q (add_zero q)).hom.app K).hom

private theorem rawSectionsComparison_locally_bijective
    (S : Scheme.{u}) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    Presheaf.IsLocallyInjective S.smallEtaleTopology (rawSectionsComparison S q K) ∧
      Presheaf.IsLocallySurjective S.smallEtaleTopology (rawSectionsComparison S q K) := by
  have : PreservesLimitsOfSize.{u, u + 1} (forget AddCommGrpCat.{u + 1}) :=
    preservesLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  obtain ⟨_, _⟩ := AbelianComparison.isLocallyBijective_derivedHomToHomology
    (J := S.smallEtaleTopology) (K⟦q⟧)
  dsimp only [rawSectionsComparison]
  constructor <;> infer_instance

private theorem rawSectionsComparison_naturality
    (S : Scheme.{u}) (q : ℤ)
    {K L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})}
    (m : K ⟶ L) (U : S.Etale)
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((abelianComparisonFree S).obj U) ⟶ K⟦q⟧) :
    ((DerivedCategory.Plus.homologyFunctor _ q).map m).hom.app (Opposite.op U)
      ((rawSectionsComparison S q K).app (Opposite.op U) z) =
      (rawSectionsComparison S q L).app (Opposite.op U)
        (z ≫ (shiftFunctor _ q).map m) := by
  let H₀ := DerivedCategory.Plus.homologyFunctor
    (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) 0
  let Hq := DerivedCategory.Plus.homologyFunctor
    (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) q
  let σ := H₀.shiftIso q 0 q (add_zero q)
  have hn := σ.hom.naturality m
  change H₀.map ((shiftFunctor _ q).map m) ≫ σ.hom.app L =
    σ.hom.app K ≫ Hq.map m at hn
  have he :
      ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _ ≫
        H₀.map z ≫ σ.hom.app K) ≫ Hq.map m =
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _ ≫
        H₀.map (z ≫ (shiftFunctor _ q).map m) ≫ σ.hom.app L := by
    rw [Category.assoc, Category.assoc, ← hn, ← H₀.map_comp_assoc]
  exact congrArg (fun g ↦ (g.hom.app (Opposite.op U))
    (((toSheafify S.smallEtaleTopology
      (uliftYoneda.{u + 1}.obj U ⋙ AddCommGrpCat.free)).app (Opposite.op U))
        (FreeAbelianGroup.of (ULift.up (𝟙 U))))) he

private theorem exists_rawSectionsComparison_local_zero_sieve
    (S : Scheme.{u}) (q : ℤ)
    {K L : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})}
    (m : K ⟶ L) (U : S.Etale)
    (x : ((DerivedCategory.Plus.homologyFunctor _ q).obj K).obj.obj (Opposite.op U))
    (hx : ((DerivedCategory.Plus.homologyFunctor _ q).map m).hom.app
      (Opposite.op U) x = 0) :
    ∃ R : Sieve U, R ∈ S.smallEtaleTopology U ∧
      ∀ (V : S.Etale) (r : V ⟶ U), R r →
        ∃ z : (DerivedCategory.Plus.singleFunctor _ 0).obj
          ((abelianComparisonFree S).obj V) ⟶ K⟦q⟧,
          (rawSectionsComparison S q K).app (Opposite.op V) z =
              ((DerivedCategory.Plus.homologyFunctor _ q).obj K).obj.map r.op x ∧
            z ≫ (shiftFunctor _ q).map m = 0 := by
  let P := (abelianComparisonFree S ⋙ DerivedCategory.Plus.singleFunctor _ 0).op ⋙
    preadditiveYoneda.obj (K⟦q⟧)
  let Q := (abelianComparisonFree S ⋙ DerivedCategory.Plus.singleFunctor _ 0).op ⋙
    preadditiveYoneda.obj (L⟦q⟧)
  let τ := rawSectionsComparison S q K
  let υ := rawSectionsComparison S q L
  obtain ⟨_, hτ⟩ := rawSectionsComparison_locally_bijective S q K
  obtain ⟨hυ, _⟩ := rawSectionsComparison_locally_bijective S q L
  let R : Sieve U :=
    { arrows := fun V r ↦ ∃ z : P.obj (Opposite.op V),
        τ.app (Opposite.op V) z =
          ((DerivedCategory.Plus.homologyFunctor _ q).obj K).obj.map r.op x ∧
          z ≫ (shiftFunctor _ q).map m = 0
      downward_closed := by
        intro V W r hr g
        obtain ⟨z, hz, hm⟩ := hr
        refine ⟨P.map g.op z, ?_, ?_⟩
        · rw [NatTrans.naturality_apply, hz, op_comp,
            ((DerivedCategory.Plus.homologyFunctor _ q).obj K).obj.map_comp]
          rfl
        · change ((DerivedCategory.Plus.singleFunctor _ 0).map
            ((abelianComparisonFree S).map g) ≫ z) ≫ (shiftFunctor _ q).map m = 0
          rw [Category.assoc, hm, Limits.comp_zero] }
  refine ⟨R, ?_, fun V r hr ↦ hr⟩
  apply S.smallEtaleTopology.transitive
    (Presheaf.imageSieve_mem S.smallEtaleTopology τ x) R
  intro V r hr
  obtain ⟨z, hz⟩ := hr
  have hy : υ.app (Opposite.op V) (z ≫ (shiftFunctor _ q).map m) =
      υ.app (Opposite.op V) 0 := by
    rw [map_zero, ← rawSectionsComparison_naturality, hz, NatTrans.naturality_apply,
      hx, map_zero]
  apply S.smallEtaleTopology.superset_covering _
    (Presheaf.equalizerSieve_mem S.smallEtaleTopology υ _ _ hy)
  intro W g hg
  refine ⟨P.map g.op z, ?_, ?_⟩
  · rw [NatTrans.naturality_apply, hz, op_comp,
      ((DerivedCategory.Plus.homologyFunctor _ q).obj K).obj.map_comp]
    rfl
  · change Q.map g.op (z ≫ (shiftFunctor _ q).map m) = Q.map g.op 0 at hg
    change ((DerivedCategory.Plus.singleFunctor _ 0).map
      ((abelianComparisonFree S).map g) ≫ z) ≫ (shiftFunctor _ q).map m = 0
    change (DerivedCategory.Plus.singleFunctor _ 0).map
      ((abelianComparisonFree S).map g) ≫ (z ≫ (shiftFunctor _ q).map m) =
      (DerivedCategory.Plus.singleFunctor _ 0).map
        ((abelianComparisonFree S).map g) ≫ 0 at hg
    simpa only [Category.assoc, Limits.comp_zero] using hg

/-- A transitioned cartesian higher-image section vanishes when it vanishes on a finite
etale cover. This is the sheaf-separatedness part of the affine-section argument.
Source: Stacks Project, Tag 0EYM, second proof, injectivity on affine etale objects.
(blueprint: lem-sc-cartesian-higher-image-affine-section-local-vanishing)
-/
theorem cartesianHigherImage_section_eq_zero_of_finite_cover
    {k : Type u} [Field k]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over (Spec (.of k)))
    [∀ i, QuasiCompact (D.obj i).hom] [∀ i, QuasiSeparated (D.obj i).hom]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (c : Cone D)
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (U : c.pt.left.Etale) (i j : I) (a : j ⟶ i)
    (x : (cartesianHigherImageStage D c f F q i).obj.obj (Opposite.op U))
    (J : Type u) [Finite J] (V : J → c.pt.left.Etale) (r : ∀ t, V t ⟶ U)
    (hcover : Sieve.ofArrows V r ∈ c.pt.left.smallEtaleTopology U)
    (hzero : ∀ t, (cartesianHigherImageTransition D c f F q a).hom.app
      (Opposite.op (V t))
      ((cartesianHigherImageStage D c f F q i).obj.map (r t).op x) = 0) :
    (cartesianHigherImageTransition D c f F q a).hom.app
      (Opposite.op U) x = 0 := by
  let G := cartesianHigherImageStage D c f F q j
  have : PreservesLimitsOfSize.{u, u + 1} (forget AddCommGrpCat.{u + 1}) :=
    preservesLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  let G' := (sheafCompose c.pt.left.smallEtaleTopology
    (forget AddCommGrpCat.{u + 1})).obj G
  apply (((isSheaf_iff_isSheaf_of_type _ _).1 G'.property).isSeparated _ hcover).ext
  intro W g hg
  obtain ⟨t, l, rfl⟩ := (Sieve.mem_ofArrows_iff V r g).mp hg
  change G.obj.map (l ≫ r t).op
    ((cartesianHigherImageTransition D c f F q a).hom.app (Opposite.op U) x) =
      G.obj.map (l ≫ r t).op 0
  rw [map_zero, op_comp, G.obj.map_comp]
  change G.obj.map l.op (G.obj.map (r t).op
    ((cartesianHigherImageTransition D c f F q a).hom.app (Opposite.op U) x)) = 0
  rw [← NatTrans.naturality_apply, hzero t, map_zero]


/-- Local sieve form of affine-section eventual vanishing.
Source: Stacks Project, Tag 0EYM, second proof, affine section reduction.
Proof: local surjectivity of the derived-Hom-to-homology comparison lifts the
section, and local injectivity at the target makes its derived image zero after
refinement. Extract a finite affine etale cover. Apply eventual vanishing of the
finite family of raw derived classes at one common stage. Naturality of homology
and its shift comparison then gives zero for the transitioned sections. Close the
finite covering family under precomposition to obtain the required sieve.
(blueprint: lem-sc-cartesian-higher-image-affine-section-local-vanishing)
-/
theorem cartesianHigherImage_affine_section_local_zero_sieve
    {k : Type u} [Field k]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over (Spec (.of k)))
    [∀ i, QuasiCompact (D.obj i).hom] [∀ i, QuasiSeparated (D.obj i).hom]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (c : Cone D) (hc : IsLimit ((Over.forget _).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (U : c.pt.left.Etale) [IsAffine U.left] (i : I)
    (x : (cartesianHigherImageStage D c f F q i).obj.obj (Opposite.op U))
    (hx : (cartesianHigherImageLeg D c f F q i).hom.app (Opposite.op U) x = 0) :
    ∃ (j : I) (a : j ⟶ i) (S : Sieve U),
      S ∈ c.pt.left.smallEtaleTopology U ∧
      ∀ (V : c.pt.left.Etale) (r : V ⟶ U), S r →
        (cartesianHigherImageTransition D c f F q a).hom.app
          (Opposite.op V) ((cartesianHigherImageStage D c f F q i).obj.map r.op x) = 0 := by
  classical
  let Kᵢ := (D+(((c.π.app i).left)^*[AddCommGrpCat.{u + 1}])).obj
    (cartesianDerivedImage f (D.obj i).hom
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F))
  let K := cartesianDerivedImage f c.pt.hom
    ((DerivedCategory.Plus.singleFunctor _ 0).obj F)
  let m := cartesianDerivedImageMap f (D.obj i).hom c.pt.hom (c.π.app i).left
    (Over.w (c.π.app i)).symm ((DerivedCategory.Plus.singleFunctor _ 0).obj F)
  obtain ⟨R, hR, hlocal⟩ :=
    exists_rawSectionsComparison_local_zero_sieve c.pt.left (q : ℤ) m U x hx
  obtain ⟨n, V, r, hr, hV, hcover⟩ :=
    (AlgebraicGeometry.Etale.exists_affine_refinement _) hR
  let J := ULift.{u} (Fin n)
  let _ : Fintype J := Fintype.ofFinite J
  let V' : J → c.pt.left.Etale := fun t ↦ V t.down
  let r' : ∀ t, V' t ⟶ U := fun t ↦ r t.down
  let (t : J) : IsAffine (V' t).left := hV t.down
  have hraw : ∀ t : J, ∃ z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((abelianComparisonFree c.pt.left).obj (V' t)) ⟶ Kᵢ⟦(q : ℤ)⟧,
      (rawSectionsComparison c.pt.left (q : ℤ) Kᵢ).app (Opposite.op (V' t)) z =
          (cartesianHigherImageStage D c f F q i).obj.map (r' t).op x ∧
        z ≫ (shiftFunctor _ (q : ℤ)).map m = 0 := by
    intro t
    exact hlocal (V' t) (r' t) (hr t.down)
  choose z hz hzm using hraw
  obtain ⟨j, a, hzero⟩ :=
    exists_cartesianHigherImage_finite_raw_classes_eq_zero D c hc f F q i J V' z hzm
  let T := (upperStarCompDerivedPlus AddCommGrpCat.{u + 1}
    (c.π.app j).left (D.map a).left (c.π.app i).left
    (congrArg (fun b ↦ b.left) (c.w a)).symm).hom.app _ ≫
      (D+(((c.π.app j).left)^*[AddCommGrpCat.{u + 1}])).map
        (cartesianDerivedImageMap f (D.obj i).hom (D.obj j).hom
          (D.map a).left (Over.w (D.map a)).symm
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))
  have hsection : ∀ t : J,
      (cartesianHigherImageTransition D c f F q a).hom.app (Opposite.op (V' t))
        ((cartesianHigherImageStage D c f F q i).obj.map (r' t).op x) = 0 := by
    intro t
    rw [← hz t]
    change ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map T).hom.app
      (Opposite.op (V' t))
        ((rawSectionsComparison c.pt.left (q : ℤ) Kᵢ).app (Opposite.op (V' t)) (z t)) = 0
    exact (rawSectionsComparison_naturality c.pt.left (q : ℤ) T (V' t) (z t)).trans
      (by rw [hzero t, map_zero])
  refine ⟨j, a, Sieve.ofArrows V' r', ?_, ?_⟩
  · apply (Scheme.ofArrows_mem_smallEtaleTopology_iff r').2
    rw [Set.eq_univ_iff_forall]
    intro y
    obtain ⟨t, v, hv⟩ := Set.mem_iUnion.mp (hcover ▸ Set.mem_univ y)
    exact Set.mem_iUnion.mpr ⟨ULift.up t, v, hv⟩
  · intro W g hg
    obtain ⟨t, l, rfl⟩ := (Sieve.mem_ofArrows_iff V' r' g).mp hg
    rw [op_comp, (cartesianHigherImageStage D c f F q i).obj.map_comp]
    change (cartesianHigherImageTransition D c f F q a).hom.app (Opposite.op W)
      ((cartesianHigherImageStage D c f F q i).obj.map l.op
        ((cartesianHigherImageStage D c f F q i).obj.map (r' t).op x)) = 0
    rw [NatTrans.naturality_apply, hsection t, map_zero]


/-- Extract a finite cover from the covering sieve of eventual local vanishing.
Source: Stacks Project, Tag 0EYM, second proof, part (2).
The affine test object is quasi-compact, so the sieve has a finite affine etale
refinement; reindex that family in the base universe and retain its vanishing.
(blueprint: lem-sc-cartesian-higher-image-affine-section-local-vanishing). -/
theorem exists_cartesianHigherImage_affine_section_local_zero
    {k : Type u} [Field k]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over (Spec (.of k)))
    [∀ i, QuasiCompact (D.obj i).hom] [∀ i, QuasiSeparated (D.obj i).hom]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (c : Cone D) (hc : IsLimit ((Over.forget _).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (U : c.pt.left.Etale) [IsAffine U.left] (i : I)
    (x : (cartesianHigherImageStage D c f F q i).obj.obj (Opposite.op U))
    (hx : (cartesianHigherImageLeg D c f F q i).hom.app (Opposite.op U) x = 0) :
    ∃ (j : I) (a : j ⟶ i) (J : Type u) (_ : Fintype J)
      (V : J → c.pt.left.Etale) (r : ∀ t, V t ⟶ U),
      Sieve.ofArrows V r ∈ c.pt.left.smallEtaleTopology U ∧
      ∀ t, (cartesianHigherImageTransition D c f F q a).hom.app
        (Opposite.op (V t))
        ((cartesianHigherImageStage D c f F q i).obj.map (r t).op x) = 0 := by
  classical
  obtain ⟨j, a, S, hS, hzero⟩ :=
    cartesianHigherImage_affine_section_local_zero_sieve D c hc f F q U i x hx
  obtain ⟨n, V, r, hr, hV, hcover⟩ :=
    (AlgebraicGeometry.Etale.exists_affine_refinement _) hS
  let J := ULift.{u} (Fin n)
  let _ : Fintype J := Fintype.ofFinite J
  let V' : J → c.pt.left.Etale := fun t => V t.down
  let r' : ∀ t, V' t ⟶ U := fun t => r t.down
  refine ⟨j, a, J, inferInstance, V', r', ?_, ?_⟩
  · apply (Scheme.ofArrows_mem_smallEtaleTopology_iff r').2
    rw [Set.eq_univ_iff_forall]
    intro z
    obtain ⟨a₀, y, hy⟩ := Set.mem_iUnion.mp (hcover ▸ Set.mem_univ z)
    refine Set.mem_iUnion.mpr ⟨ULift.up a₀, ?_⟩
    exact ⟨y, hy⟩
  · intro t
    exact hzero (V' t) (r' t) (hr t.down)

end AlgebraicGeometry.Etale
