/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.AlgebraicGeometry.EtaleLimitFiniteCechComplexColimit
import WeilConjectures.AlgebraicGeometry.EtaleCechVanishingCriterion
import WeilConjectures.CategoryTheory.InjectiveSheafCechAcyclic
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.CategoryTheory.Sites.LocalSite
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Descent
public import Mathlib.Algebra.Category.Grp.Zero

/-! # Etale replacement: construction and vanishing

Source: Stacks Project, Tags 0EXZ, 09YP, 09YN and 09YQ.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- A compatible injective coefficient system has an acyclic pulled-back colimit.
Source: Stacks Project, Tags 09YP and 09YQ, Cech acyclicity argument using 09YN.
(blueprint: lem-weil-pbc-etale-limit-injective-colimit-acyclic).

Proof: The limit and its projection morphisms are qcqs with affine projections.
Restrict to the cofinal finite qcqs etale covers. Descend each finite affine cover,
its maps and its finitely many objects to a common stage using the affine etale site
colimit presentation. Every iterated fibre product in its Cech nerve is qcqs and has
an inverse presentation with affine transitions. Degree-zero section continuity,
including eventual equality, identifies sections of the colimit sheaf on each such
object with the filtered colimit of the stage sections. The canonical units in this
comparison commute with restrictions. Finite products commute with filtered group
colimits, so the entire Cech complex is the filtered colimit of the stage complexes.
The stage coefficient sheaves are injective, hence their positive Cech cohomology
vanishes. Exact filtered group colimits preserve this vanishing. The Cech criterion
on the cofinal finite qcqs covers gives positive object cohomology vanishing. Apply
it to the terminal etale object and degree n+1 to obtain global vanishing.
No higher-degree continuity is used. Empty schemes, the zero system, degree zero
and a singleton index satisfy the same argument.
-/
theorem etale_limit_injective_colimit_acyclic
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f) ≫ φ g)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (hG : ∀ (i j : I) (f : i ⟶ j), G.map f =
      (eG i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫ (eG j).inv)
    (L : Cocone G) (hL : IsColimit L)
    (hinj : ∀ i : I, Injective (F i)) (n : ℕ) :
    Subsingleton (Sheaf.H L.pt (n + 1)) := by
  classical
  have shortComplexHomologyColimit (I : Type u) [SmallCategory I] [IsFiltered I] :
      PreservesColimitsOfShape I (ShortComplex.homologyFunctor AddCommGrpCat.{u + 1}) := by
    let L := colim (J := I) (C := AddCommGrpCat.{u + 1})
    have : HasFilteredColimitsOfSize.{u, u} AddCommGrpCat.{u + 1} :=
      hasFilteredColimitsOfSize_of_univLE.{u, u, u + 1, u + 1}
    have : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
      AB5OfSize_of_univLE.{u, u, u + 1, u + 1, u + 1, u + 2} AddCommGrpCat.{u + 1}
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
  have complexHomologyColimit (I : Type u) [SmallCategory I] [IsFiltered I]
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
  let (U : c.pt.Etale) : HasFiniteProducts (Over U) :=
    Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks
  let (i : Iᵒᵖ) : IsAffineHom (c.π.app i) := isAffineHom_π_app D c hc i
  let : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  let i : I := Classical.choice inferInstance
  let : QuasiSeparatedSpace c.pt := quasiSeparatedSpace_of_quasiSeparated (c.π.app (op i))
  let B : Set c.pt.Etale := {U | CompactSpace U.left ∧ QuasiSeparatedSpace U.left}
  let Cov (U : c.pt.Etale) (K : Type (u + 1)) (V : K → c.pt.Etale)
      (f : ∀ k : K, V k ⟶ U) : Prop :=
    Finite K ∧ U ∈ B ∧ (∀ k, V k ∈ B) ∧
      Sieve.ofArrows V f ∈ c.pt.smallEtaleTopology U
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
    exact Scheme.compactSpace_and_quasiSeparatedSpace_piObj _ (fun j ↦ hV (a j))
  have hcofinal (U : c.pt.Etale) (hU : U ∈ B) (K : Type (u + 1))
      (V : K → c.pt.Etale) (f : ∀ k : K, V k ⟶ U)
      (hf : Sieve.ofArrows V f ∈ c.pt.smallEtaleTopology U) :
      ∃ (M : Type (u + 1)) (W : M → c.pt.Etale) (g : ∀ m : M, W m ⟶ U),
        Cov U M W g ∧ ∀ m : M, ∃ (k : K) (t : W m ⟶ V k), t ≫ f k = g m := by
    let := hU.1
    obtain ⟨m, W, g, hR, hW, hg⟩ := (AlgebraicGeometry.Etale.exists_affine_refinement _) hf
    refine ⟨ULift.{u + 1} (Fin m), fun l ↦ W l.down, fun l ↦ g l.down,
      ⟨inferInstance, hU, ?_, ?_⟩, ?_⟩
    · intro l
      have := hW l.down
      exact ⟨inferInstance, inferInstance⟩
    · apply (Scheme.ofArrows_mem_smallEtaleTopology_iff _).2
      apply Set.eq_univ_of_forall
      intro x
      obtain ⟨l, y, rfl⟩ := Set.mem_iUnion.mp (hg.symm ▸ Set.mem_univ x)
      exact Set.mem_iUnion.mpr ⟨⟨l⟩, y, rfl⟩
    · intro l
      obtain ⟨k, t, ht⟩ := Sieve.ofArrows.exists (hR l.down)
      exact ⟨k, t, ht.symm⟩
  have hcech (U K V f) (h : Cov U K V f) (p : ℕ) (hp : 0 < p) :
      IsZero (((cechComplexFunctor fun k : K ↦ Over.mk (f k)).obj
        ((Over.forget U).op ⋙ L.pt.obj)).homology p) := by
    let := h.1
    let := h.2.1.1
    let := h.2.1.2
    obtain ⟨i₀, A, Uj, Vj, fj, eA, cA, eK, hcov, ⟨hcA⟩⟩ :=
      etale_limit_finite_cech_complex_colimit D c hc F φ hidentity hcomposition
        G eG hG L hL U K V f h.2.2.1 h.2.2.2
    let J := {j : I // i₀ ≤ j}
    let : Nonempty J := ⟨⟨i₀, le_rfl⟩⟩
    let : IsDirected J (· ≤ ·) := ⟨fun j k ↦ by
      obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j.val k.val
      exact ⟨⟨l, j.property.trans hjl⟩, hjl, hkl⟩⟩
    let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℕ) p
    have : PreservesColimitsOfShape J H :=
      complexHomologyColimit J (shortComplexHomologyColimit J) p
    have hzero : IsZero (A ⋙ H) := Functor.isZero _ (fun j ↦ by
      let := hinj j.val
      have hz := injective_sheaf_cech_acyclic (D.obj (op j.val)) (F j.val)
        (Uj j) K (Vj j) (fj j) (hcov j) p hp
      exact hz.of_iso (H.mapIso (eA j)))
    exact ((isColimitOfPreserves H hcA).isZero_pt hzero).of_iso (H.mapIso eK).symm
  let T : c.pt.Etale := Scheme.Etale.mk (𝟙 c.pt)
  have hT : T ∈ B := ⟨‹CompactSpace c.pt›, ‹QuasiSeparatedSpace c.pt›⟩
  have hz := Scheme.isZero_rightDerived_etale_of_cech_vanishing c.pt B Cov L.pt
    hcover hB hcofinal hcech T hT (n + 1) (Nat.zero_lt_succ n)
  let Γ := Sheaf.Γ c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}
  let hterminal : IsTerminal T := MorphismProperty.Over.mkIdTerminal @Etale c.pt
  let e := Sheaf.ΓNatIsoSheafSections c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}
    hterminal
  have : ((sheafSections c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op T)).Additive := Functor.additive_of_iso e
  let d : Γ.rightDerived (n + 1) ≅
      ((sheafSections c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (op T)).rightDerived (n + 1) :=
    ⟨e.hom.rightDerived (n + 1), e.inv.rightDerived (n + 1), by
      rw [← NatTrans.rightDerived_comp, e.hom_inv_id, NatTrans.rightDerived_id], by
      rw [← NatTrans.rightDerived_comp, e.inv_hom_id, NatTrans.rightDerived_id]⟩
  have hΓ : IsZero ((Γ.rightDerived (n + 1)).obj L.pt) := hz.of_iso (d.app L.pt)
  let eSingle := Γ.homologyRightDerivedFunctorObjSingleFunctorIso L.pt (n + 1)
  obtain ⟨eH⟩ := Scheme.nonempty_sheafH_extDerivedIso c.pt (n + 1)
  have hH : IsZero ((Sheaf.functorH c.pt.smallEtaleTopology (n + 1)).obj L.pt) :=
    (hΓ.of_iso eSingle).of_iso (eH.app L.pt)
  exact AddCommGrpCat.subsingleton_of_isZero hH

end AlgebraicGeometry.Etale
