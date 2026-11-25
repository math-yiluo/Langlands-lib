/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleComplexCohomologyPresentationData
public import WeilConjectures.AlgebraicGeometry.RawAffineRestrictedCohomology
import WeilConjectures.AlgebraicGeometry.RestrictedOverSingleCoherence

/-! # Geometric complex data for restricted abelian cohomology

Source: Stacks Project, Tags 09Z1 and 0EZM.
(blueprint: lem-sbc-restricted-over-abelian-complex-data).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- The abelian coefficient sheaf pulled back from the fixed scheme W. 
(blueprint: lem-sbc-restricted-over-abelian-complex-data)
-/
noncomputable def restrictedOverCoefficient {W : Scheme.{u}}
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (A : Over W) :=
  (upperStar AddCommGrpCat.{u + 1} A.hom).obj F

/-- Integer-degree cohomology on the actual etale fibre product. 
(blueprint: lem-sbc-restricted-over-abelian-complex-data)
-/
noncomputable def restrictedOverCohomology {W S : Scheme.{u}} (k : W ⟶ S)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)
    (A : Over W) (U : S.Etale) : AddCommGrpCat.{u + 1} :=
  (cohomology AddCommGrpCat.{u + 1} (pullback U.hom (A.hom ≫ k)) q).obj
    (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj
      ((upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom (A.hom ≫ k))).obj
        (restrictedOverCoefficient F A))))

/-- The canonical map is derived pullback followed by the coefficient identification.
It is written explicitly and is not selected from an existence theorem. 
(blueprint: lem-sbc-restricted-over-abelian-complex-data)
-/
noncomputable def restrictedOverCohomologyMap {W S : Scheme.{u}} (k : W ⟶ S)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)
    {A B : Over W} (f : A ⟶ B) (U : S.Etale) :
    restrictedOverCohomology k F q B U ⟶ restrictedOverCohomology k F q A U := by
  let w : f.left ≫ (B.hom ≫ k) = A.hom ≫ k := by rw [← Category.assoc, Over.w]
  let a := rawAffineRestrictedMap f.left (B.hom ≫ k) (A.hom ≫ k) w U
  let R := (upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom (B.hom ≫ k))).obj
    (restrictedOverCoefficient F B)
  let φ := (upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
    (Over.w f).symm).inv.app F
  exact rawAffineComplexPullback q a ((CochainComplex.singleFunctor _ 0).obj R) ≫
    (cohomology AddCommGrpCat.{u + 1} (pullback U.hom (A.hom ≫ k)) q).map
      (DerivedCategory.Q.map
        (((upperStar AddCommGrpCat.{u + 1} a).mapCochainComplexSingleFunctor 0).hom.app R ≫
          (CochainComplex.singleFunctor _ 0).map
            (rawAffineRestrictedCoefficient f.left (B.hom ≫ k) (A.hom ≫ k) w
              (restrictedOverCoefficient F B) (restrictedOverCoefficient F A) φ U)))

set_option backward.isDefEq.respectTransparency true in
/-- Geometric complex data for restricted abelian cohomology of fixed coefficients.
Source: Stacks Project, Tag 09Z1, affine-object reduction in lemma-relative-colimit;
Tag 0EZM, lemma-colimit-variant-complexes, before invoking continuity.
(blueprint: lem-sbc-restricted-over-abelian-complex-data).

Proof: Base change D and c to U using the pullbacks U times_S D(i). The universal
property of each pullback defines the transition arrows and cone arrows, proves
functoriality, and identifies the resulting cone as limiting. Affineness survives
base change. The maps to affine U are qcqs by base change, so their sources are
compact and quasi-separated. Restrict the sheaves A.hom^*F to these fibre products
and form their degree-zero single complexes. The coefficient identifications are
upperStarComp inverses, restricted using the two comparisons displayed in
rawAffineRestrictedCoefficient. Unit and associativity coherence give the complex
identity and composition equations. The lower bound is zero. On the limiting
scheme these complexes identify with the pullback of F from W, in degree zero.
Take the constant diagram of that complex and its identity cocone. I opposite
is nonempty and connected, so that cocone is colimiting; the composition comparisons
give eG and its map equation. Set p=q and P=rawAffineComplexPullback q. The stage
cohomology is precisely restrictedOverCohomology; compose the single-complex
identifications with e to give eH. Identify the constant cocone point similarly
and compose with e₀ to obtain the apex isomorphism. The definitions of
restrictedOverCohomologyMap and rawAffineRestrictedCoefficient identify the stage
maps with P followed by cohomology of phi, and the cone maps with P followed by
cohomology of the coefficient leg. The assumed squares give hH and hB.
No derived Hom, scalar comparison, or cohomology continuity is used. For q<0
single-complex cohomology vanishes; the identical construction still applies.
For an empty test object the same pullback and zero sheaf constructions apply. -/
theorem restrictedOverAbelianCocone_complex_data
    {W S : Scheme.{u}} (k : W ⟶ S)
    (F₀ : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D₀ : I ⥤ Over W)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D₀.map f).left]
    [∀ i, QuasiCompact ((D₀.obj i).hom ≫ k)]
    [∀ i, QuasiSeparated ((D₀.obj i).hom ≫ k)]
    (c₀ : Cone D₀) (hc₀ : IsLimit ((Over.forget W).mapCone c₀))
    [QuasiCompact (c₀.pt.hom ≫ k)] [QuasiSeparated (c₀.pt.hom ≫ k)]
    (U : S.Etale) [IsAffine U.left]
    (H : Iᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (B : Cocone H)
    (e : ∀ i : I, H.obj (op i) ≅ restrictedOverCohomology k F₀ q (D₀.obj i) U)
    (e₀ : B.pt ≅ restrictedOverCohomology k F₀ q c₀.pt U)
    (he : ∀ (i j : I) (f : j ⟶ i), H.map f.op ≫ (e j).hom =
      (e i).hom ≫ restrictedOverCohomologyMap k F₀ q (D₀.map f) U)
    (he₀ : ∀ i : I, B.ι.app (op i) ≫ e₀.hom =
      (e i).hom ≫ restrictedOverCohomologyMap k F₀ q (c₀.π.app i) U) :
  EtaleComplexCohomologyPresentationData H B := by
  let D := restrictedOverDiagram k D₀ U
  let c : Cone D := restrictedOverCone k D₀ c₀ U
  let K : ∀ i : I, CochainComplex
      (Sheaf (D.obj i).smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ :=
    fun i ↦ restrictedOverSingle k F₀ (D₀.obj i) U
  let φ : ∀ {i j : I} (f : j ⟶ i),
      ((upperStar AddCommGrpCat.{u + 1} (D.map f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (K i) ⟶ K j :=
    fun {i j : I} (f : j ⟶ i) ↦ (restrictedOverSingleIso k F₀ (D₀.map f) U).hom
  let G : Iᵒᵖ ⥤ CochainComplex
      (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ := restrictedOverSingleG k F₀ D₀ c₀ U
  let eG : ∀ i : I, G.obj (op i) ≅
      ((upperStar AddCommGrpCat.{u + 1} (c.π.app i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (K i) := restrictedOverSingleConeIso k F₀ D₀ c₀ U
  let L : Cocone G := constCocone Iᵒᵖ (restrictedOverSingle k F₀ c₀.pt U)
  obtain ⟨hid, hcomp, hG⟩ := restrictedOverSingle_coherence k F₀ D₀ c₀ U
    D c K @φ G eG rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
  set_option backward.isDefEq.respectTransparency false in
  have hc : IsLimit c := by
    let E := D₀ ⋙ Over.map k
    let cE := (Over.map k).mapCone c₀
    have hcE : IsLimit ((Over.forget S).mapCone cE) := hc₀
    let P := Over.pullback U.hom ⋙ Over.forget U.left
    let eD : E ⋙ P ≅ D :=
      NatIso.ofComponents (fun i ↦ pullbackSymmetry ((D₀.obj i).hom ≫ k) U.hom) (by
        intro i j f
        apply pullback.hom_ext <;>
          simp [E, P, D, restrictedOverDiagram, rawAffineRestrictedMap, Category.assoc])
    have : IsConnected I := IsCofiltered.isConnected I
    have : PreservesLimitsOfShape I P := by dsimp only [P]; infer_instance
    have h := isLimitOfPreserves P (isLimitOfReflects (Over.forget S) hcE)
    apply ((IsLimit.postcomposeHomEquiv eD (P.mapCone cE)).symm h).ofIsoLimit
    refine Cone.ext (pullbackSymmetry (c₀.pt.hom ≫ k) U.hom) ?_
    intro i
    change
      ((Over.pullback U.hom).map ((Over.map k).map (c₀.π.app i))).left ≫
        (pullbackSymmetry ((D₀.obj i).hom ≫ k) U.hom).hom =
      (pullbackSymmetry (c₀.pt.hom ≫ k) U.hom).hom ≫ c.π.app i
    apply pullback.hom_ext <;>
      simp [c, restrictedOverCone, rawAffineRestrictedMap, Category.assoc]
  have hcompact (i : I) : CompactSpace (D.obj i) := by
    dsimp [D, restrictedOverDiagram]
    infer_instance
  have hqs (i : I) : QuasiSeparatedSpace (D.obj i) := by
    have : QuasiSeparatedSpace U.left := quasiSeparatedSpace_of_isAffine U.left
    exact @quasiSeparatedSpace_of_quasiSeparated
      (pullback U.hom ((D₀.obj i).hom ≫ k) : Scheme.{u}) U.left
      (pullback.fst U.hom ((D₀.obj i).hom ≫ k)) ‹QuasiSeparatedSpace U.left› inferInstance
  set_option backward.isDefEq.respectTransparency false in
  have haffine (i j : I) (f : i ⟶ j) : IsAffineHom (D.map f) := by
    dsimp [D, restrictedOverDiagram, rawAffineRestrictedMap]
    exact MorphismProperty.pullbackMap (P := @IsAffineHom)
      (by infer_instance) (by infer_instance) (by simp)
      (by rw [← Category.assoc, Over.w])
  let eH : ∀ i : I, H.obj (op i) ≅
      (cohomology AddCommGrpCat.{u + 1} (D.obj i) q).obj
        (DerivedCategory.Q.obj (K i)) := e
  let eB : B.pt ≅ (cohomology AddCommGrpCat.{u + 1} c.pt q).obj
      (DerivedCategory.Q.obj L.pt) := e₀
  have : IsConnected Iᵒᵖ := IsFiltered.isConnected Iᵒᵖ
  refine EtaleComplexCohomologyPresentationData.intro D c hc hcompact hqs haffine
    K @φ hid hcomp 0 ?_ G eG hG q (@rawAffineComplexPullback.{u} q)
    ?_ eH ?_ L (isColimitConstCocone Iᵒᵖ _) eB ?_ trivial
  · intro i n hn
    exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
      ((upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom ((D₀.obj i).hom ≫ k))).obj
        (restrictedOverCoefficient F₀ (D₀.obj i))) n (ne_of_lt hn)
  · intro X Y f T
    rfl
  · intro i j f
    apply (cancel_mono (e j).hom).1
    dsimp only [D, restrictedOverDiagram, K, φ, eH]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact he i j f
  · intro i
    change B.ι.app (op i) ≫ e₀.hom = (e i).hom ≫
      rawAffineComplexPullback q
        (rawAffineRestrictedMap (c₀.π.app i).left ((D₀.obj i).hom ≫ k)
          (c₀.pt.hom ≫ k) (by rw [← Category.assoc, Over.w]; rfl) U)
        (restrictedOverSingle k F₀ (D₀.obj i) U) ≫
      (cohomology AddCommGrpCat.{u + 1} (pullback U.hom (c₀.pt.hom ≫ k)) q).map
        (DerivedCategory.Q.map ((restrictedOverSingleIso k F₀ (c₀.π.app i) U).hom ≫
          𝟙 (restrictedOverSingle k F₀ c₀.pt U)))
    exact (he₀ i).trans (by congr 2)

end AlgebraicGeometry.Etale
