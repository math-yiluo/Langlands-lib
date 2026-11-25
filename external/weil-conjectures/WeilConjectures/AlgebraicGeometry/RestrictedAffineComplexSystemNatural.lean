/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawAffineRestrictedCohomology
public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawComplexPresentation
import WeilConjectures.AlgebraicGeometry.RestrictedAffineNaturalCoefficientSystem
import WeilConjectures.AlgebraicGeometry.RawAffineComplexSystemMapCoherence

/-! # Geometric complex system for restricted cohomology

Source: Stacks Project, Tag 09Z1 proof, and Tag 0EZM for the canonical maps.
(blueprint: lem-sbc-restricted-affine-complex-system-natural).
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true in
private theorem presentation_of_data
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (H : Iᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (B : Cocone H)
    (D : I ⥤ Scheme.{u})
    (c : Cone D)
    (hc : IsLimit c)
    (hcompact : ∀ i : I, CompactSpace (D.obj i))
    (hqs : ∀ i : I, QuasiSeparatedSpace (D.obj i))
    (haffine : ∀ (i j : I) (f : i ⟶ j), IsAffineHom (D.map f))
    (F : ∀ i : I, CochainComplex (Sheaf (D.obj i).smallEtaleTopology
      AddCommGrpCat.{u + 1}) ℤ)
    (φ : ∀ {i j : I} (f : j ⟶ i),
      ((upperStar AddCommGrpCat.{u + 1} (D.map f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (NatIso.mapHomologicalComplex
        (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id i)))
        (ComplexShape.up ℤ)).hom.app (F i) ≫
      (NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{u + 1} (D.obj i))
        (ComplexShape.up ℤ)).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : j ⟶ i) (g : k ⟶ j),
      φ (g ≫ f) =
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{u + 1} (D.map g) (D.map f)
            (D.map (g ≫ f)) (D.map_comp g f))
          (ComplexShape.up ℤ)).hom.app (F i) ≫
        ((upperStar AddCommGrpCat.{u + 1} (D.map g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (φ f) ≫ φ g)
    (a : ℤ)
    (hbelow : ∀ (i : I) (n : ℤ), n < a → IsZero ((F i).X n))
    (G : Iᵒᵖ ⥤ CochainComplex (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (eG : ∀ i : I, G.obj (op i) ≅
      ((upperStar AddCommGrpCat.{u + 1} (c.π.app i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (F i))
    (hG : ∀ (i j : I) (f : j ⟶ i), G.map f.op =
      (eG i).hom ≫
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{u + 1} (c.π.app j) (D.map f)
            (c.π.app i) (c.w f).symm) (ComplexShape.up ℤ)).hom.app (F i) ≫
        ((upperStar AddCommGrpCat.{u + 1} (c.π.app j)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (φ f) ≫ (eG j).inv)
    (p : ℤ)
    (P : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (K : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ),
      (cohomology AddCommGrpCat.{u + 1} Y p).obj (DerivedCategory.Q.obj K) ⟶
      (cohomology AddCommGrpCat.{u + 1} X p).obj
        (DerivedCategory.Q.obj
          (((upperStar AddCommGrpCat.{u + 1} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)))
    (hP : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      (K : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ),
      P f K = (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} p).map
        ((rightDerivedGlobalSections AddCommGrpCat.{u + 1} Y).map
          ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
            (DerivedCategory.Q.obj K)) ≫
        (Functor.rightDerivedFunctorCompIso'
          (lowerStar AddCommGrpCat.{u + 1} f)
          (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1})
          (Functor.isoWhiskerLeft (lowerStar AddCommGrpCat.{u + 1} f)
              (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}
                terminalIsTerminal) ≪≫
            lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} f ≪≫
            (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}
              terminalIsTerminal).symm)).hom.app
                ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategory.obj
                  (DerivedCategory.Q.obj K)) ≫
        (rightDerivedGlobalSections AddCommGrpCat.{u + 1} X).map
          ((upperStar AddCommGrpCat.{u + 1} f).mapDerivedCategoryFactors.hom.app K)))
    (eH : ∀ i : I, H.obj (op i) ≅
      (cohomology AddCommGrpCat.{u + 1} (D.obj i) p).obj (DerivedCategory.Q.obj (F i)))
    (hH : ∀ (i j : I) (f : j ⟶ i), H.map f.op =
      (eH i).hom ≫ P (D.map f) (F i) ≫
        (cohomology AddCommGrpCat.{u + 1} (D.obj j) p).map
          (DerivedCategory.Q.map (φ f)) ≫ (eH j).inv)
    (L : Cocone G)
    (hL : IsColimit L)
    (eB : B.pt ≅ (cohomology AddCommGrpCat.{u + 1} c.pt p).obj
      (DerivedCategory.Q.obj L.pt))
    (hB : ∀ i : I, B.ι.app (op i) ≫ eB.hom =
      (eH i).hom ≫ P (c.π.app i) (F i) ≫
        (cohomology AddCommGrpCat.{u + 1} c.pt p).map
          (DerivedCategory.Q.map ((eG i).inv ≫ L.ι.app (op i)))) :
    EtaleComplexCohomologyPresentation H B := by
  exact ⟨D, c, hc, hcompact, hqs, haffine, F, φ, hidentity,
    hcomposition, a, hbelow, G, eG, hG, p, P, hP, eH, hH, L, hL, eB, hB,
    trivial⟩

private lemma identity_pair {C : Type*} [Category C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) : f ≫ g = 𝟙 X ≫ f ≫ g ≫ 𝟙 Z := by
  simp only [Category.id_comp, Category.comp_id]

private lemma identity_leg {C : Type*} [Category C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g) ≫ 𝟙 Z = 𝟙 X ≫ f ≫ g := by
  simp only [Category.id_comp, Category.comp_id]

private theorem rawAffineComplexPullback_formula (p : ℤ) {X Y : Scheme.{v}} (f : X ⟶ Y)
    (K : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ) :
    rawAffineComplexPullback p f K =
  (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} p).map
        ((rightDerivedGlobalSections AddCommGrpCat.{v + 1} Y).map
          ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).unit.app
            (DerivedCategory.Q.obj K)) ≫
        (Functor.rightDerivedFunctorCompIso'
          (lowerStar AddCommGrpCat.{v + 1} f)
          (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1})
          (Functor.isoWhiskerLeft (lowerStar AddCommGrpCat.{v + 1} f)
              (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{v + 1}
                terminalIsTerminal) ≪≫
            lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{v + 1} f ≪≫
            (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{v + 1}
              terminalIsTerminal).symm)).hom.app
                ((upperStar AddCommGrpCat.{v + 1} f).mapDerivedCategory.obj
                  (DerivedCategory.Q.obj K)) ≫
        (rightDerivedGlobalSections AddCommGrpCat.{v + 1} X).map
          ((upperStar AddCommGrpCat.{v + 1} f).mapDerivedCategoryFactors.hom.app K)) := by
  rfl


attribute [local irreducible] cohomology upperStar rawAffineComplexPullback
  rawAffineRestrictedCohomology rightDerivedGlobalSections DerivedCategory.Q

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency true in
/-- The restricted-cohomology diagram comes from a qcqs scheme limit and
single complexes with a common lower bound, before any comparison with raw Hom.
Source: Stacks Project, Tag 09Z1 proof, before applying cohomology continuity;
Tag 0EZM for the cohomology cocone of complexes.
(blueprint: lem-sbc-restricted-affine-complex-system-natural).

Proof: Base change the underlying scheme diagram and cone along U.hom. Define
the induced maps by the pullback universal property; uniqueness proves their
identity and composition laws and that the new cone is limiting. Affine maps
remain affine after base change. The qcqs structure maps remain qcqs, and their
target U is affine, so all stage schemes are compact and quasi-separated.
Restrict the sheaves along the second projections of these pullbacks. Compare
the two composites around each pullback square using upperStarComp; restrict
phi through this comparison. The identity and associativity coherence of
upperStarComp transports hphiid and hphicomp to the restricted transition laws.
Put these sheaves into degree-zero single complexes. The lower bound is zero,
and mapCochainComplexSingleFunctor gives the required complex transitions.
Restrict H at the limit and use the comparison on each cone triangle and eH
to construct eG; hH gives hG. Map the colimit cocone of H by restriction, which
is a left adjoint, and then by the single functor, which preserves colimits
termwise. This is L and proves hL. Use the fixed map rawAffineComplexPullback for every
cohomology pullback. Take T to the cohomology groups of the stage complexes;
its transition maps are P followed by the coefficient map. Naturality and
composition of the derived adjunction unit prove hT and the functor laws.
Take B to the limit cohomology with the same pullback/coefficient legs. The
cone equations and coefficient cocone equations prove that these legs form a
cocone and give hB. The stage restrictionIso is the identity under the single
complex identifications. The colimit comparison from restriction identifies
L.pt with the single complex of the restriction of colimit H, giving
restrictionLimitIso. The inverse-image composition comparison on each cone
triangle is exactly rawAffineRestrictedCoefficient. Thus the leg equality
is exactly rawAffineRestrictedCohomologyMap, proving the leg equation.
For a stage arrow f, the induced pullback map is rawAffineRestrictedMap of
D.map f.op. Its restricted coefficient map is rawAffineRestrictedCoefficient
of phi f, by the same two inverse-image composition comparisons. Applying
cohomology to the single-functor comparison gives exactly the displayed
restricted cohomology map. The stage restriction isomorphisms therefore
intertwine T.map f with that map. This is a separate transition equation:
it does not follow from equality of the cocone legs, which need not be monic.
This construction asserts no IsColimit B and uses no cohomology continuity. -/
theorem exists_restricted_affine_complex_system_natural {S : Scheme.{v}}
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over S)
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i : Iᵒᵖ, QuasiCompact (D.obj i).hom]
    [∀ i : Iᵒᵖ, QuasiSeparated (D.obj i).hom]
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (((D.map f.op).left)^*[AddCommGrpCat.{v + 1}]).obj (F i) ⟶ F j)
    (hφid : ∀ i : I, HEq (φ (𝟙 i))
      ((upperStarId AddCommGrpCat.{v + 1} (D.obj (op i)).left).hom.app (F i)))
    (hφcomp : ∀ {i j k : I} (f : i ⟶ j) (g : j ⟶ k), HEq (φ (f ≫ g))
      ((upperStarComp AddCommGrpCat.{v + 1} (D.map g.op).left
          (D.map f.op).left).hom.app (F i) ≫
        (((D.map g.op).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ φ g))
    (H : I ⥤ Sheaf c.pt.left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (eH : ∀ i : I, H.obj i ≅
      (((c.π.app (op i)).left)^*[AddCommGrpCat.{v + 1}]).obj (F i))
    (hH : ∀ {i j : I} (f : i ⟶ j), H.map f =
      (eH i).hom ≫
        (upperStarComp AddCommGrpCat.{v + 1} (c.π.app (op j)).left (D.map f.op).left
          (c.π.app (op i)).left
          (congrArg (fun t => t.left) (c.w f.op)).symm).hom.app (F i) ≫
        (((c.π.app (op j)).left)^*[AddCommGrpCat.{v + 1}]).map (φ f) ≫ (eH j).inv)
    [HasColimit H] (p : ℕ)
    (U : S.Etale) [IsAffine U.left] :
    ∃ (T : (Iᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{v + 1}) (B : Cocone T),
    EtaleComplexCohomologyPresentation T B ∧ ∃
    (restrictionIso : ∀ i : (Iᵒᵖ)ᵒᵖ,
      rawAffineRestrictedCohomology (D.obj (op i.unop.unop)).hom p
        (F i.unop.unop) U ≅ T.obj i)
    (restrictionLimitIso : rawAffineRestrictedCohomology c.pt.hom p (colimit H) U ≅ B.pt),
    (∀ (i : (Iᵒᵖ)ᵒᵖ)
      (t : rawAffineRestrictedCohomology (D.obj (op i.unop.unop)).hom p
        (F i.unop.unop) U),
      B.ι.app i ((restrictionIso i).hom t) = restrictionLimitIso.hom
        (rawAffineRestrictedCohomologyMap (c.π.app (op i.unop.unop)).left
          (D.obj (op i.unop.unop)).hom c.pt.hom (Over.w (c.π.app (op i.unop.unop))) p
          (F i.unop.unop) (colimit H)
          ((eH i.unop.unop).inv ≫ colimit.ι H i.unop.unop) U t)) ∧
    (∀ {i j : I} (f : i ⟶ j)
      (t : rawAffineRestrictedCohomology (D.obj (op i)).hom p (F i) U),
      T.map ((opOpEquivalence I).inverse.map f) ((restrictionIso (op (op i))).hom t) =
        (restrictionIso (op (op j))).hom
          (rawAffineRestrictedCohomologyMap (D.map f.op).left
            (D.obj (op i)).hom (D.obj (op j)).hom (Over.w (D.map f.op)) p
            (F i) (F j) (φ f) U t)) := by
  obtain ⟨D', c', hc', compact, qs, affine, K, ψ, hid, hcomp, hbelow,
    G, eG, hG, L, hL, hbelowL, r, rL, hr, ht⟩ :=
    exists_restricted_affine_natural_coefficient_system
      D c hc F φ hφid hφcomp H eH hH p U
  have hKplus (i : Iᵒᵖ) : CochainComplex.plus _ (K i) :=
    ⟨0, (CochainComplex.isStrictlyGE_iff _ 0).2 (hbelow i)⟩
  have hLplus : CochainComplex.plus _ L.pt :=
    ⟨0, (CochainComplex.isStrictlyGE_iff _ 0).2 hbelowL⟩
  obtain ⟨hmid, hmcomp, hb⟩ := rawAffineComplex_system_map_coherence
    D' c' K hKplus ψ hid hcomp G eG hG L hLplus (p : ℤ)
  let T : (Iᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{v + 1} :=
    { obj := fun i ↦
        (cohomology AddCommGrpCat.{v + 1} (D'.obj i.unop) (p : ℤ)).obj
          (DerivedCategory.Q.obj (K i.unop))
      map := fun f ↦ rawAffineComplexPullback (p : ℤ) (D'.map f.unop) (K _) ≫
        (cohomology AddCommGrpCat.{v + 1} (D'.obj _) (p : ℤ)).map
          (DerivedCategory.Q.map (ψ f.unop))
      map_id := fun i ↦ hmid i.unop
      map_comp := fun f g ↦ hmcomp _ _ _ f.unop g.unop }
  let B : Cocone T :=
    { pt := (cohomology AddCommGrpCat.{v + 1} c'.pt (p : ℤ)).obj
        (DerivedCategory.Q.obj L.pt)
      ι :=
        { app := fun i ↦ rawAffineComplexPullback (p : ℤ) (c'.π.app i.unop) (K _) ≫
            (cohomology AddCommGrpCat.{v + 1} c'.pt (p : ℤ)).map
              (DerivedCategory.Q.map ((eG i.unop).inv ≫ L.ι.app i))
          naturality := fun i j f ↦ by
            simpa [T] using hb i.unop j.unop f.unop } }
  refine ⟨T, B, ?_, (fun i ↦ r i.unop), rL, ?_, ?_⟩
  · exact presentation_of_data T B D' c' hc' compact qs affine K ψ hid hcomp 0 hbelow
      G eG hG (p : ℤ) (rawAffineComplexPullback (p : ℤ))
      (fun f K ↦ rawAffineComplexPullback_formula (p : ℤ) f K)
      (fun i ↦ Iso.refl _)
      (fun i j f ↦ identity_pair _ _) L hL (Iso.refl _)
      (fun i ↦ identity_leg _ _)
  · intro i t
    exact ConcreteCategory.congr_hom (hr i.unop) t
  · intro i j f t
    exact ConcreteCategory.congr_hom (ht f) t

end AlgebraicGeometry.Etale
