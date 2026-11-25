/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawAffineRestrictedCohomology
import WeilConjectures.AlgebraicGeometry.RestrictedAffineCoefficientSystem
import WeilConjectures.AlgebraicGeometry.RawAffineComplexSystemMapCoherence

/-! # Geometric complex system for restricted cohomology

Source: Stacks Project, Tag 09Z1 proof, and Tag 0EZM for the canonical maps.
(blueprint: lem-sbc-restricted-affine-complex-system).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

-- The existential conclusion records properties that later binders need not reference.
set_option linter.unusedVariables false in
/-- The restricted-cohomology diagram comes from a qcqs scheme limit and
single complexes with a common lower bound, before any comparison with raw Hom.
Source: Stacks Project, Tag 09Z1 proof, before applying cohomology continuity;
Tag 0EZM for the cohomology cocone of complexes.
(blueprint: lem-sbc-restricted-affine-complex-system).

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
is exactly rawAffineRestrictedCohomologyMap, proving the last equation.
This construction asserts no IsColimit B and uses no cohomology continuity. -/
theorem exists_restricted_affine_complex_system {S : Scheme.{v}}
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
    ∃
    (D' : Iᵒᵖ ⥤ Scheme.{v})
    (c' : Cone D')
    (hc : IsLimit c')
    (compact : ∀ i : Iᵒᵖ, CompactSpace (D'.obj i))
    (quasiSeparated : ∀ i : Iᵒᵖ, QuasiSeparatedSpace (D'.obj i))
    (affine : ∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D'.map f))
    (K : ∀ i : Iᵒᵖ, CochainComplex (Sheaf (D'.obj i).smallEtaleTopology
      AddCommGrpCat.{v + 1}) ℤ)
    (ψ : ∀ {i j : Iᵒᵖ} (f : j ⟶ i),
      ((upperStar AddCommGrpCat.{v + 1} (D'.map f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (K i) ⟶ K j)
    (hidentity : ∀ i : Iᵒᵖ, ψ (𝟙 i) =
      (NatIso.mapHomologicalComplex
        (eqToIso (congrArg (upperStar AddCommGrpCat.{v + 1}) (D'.map_id i)))
        (ComplexShape.up ℤ)).hom.app (K i) ≫
      (NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{v + 1} (D'.obj i))
        (ComplexShape.up ℤ)).hom.app (K i))
    (hcomposition : ∀ (i j k : Iᵒᵖ) (f : j ⟶ i) (g : k ⟶ j),
      ψ (g ≫ f) =
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{v + 1} (D'.map g) (D'.map f)
            (D'.map (g ≫ f)) (D'.map_comp g f))
          (ComplexShape.up ℤ)).hom.app (K i) ≫
        ((upperStar AddCommGrpCat.{v + 1} (D'.map g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (ψ f) ≫ ψ g)
    (hbelow : ∀ (i : Iᵒᵖ) (n : ℤ), n < 0 → IsZero ((K i).X n))
    (G : (Iᵒᵖ)ᵒᵖ ⥤ CochainComplex (Sheaf c'.pt.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    (eG : ∀ i : Iᵒᵖ, G.obj (op i) ≅
      ((upperStar AddCommGrpCat.{v + 1} (c'.π.app i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (K i))
    (hG : ∀ (i j : Iᵒᵖ) (f : j ⟶ i), G.map f.op =
      (eG i).hom ≫
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{v + 1} (c'.π.app j) (D'.map f)
            (c'.π.app i) (c'.w f).symm) (ComplexShape.up ℤ)).hom.app (K i) ≫
        ((upperStar AddCommGrpCat.{v + 1} (c'.π.app j)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (ψ f) ≫ (eG j).inv)
    (T : (Iᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{v + 1})
    (eT : ∀ i : Iᵒᵖ, T.obj (op i) ≅
      (cohomology AddCommGrpCat.{v + 1} (D'.obj i) (p : ℤ)).obj (DerivedCategory.Q.obj (K i)))
    (hT : ∀ (i j : Iᵒᵖ) (f : j ⟶ i), T.map f.op =
      (eT i).hom ≫ rawAffineComplexPullback (p : ℤ) (D'.map f) (K i) ≫
        (cohomology AddCommGrpCat.{v + 1} (D'.obj j) (p : ℤ)).map
          (DerivedCategory.Q.map (ψ f)) ≫ (eT j).inv)
    (L : Cocone G)
    (hL : IsColimit L)
    (B : Cocone T)
    (eB : B.pt ≅ (cohomology AddCommGrpCat.{v + 1} c'.pt (p : ℤ)).obj
      (DerivedCategory.Q.obj L.pt))
    (hB : ∀ i : Iᵒᵖ, B.ι.app (op i) ≫ eB.hom =
      (eT i).hom ≫ rawAffineComplexPullback (p : ℤ) (c'.π.app i) (K i) ≫
        (cohomology AddCommGrpCat.{v + 1} c'.pt (p : ℤ)).map
          (DerivedCategory.Q.map ((eG i).inv ≫ L.ι.app (op i))))
    (restrictionIso : ∀ i : (Iᵒᵖ)ᵒᵖ,
      rawAffineRestrictedCohomology (D.obj (op i.unop.unop)).hom p
        (F i.unop.unop) U ≅ T.obj i)
    (restrictionLimitIso : rawAffineRestrictedCohomology c.pt.hom p (colimit H) U ≅ B.pt),
    ∀ (i : (Iᵒᵖ)ᵒᵖ)
      (t : rawAffineRestrictedCohomology (D.obj (op i.unop.unop)).hom p
        (F i.unop.unop) U),
      B.ι.app i ((restrictionIso i).hom t) = restrictionLimitIso.hom
        (rawAffineRestrictedCohomologyMap (c.π.app (op i.unop.unop)).left
          (D.obj (op i.unop.unop)).hom c.pt.hom (Over.w (c.π.app (op i.unop.unop))) p
          (F i.unop.unop) (colimit H)
          ((eH i.unop.unop).inv ≫ colimit.ι H i.unop.unop) U t) := by
  obtain ⟨D', c', hc', compact, quasiSeparated, affine, K, ψ, hid, hcomp, hbelow,
    G, eG, hG, L, hL, hbelowL, r, rL, hr⟩ := exists_restricted_affine_coefficient_system
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
  refine ⟨D', c', hc', compact, quasiSeparated, affine, K, ψ, hid, hcomp, hbelow,
    G, eG, hG, T, (fun i ↦ Iso.refl _), ?_, L, hL, B, Iso.refl _, ?_,
    (fun i ↦ r i.unop), rL, ?_⟩
  · intro i j f
    simp [T]
  · intro i
    simp [B]
  · intro i t
    exact congrArg (fun a ↦ a t) (hr i.unop)

end AlgebraicGeometry.Etale
