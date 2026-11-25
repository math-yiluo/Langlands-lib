/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ChartBoundaryLine
public import WeilConjectures.SixFunctors.Etale.Derived.SupportsCounit
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerAffineLine
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ProjectiveLineCohomologyChartBoundary
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ProjectiveLineCohomologyTriangle
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.SupportsBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.SupportsOpenImmersion

/-!
# The cohomology of the projective line

The cohomology of the projective line: for a scheme `S` on which the exponent of the finite
coefficient ring `Λ` is invertible and a normalized rank-one datum, the auxiliary decomposition map
`(1, -h) : Λ_S(1)[2] ⊕ Λ_S ⟶ Rq_*(Λ_{ℙ¹_S}(1)[2])` of the projective line `q : ℙ¹_S ⟶ S`
(`AlgebraicGeometry.Etale.projectiveLineDecompositionMapAux`, with the auxiliary class
`-h = c₁(𝒪(-∞))`) is an isomorphism
(`AlgebraicGeometry.Etale.isIso_projectiveLineDecompositionMapAux`), hence so is the decomposition
map `(1, h)` with the hyperplane class `h = c₁(𝒪(1))` of the notes
(`AlgebraicGeometry.Etale.isIso_projectiveLineDecompositionMap`).

## The argument

Isomorphisms are detected at the geometric points `x : Spec Ω ⟶ S`
(`AlgebraicGeometry.Etale.isIso_of_isIso_leftDerivedUpperStar_algClosurePoint_map`). By proper
base change, the pullback of the decomposition map along `x` is the map
`(η, c♭) : Lx^*(Λ_S(1)[2]) ⊕ Lx^* Λ_S ⟶ Rq'_* Lg'^*(Λ(1)[2])` of the projective line
`q' : ℙ¹_Ω ⟶ Spec Ω`, where `c` is the pullback of the hyperplane class `h`. The class `h` is the
class with supports of the section at infinity with forgotten supports
(`AlgebraicGeometry.Etale.chartBoundaryClass_eq`), so `c` is the restriction of this class with
supports along `g' : ℙ¹_Ω ⟶ ℙ¹_S`. Over the algebraically closed field `Ω`:

* the unit `Λ_Ω(1)[2] ⟶ Rp_* Lp^* Λ_Ω(1)[2]` of the affine line `p : 𝔸¹_Ω ⟶ Spec Ω`, the
  complement of the section at infinity, is an isomorphism (the affine line is acyclic);
* the adjoint of the restricted class with supports is an isomorphism: restricting further to the
  chart at infinity `𝔸¹_Ω ⟶ ℙ¹_Ω`, it is, up to an automorphism of the support, the Kummer
  boundary of the coordinate of `𝔸¹_Ω`, which is the fundamental class of the zero section by the
  rank-one normalisation `AlgebraicGeometry.Etale.HasKummerClass.IsNormalized`.

The decomposition criterion `AlgebraicGeometry.Etale.isIso_biprodDesc_of_isIso_supportedClassMap`
applied to the localization triangle of the section at infinity concludes.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

section BaseChange

variable {X S X' S' : Scheme.{u}} {q : X ⟶ S} {x : S' ⟶ S} {q' : X' ⟶ S'} {g' : X' ⟶ X}

/-- **Base change of a map out of a biproduct into a proper direct image.** For a cartesian square
`g' ≫ q = q' ≫ x` with `q` proper, the pullback along `x` of
`(η_M ≫ Rq_* a, η_N ≫ Rq_* b) : M ⊕ N ⟶ Rq_* K` is an isomorphism as soon as the corresponding
map `Lx^* M ⊕ Lx^* N ⟶ Rq'_* Lg'^* K` built from `Lg'^* a` and `Lg'^* b` is one: they differ by
the proper base change isomorphism `Lx^* Rq_* ≅ Rq'_* Lg'^*`. -/
theorem isIso_leftDerivedUpperStar_map_biprodDesc_of_isPullback (sq : IsPullback g' q' q x)
    [IsProper q] {M N : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (a : (L((q)^*[ModuleCat.{u + 1} Λ])).obj M ⟶ K)
    (b : (L((q)^*[ModuleCat.{u + 1} Λ])).obj N ⟶ K)
    (h : IsIso (biprod.desc
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q').unit.app
          ((L((x)^*[ModuleCat.{u + 1} Λ])).obj M) ≫
        (R((q')_*[ModuleCat.{u + 1} Λ])).map
          ((derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq.toCommSq).hom.app M ≫
            (L((g')^*[ModuleCat.{u + 1} Λ])).map a))
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q').unit.app
          ((L((x)^*[ModuleCat.{u + 1} Λ])).obj N) ≫
        (R((q')_*[ModuleCat.{u + 1} Λ])).map
          ((derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq.toCommSq).hom.app N ≫
            (L((g')^*[ModuleCat.{u + 1} Λ])).map b)))) :
    IsIso ((L((x)^*[ModuleCat.{u + 1} Λ])).map (biprod.desc
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).unit.app M ≫
        (R((q)_*[ModuleCat.{u + 1} Λ])).map a)
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).unit.app N ≫
        (R((q)_*[ModuleCat.{u + 1} Λ])).map b))) := by
  have := Etale.isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring Λ
    isAddTorsion_of_finite sq
  have key {P : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
      (c : (L((q)^*[ModuleCat.{u + 1} Λ])).obj P ⟶ K) :
      (L((x)^*[ModuleCat.{u + 1} Λ])).map
          ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).unit.app P ≫
            (R((q)_*[ModuleCat.{u + 1} Λ])).map c) ≫
          (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app K =
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q').unit.app
          ((L((x)^*[ModuleCat.{u + 1} Λ])).obj P) ≫
        (R((q')_*[ModuleCat.{u + 1} Λ])).map
          ((derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq.toCommSq).hom.app P ≫
            (L((g')^*[ModuleCat.{u + 1} Λ])).map c) := by
    have hn := (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).naturality c
    dsimp only [Functor.comp_obj, Functor.comp_map] at hn
    rw [Functor.map_comp, Category.assoc, hn, ← Category.assoc,
      map_unit_derivedBaseChangeMap_app (ModuleCat.{u + 1} Λ) sq.toCommSq P, Functor.map_comp,
      Category.assoc]
  have := preservesBinaryBiproducts_of_preservesBiproducts (L((x)^*[ModuleCat.{u + 1} Λ]))
  rw [← isIso_comp_right_iff _ ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app K),
    ← biprod.mapBiprod_hom_desc, Category.assoc]
  refine IsIso.comp_isIso' inferInstance ?_
  dsimp only [Functor.id_obj, Functor.comp_obj] at h ⊢
  convert h using 1
  apply biprod.hom_ext'
  · rw [biprod.inl_desc_assoc, biprod.inl_desc, key]
  · rw [biprod.inr_desc_assoc, biprod.inr_desc, key]

end BaseChange

section Restriction

omit [Finite Λ] in
/-- The identifications `Lf^* Λ ≅ Λ` of the constant complexes compose: the inverse of the one
of a composite `f ≫ g` is the composite of the inverses, through `L(f ≫ g)^* ≅ Lf^* Lg^*`. -/
lemma leftDerivedUpperStarConstantComplexIso_inv_comp {X Y T : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ T) (fg : X ⟶ T) (h : fg = f ≫ g) :
    (leftDerivedUpperStarConstantComplexIso Λ f).inv ≫
        (L((f)^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarConstantComplexIso Λ g).inv ≫
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f g fg h).inv.app (constantComplex Λ T) =
      (leftDerivedUpperStarConstantComplexIso Λ fg).inv := by
  rw [leftDerivedUpperStarConstantComplexIso_comp Λ f g fg h]
  simp

/-- **Restricting a class with supports along two factorisations of the same map.** For a
commutative square `m ≫ ι = w ≫ G` and cartesian squares of closed immersions over `G`, `w`,
`ι` and `m`, restricting a class `γ` with supports first along `G` and then along `w` gives the
same class as restricting it first along `ι` and then along `m`, for a suitable identification
`τ_w` of the coefficients. -/
lemma exists_restrictSupportedClass_eq_restrictSupportedClass
    {X U A V Z ZU ZA ZV : Scheme.{u}} (G : U ⟶ X) (w : A ⟶ U) (m : A ⟶ V) (ι : V ⟶ X)
    (hm : m ≫ ι = w ≫ G) (i : Z ⟶ X) (iU : ZU ⟶ U) (iA : ZA ⟶ A) (iV : ZV ⟶ V)
    [IsClosedImmersion i] [IsClosedImmersion iU] [IsClosedImmersion iA] [IsClosedImmersion iV]
    (gU : ZU ⟶ Z) (hgU : IsPullback gU iU i G) (gW : ZA ⟶ ZU) (hW : IsPullback gW iA iU w)
    (gV : ZV ⟶ Z) (hgV : IsPullback gV iV i ι) (g₂ : ZA ⟶ ZV) (hg₂ : IsPullback g₂ iA iV m)
    {L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {LV : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {LA : DerivedCategory (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (τι : (L((ι)^*[ModuleCat.{u + 1} Λ])).obj L ≅ LV)
    (τm : (L((m)^*[ModuleCat.{u + 1} Λ])).obj LV ≅ LA)
    (γ : constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L)) :
    ∃ τw : (L((w)^*[ModuleCat.{u + 1} Λ])).obj ((L((G)^*[ModuleCat.{u + 1} Λ])).obj L) ≅ LA,
      restrictSupportedClass Λ w iU iA gW hW (leftDerivedUpperStarConstantComplexIso Λ w).inv τw
          (restrictSupportedClass Λ G i iU gU hgU (leftDerivedUpperStarConstantComplexIso Λ G).inv
            (Iso.refl _) γ) =
        restrictSupportedClass Λ m iV iA g₂ hg₂ (leftDerivedUpperStarConstantComplexIso Λ m).inv τm
          (restrictSupportedClass Λ ι i iV gV hgV
            (leftDerivedUpperStarConstantComplexIso Λ ι).inv τι γ) := by
  refine ⟨((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) w G (w ≫ G) rfl).app L ≪≫
      (L((w)^*[ModuleCat.{u + 1} Λ])).mapIso (Iso.refl _)).symm ≪≫
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) m ι (w ≫ G) hm.symm).app L ≪≫
      (L((m)^*[ModuleCat.{u + 1} Λ])).mapIso τι ≪≫ τm, ?_⟩
  rw [← restrictSupportedClass_restrictSupportedClass Λ G w (w ≫ G) rfl i iU iA gU hgU gW hW
      (gW ≫ gU) (hW.paste_horiz hgU),
    ← restrictSupportedClass_restrictSupportedClass Λ ι m (w ≫ G) hm.symm i iV iA gV hgV g₂ hg₂
      (gW ≫ gU) (hW.paste_horiz hgU),
    leftDerivedUpperStarConstantComplexIso_inv_comp,
    leftDerivedUpperStarConstantComplexIso_inv_comp]
  congr 1
  ext
  simp

end Restriction

variable [HasKummerClass Λ]

section Field

variable (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [HasInvertibleExponent Λ (Spec (.of Ω))]

/-- **The affine line is acyclic for `Λ(1)[2]`.** Over an algebraically closed field `Ω`, the
unit `Λ_Ω(1)[2] ⟶ Rp_* Lp^* Λ_Ω(1)[2]` of the affine line `p : 𝔸¹_Ω ⟶ Spec Ω` is an
isomorphism. -/
theorem isIso_unit_tateObject_shift_affineLine :
    IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      (𝔸(ULift.{u} (Fin 1); Spec (.of Ω)) ↘ Spec (.of Ω))).unit.app
        ((tateObject Λ (Spec (.of Ω)) 1)⟦(2 : ℤ)⟧)) := by
  obtain ⟨LT, -, hLT, ⟨eTY⟩⟩ := HasTateTwist.exists_isLocallyConstantSheaf_twistObject
    (Λ := Λ) (Spec (.of Ω)) 1
  have := isIso_unit_affineLine_of_cohomology Λ (𝟙 (Spec (.of Ω)))
    (isZero_cohomology_affineLine Λ (k := Ω))
    (nonempty_iso_cohomology_zero_affineLine Λ (k := Ω)).some
    (boundedConstructibleFiniteTor_tateObject Λ _ 1) eTY hLT
  rw [← Adjunction.unit_app_shift_commShiftIso_inv_app]
  infer_instance

end Field

section GeometricPoint

variable [HasKummerClass.IsNormalized Λ] {S : Scheme.{u}} [HasInvertibleExponent Λ S]
  (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ S)

omit [IsAlgClosed Ω] in
/-- **The restricted class of the section at infinity is a fundamental class.** For a geometric
point `x : Spec Ω ⟶ S`, the adjoint of the restriction along `ℙ¹_Ω ⟶ ℙ¹_S` of the class with
supports of the section at infinity (`AlgebraicGeometry.Etale.chartBoundarySupportedClass`) is an
isomorphism. -/
theorem isIso_supportedClassMap_restrictSupportedClass_chartBoundarySupportedClass
    (gZ : ProjectiveSpace.lineInfinity (Spec (.of Ω)) ⟶ ProjectiveSpace.lineInfinity S)
    (hgZ : IsPullback gZ (ProjectiveSpace.lineInfinityι (Spec (.of Ω)))
      (ProjectiveSpace.lineInfinityι S) (ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) x)) :
    haveI : HasInvertibleExponent Λ (Spec (.of Ω)) := .of_hom x
    IsIso (supportedClassMap Λ (ProjectiveSpace.lineInfinityι (Spec (.of Ω)))
      (restrictSupportedClass Λ (ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) x)
        (ProjectiveSpace.lineInfinityι S) (ProjectiveSpace.lineInfinityι (Spec (.of Ω))) gZ hgZ
        (leftDerivedUpperStarConstantComplexIso Λ
          (ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) x)).inv (Iso.refl _)
        (chartBoundarySupportedClass Λ (ProjectiveSpace.lineInfinityOpen S)
          (ProjectiveSpace.coordRatio (Option (ULift.{u} (Fin 1))) S (some ⟨0⟩) none)))) := by
  have : HasInvertibleExponent Λ (Spec (.of Ω)) := .of_hom x
  have : HasInvertibleExponent Λ (ProjectiveSpace.lineInfinityOpen S) :=
    .of_hom (ProjectiveSpace.lineInfinityOpen S).ι
  obtain ⟨gW, hgW, hW⟩ := ProjectiveSpace.exists_isIso_isPullback_lineInfinityChart (Spec (.of Ω))
  obtain ⟨m, hm, hmc⟩ := ProjectiveSpace.exists_lift_lineInfinityChart_map x
  have hs : m.appTop '' {ProjectiveSpace.lineInfinityCoord S} =
      {AffineSpace.coord (Spec (.of Ω)) (ULift.up 0)} := by
    rw [Set.image_singleton, hmc]
  obtain ⟨τw, hτw⟩ := exists_restrictSupportedClass_eq_restrictSupportedClass Λ
    (ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) x)
    (ProjectiveSpace.lineInfinityChart (Spec (.of Ω))) m (ProjectiveSpace.lineInfinityOpen S).ι hm
    (ProjectiveSpace.lineInfinityι S) (ProjectiveSpace.lineInfinityι (Spec (.of Ω)))
    (𝔸(ULift.{u} (Fin 1); Spec (.of Ω)).zeroLocusSubschemeι
      {AffineSpace.coord (Spec (.of Ω)) (ULift.up 0)})
    ((ProjectiveSpace.lineInfinityOpen S).toScheme.zeroLocusSubschemeι
      {ProjectiveSpace.lineInfinityCoord S}) gZ hgZ gW hW (𝟙 _)
    (isPullback_id_comp_of_mono _ _) _ (isPullback_zeroLocusSubschemeι m _ _ hs)
    (leftDerivedUpperStarTateTwoIso Λ (ProjectiveSpace.lineInfinityOpen S).ι)
    (leftDerivedUpperStarTateTwoIso Λ m)
    (chartBoundarySupportedClass Λ (ProjectiveSpace.lineInfinityOpen S)
      (ProjectiveSpace.coordRatio (Option (ULift.{u} (Fin 1))) S (some ⟨0⟩) none))
  obtain ⟨θ, hθ, hθγ⟩ := exists_supportedClassMap_restrictSupportedClass_chartBoundarySupportedClass
    Λ (ProjectiveSpace.lineInfinityOpen S)
    (ProjectiveSpace.coordRatio (Option (ULift.{u} (Fin 1))) S (some ⟨0⟩) none)
  have hφ : IsIso ((L((gW)^*[ModuleCat.{u + 1} Λ])).map (supportedClassMap Λ
      (ProjectiveSpace.lineInfinityι (Spec (.of Ω)))
      (restrictSupportedClass Λ (ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) x)
        (ProjectiveSpace.lineInfinityι S) (ProjectiveSpace.lineInfinityι (Spec (.of Ω))) gZ hgZ
        (leftDerivedUpperStarConstantComplexIso Λ
          (ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) x)).inv (Iso.refl _)
        (chartBoundarySupportedClass Λ (ProjectiveSpace.lineInfinityOpen S)
          (ProjectiveSpace.coordRatio (Option (ULift.{u} (Fin 1))) S (some ⟨0⟩) none))))) := by
    rw [← isIso_supportedClassMap_restrictSupportedClass_iff Λ
      (ProjectiveSpace.lineInfinityChart (Spec (.of Ω)))
      (ProjectiveSpace.lineInfinityι (Spec (.of Ω))) _ gW hW _ _ τw _
      (isIso_supportedRestriction_of_isOpenImmersion Λ _ _ _ _ hW _ _ τw), hτw,
      isIso_supportedClassMap_restrictSupportedClass_iff_of_eq Λ m _ _ _
        (isPullback_zeroLocusSubschemeι m _ _ hs) _ _ _ _ _ θ hθγ, leftDerivedUpperStarTateTwoIso,
      restrictSupportedClass_shiftSupportedClass, kummerBoundary_baseChange_of_eq Λ m _ _ hmc]
    exact HasKummerClass.IsNormalized.isIso_supportedClassMap_kummerBoundary_coord
      (Λ := Λ) (k := Ω) (Spec (.of Ω)) (𝟙 _)
  exact isIso_of_reflects_iso _ (L((gW)^*[ModuleCat.{u + 1} Λ]))

/-- The pullback of the decomposition map of the projective line to a geometric point is an
isomorphism. -/
theorem isIso_leftDerivedUpperStar_map_projectiveLineDecompositionMapAux :
    IsIso ((L((x)^*[ModuleCat.{u + 1} Λ])).map (projectiveLineDecompositionMapAux Λ S)) := by
  have : HasInvertibleExponent Λ (Spec (.of Ω)) := .of_hom x
  obtain ⟨gZ, hgZ⟩ := ProjectiveSpace.exists_isPullback_lineInfinityι_map x
  have sq := ProjectiveSpace.isPullback_map (Option (ULift.{u} (Fin 1))) x
  have hM : IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      (𝔸(ULift.{u} (Fin 1); Spec (.of Ω)) ↘ Spec (.of Ω))).unit.app
        ((L((x)^*[ModuleCat.{u + 1} Λ])).obj ((tateObject Λ S 1)⟦(2 : ℤ)⟧))) := by
    rw [NatTrans.isIso_app_iff_of_iso _ (leftDerivedUpperStarTateTwoIso Λ x)]
    exact isIso_unit_tateObject_shift_affineLine Λ Ω
  have h := isIso_biprodDesc_of_isIso_supportedClassMap Λ
    (ℙ(Option (ULift.{u} (Fin 1)); Spec (.of Ω)) ↘ Spec (.of Ω))
    (ProjectiveSpace.lineInfinityι (Spec (.of Ω)))
    (AffineSpace.toRelativeProjectiveSpace (ULift.{u} (Fin 1)) (Spec (.of Ω)))
    (ProjectiveSpace.range_lineInfinityι_eq_compl_range_toRelativeProjectiveSpace _) _
    (AffineSpace.toRelativeProjectiveSpace_over _ _)
    ((derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq.toCommSq).app _ ≪≫
      (L((ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) x)^*[ModuleCat.{u + 1} Λ])).mapIso
        (leftDerivedUpperStarTateTwoIso Λ (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)))
    ((derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq.toCommSq).app (constantComplex Λ S) ≪≫
      (L((ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) x)^*[ModuleCat.{u + 1} Λ])).mapIso
        (leftDerivedUpperStarConstantComplexIso Λ (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)) ≪≫
      leftDerivedUpperStarConstantComplexIso Λ (ProjectiveSpace.map (Option (ULift.{u} (Fin 1))) x))
    hM _ (isIso_supportedClassMap_restrictSupportedClass_chartBoundarySupportedClass Λ Ω x gZ hgZ)
  rw [restrictSupportedClass_comp_counit, ← chartBoundaryClass_eq] at h
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc,
    Iso.hom_inv_id_assoc] at h
  erw [Iso.refl_hom, Category.comp_id, ← Functor.map_comp] at h
  rw [projectiveLineDecompositionMapAux, Adjunction.homEquiv_unit]
  exact isIso_leftDerivedUpperStar_map_biprodDesc_of_isPullback Λ sq _ _ h

end GeometricPoint

/-- *The cohomology of the projective line*, auxiliary form. For a scheme `S` on which the exponent
of `Λ` is invertible and a normalized rank-one datum, the auxiliary decomposition map
`(1, -h) : Λ_S(1)[2] ⊕ Λ_S ⟶ Rq_*(Λ_{ℙ¹_S}(1)[2])`
(`AlgebraicGeometry.Etale.projectiveLineDecompositionMapAux`, with `-h = c₁(𝒪(-∞))`) is an
isomorphism. It is checked at
the geometric points of `S`
(`AlgebraicGeometry.Etale.isIso_leftDerivedUpperStar_map_projectiveLineDecompositionMapAux`). -/
theorem isIso_projectiveLineDecompositionMapAux [HasKummerClass.IsNormalized Λ] (S : Scheme.{u})
    [HasInvertibleExponent Λ S] : IsIso (projectiveLineDecompositionMapAux Λ S) :=
  isIso_of_isIso_leftDerivedUpperStar_algClosurePoint_map Λ _ fun y ↦
    isIso_leftDerivedUpperStar_map_projectiveLineDecompositionMapAux Λ _ (S.algClosurePoint y)

/-- *The cohomology of the projective line*: the decomposition map `(1, h)` with the
hyperplane class of the notes (`AlgebraicGeometry.Etale.projectiveLineDecompositionMap`) is an
isomorphism: it is the auxiliary one up to the automorphism `1 ⊕ (-1)`
(`AlgebraicGeometry.Etale.isIso_projectiveLineDecompositionMap_iff`). -/
theorem isIso_projectiveLineDecompositionMap [HasKummerClass.IsNormalized Λ] (S : Scheme.{u})
    [HasInvertibleExponent Λ S] : IsIso (projectiveLineDecompositionMap Λ S) :=
  (isIso_projectiveLineDecompositionMap_iff Λ S).2 (isIso_projectiveLineDecompositionMapAux Λ S)

/-- *The trace of the projective line*
`Tr_q : Rq_*(Λ_{ℙ¹_S}(1)[2]) ⟶ Λ_S`, the second component of the inverse of the decomposition
isomorphism `(1, h)` (`AlgebraicGeometry.Etale.projectiveLineDecompositionMap`,
`AlgebraicGeometry.Etale.isIso_projectiveLineDecompositionMap`), `h = c₁(𝒪(1))` the hyperplane
class of the notes; it is characterised by `Tr_q ∘ h♭ = 1` and `Tr_q ∘ η = 0`
(`AlgebraicGeometry.Etale.homEquiv_projectiveLineHyperplaneClass_comp_projectiveLineTrace`). It is
the negative of the auxiliary trace `AlgebraicGeometry.Etale.projectiveLineTraceAux`, normalized
by `-h` (`AlgebraicGeometry.Etale.projectiveLineTrace_eq_neg`). -/
noncomputable def projectiveLineTrace [HasKummerClass.IsNormalized Λ] (S : Scheme.{u})
    [HasInvertibleExponent Λ S] :
    (R(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))_*[ModuleCat.{u + 1} Λ])).obj
        ((tateObject Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1)⟦(2 : ℤ)⟧) ⟶ constantComplex Λ S :=
  haveI := isIso_projectiveLineDecompositionMap Λ S
  inv (projectiveLineDecompositionMap Λ S) ≫ biprod.snd

/-- The auxiliary trace: the second component of the inverse of the auxiliary decomposition
isomorphism `(1, -h)` (`AlgebraicGeometry.Etale.projectiveLineDecompositionMapAux`), normalized by
`-h`; the trace of the notes is its negative (`AlgebraicGeometry.Etale.projectiveLineTrace_eq_neg`).
-/
noncomputable def projectiveLineTraceAux [HasKummerClass.IsNormalized Λ] (S : Scheme.{u})
    [HasInvertibleExponent Λ S] :
    (R(((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))_*[ModuleCat.{u + 1} Λ])).obj
        ((tateObject Λ ℙ(Option (ULift.{u} (Fin 1)); S) 1)⟦(2 : ℤ)⟧) ⟶ constantComplex Λ S :=
  haveI := isIso_projectiveLineDecompositionMapAux Λ S
  inv (projectiveLineDecompositionMapAux Λ S) ≫ biprod.snd

/-- The trace of the notes is the negative of the auxiliary trace. -/
lemma projectiveLineTrace_eq_neg [HasKummerClass.IsNormalized Λ] (S : Scheme.{u})
    [HasInvertibleExponent Λ S] :
    projectiveLineTrace Λ S = -projectiveLineTraceAux Λ S := by
  have := isIso_projectiveLineDecompositionMapAux Λ S
  have := isIso_projectiveLineDecompositionMap Λ S
  have hmap : IsIso (biprod.map (𝟙 ((tateObject Λ S 1)⟦(2 : ℤ)⟧)) (-𝟙 (constantComplex Λ S))) :=
    ⟨biprod.map (𝟙 _) (-𝟙 _), by ext <;> simp, by ext <;> simp⟩
  have hinv : inv (biprod.map (𝟙 ((tateObject Λ S 1)⟦(2 : ℤ)⟧)) (-𝟙 (constantComplex Λ S))) =
      biprod.map (𝟙 _) (-𝟙 _) := by
    rw [IsIso.inv_eq_of_hom_inv_id]
    ext <;> simp
  unfold projectiveLineTrace projectiveLineTraceAux projectiveLineDecompositionMap
  rw [IsIso.inv_comp, hinv, Category.assoc, biprod.map_snd]
  simp only [Preadditive.comp_neg, Category.comp_id]

end Etale

end AlgebraicGeometry
