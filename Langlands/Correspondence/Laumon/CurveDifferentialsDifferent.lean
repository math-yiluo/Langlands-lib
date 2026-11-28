import Langlands.MathlibBase
import Langlands.Correspondence.Laumon.CurveDifferentialsStalk
import Langlands.AlgebraicGeometry.StalkKaehler
import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import WeilConjectures.AlgebraicGeometry.Curve.DivisorIdealSheaf

/-!
# Differentials and the different of a finite separable morphism of curves

For a morphism `f : Y ⟶ X` of schemes over `Spec κ`, the morphism
`f^* Ω¹_{X/κ} ⟶ Ω¹_{Y/κ}` adjoint to `Ω¹_{X/κ} ⟶ f_* Ω¹_{Y/κ}`, `d s ↦ d (f^♯ s)`. For a
finite separable morphism of smooth proper curves over a perfect field, its zero scheme is the
ideal sheaf of the different divisor `D_f`, and `Ω¹_{Y/κ} ≅ f^* Ω¹_{X/κ} ⊗ 𝒪_Y(D_f)`. The
theorem `curveDifferentialsDifferentStatement` proves `CurveDifferentialsDifferentStatement`.
The local cokernel lengths come from the curve case of Serre's characterization of the different
by relative differentials (*Local Fields*, III §7, Prop. 14); the zero scheme of the map then
identifies the divisor `D_f` and gives the line-bundle isomorphism.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MonoidalCategory
  KaehlerDifferential Langlands.AlgebraicGeometry Langlands.CommutativeAlgebra

open scoped AlgebraicGeometry.Scheme.Modules

namespace Langlands.Henniart.Laumon

section Map

variable {κ : Type u} [CommRing κ] {X Y : Scheme.{u}} (gX : X ⟶ Spec (.of κ)) (f : Y ⟶ X)

/-- The morphism `Ω¹_{X/κ} ⟶ f_* Ω¹_{Y/κ}` sending `d s` to `d (f^♯ s)`, for `Y` over `Spec κ`
through `f`. -/
def differentialsPushforwardHom :
    gX.relativeDifferentials ⟶
      (Scheme.Modules.pushforward f).obj (f ≫ gX).relativeDifferentials :=
  (gX.relativeDifferentialsHomEquiv _).symm (gX.pushforwardDerivation f)

/-- The morphism `f^* Ω¹_{X/κ} ⟶ Ω¹_{Y/κ}`, adjoint to `differentialsPushforwardHom`. -/
def differentialsPullbackHom :
    (Scheme.Modules.pullback f).obj gX.relativeDifferentials ⟶ (f ≫ gX).relativeDifferentials :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    (differentialsPushforwardHom gX f)

/-- `differentialsPushforwardHom` on sections over `V`, as an additive map
`Γ(Ω¹_{X/κ}, V) → Γ(Ω¹_{Y/κ}, f⁻¹ V)`. -/
def differentialsPushforwardApp (V : X.Opens) :
    Γ(gX.relativeDifferentials, V) →+ Γ((f ≫ gX).relativeDifferentials, f ⁻¹ᵁ V) :=
  ((differentialsPushforwardHom gX f).app V).hom

theorem differentialsPushforwardApp_sectionsD (V : X.Opens) (a : Γ(X, V)) :
    differentialsPushforwardApp gX f V (gX.sectionsD V a) =
      (f ≫ gX).sectionsD (f ⁻¹ᵁ V) (f.app V a) :=
  gX.pushforwardDerivation_desc_app_d f V a

theorem differentialsPushforwardApp_smul (V : X.Opens) (a : Γ(X, V))
    (s : Γ(gX.relativeDifferentials, V)) :
    differentialsPushforwardApp gX f V (a • s) =
      f.app V a • differentialsPushforwardApp gX f V s :=
  Scheme.Modules.Hom.app_smul _ a s

/-- `f^* Ω¹_{X/κ} ⟶ Ω¹_{Y/κ}` sends the pullback `η s` of a section `s` of `Ω¹_{X/κ}` over `V`
to the image of `s` in `Γ(Ω¹_{Y/κ}, f⁻¹ V)`. -/
theorem differentialsPullbackHom_app_unit (V : X.Opens) (s : Γ(gX.relativeDifferentials, V)) :
    (differentialsPullbackHom gX f).app (f ⁻¹ᵁ V)
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app _).app V s) =
      differentialsPushforwardApp gX f V s := by
  have h := (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_unit _ _
    (differentialsPullbackHom gX f)
  rw [differentialsPullbackHom, Equiv.apply_symm_apply] at h
  rw [differentialsPushforwardApp, h, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforward_map_app]
  rfl

end Map

section Stalk

variable {κ : Type u} [CommRing κ] {X Y : Scheme.{u}} {gX : X ⟶ Spec (.of κ)} {f : Y ⟶ X}
  {y : Y} [Algebra κ (X.presheaf.stalk (f y))] [Algebra κ (Y.presheaf.stalk y)]
  [Algebra (X.presheaf.stalk (f y)) (Y.presheaf.stalk y)]
  [IsScalarTower κ (X.presheaf.stalk (f y)) (Y.presheaf.stalk y)]
  (hAO : algebraMap (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) = (f.stalkMap y).hom)
  (hκX : ∀ (U : X.Opens) (hU : f y ∈ U),
    (X.presheaf.germ U (f y) hU).hom.comp (gX.specStructureMap U).hom =
      algebraMap κ (X.presheaf.stalk (f y)))
  (hκY : ∀ (U : Y.Opens) (hU : y ∈ U),
    (Y.presheaf.germ U y hU).hom.comp ((f ≫ gX).specStructureMap U).hom =
      algebraMap κ (Y.presheaf.stalk y))

include hAO in
/-- **The stalk of `Ω¹_{X/κ} ⟶ f_* Ω¹_{Y/κ}`.** For affine opens `V ∋ f y` and `f⁻¹ V`, the
image in `Ω[𝒪_{Y,y}⁄κ]` of `differentialsPushforwardHom` applied to a section `s` is the image of
the germ of `s` under `KaehlerDifferential.map κ κ 𝒪_{X,f(y)} 𝒪_{Y,y}`. -/
theorem toStalk_differentialsPushforwardHom {V : X.Opens} (hV : IsAffineOpen V)
    (hV' : IsAffineOpen (f ⁻¹ᵁ V)) (hy : f y ∈ V) (hy' : y ∈ f ⁻¹ᵁ V)
    (s : Γ(gX.relativeDifferentials, V)) :
    StalkKaehler.toStalk (f ≫ gX) hκY (f ⁻¹ᵁ V) hV' hy'
        (differentialsPushforwardApp gX f V s) =
      map κ κ (X.presheaf.stalk (f y)) (Y.presheaf.stalk y)
        (StalkKaehler.toStalk gX hκX V hV hy s) := by
  let := (gX.specStructureMap V).hom.toAlgebra
  obtain ⟨ω, rfl⟩ := (gX.kaehlerSectionsEquiv V rfl hV).surjective s
  have hω : ω ∈ Submodule.span Γ(X, V) (Set.range (D κ Γ(X, V))) := by
    rw [span_range_derivation]; trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    rw [gX.kaehlerSectionsEquiv_D, differentialsPushforwardApp_sectionsD,
      StalkKaehler.toStalk_sectionsD, StalkKaehler.toStalk_sectionsD, map_D, hAO,
      Scheme.Hom.germ_stalkMap_apply]
  | zero =>
    rw [map_zero, map_zero, StalkKaehler.toStalk_zero, StalkKaehler.toStalk_zero, map_zero]
  | add x z _ _ hx hz =>
    rw [map_add, map_add, StalkKaehler.toStalk_add, StalkKaehler.toStalk_add, hx, hz, map_add]
  | smul a x _ hx =>
    rw [LinearEquiv.map_smul, differentialsPushforwardApp_smul, StalkKaehler.toStalk_smul,
      StalkKaehler.toStalk_smul, hx, LinearMap.map_smul,
      ← algebraMap_smul (Y.presheaf.stalk y) (X.presheaf.germ V (f y) hy a), hAO,
      Scheme.Hom.germ_stalkMap_apply]

end Stalk


section Curve

variable (κ : Type u) [Field κ]

/-- The `κ`-algebra structure `stalkAlgebraOver` of `𝒪_{Z,z}` is the germ at `z` of the
structure map `κ → Γ(Z, U)` on any open `U ∋ z`. -/
theorem germ_comp_specStructureMap_eq_stalkAlgebraOver {Z : Scheme.{u}} [Z.Over (Spec (.of κ))]
    (z : Z) (U : Z.Opens) (hz : z ∈ U) :
    (Z.presheaf.germ U z hz).hom.comp ((Z ↘ Spec (.of κ)).specStructureMap U).hom =
      (Z.presheaf.Γgerm z).hom.comp (Scheme.globalSectionsRingHom κ (X := Z)) := by
  let := stalkAlgebraOver κ Z z
  refine StalkKaehler.germ_comp_specStructureMap_of_top _ ?_ U hz
  rw [RingHom.algebraMap_toAlgebra, Scheme.Hom.specStructureMap, Scheme.globalSectionsRingHom,
    TopCat.Presheaf.Γgerm, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
  congr 1
  simp only [Scheme.Hom.appLE, Category.assoc]
  erw [TopCat.Presheaf.germ_res]
  rfl

variable {X Y : Scheme.{u}} [X.Over (Spec (.of κ))] (f : Y ⟶ X)

/-- The structure map of `Y` through `f`, followed by the germ at `y`, is the structure map
`κ → 𝒪_{X,f(y)}` followed by the stalk map of `f`. -/
theorem germ_comp_specStructureMap_comp (y : Y) (U : Y.Opens) (hy : y ∈ U) :
    (Y.presheaf.germ U y hy).hom.comp ((f ≫ X ↘ Spec (.of κ)).specStructureMap U).hom =
      (f.stalkMap y).hom.comp
        ((X.presheaf.Γgerm (f y)).hom.comp (Scheme.globalSectionsRingHom κ (X := X))) := by
  let : Algebra κ (Y.presheaf.stalk y) :=
    ((f.stalkMap y).hom.comp
      ((X.presheaf.Γgerm (f y)).hom.comp (Scheme.globalSectionsRingHom κ (X := X)))).toAlgebra
  refine StalkKaehler.germ_comp_specStructureMap_of_top _ ?_ U hy
  rw [RingHom.algebraMap_toAlgebra, Scheme.Hom.specStructureMap, Scheme.globalSectionsRingHom,
    TopCat.Presheaf.Γgerm, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp,
    ← CommRingCat.hom_comp]
  ext a
  simp only [Scheme.Hom.appLE]
  simp
  exact (f.germ_stalkMap_apply ⊤ y trivial _).symm

end Curve

section ClosedPoint

variable (κ : Type u) [Field κ] {X Y : Scheme.{u}} [X.Over (Spec (.of κ))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of κ))] [IsIntegral X] [IsIntegral Y]
  [Y.Over (Spec (.of κ))] [SmoothOfRelativeDimension 1 (Y ↘ Spec (.of κ))]
  (f : Y ⟶ X) [f.IsOver (Spec (.of κ))] [IsFinite f] (hgen : f (genericPoint Y) = genericPoint X)
  (hsep : letI := (f.functionFieldMap hgen).hom.toAlgebra
      Algebra.IsSeparable X.functionField Y.functionField)
  [IsLocallyNoetherian Y]

include hsep in
/-- **The zero scheme of `f^* Ω¹_{X/κ} ⟶ Ω¹_{Y/κ}` at a closed point.** For `κ` perfect and `y`
a closed point of `Y`, the order at `y` of the zero scheme of `differentialsPullbackHom` is the
different exponent `δ_y`, and the morphism is nonzero. -/
theorem ordAt_zeroLocus_differentialsPullbackHom [PerfectField κ] (y : Y) (hy : IsClosed {y}) :
    (differentialsPullbackHom (X ↘ Spec (.of κ)) f).zeroLocus.ordAt y =
        curveDifferentExponent f y ∧
      differentialsPullbackHom (X ↘ Spec (.of κ)) f ≠ 0 := by
  have : SmoothOfRelativeDimension 1 (f ≫ X ↘ Spec (.of κ)) := by
    rw [comp_over]; infer_instance
  have := (X ↘ Spec (.of κ)).isInvertible_relativeDifferentials
  have := (f ≫ X ↘ Spec (.of κ)).isInvertible_relativeDifferentials
  have : SheafOfModules.IsInvertible.{u, u, u}
      ((Scheme.Modules.pullback f).obj (X ↘ Spec (.of κ)).relativeDifferentials) :=
    .pullback inferInstance
  obtain ⟨⟨V, hV⟩, hyV, -, eX, heX⟩ := Scheme.Modules.exists_isFreeGenerator
    (X ↘ Spec (.of κ)).relativeDifferentials (x := f y) (W := ⊤) trivial
  replace hV : IsAffineOpen V := hV
  replace hyV : f y ∈ V := hyV
  have hV' : IsAffineOpen (f ⁻¹ᵁ V) := hV.preimage f
  have hη := Scheme.Modules.IsFreeGenerator.pullback_unit_app f heX
  obtain ⟨⟨U', hU'⟩, hyU', hU'le, eN, hN⟩ := Scheme.Modules.exists_isFreeGenerator
    (f ≫ X ↘ Spec (.of κ)).relativeDifferentials (x := y) (W := f ⁻¹ᵁ V) hyV
  replace hU' : IsAffineOpen U' := hU'
  replace hyU' : y ∈ U' := hyU'
  replace hU'le : U' ≤ f ⁻¹ᵁ V := hU'le
  have hM := hη.map hU'le
  set eM := ((Scheme.Modules.pullback f).obj (X ↘ Spec (.of κ)).relativeDifferentials).presheaf.map
    (homOfLE hU'le).op (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app _).app V eX)
    with heM
  obtain ⟨b, hb⟩ := hN.exists_smul_eq ((differentialsPullbackHom (X ↘ Spec (.of κ)) f).app U' eM)
  have hφ : (differentialsPullbackHom (X ↘ Spec (.of κ)) f).app U' eM =
      (f ≫ X ↘ Spec (.of κ)).relativeDifferentials.presheaf.map (homOfLE hU'le).op
        (differentialsPushforwardApp (X ↘ Spec (.of κ)) f V eX) := by
    rw [heM]
    exact (Scheme.Modules.Hom.app_presheaf_map (differentialsPullbackHom _ f) (homOfLE hU'le)
      _).trans (congrArg _ (differentialsPullbackHom_app_unit _ f V eX))
  have hideal := Scheme.Modules.Hom.ideal_zeroLocus _ ⟨U', hU'⟩ hM hN hb.symm
  -- The local algebra at `y`.
  let : Algebra (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) := (f.stalkMap y).hom.toAlgebra
  let : Algebra κ (X.presheaf.stalk (f y)) := stalkAlgebraOver κ X (f y)
  let : Algebra κ (Y.presheaf.stalk y) :=
    ((algebraMap (X.presheaf.stalk (f y)) (Y.presheaf.stalk y)).comp
      (algebraMap κ (X.presheaf.stalk (f y)))).toAlgebra
  have : IsScalarTower κ (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hκX : ∀ (U : X.Opens) (hU : f y ∈ U),
      (X.presheaf.germ U (f y) hU).hom.comp ((X ↘ Spec (.of κ)).specStructureMap U).hom =
        algebraMap κ (X.presheaf.stalk (f y)) :=
    fun U hU ↦ germ_comp_specStructureMap_eq_stalkAlgebraOver κ (f y) U hU
  have hκY : ∀ (U : Y.Opens) (hU : y ∈ U),
      (Y.presheaf.germ U y hU).hom.comp ((f ≫ X ↘ Spec (.of κ)).specStructureMap U).hom =
        algebraMap κ (Y.presheaf.stalk y) :=
    fun U hU ↦ germ_comp_specStructureMap_comp κ f y U hU
  obtain ⟨e, he⟩ := StalkKaehler.exists_linearEquiv_of_isFreeGenerator (hκ := hκY) hU' hyU' hN
  have hω := StalkKaehler.span_toStalk_eq_top (hκ := hκX) hV hyV heX
  have hc : map κ κ (X.presheaf.stalk (f y)) (Y.presheaf.stalk y)
      (StalkKaehler.toStalk _ hκX V hV hyV eX) = Y.presheaf.germ U' y hyU' b • e 1 := by
    rw [he, ← StalkKaehler.toStalk_smul, hb, hφ, StalkKaehler.toStalk_map hV' hU' hU'le hyU',
      toStalk_differentialsPushforwardHom rfl hκX hκY hV hV' hyV (hU'le hyU')]
  have hlen := KaehlerMapBaseChange.length_quot_range_mapBaseChange_eq_ord κ
    (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) hω e hc
  have h3 := stalkDifferentialsCokernelLength_eq κ f hgen hsep y hy
  change Module.length (Y.presheaf.stalk y) (Ω[Y.presheaf.stalk y⁄κ] ⧸ LinearMap.range
    (KaehlerDifferential.mapBaseChange κ (X.presheaf.stalk (f y)) (Y.presheaf.stalk y))) = _
    at h3
  rw [hlen] at h3
  have hcoh := Scheme.coheight_eq_one_of_isClosed (Y ↘ Spec (.of κ)) hy
  have := Scheme.isDiscreteValuationRing_stalk_of_coheight_eq_one (Y ↘ Spec (.of κ)) hcoh
  have hb0 : Y.presheaf.germ U' y hyU' b ≠ 0 := by
    intro h
    rw [h, Ring.ord_eq_addVal, AddValuation.map_zero] at h3
    exact ENat.top_ne_natCast _ h3
  refine ⟨?_, ?_⟩
  · have : Nonempty U' := ⟨⟨y, hyU'⟩⟩
    rw [Scheme.IdealSheafData.ordAt_eq _ hyU' hideal,
      ← Scheme.algebraMap_germ_eq_germToFunctionField Y hyU' b, Scheme.ord_algebraMap_stalk hcoh hb0,
      h3, ENat.toNat_natCast]
  · intro h0
    apply hb0
    have hb' : b • eN = (0 : Γ(Y, U')) • eN := by
      rw [hb, h0, zero_smul]
      rfl
    rw [hN.smul_left_injective hb', map_zero]

end ClosedPoint

/-- **Differentials and the different**: a proof of `CurveDifferentialsDifferentStatement`. The
closed-point lengths use the curve case of Serre, *Local Fields*, III §7, Prop. 14; the
line-bundle isomorphism comes from the zero scheme of `f^* Ω¹_{X/κ} ⟶ Ω¹_{Y/κ}`. -/
theorem curveDifferentialsDifferentStatement : CurveDifferentialsDifferentStatement.{u} := by
  intro κ _ _ X Y _ _ _ _ _ _ _ _ _ _ f _ _ hgen hsep
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of κ))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of κ))
  have : IsNoetherian Y := {}
  have : SmoothOfRelativeDimension 1 (f ≫ X ↘ Spec (.of κ)) := by
    rw [comp_over]; infer_instance
  have := (X ↘ Spec (.of κ)).isInvertible_relativeDifferentials
  have := (f ≫ X ↘ Spec (.of κ)).isInvertible_relativeDifferentials
  have : SheafOfModules.IsInvertible.{u, u, u}
      ((Scheme.Modules.pullback f).obj (X ↘ Spec (.of κ)).relativeDifferentials) :=
    .pullback inferInstance
  obtain ⟨y₀, -, hy₀⟩ := isClosed_univ.exists_closed_singleton (X := Y) Set.univ_nonempty
  have hφ := (ordAt_zeroLocus_differentialsPullbackHom κ f hgen hsep y₀ hy₀).2
  have hinv := Scheme.Modules.Hom.isInvertible_zeroLocus hφ
  obtain ⟨E, hE⟩ := hinv.exists_eq_idealSheaf (Y ↘ Spec (.of κ))
  have hEy (P : closedPoints Y) : E P = curveDifferentExponent f P.1 := by
    have h := (ordAt_zeroLocus_differentialsPullbackHom κ f hgen hsep P.1 P.2).1
    rw [hE, Scheme.Divisor.ordAt_idealSheaf (Y ↘ Spec (.of κ)) E P] at h
    exact_mod_cast h
  have hD : curveDifferent f = E := by
    have hfin : (Function.support fun P : closedPoints Y ↦ curveDifferentExponent f P.1).Finite :=
      E.support.finite_toSet.subset fun P hP ↦ by
        rw [Function.mem_support] at hP
        rw [Finset.mem_coe, Finsupp.mem_support_iff, hEy]
        exact hP
    rw [curveDifferent, dite_eq_left_of_eq_true (eq_true hfin)]
    ext P
    rw [Finsupp.ofSupportFinite_coe, hEy]
  have hlen (P : closedPoints Y) :
      stalkDifferentialsCokernelLength κ f P.1 = curveDifferentExponent f P.1 :=
    stalkDifferentialsCokernelLength_eq κ f hgen hsep P.1 P.2
  refine ⟨fun y ↦ isStalkDifferentialsMapInjective_of_isSeparable κ f hgen hsep y, ?_, hlen,
    fun P ↦ by rw [hD, hEy], ?_⟩
  · refine ((E.support.finite_toSet.image Subtype.val).union
      (Set.finite_singleton (genericPoint Y))).subset fun y hy ↦ ?_
    by_cases hyc : IsClosed {y}
    · refine Or.inl ⟨⟨y, hyc⟩, ?_, rfl⟩
      rw [Finset.mem_coe, Finsupp.mem_support_iff, hEy]
      intro h0
      apply hy
      rw [hlen ⟨y, hyc⟩, h0, Nat.cast_zero]
    · refine Or.inr (Scheme.eq_genericPoint_of_coheight_eq_zero ?_)
      have h1 := Scheme.coheight_le_one_of_smoothOfRelativeDimension_one (Y ↘ Spec (.of κ)) y
      have h2 : Order.coheight y ≠ 1 := fun h ↦
        hyc (Scheme.isClosed_of_coheight_eq_one (Y ↘ Spec (.of κ)) h)
      have h3 : Order.coheight y < 1 := lt_of_le_of_ne h1 h2
      exact Order.lt_one_iff.mp h3
  · obtain ⟨e⟩ := Scheme.Modules.Hom.nonempty_iso_dual_toModules_tensorObj
      (differentialsPullbackHom (X ↘ Spec (.of κ)) f) hinv
    refine ⟨eqToIso (by rw [comp_over]) ≪≫ e ≪≫ eqToIso (by rw [hE, hD]) ≪≫ β_ _ _⟩

end Langlands.Henniart.Laumon
