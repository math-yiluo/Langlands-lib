import Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisor
import Langlands.AlgebraicGeometry.Modules.ProperFormalCoherentExistenceOfFLT
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Langlands.CommutativeAlgebra.FibrewiseRegularFlat

/-! # Ideal sheaves with regular local equations are effective Cartier -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard.LocalEquationCartier

open StructureKernelModule

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- Restriction maps between affine opens are flat. -/
lemma flat_res {U W : X.affineOpens} (h : W.1 ≤ U.1) :
    (X.presheaf.map (homOfLE h).op).hom.Flat := by
  have := HasRingHomProperty.appLE (P := @Flat) (𝟙 X) inferInstance U W h
  have heq : (𝟙 X : X ⟶ X).appLE U.1 W.1 h = X.presheaf.map (homOfLE h).op := by
    simp [Scheme.Hom.appLE]
  rwa [heq] at this

/-- Over an open `W` inside an affine open `U`, the restriction of an element of the ideal over
`U` is killed by the closed immersion. -/
lemma subschemeι_app_res_eq_zero {U : X.affineOpens} {s : Γ(X, U.1)} (hs : s ∈ I.ideal U)
    (W : X.Opens) (hW : W ≤ U.1) :
    I.subschemeι.app W (X.presheaf.map (homOfLE hW).op s) = 0 := by
  have h0 : I.subschemeι.app U.1 s = 0 := by
    rw [← RingHom.mem_ker, I.ker_subschemeι_app U]
    exact hs
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.naturality, ConcreteCategory.comp_apply, h0,
    map_zero]

variable {U : X.affineOpens} (s : Γ(X, U.1)) (hs : s ∈ I.ideal U)

/-- The restriction of `s` to an open of `U`. -/
abbrev sRes (V : (U.1 : X.Opens).toScheme.Opens) : Γ(X, (U.1 : X.Opens).ι ''ᵁ V) :=
  X.presheaf.map (homOfLE (show (U.1 : X.Opens).ι ''ᵁ V ≤ U.1 from
    (Scheme.Hom.image_le_opensRange _ _).trans (by simp))).op s

/-- Multiplication by `s` on sections over an open of `U`, landing in the ideal. -/
def mulFun (V : (U.1 : X.Opens).toScheme.Opens) :
    Γ(X, (U.1 : X.Opens).ι ''ᵁ V) →+ RingHom.ker (I.subschemeι.app ((U.1 : X.Opens).ι ''ᵁ V)).hom where
  toFun a := ⟨a * sRes s V, by
    rw [RingHom.mem_ker, map_mul, subschemeι_app_res_eq_zero I hs, mul_zero]⟩
  map_zero' := Subtype.ext (zero_mul _)
  map_add' a b := Subtype.ext (add_mul _ _ _)

lemma mulFun_val (V : (U.1 : X.Opens).toScheme.Opens) (a : Γ(X, (U.1 : X.Opens).ι ''ᵁ V)) :
    (mulFun I s hs V a).1 = a * sRes s V := rfl

/-- Multiplication by an element of the ideal, from the structure sheaf of `U` to the restricted
ideal module. -/
def mulEquation : SheafOfModules.unit (U.1 : X.Opens).toScheme.ringCatSheaf ⟶
    (kernelModule I.subschemeι).restrict (U.1 : X.Opens).ι :=
  ⟨PresheafOfModules.homMk
    { app := fun V ↦ AddCommGrpCat.ofHom (mulFun I s hs V.unop)
      naturality := by
        intro V V' i
        ext a
        refine Subtype.ext ?_
        show X.presheaf.map ((U.1 : X.Opens).ι.opensFunctor.map i.unop).op
            (show Γ(X, (U.1 : X.Opens).ι ''ᵁ V.unop) from a) * sRes s V'.unop =
          X.presheaf.map ((U.1 : X.Opens).ι.opensFunctor.map i.unop).op
            ((show Γ(X, (U.1 : X.Opens).ι ''ᵁ V.unop) from a) * sRes s V.unop)
        rw [map_mul]
        congr 1
        rw [← ConcreteCategory.comp_apply (X.presheaf.map _) (X.presheaf.map _),
          ← Functor.map_comp]
        rfl }
    (by
      intro V r a
      refine Subtype.ext ?_
      show ((show Γ(X, (U.1 : X.Opens).ι ''ᵁ V.unop) from r) *
        (show Γ(X, (U.1 : X.Opens).ι ''ᵁ V.unop) from a)) * sRes s V.unop =
          ((U.1 : X.Opens).ι.appIso V.unop).inv r *
            ((show Γ(X, (U.1 : X.Opens).ι ''ᵁ V.unop) from a) * sRes s V.unop)
      rw [Scheme.Opens.ι_appIso, Iso.refl_inv]
      rw [mul_assoc]
      rfl)⟩

/-- Over affine opens of `U`, multiplication by a regular generator of the ideal is bijective. -/
lemma bijective_mulEquation (hgen : I.ideal U = Ideal.span {s}) (hreg : IsSMulRegular Γ(X, U.1) s)
    (V : (U.1 : X.Opens).toScheme.Opens) (hV : IsAffineOpen V) :
    Function.Bijective (Scheme.Modules.Hom.app (mulEquation I s hs) V) := by
  let W : X.affineOpens := ⟨(U.1 : X.Opens).ι ''ᵁ V, hV.image_of_isOpenImmersion _⟩
  have hWU : W.1 ≤ U.1 := (Scheme.Hom.image_le_opensRange _ _).trans (by simp)
  let ρ := (X.presheaf.map (homOfLE hWU).op).hom
  let _ := ρ.toAlgebra
  have : Module.Flat Γ(X, U.1) Γ(X, W.1) := flat_res hWU
  have hregW : IsSMulRegular Γ(X, W.1) (sRes s V) := hreg.of_flat
  constructor
  · intro a b hab
    have h := congrArg Subtype.val hab
    change (show Γ(X, W.1) from a) * sRes s V = (show Γ(X, W.1) from b) * sRes s V at h
    rw [mul_comm, mul_comm (show Γ(X, W.1) from b)] at h
    exact hregW h
  · intro k
    have hk : k.1 ∈ I.ideal W := by
      rw [← I.ker_subschemeι_app W]
      exact k.2
    rw [← I.map_ideal hWU, hgen, Ideal.map_span, Set.image_singleton,
      Ideal.mem_span_singleton'] at hk
    obtain ⟨a, ha⟩ := hk
    exact ⟨a, Subtype.ext ha⟩

/-- **Local regular equations give effective Cartier ideals.** If every point has an affine
neighbourhood on which the ideal is generated by one regular element, the ideal is effective
Cartier. -/
theorem isEffectiveCartierIdeal_of_local
    (h : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ s : Γ(X, U.1),
      I.ideal U = Ideal.span {s} ∧ IsSMulRegular Γ(X, U.1) s) :
    IsEffectiveCartierIdeal I := by
  intro x
  obtain ⟨U, hx, s, hgen, hreg⟩ := h x
  have hs : s ∈ I.ideal U := hgen ▸ Ideal.mem_span_singleton_self s
  have : IsIso (mulEquation I s hs) :=
    Langlands.AlgebraicGeometry.Modules.ProperFormalCoherentExistenceOfFLT.isIso_of_bijective_of_basis
      (P := fun V : (U.1 : X.Opens).toScheme.Opens => IsAffineOpen V)
      (fun y V hy => by
        obtain ⟨W, hW, hyW, hWV⟩ := exists_isAffineOpen_mem_and_subset hy
        exact ⟨W, hW, hyW, hWV⟩)
      _ (fun V hV => bijective_mulEquation I s hs hgen hreg V hV)
  exact ⟨U.1, hx, ⟨(asIso (mulEquation I s hs)).symm⟩⟩

/-- **Flatness of the subscheme from local data.** If around every point there are affine opens
`U` of `X` and `V` of `S` (over each other) such that `Γ(S, V) → Γ(X, U) ⧸ I(U)` is flat, then the
closed subscheme of `I` is flat over `S`. -/
theorem flat_subscheme_of_local {S : Scheme.{u}} (f : X ⟶ S)
    (h : ∀ x : X, ∃ (V : S.affineOpens) (U : X.affineOpens) (_ : x ∈ U.1) (e : U.1 ≤ f ⁻¹ᵁ V.1),
      ((Ideal.Quotient.mk (I.ideal U)).comp (f.appLE V.1 U.1 e).hom).Flat) :
    Flat (I.subschemeι ≫ f) := by
  have hQ : RingHom.StableUnderCompositionWithLocalizationAwaySource RingHom.Flat := by
    intro R S T _ _ _ _ r _ g hg
    exact RingHom.Flat.comp (RingHom.Flat.holdsForLocalizationAway S r) hg
  rw [HasRingHomProperty.iff_exists_appLE (P := @Flat) hQ]
  intro x
  obtain ⟨V, U, hx, e, hflat⟩ := h (I.subschemeι x)
  have hU' : IsAffineOpen (I.subschemeι ⁻¹ᵁ U.1) := U.2.preimage _
  refine ⟨V, ⟨_, hU'⟩, hx, fun y hy => e hy, ?_⟩
  have heq : (I.subschemeι ≫ f).appLE V.1 (I.subschemeι ⁻¹ᵁ U.1) (fun y hy => e hy) =
      f.appLE V.1 U.1 e ≫ CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U)) ≫
        (I.subschemeObjIso U).inv := by
    rw [← I.subschemeι_app U, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  rw [heq, CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.comp_assoc, CommRingCat.hom_ofHom]
  exact RingHom.Flat.comp hflat (RingHom.Flat.of_bijective
    (ConcreteCategory.bijective_of_isIso (I.subschemeObjIso U).inv))

/-- **Relative effective Cartier ideals from local equations.** If around every point the ideal
is generated by one regular element whose quotient is flat over the base, the ideal is relative
effective Cartier. -/
theorem isRelativeEffectiveCartierIdeal_of_local {S : Scheme.{u}} (f : X ⟶ S)
    (h : ∀ x : X, ∃ (V : S.affineOpens) (U : X.affineOpens) (_ : x ∈ U.1) (e : U.1 ≤ f ⁻¹ᵁ V.1)
      (s : Γ(X, U.1)), I.ideal U = Ideal.span {s} ∧ IsSMulRegular Γ(X, U.1) s ∧
        ((Ideal.Quotient.mk (Ideal.span {s})).comp (f.appLE V.1 U.1 e).hom).Flat) :
    IsRelativeEffectiveCartierIdeal f I := by
  refine ⟨isEffectiveCartierIdeal_of_local I fun x => ?_, flat_subscheme_of_local I f fun x => ?_⟩
  · obtain ⟨V, U, hx, e, s, hgen, hreg, -⟩ := h x
    exact ⟨U, hx, s, hgen, hreg⟩
  · obtain ⟨V, U, hx, e, s, hgen, -, hflat⟩ := h x
    refine ⟨V, U, hx, e, ?_⟩
    rw [hgen]
    exact hflat

/-- **Kleiman's Lemma 3.4, (iii) ⇒ (i).** Let `f : X ⟶ S` be flat with `X` locally noetherian.
If around every point the ideal is generated by one element that is regular in every fibre local
ring, then the ideal is relative effective Cartier. -/
theorem isRelativeEffectiveCartierIdeal_of_fibreRegular {S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [IsLocallyNoetherian X]
    (h : ∀ x : X, ∃ (V : S.affineOpens) (U : X.affineOpens) (_ : x ∈ U.1) (e : U.1 ≤ f ⁻¹ᵁ V.1)
      (s : Γ(X, U.1)), I.ideal U = Ideal.span {s} ∧
        letI := (f.appLE V.1 U.1 e).hom.toAlgebra
        ∀ (P : Ideal Γ(X, U.1)) [P.IsMaximal], IsSMulRegular (Localization.AtPrime P ⧸
          (P.comap (algebraMap Γ(S, V.1) Γ(X, U.1))).map
            (algebraMap Γ(S, V.1) (Localization.AtPrime P)))
          (algebraMap Γ(X, U.1) (Localization.AtPrime P) s)) :
    IsRelativeEffectiveCartierIdeal f I := by
  apply isRelativeEffectiveCartierIdeal_of_local I f
  intro x
  obtain ⟨V, U, hx, e, s, hgen, hfib⟩ := h x
  let _ := (f.appLE V.1 U.1 e).hom.toAlgebra
  have : Module.Flat Γ(S, V.1) Γ(X, U.1) :=
    HasRingHomProperty.appLE (P := @Flat) f inferInstance V U e
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  obtain ⟨hreg, hflat⟩ :=
    Langlands.CommutativeAlgebra.FibrewiseRegular.regular_and_flat_quotient s hfib
  refine ⟨V, U, hx, e, s, hgen, hreg, ?_⟩
  rw [RingHom.Flat]
  exact hflat

end Langlands.AlgebraicGeometry.Picard.LocalEquationCartier
