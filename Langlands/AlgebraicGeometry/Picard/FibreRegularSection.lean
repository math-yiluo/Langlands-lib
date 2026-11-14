import Langlands.AlgebraicGeometry.Picard.SectionZeroIdealDual
import Langlands.AlgebraicGeometry.Picard.LocalEquationCartier
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Langlands.CommutativeAlgebra.FibreLocalDomain

/-! # Sections not vanishing on integral fibres

Let `f : X ⟶ S` be geometrically integral. For an affine open `U ⊆ f⁻¹ V` over an affine open
`V` of `S` and a field `K` over `Γ(S, V)`, the ring `Γ(X, U) ⊗ K` is a domain (or zero). If a
section `σ` of a line bundle on `X` does not vanish on the fibre `X_K`, its local equation `s` on
`U` satisfies `s ⊗ 1 ≠ 0`. These are the inputs of the fibrewise criterion for relative effective
Cartier divisors. -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct
open Langlands.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.SectionZeroIdeal

section Integral

variable {X : Scheme.{u}} [IsIntegral X] {L : LineBundle X} {σ : Γ(L.obj, ⊤)}

/-- **On an integral scheme, a section whose zero ideal vanishes on a nonempty affine open is
zero.** -/
theorem eq_zero_of_ideal_eq_bot {W : X.affineOpens} (hW : (W.1 : Set X).Nonempty)
    (h : (zeroIdeal L σ).ideal W = ⊥) : σ = 0 := by
  obtain ⟨x, hxW⟩ := hW
  obtain ⟨W₀, ⟨hW₀a, W₀', hW₀', ⟨t₀⟩⟩, hxW₀, hW₀W⟩ := frameOpen_basis L x W.1 hxW
  let i₀ : W₀ ⟶ W₀' := homOfLE hW₀'
  -- `σ` vanishes on `W₀`
  have h₀ : res L σ W₀ = 0 := by
    have hi : (zeroIdeal L σ).ideal ⟨W₀, hW₀a⟩ = ⊥ := by
      rw [← (zeroIdeal L σ).map_ideal (U := ⟨W₀, hW₀a⟩) (V := W) hW₀W, h, Ideal.map_bot]
    rw [zeroIdeal_ideal_of_equiv L σ ⟨W₀, hW₀a⟩ (coordEquiv t₀ i₀),
      Ideal.span_singleton_eq_bot] at hi
    rw [← (coordEquiv t₀ i₀).map_eq_zero_iff]
    exact hi
  -- hence on a frame open around every point
  have hloc : ∀ y : X, ∃ (Wy : X.Opens), y ∈ Wy ∧ res L σ Wy = 0 := by
    intro y
    obtain ⟨Wy, ⟨-, Wy', hWy', ⟨ty⟩⟩, hyW, -⟩ := frameOpen_basis L y ⊤ trivial
    refine ⟨Wy, hyW, ?_⟩
    let iy : Wy ⟶ Wy' := homOfLE hWy'
    have hne : Nonempty (Wy ⊓ W₀ : X.Opens) := by
      obtain ⟨z, hz⟩ := nonempty_preirreducible_inter Wy.2 W₀.2 ⟨y, hyW⟩ ⟨x, hxW₀⟩
      exact ⟨⟨z, hz⟩⟩
    rw [← coord_smul_trivGen ty iy (res L σ Wy)]
    suffices hc : coord ty iy (res L σ Wy) = 0 by rw [hc, zero_smul]
    apply map_injective_of_isIntegral X (homOfLE (inf_le_left : Wy ⊓ W₀ ≤ Wy))
    rw [map_zero]
    -- the restriction of the coordinate is the coordinate of the restriction
    have hr : L.obj.presheaf.map (homOfLE (inf_le_left : Wy ⊓ W₀ ≤ Wy)).op (res L σ Wy) = 0 := by
      rw [res_map, ← res_map σ (inf_le_right : Wy ⊓ W₀ ≤ W₀), h₀, map_zero]
    have hcoord := internalHomEval_restrict L.obj (Langlands.SchemeModule.structureModule X)
      (homOfLE (inf_le_left : Wy ⊓ W₀ ≤ Wy)) (dualGen ty iy) (res L σ Wy)
    change X.presheaf.map (homOfLE inf_le_left).op (coord ty iy (res L σ Wy)) = 0
    erw [← hcoord, hr, map_zero]
  choose Wy hyW hWy using hloc
  refine TopCat.Sheaf.eq_of_locally_eq' (F := ⟨L.obj.presheaf, L.obj.isSheaf⟩) Wy ⊤
    (fun _ => homOfLE le_top) (fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hyW y⟩) _ _
    fun y => ?_
  change res L σ (Wy y) = L.obj.presheaf.map _ 0
  rw [hWy y, map_zero]

end Integral

section Fibre

variable {S X : Scheme.{u}} (f : X ⟶ S) {V : S.affineOpens} {U : X.affineOpens}
  (e : U.1 ≤ f ⁻¹ᵁ V.1) (K : Type u) [Field K] [Algebra Γ(S, V.1) K]

/-- The point `Spec K ⟶ S` through the affine open `V`. -/
abbrev fibrePoint : Spec (.of K) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V.1) K)) ≫ V.2.fromSpec

/-- The affine chart `Spec (Γ(X, U) ⊗ K)` of the fibre, as a pullback. -/
abbrev fibreChart :=
  letI := (f.appLE V.1 U.1 e).hom.toAlgebra
  pullback (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V.1) Γ(X, U.1))))
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V.1) K)))

lemma fibreChart_w :
    letI := (f.appLE V.1 U.1 e).hom.toAlgebra
    Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V.1) Γ(X, U.1))) ≫ V.2.fromSpec =
      U.2.fromSpec ≫ f := by
  letI := (f.appLE V.1 U.1 e).hom.toAlgebra
  rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom]
  exact IsAffineOpen.SpecMap_appLE_fromSpec f V.2 U.2 e

/-- The open immersion of the affine chart into the fibre `X ×_S Spec K`. -/
def fibreChartι : fibreChart f e K ⟶ pullback f (fibrePoint K (V := V)) :=
  letI := (f.appLE V.1 U.1 e).hom.toAlgebra
  pullback.map _ _ _ _ U.2.fromSpec (𝟙 _) V.2.fromSpec (fibreChart_w f e) (by simp)

instance : IsOpenImmersion (fibreChartι f e K) := by
  letI := (f.appLE V.1 U.1 e).hom.toAlgebra
  unfold fibreChartι
  infer_instance

/-- **Affine pieces of geometrically integral fibres are domains.** -/
theorem isDomain_tensor [GeometricallyIntegral f]
    [Nontrivial (letI := (f.appLE V.1 U.1 e).hom.toAlgebra; Γ(X, U.1) ⊗[Γ(S, V.1)] K)] :
    letI := (f.appLE V.1 U.1 e).hom.toAlgebra
    IsDomain (Γ(X, U.1) ⊗[Γ(S, V.1)] K) := by
  letI := (f.appLE V.1 U.1 e).hom.toAlgebra
  have hint : IsIntegral (pullback f (fibrePoint K (V := V))) :=
    GeometricallyIntegral.geometrically_isIntegral (f := f) (fibrePoint K (V := V))
      (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
  let eZ := pullbackSpecIso Γ(S, V.1) Γ(X, U.1) K
  have : Nonempty (fibreChart f e K) := by
    obtain ⟨x⟩ : Nonempty (Spec (.of (Γ(X, U.1) ⊗[Γ(S, V.1)] K))) := inferInstance
    exact ⟨eZ.inv x⟩
  have : IsIntegral (fibreChart f e K) := isIntegral_of_isOpenImmersion (fibreChartι f e K)
  have : IsIntegral (Spec (.of (Γ(X, U.1) ⊗[Γ(S, V.1)] K))) := IsIntegral.of_isIso eZ.hom
  exact (affine_isIntegral_iff _).1 this

/-- The local equation, pulled back to the affine chart of the fibre, is `s ⊗ 1`. -/
lemma appLE_fibreChart_eq_zero (s : Γ(X, U.1))
    (h0 : letI := (f.appLE V.1 U.1 e).hom.toAlgebra; s ⊗ₜ[Γ(S, V.1)] (1 : K) = 0)
    (hle : (⊤ : (fibreChart f e K).Opens) ≤ (pullback.fst _ _ ≫ U.2.fromSpec) ⁻¹ᵁ U.1) :
    ((pullback.fst _ _ ≫ U.2.fromSpec).appLE U.1 ⊤ hle) s = 0 := by
  letI := (f.appLE V.1 U.1 e).hom.toAlgebra
  rw [Scheme.Hom.comp_appLE, CommRingCat.comp_apply, U.2.fromSpec_app_self_apply,
    ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  let eZ := pullbackSpecIso Γ(S, V.1) Γ(X, U.1) K
  let φ : Γ(X, U.1) ⟶ CommRingCat.of (Γ(X, U.1) ⊗[Γ(S, V.1)] K) :=
    CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  have hfst : pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V.1) Γ(X, U.1))))
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V.1) K))) = eZ.hom ≫ Spec.map φ := by
    rw [← pullbackSpecIso_inv_fst, Iso.hom_inv_id_assoc]
  have hc : ∀ {g₁ g₂ : fibreChart f e K ⟶ Spec Γ(X, U.1)} (h : g₁ = g₂) (e₁ e₂),
      g₁.appLE ⊤ ⊤ e₁ = g₂.appLE ⊤ ⊤ e₂ := by
    intro g₁ g₂ h e₁ e₂; subst h; rfl
  rw [hc hfst _ (by simp), Scheme.Hom.comp_appLE, CommRingCat.comp_apply]
  have hnat := congrArg (fun F => (ConcreteCategory.hom F) s) (Scheme.ΓSpecIso_inv_naturality φ)
  simp only [CommRingCat.comp_apply] at hnat
  change (eZ.hom.appLE _ ⊤ _) ((Spec.map φ).appTop ((Scheme.ΓSpecIso Γ(X, U.1)).inv s)) = 0
  rw [← hnat]
  change (eZ.hom.appLE _ ⊤ _) ((Scheme.ΓSpecIso _).inv (s ⊗ₜ[Γ(S, V.1)] (1 : K))) = 0
  rw [h0, map_zero, map_zero]

/-- **A section not vanishing on the fibre over `K` has local equation `s` with `s ⊗ 1 ≠ 0`.** -/
theorem tmul_ne_zero [GeometricallyIntegral f] {L : LineBundle X} (σ : Γ(L.obj, ⊤))
    (s : Γ(X, U.1)) (hs : (zeroIdeal L σ).ideal U = Ideal.span {s})
    [Nontrivial (letI := (f.appLE V.1 U.1 e).hom.toAlgebra; Γ(X, U.1) ⊗[Γ(S, V.1)] K)]
    (hK : pullbackSection (pullback.fst f (fibrePoint K (V := V))) L σ ≠ 0) :
    letI := (f.appLE V.1 U.1 e).hom.toAlgebra
    s ⊗ₜ[Γ(S, V.1)] (1 : K) ≠ 0 := by
  letI := (f.appLE V.1 U.1 e).hom.toAlgebra
  intro h0
  apply hK
  have hint : IsIntegral (pullback f (fibrePoint K (V := V))) :=
    GeometricallyIntegral.geometrically_isIntegral (f := f) (fibrePoint K (V := V))
      (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
  let eZ := pullbackSpecIso Γ(S, V.1) Γ(X, U.1) K
  have : IsAffine (fibreChart f e K) := IsAffine.of_isIso eZ.hom
  let j := fibreChartι f e K
  let W : (pullback f (fibrePoint K (V := V))).affineOpens :=
    ⟨j ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion j⟩
  have hWne : Set.Nonempty ((W.1 : (pullback f (fibrePoint K (V := V))).Opens) :
      Set ↥(pullback f (fibrePoint K (V := V)))) := by
    obtain ⟨x⟩ : Nonempty (Spec (.of (Γ(X, U.1) ⊗[Γ(S, V.1)] K))) := inferInstance
    exact ⟨j.base (eZ.inv.base x), ⟨eZ.inv.base x, trivial, rfl⟩⟩
  apply eq_zero_of_ideal_eq_bot hWne
  rw [← zeroIdeal_comap]
  set J := (zeroIdeal L σ).comap (pullback.fst f (fibrePoint K (V := V)))
  -- the pullback of `J` to the chart vanishes
  have hg : j ≫ pullback.fst f (fibrePoint K (V := V)) = pullback.fst _ _ ≫ U.2.fromSpec :=
    pullback.lift_fst _ _ _
  have hle : (⊤ : (fibreChart f e K).Opens) ≤ (pullback.fst _ _ ≫ U.2.fromSpec) ⁻¹ᵁ U.1 := by
    intro z _
    change U.2.fromSpec.base _ ∈ U.1
    exact U.2.range_fromSpec.le ⟨_, rfl⟩
  have hJ : (J.comap j).ideal ⟨⊤, isAffineOpen_top _⟩ = ⊥ := by
    rw [← Scheme.IdealSheafData.comap_comp, hg,
      Scheme.IdealSheafData.ideal_comap_of_le _ _ U ⟨⊤, isAffineOpen_top _⟩ hle, hs,
      Ideal.map_span, Set.image_singleton, appLE_fibreChart_eq_zero f e K s h0 hle,
      Ideal.span_singleton_eq_bot.mpr rfl]
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at hJ
  have hJ' : (J.ideal W).comap (j.appIso ⊤).inv.hom = ⊥ := hJ
  rw [eq_bot_iff]
  intro x hx
  have hx' : (j.appIso ⊤).hom x ∈ (J.ideal W).comap (j.appIso ⊤).inv.hom := by
    rw [Ideal.mem_comap]
    change ((j.appIso ⊤).hom ≫ (j.appIso ⊤).inv) x ∈ _
    rw [Iso.hom_inv_id]
    exact hx
  rw [hJ', Ideal.mem_bot] at hx'
  rw [Ideal.mem_bot]
  have := congrArg (j.appIso ⊤).inv hx'
  change ((j.appIso ⊤).hom ≫ (j.appIso ⊤).inv) x = _ at this
  rw [Iso.hom_inv_id, map_zero] at this
  exact this

end Fibre

section Assembly

lemma isFrameOn_trivGen {X : Scheme.{u}} {M : X.Modules} {W V : X.Opens}
    (t : M.restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf) (i : V ⟶ W) :
    Scheme.Modules.IsFrameOn (trivGen t i) V := by
  intro W' hW'V _
  have h : M.presheaf.map (homOfLE hW'V).op (trivGen t i) = trivGen t (homOfLE hW'V ≫ i) :=
    trivGen_restrict t i (homOfLE hW'V)
  simp only [h]
  exact (coordEquiv t (homOfLE hW'V ≫ i)).symm.bijective

/-- **Sections not vanishing on any geometric fibre of a flat geometrically integral morphism are
regular, and their zero loci are relative effective Cartier divisors.** -/
theorem isRegularSection_and_isRelativeEffectiveCartierIdeal {S X : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsLocallyNoetherian X] [GeometricallyIntegral f] {L : LineBundle X}
    (σ : Γ(L.obj, ⊤))
    (hσ : ∀ (K : Type u) [Field K] (k : Spec (.of K) ⟶ S),
      pullbackSection (pullback.fst f k) L σ ≠ 0) :
    IsRegularSection L σ ∧ IsRelativeEffectiveCartierIdeal f (zeroIdeal L σ) := by
  have hloc : ∀ x : X, ∃ (V : S.affineOpens) (U : X.affineOpens) (_ : x ∈ U.1)
      (e : U.1 ≤ f ⁻¹ᵁ V.1) (s : Γ(X, U.1)) (g : Γ(L.obj, U.1)),
      (zeroIdeal L σ).ideal U = Ideal.span {s} ∧ res L σ U.1 = s • g ∧
      Scheme.Modules.IsFrameOn g U.1 ∧
      letI := (f.appLE V.1 U.1 e).hom.toAlgebra
      ∀ (P : Ideal Γ(X, U.1)) [P.IsMaximal], IsSMulRegular (Localization.AtPrime P ⧸
        (P.comap (algebraMap Γ(S, V.1) Γ(X, U.1))).map
          (algebraMap Γ(S, V.1) (Localization.AtPrime P)))
        (algebraMap Γ(X, U.1) (Localization.AtPrime P) s) := by
    intro x
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.base x)) isOpen_univ
    obtain ⟨W, ⟨hWa, W', hWW', ⟨t⟩⟩, hxW, hWV⟩ :=
      frameOpen_basis L x (f ⁻¹ᵁ V) (show f.base x ∈ V from hxV)
    let i : W ⟶ W' := homOfLE hWW'
    let s := coord t i (res L σ W)
    have hs : (zeroIdeal L σ).ideal ⟨W, hWa⟩ = Ideal.span {s} :=
      zeroIdeal_ideal_of_equiv L σ ⟨W, hWa⟩ (coordEquiv t i)
    refine ⟨⟨V, hV⟩, ⟨W, hWa⟩, hxW, hWV, s, trivGen t i, hs,
      (coord_smul_trivGen t i _).symm, isFrameOn_trivGen t i, ?_⟩
    letI := (f.appLE V W hWV).hom.toAlgebra
    intro P _
    set p := P.comap (algebraMap Γ(S, V) Γ(X, W))
    obtain ⟨q, hq, -⟩ := Langlands.CommutativeAlgebra.FibreLocalDomain.exists_fiber_prime
      (A := Γ(S, V)) P
    let c := Algebra.TensorProduct.comm Γ(S, V) Γ(X, W) p.ResidueField
    have : Nontrivial (p.Fiber Γ(X, W)) := by
      by_contra hn
      rw [not_nontrivial_iff_subsingleton] at hn
      exact hq.ne_top (Subsingleton.elim _ _)
    have : Nontrivial (Γ(X, W) ⊗[Γ(S, V)] p.ResidueField) := c.toEquiv.nontrivial
    have hdom := isDomain_tensor (V := ⟨V, hV⟩) (U := ⟨W, hWa⟩) f hWV p.ResidueField
    have hne := tmul_ne_zero (V := ⟨V, hV⟩) (U := ⟨W, hWa⟩) f hWV p.ResidueField σ s hs
      (hσ _ _)
    have hdom' : IsDomain (p.Fiber Γ(X, W)) := c.symm.toMulEquiv.isDomain
    have hne' : (1 : p.ResidueField) ⊗ₜ[Γ(S, V)] s ≠ 0 := by
      intro h
      apply hne
      have := congrArg c.symm h
      rwa [map_zero, Algebra.TensorProduct.comm_symm_tmul] at this
    exact Langlands.CommutativeAlgebra.FibreLocalDomain.isSMulRegular_of_isDomain_fiber P s
      hdom' hne'
  constructor
  · apply isRegularSection_of_local
    intro x
    obtain ⟨V, U, hxU, e, s, g, -, hσg, hg, hreg⟩ := hloc x
    letI := (f.appLE V.1 U.1 e).hom.toAlgebra
    have : Module.Flat Γ(S, V.1) Γ(X, U.1) :=
      HasRingHomProperty.appLE (P := @Flat) f inferInstance V U e
    have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    exact ⟨U, g, s, hxU, hg, hσg,
      (Langlands.CommutativeAlgebra.FibrewiseRegular.regular_and_flat_quotient s hreg).1⟩
  · apply LocalEquationCartier.isRelativeEffectiveCartierIdeal_of_fibreRegular _ f
    intro x
    obtain ⟨V, U, hxU, e, s, g, hs, -, -, hreg⟩ := hloc x
    exact ⟨V, U, hxU, e, s, hs, hreg⟩

end Assembly

end Langlands.AlgebraicGeometry.Picard.SectionZeroIdeal
