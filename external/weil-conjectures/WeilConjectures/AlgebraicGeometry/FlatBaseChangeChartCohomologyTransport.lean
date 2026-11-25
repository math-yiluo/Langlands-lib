/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ResolutionSectionClassOpenRestriction
public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
import WeilConjectures.AlgebraicGeometry.FlatBaseChangeChartCoefficientTransport
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapFunctorial
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapBasicProperties

/-! # Cohomology transport from the affine scalar-extension chart

Source: Stacks Project, Tags 02KH and 01FB.
-/

@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives
attribute [local irreducible] moduleCohomologyFMap cohomologyOpenRestriction
  pushforwardComp pushforwardCongr pushforwardId

private theorem chart_fmap_congr {Y Z : Scheme.{u}}
    {h k : Y ⟶ Z} (e : h = k) {A : Z.Modules} {B : Y.Modules}
    (φ : A ⟶ (pushforward h).obj B) (p : ℕ) :
    moduleCohomologyFMap h φ p =
      moduleCohomologyFMap k (φ ≫ (pushforwardCongr e).hom.app B) p := by
  subst k
  have hc : (pushforwardCongr (rfl : h = h)).hom.app B = 𝟙 _ := by
    ext U
    simp
  rw [hc, Category.comp_id]

private theorem chart_fmap_identity (Y : Scheme.{u}) (A : Y.Modules) (p : ℕ) :
    moduleCohomologyFMap (𝟙 Y) ((pushforwardId Y).inv.app A) p = 𝟙 _ := by
  have he : (pushforwardId Y).inv.app A = 𝟙 A := by
    ext U
    simp
  rw [he]
  refine ((moduleCohomologyFMap_basic_properties (𝟙 Y) (𝟙 A) p).2.2.1
    Y A A (𝟙 A)).trans ?_
  ext x
  simp

private theorem chart_fmap_inverse {Y Z : Scheme.{u}} (σ : Y ≅ Z)
    {A : Z.Modules} {B : Y.Modules}
    (φ : A ⟶ (pushforward σ.hom).obj B)
    (ψ : B ⟶ (pushforward σ.inv).obj A)
    (hc : φ ≫ (pushforward σ.hom).map ψ ≫
      (pushforwardComp σ.inv σ.hom).hom.app A ≫
      (pushforwardCongr σ.inv_hom_id).hom.app A = (pushforwardId Z).inv.app A)
    (p : ℕ) :
    moduleCohomologyFMap σ.hom φ p ≫ moduleCohomologyFMap σ.inv ψ p = 𝟙 _ := by
  rw [← moduleCohomologyFMap_comp, chart_fmap_congr σ.inv_hom_id]
  simp only [Category.assoc] at hc ⊢
  rw [hc]
  exact chart_fmap_identity Z A p

private theorem chart_fmap_naturality_apply {Y Z : Scheme.{u}} (h : Y ⟶ Z)
    {A : Z.Modules} {B : Y.Modules} (φ : A ⟶ (pushforward h).obj B)
    (α : A ⟶ A) (β : B ⟶ B) (hs : α ≫ φ = φ ≫ (pushforward h).map β)
    (p : ℕ) (x : (RingedSpace.moduleCohomology Z.toRingedSpace p).obj A) :
    moduleCohomologyFMap h φ p
        (((RingedSpace.moduleCohomology Z.toRingedSpace p).map α).hom x) =
      ((RingedSpace.moduleCohomology Y.toRingedSpace p).map β).hom
        (moduleCohomologyFMap h φ p x) := by
  have hsource := moduleCohomologyFMap_source_naturality h α φ p
  have htarget := moduleCohomologyFMap_target_naturality h β φ p
  rw [hs] at hsource
  exact ConcreteCategory.congr_hom (hsource.trans htarget.symm) x

private theorem chart_fmap_unit_square {Z T U L : Scheme.{u}}
    (b : T ⟶ Z) (s : L ⟶ T) (q : U ⟶ Z) (j : L ⟶ U) (e : s ≫ b = j ≫ q)
    {K N : Z.Modules} {A : T.Modules} {B : U.Modules} {M : L.Modules}
    (α : K ⟶ N) (η : N ⟶ (pushforward b).obj A)
    (φ : A ⟶ (pushforward s).obj M) (ψ : K ⟶ (pushforward q).obj B)
    (r : B ⟶ (pushforward j).obj M)
    (hc : α ≫ η ≫ (pushforward b).map φ ≫ (pushforwardComp s b).hom.app M ≫
        (pushforwardCongr e).hom.app M =
      ψ ≫ (pushforward q).map r ≫ (pushforwardComp j q).hom.app M) (p : ℕ) :
    (forget₂ _ AddCommGrpCat.{u}).map
        ((RingedSpace.moduleCohomology Z.toRingedSpace p).map α) ≫
        moduleCohomologyFMap b η p ≫ moduleCohomologyFMap s φ p =
      moduleCohomologyFMap q ψ p ≫ moduleCohomologyFMap j r p := by
  rw [← moduleCohomologyFMap_comp, moduleCohomologyFMap_source_naturality,
    chart_fmap_congr e]
  simp only [Category.assoc] at hc ⊢
  rw [hc, moduleCohomologyFMap_comp]

-- Elaborating the coefficient comparisons uses several module functors.
/-- Transport along the affine chart identifies its unit map with open restriction
of the specified coefficient h-map. No Leray edge or higher image is involved.
Source: Stacks Project, Tag 02KH, first paragraph of the proof; Tag 01FB,
Remark 20.14.2; Tags 0096 (Lemma 6.26.2) and 0097 (Lemma 6.26.3).
(blueprint: new-flat-base-change-chart-cohomology-transport)

Proof: Write U0 = f inverse V and L = f' inverse W. The affine identifications
V = Spec Gamma(V) and W = Spec Gamma(W), together with the equality hAlgebra,
identify U0 times Spec Gamma(W) over Spec Gamma(V) with L. Construct the two inverse
maps by the fibre-product universal property, and check the inverse identities by
the two projections. Under this scheme isomorphism pullback composition identifies
the chart coefficient N_B with G restricted to L, where G = tensorPullback(g') F.
The tensor pullback adjunction and ordinary pullback adjunction determine the same
pullback functor up to their unique adjunction-compatible isomorphism. Composing
this with restrictFunctorIsoPullback gives the coefficient identification.
Apply module cohomology along the scheme isomorphism and this coefficient iso;
functoriality and the two inverse identities give an additive equivalence t.
The projection to Spec Gamma(W) equals the restricted f' followed by W.toSpecGamma,
so naturality for multiplication by a global section gives t's scalar equation.
To prove the last equation, transpose both coefficient maps across the pullback
adjunction. The composite-unit identities reduce their equality to D.unit_square
restricted to L. The restriction composition iso used in cohomologyOpenRestriction
is exactly the coefficient comparison in this calculation. Apply source and target
naturality and composition of moduleCohomologyFMap to this equality. This gives the
unit formula without inverting the unit h-map. The fibre-product and adjunction
arguments cover empty opens, degree zero and zero coefficients as well. -/
theorem exists_flatBaseChange_chart_cohomology_transport
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (F : X.Modules) (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
    (p : ℕ) (V : S.Opens) (W : S'.Opens) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (eVW : W ≤ g ⁻¹ᵁ V) (D : FlatBaseChangeOpenChoices f g F I J V)
    [Algebra Γ(S, V) Γ(S', W)]
    (hAlgebra : algebraMap Γ(S, V) Γ(S', W) = (g.appLE V W eVW).hom) :
    let h := f.resLE V (f ⁻¹ᵁ V) le_rfl ≫ V.toSpecΓ
    let N := (pullback (f ⁻¹ᵁ V).ι).obj F
    let T := baseChangedScheme (S := Γ(S', W)) h
    let A := baseChangedModule (S := Γ(S', W)) h N
    let C := RingedSpace.moduleCohomology T.toRingedSpace p
    let G := (tensorPullback (pullback.snd g f)).obj F
    let U := (pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)
    let L := (pullback.fst g f) ⁻¹ᵁ W
    let e : L ≤ U := by
      change (pullback.fst g f) ⁻¹ᵁ W ≤ (pullback.snd g f) ⁻¹ᵁ (f ⁻¹ᵁ V)
      rw [flatBaseChangeOpenEquality f g V]
      exact (pullback.fst g f).preimage_mono eVW
    let M := (restrictFunctor L.ι).obj G
    let C' := RingedSpace.moduleCohomology L.toScheme.toRingedSpace p
    let k := (pullback.fst g f).resLE W L le_rfl ≫ W.toSpecΓ
    ∃ t : C.obj A ≃+ C'.obj M,
      (∀ (a : Γ(S', W)) (y : C.obj A),
        t ((C.map (A.smulHom (((Scheme.ΓSpecIso Γ(S', W)).inv ≫
          (baseChangeSnd (S := Γ(S', W)) h).appTop).hom a))).hom y) =
        ((C'.map (M.smulHom (((Scheme.ΓSpecIso Γ(S', W)).inv ≫ k.appTop).hom a))).hom
          (t y))) ∧
      (∀ x : (RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p).obj
          ((restrictFunctor (f ⁻¹ᵁ V).ι).obj F),
        t (moduleCohomologyFMap (baseChangeFst (S := Γ(S', W)) h)
          (baseChangeUnit (S := Γ(S', W)) h N) p
          (((RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p).map
            ((restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app F).hom).hom x)) =
        cohomologyOpenRestriction G U L e p
          (moduleCohomologyFMap ((pullback.snd g f).resLE (f ⁻¹ᵁ V) U le_rfl)
            D.psi p x)) := by
  classical
  intro h N T A C G U L e M C' k
  -- Eliminate a named hypothesis to avoid generalizing the full coefficient-transport proof.
  have hcoefficient :=
    exists_flatBaseChange_chart_coefficient_transport f g F I J V W hV hW eVW D hAlgebra
  rcases hcoefficient with ⟨σ, φ, ψ, hφψ, hψφ, hscalar, ef, hunit⟩
  let a := moduleCohomologyFMap σ.hom φ p
  let b := moduleCohomologyFMap σ.inv ψ p
  have hab : a ≫ b = 𝟙 _ := chart_fmap_inverse σ φ ψ hφψ p
  have hba : b ≫ a = 𝟙 _ := chart_fmap_inverse σ.symm ψ φ hψφ p
  let t : C.obj A ≃+ C'.obj M :=
    { toFun := a.hom
      invFun := b.hom
      left_inv := fun x ↦ ConcreteCategory.congr_hom hab x
      right_inv := fun x ↦ ConcreteCategory.congr_hom hba x
      map_add' := a.hom.map_add }
  refine ⟨t, ?_, ?_⟩
  · intro s y
    exact chart_fmap_naturality_apply σ.hom φ
      (A.smulHom (((Scheme.ΓSpecIso Γ(S', W)).inv ≫
        (baseChangeSnd (S := Γ(S', W)) h).appTop).hom s))
      (M.smulHom (((Scheme.ΓSpecIso Γ(S', W)).inv ≫ k.appTop).hom s)) (hscalar s) p y
  · let j := (Limits.pullback g f).homOfLE e
    let c := (restrictFunctorComp j U.ι).symm.app G ≪≫
      (restrictFunctorCongr ((Limits.pullback g f).homOfLE_ι e)).app G
    let r := (restrictAdjunction j).unit.app ((restrictFunctor U.ι).obj G) ≫
      (pushforward j).map c.hom
    let q := (pullback.snd g f).resLE (f ⁻¹ᵁ V) U le_rfl
    let α := ((restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app F).hom
    have hu : (forget₂ _ AddCommGrpCat.{u}).map
        ((RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p).map α) ≫
        moduleCohomologyFMap (baseChangeFst (S := Γ(S', W)) h)
          (baseChangeUnit (S := Γ(S', W)) h N) p ≫ a =
        moduleCohomologyFMap q D.psi p ≫ moduleCohomologyFMap j r p :=
      chart_fmap_unit_square (baseChangeFst (S := Γ(S', W)) h) σ.hom q j ef
        α (baseChangeUnit (S := Γ(S', W)) h N) φ D.psi r hunit p
    intro x
    unfold cohomologyOpenRestriction
    dsimp only [t]
    have hx := congrArg (fun z ↦ z.hom x) hu
    simp only [AddCommGrpCat.hom_comp, ModuleCat.forget₂_map,
      AddCommGrpCat.hom_ofHom, AddMonoidHom.comp_apply] at hx
    exact hx

end AlgebraicGeometry.Scheme.Modules
