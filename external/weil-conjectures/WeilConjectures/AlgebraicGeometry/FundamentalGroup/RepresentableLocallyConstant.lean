/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ConstantSheafOfTypes
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.EtaleDescent
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocallyTrivial
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.RepresentableGluing

/-!
# Finite locally constant sheaves of sets are represented by finite étale schemes

Let `Y` be a scheme. This file proves the two halves of the dictionary between finite étale
`Y`-schemes and finite locally constant sheaves of sets on the small étale site of `Y`.

* For a finite étale `Y`-scheme `X`, the sheaf `U ↦ Hom_Y(U, X)` is constant over every member
  of an étale cover trivialising `X`
  (`AlgebraicGeometry.Scheme.FiniteEtale.exists_etale_isPullback_sigma`, blueprint
  `lem-fet-locally-trivial`), and its stalks are the geometric fibres of `X`, which
  are finite (`AlgebraicGeometry.Scheme.Etale.isConstant_over_uliftYoneda_of_isPullback`,
  `AlgebraicGeometry.Scheme.Etale.finite_sheafFiber_uliftYoneda`).
* Conversely, a sheaf of sets `E` with finite stalks which is constant over the members of an
  étale cover is represented by a finite étale `Y`-scheme
  (`AlgebraicGeometry.Scheme.Etale.exists_representableBy_of_isConstant`). Over a member `T` of
  the cover, `E` is represented by a trivial cover `∐_{s ∈ S} T`. Every point of `Y` has an affine
  open neighbourhood `U` with a surjective étale map `W ⟶ U` from an affine scheme `W` which
  factors through a member of the cover, so `E` is represented over `U` by effective descent
  along `W ⟶ U` (`AlgebraicGeometry.Scheme.Etale.exists_representableBy_of_isAffine`), and the
  representations over these `U` glue
  (`AlgebraicGeometry.Scheme.Etale.exists_representableBy_of_isBasis`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

namespace Etale

variable {Y : Scheme.{u}}

/-! ### Representable sheaves of finite étale schemes -/

section Yoneda

variable {X U : Y.Etale} {S : Type u} {fst : (∐ fun _ : S ↦ U.left) ⟶ X.left}

/-- If `X ×_Y U` is the trivial cover `∐_{s ∈ S} U`, then `Y`-morphisms `Z ⟶ X` from `Z` over
`U` are `U`-morphisms into the trivial cover. -/
noncomputable def homEquivOfIsPullbackSigma
    (h : IsPullback fst (Sigma.desc fun _ ↦ 𝟙 U.left) X.hom U.hom) (Z : Over U) :
    (Z.left ⟶ X) ≃ (Z ⟶ trivialOver S U) where
  toFun φ := Over.homMk (homMk (h.lift φ.left Z.hom.left (by rw [w_left, w_left]))
      ((h.lift_snd_assoc _ _ _ U.hom).trans (w_left Z.hom)))
        (EtaleTorsor.etaleHom_ext (h.lift_snd _ _ _))
  invFun t := t.left ≫ homMk fst h.w
  left_inv φ := EtaleTorsor.etaleHom_ext (by simp)
  right_inv t := Over.OverMorphism.ext (EtaleTorsor.etaleHom_ext (h.hom_ext (by simp)
    ((h.lift_snd _ _ _).trans (congr_arg (fun f ↦ f.left) (Over.w t)).symm)))

lemma homEquivOfIsPullbackSigma_comp
    (h : IsPullback fst (Sigma.desc fun _ ↦ 𝟙 U.left) X.hom U.hom) {Z Z' : Over U} (f : Z' ⟶ Z)
    (φ : Z.left ⟶ X) :
    homEquivOfIsPullbackSigma h Z' (f.left ≫ φ) = f ≫ homEquivOfIsPullbackSigma h Z φ :=
  (homEquivOfIsPullbackSigma h Z').symm.injective (EtaleTorsor.etaleHom_ext (by
    simp [homEquivOfIsPullbackSigma]))

/-- If `X ×_Y U` is a trivial cover of `U`, the sheaf `U' ↦ Hom_Y(U', X)` is constant over
`U`. -/
theorem isConstant_over_uliftYoneda_of_isPullback
    (h : IsPullback fst (Sigma.desc fun _ ↦ 𝟙 U.left) X.hom U.hom) :
    ((Y.smallEtaleTopology.uliftYoneda.{u + 1}.obj X).over U).IsConstant
      (Y.smallEtaleTopology.over U) := by
  let _ : TopologicalSpace S := ⊥
  have : DiscreteTopology S := ⟨rfl⟩
  let S₀ := ULift.{u + 1} S
  let _ : TopologicalSpace S₀ := ⊥
  have : DiscreteTopology S₀ := ⟨rfl⟩
  refine isConstant_over_of_iso_continuousMapSheafOfTypes (S := S₀) _
    (NatIso.ofComponents (fun Z ↦ Equiv.toIso (Equiv.ulift.trans
      ((homEquivOfIsPullbackSigma h Z.unop).trans ((trivialOverHomEquiv Z.unop).trans
        (continuousMapEquivOfEquiv Equiv.ulift.symm))))) fun {Z Z'} f ↦ ?_)
  ext φ
  change continuousMapEquivOfEquiv Equiv.ulift.symm (trivialOverHomEquiv Z'.unop
    (homEquivOfIsPullbackSigma h Z'.unop (f.unop.left ≫ φ.down))) = _
  rw [homEquivOfIsPullbackSigma_comp, trivialOverHomEquiv_comp]
  rfl

end Yoneda

/-- The stalks of the sheaf `U ↦ Hom_Y(U, X)` of a finite étale `Y`-scheme `X` are finite: they
are quotients of the geometric fibres of `X`. -/
theorem finite_sheafFiber_uliftYoneda (X : Y.Etale) [IsFinite X.hom] {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y) :
    Finite (ToType ((pointSmallEtale s).sheafFiber.obj
      (Y.smallEtaleTopology.uliftYoneda.{u + 1}.obj X))) := by
  let Φ := pointSmallEtale s
  let P : Y.Etaleᵒᵖ ⥤ Type (u + 1) := (Y.smallEtaleTopology.uliftYoneda.{u + 1}.obj X).obj
  have : Finite (Φ.fiber.obj X) := FiniteEtale.finite_fiber s ⟨X, inferInstance⟩
  refine Finite.of_surjective (fun x : Φ.fiber.obj X ↦
    Φ.toPresheafFiber X x P (show P.obj (op X) from ULift.up (𝟙 X))) fun z ↦ ?_
  obtain ⟨Z, x, ⟨φ⟩, rfl⟩ := Φ.toPresheafFiber_jointly_surjective (P := P) z
  refine ⟨Φ.fiber.map φ x, ?_⟩
  have := ConcreteCategory.congr_hom (Φ.toPresheafFiber_w φ x P)
    (show P.obj (op X) from ULift.up (𝟙 X))
  refine this.symm.trans ?_
  change Φ.toPresheafFiber Z x P (show P.obj (op Z) from ULift.up (φ ≫ 𝟙 X)) = _
  rw [Category.comp_id]

/-! ### Locally constant sheaves are representable -/

/-- **Finite locally constant sheaves of sets are represented by finite étale schemes.** A sheaf
of sets `E` on the small étale site of `Y` with finite stalks which is constant over every member
of an étale cover of `Y` is represented by a finite étale `Y`-scheme. -/
theorem exists_representableBy_of_isConstant (E : Sheaf Y.smallEtaleTopology (Type (u + 1)))
    (𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage Y)
    (h𝒰 : ∀ i, (E.over (𝒰.etalePrecoverageToEtale i)).IsConstant
      (Y.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i)))
    (hE : IsFiniteSheaf E) :
    ∃ X : Y.Etale, IsFinite X.hom ∧ Nonempty (E.obj.RepresentableBy X) := by
  let 𝔅 : Set Y.Opens := {U | IsAffineOpen U ∧ ∃ (i : 𝒰.I₀) (W : Y.Etale)
    (_ : W ⟶ 𝒰.etalePrecoverageToEtale i) (p : W ⟶ openObj U), IsAffine W.left ∧
      Surjective p.left ∧ Nonempty W.left}
  have h𝔅 : TopologicalSpace.Opens.IsBasis 𝔅 := by
    rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
    intro V y hy
    have : JointlySurjective etalePrecoverage.{u} :=
      inferInstanceAs (JointlySurjective (precoverage @Etale))
    obtain ⟨i, x, hx⟩ := 𝒰.exists_eq y
    have : Etale (𝒰.f i) := 𝒰.map_prop i
    obtain ⟨U, hU, hyU, hUV, W, _, q, _, p, hpq, hp⟩ :=
      exists_isAffineOpen_surjective_etale (𝒰.f i) hy ⟨x, hx⟩
    obtain ⟨w, hw⟩ := p.surjective ⟨y, hyU⟩
    exact ⟨U, ⟨hU, i, Etale.mk (q ≫ 𝒰.f i), homMk q rfl, homMk p hpq,
      inferInstanceAs (IsAffine W), hp, ⟨w⟩⟩, hyU, hUV⟩
  refine exists_representableBy_of_isBasis E 𝔅 h𝔅 fun U ↦ ?_
  obtain ⟨hU, i, W, a, p, hW, hp, ⟨w⟩⟩ := U.2
  obtain ⟨S, _, hS⟩ := exists_representableBy_trivialOver_of_isConstant E hE _ (a.left w) (h𝒰 i)
  have : IsAffine (openObj U.1).left := hU
  exact exists_representableBy_of_isAffine E p (trivialOver S W) (hS a).some

end Etale

end AlgebraicGeometry.Scheme
