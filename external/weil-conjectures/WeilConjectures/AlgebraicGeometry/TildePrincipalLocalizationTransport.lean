/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Principal localization of tilde sections transported by an affine isomorphism

Source: Stacks Project, Schemes, Lemma 01HV (2), (4), (5).
(blueprint: lem-weil-pbc-tilde-principal-localization-transport)
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace LocalizedModule

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private noncomputable def transportSection {R : CommRingCat.{u}}
    {X : Scheme.{u}} (e : X ≅ Spec R)
    (H : (Spec R).Modules) (V : X.Opens)
    (U : (Spec R).Opens) (h : e.hom ''ᵁ V = U) :
    (H.restrict e.hom).val.obj (op V) ≃+ H.val.obj (op U) :=
  ((H.restrictAppIso e.hom V) ≪≫
    H.presheaf.mapIso (eqToIso h.symm).op).addCommGroupIsoToAddEquiv

private noncomputable def transportRing {R : CommRingCat.{u}}
    {X : Scheme.{u}} (e : X ≅ Spec R) (V : X.Opens)
    (U : (Spec R).Opens) (h : e.hom ''ᵁ V = U) :
    X.ringCatSheaf.obj.obj (op V) ≃+* (Spec R).presheaf.obj (op U) :=
  ((e.hom.appIso V).symm ≪≫
    (Spec R).presheaf.mapIso (eqToIso h.symm).op).commRingCatIsoToRingEquiv

private theorem transportSection_smul {R : CommRingCat.{u}}
    {X : Scheme.{u}} (e : X ≅ Spec R)
    (H : (Spec R).Modules) (V : X.Opens)
    (U : (Spec R).Opens) (h : e.hom ''ᵁ V = U)
    (x : X.ringCatSheaf.obj.obj (op V)) (s : (H.restrict e.hom).val.obj (op V)) :
    transportSection e H V U h (x • s) =
      transportRing e V U h x • transportSection e H V U h s := by
  subst U
  simp only [transportSection, transportRing, eqToIso_refl, Iso.op_refl,
    Functor.mapIso_refl, Iso.trans_refl]
  rfl

private theorem transportSection_res {R : CommRingCat.{u}}
    {X : Scheme.{u}} (e : X ≅ Spec R)
    (H : (Spec R).Modules) (V W : X.Opens) (hle : W ≤ V)
    (U T : (Spec R).Opens)
    (hV : e.hom ''ᵁ V = U) (hW : e.hom ''ᵁ W = T)
    (s : (H.restrict e.hom).val.obj (op V)) :
    transportSection e H W T hW ((H.restrict e.hom).val.map (homOfLE hle).op s) =
      H.val.map (homOfLE (hW ▸ hV ▸ e.hom.image_mono hle)).op
        (transportSection e H V U hV s) := by
  subst U T
  simp only [transportSection, eqToIso_refl, Iso.op_refl,
    Functor.mapIso_refl, Iso.trans_refl]
  rfl

private theorem transportRing_constant {R : CommRingCat.{u}}
    {X : Scheme.{u}} (e : X ≅ Spec R) (V : X.Opens)
    (U : (Spec R).Opens) (h : e.hom ''ᵁ V = U) (x : R) :
    transportRing e V U h ((e.hom.appLE ⊤ V (by simp))
      ((Scheme.ΓSpecIso R).inv x)) =
      algebraMap R ((Spec R).presheaf.obj (op U)) x := by
  subst U
  simp only [transportRing, eqToIso_refl, Iso.op_refl,
    Functor.mapIso_refl, Iso.trans_refl]
  have heq := e.hom.appLE_appIso_inv (U := ⊤) (V := V) (by simp)
  exact congr($(heq).hom ((Scheme.ΓSpecIso R).inv x))

private theorem tildeLocalization_smul
    (R : CommRingCat.{u}) (N : ModuleCat.{u} R) (r : R) :
    let K : Type u := (Spec R).presheaf.obj (op (PrimeSpectrum.basicOpen r))
    let σ := IsLocalization.algEquiv (Submonoid.powers r) K (Localization.Away r)
    let q := (IsLocalizedModule.iso (Submonoid.powers r)
      (tilde.toOpen (R := R) N (PrimeSpectrum.basicOpen r)).hom).symm
    ∀ (x : K) (s : (tilde (R := R) N).val.obj (op (PrimeSpectrum.basicOpen r))),
      q (x • s) = σ x • q s := by
  dsimp only
  let K : Type u := (Spec R).presheaf.obj (op (PrimeSpectrum.basicOpen r))
  let σ := IsLocalization.algEquiv (Submonoid.powers r) K (Localization.Away r)
  let q := (IsLocalizedModule.iso (Submonoid.powers r)
    (tilde.toOpen (R := R) N (PrimeSpectrum.basicOpen r)).hom).symm
  let : Module K (LocalizedModule.Away r N) :=
    Module.compHom (LocalizedModule.Away r N) σ.toRingHom
  have : IsScalarTower R K (LocalizedModule.Away r N) :=
    IsScalarTower.of_algebraMap_smul fun x s ↦ by
      change σ (algebraMap R K x) • s = x • s
      rw [σ.commutes, IsScalarTower.algebraMap_smul]
  let P := (modulesSpecToSheaf.obj (tilde (R := R) N)).presheaf.obj
    (op (PrimeSpectrum.basicOpen r))
  let : Module K P := ((tilde (R := R) N).val.obj
    (op (PrimeSpectrum.basicOpen r))).isModule
  have : IsScalarTower R K P :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  intro x s
  exact (IsLocalization.linearMap_compatibleSMul (Submonoid.powers r) K
    ((modulesSpecToSheaf.obj (tilde (R := R) N)).presheaf.obj
      (op (PrimeSpectrum.basicOpen r)))
    (LocalizedModule.Away r N)).map_smul q.toLinearMap x s

/-- Transport the global and principal-open section identifications of tilde along
an affine isomorphism, preserving the section-ring action and restriction of
whole-chart sections.

Source: Stacks Project, Schemes, Lemma 01HV (2), (4), (5).
(blueprint: lem-weil-pbc-tilde-principal-localization-transport)

Proof:
For the whole scheme compose restrictAppIso with the inverse of tilde.isoTop.
For D(r), compose restrictAppIso with the inverse of the localization equivalence
induced by tilde.toOpen. The image of the inverse image of D(r) under the
isomorphism is D(r). The section-ring equivalence t is the inverse of the
canonical localization equivalence on Spec R, composed with the inverse of
appIso. It sends every pulled-back constant x to x/1. Scalar compatibility
follows from smul_restrictAppIso_hom and the localized scalar action on tilde;
linearity over R extends to R_r because powers of r act invertibly.
The normalization on whole-scheme restrictions follows from toOpen_res and
the inverse laws of isoTop. If r=0 all principal-open objects are zero, and
if r is a unit the equivalences are the global-section equivalences. -/
theorem tilde_principalLocalization_transport
    (R : CommRingCat.{u}) (N : ModuleCat.{u} R)
    (X : Scheme.{u}) (e : X ≅ Spec R) :
    let G := Scheme.Modules.restrict (tilde (R := R) N) e.hom
    ∃ b : G.val.obj (op ⊤) ≃+ N,
      ∀ r : R,
        let V := e.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r
        ∃ t : X.ringCatSheaf.obj.obj (op V) ≃+* Localization.Away r,
          (∀ x : R, t ((e.hom.appLE ⊤ V (by simp))
            ((Scheme.ΓSpecIso R).inv x)) =
              algebraMap R (Localization.Away r) x) ∧
          ∃ d : G.val.obj (op V) ≃+ LocalizedModule.Away r N,
            (∀ (x : X.ringCatSheaf.obj.obj (op V)) (s : G.val.obj (op V)),
              d (x • s) = t x • d s) ∧
            ∀ s : G.val.obj (op ⊤),
              d (G.val.map V.leTop.op s) = mk (b s) 1 := by
  classical
  dsimp only
  let H := tilde (R := R) N
  let G := H.restrict e.hom
  have htop : e.hom ''ᵁ ⊤ = ⊤ := by
    simp [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
  let b := (transportSection e H ⊤ ⊤ htop).trans
    (tilde.isoTop (R := R) N).toLinearEquiv.symm.toAddEquiv
  refine ⟨b, ?_⟩
  intro r
  let V := e.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r
  have hV : e.hom ''ᵁ V = PrimeSpectrum.basicOpen r := by
    simp [V, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.opensRange_of_isIso]
  let K : Type u := (Spec R).presheaf.obj (op (PrimeSpectrum.basicOpen r))
  let σ := IsLocalization.algEquiv (Submonoid.powers r) K (Localization.Away r)
  let t := (transportRing e V (PrimeSpectrum.basicOpen r) hV).trans σ.toRingEquiv
  let q := (IsLocalizedModule.iso (Submonoid.powers r)
    (tilde.toOpen (R := R) N (PrimeSpectrum.basicOpen r)).hom).symm
  let d := (transportSection e H V (PrimeSpectrum.basicOpen r) hV).trans q.toAddEquiv
  refine ⟨t, ?_, d, ?_, ?_⟩
  · intro x
    change σ (transportRing e V (PrimeSpectrum.basicOpen r) hV _) = _
    rw [transportRing_constant]
    exact σ.commutes x
  · intro x s
    change q (transportSection e H V (PrimeSpectrum.basicOpen r) hV (x • s)) = _
    rw [transportSection_smul]
    exact tildeLocalization_smul R N r _ _
  · intro s
    change q (transportSection e H V (PrimeSpectrum.basicOpen r) hV
      (G.val.map V.leTop.op s)) = mk (b s) 1
    refine (congrArg q (transportSection_res e H ⊤ V le_top ⊤
      (PrimeSpectrum.basicOpen r) htop hV s)).trans ?_
    let s' := transportSection e H ⊤ ⊤ htop s
    have hs' : (tilde.toOpen (R := R) N ⊤)
        ((tilde.isoTop (R := R) N).toLinearEquiv.symm s') = s' :=
      (tilde.isoTop (R := R) N).toLinearEquiv.apply_symm_apply s'
    have hres := tilde.toOpen_res (R := R) N ⊤ (PrimeSpectrum.basicOpen r)
      (homOfLE (show PrimeSpectrum.basicOpen r ≤
        (⊤ : Opens (PrimeSpectrum.Top R)) from le_top))
    have hnorm : H.val.map (PrimeSpectrum.basicOpen r).leTop.op s' =
        (tilde.toOpen (R := R) N (PrimeSpectrum.basicOpen r)) (b s) := by
      rw [← hs']
      exact congr($(hres).hom (b s))
    refine (congrArg q hnorm).trans ?_
    exact IsLocalizedModule.iso_symm_apply (Submonoid.powers r)
      (tilde.toOpen (R := R) N (PrimeSpectrum.basicOpen r)).hom (b s)

end AlgebraicGeometry
