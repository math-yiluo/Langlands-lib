/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.ProjChartRestrictionIsLocalized

/-!
# Localization of sections of a graded-module chart

Source: Stacks Project, Constructions, Section 01M3 and Lemmas 01M4, 01M7 and 01MB.
(blueprint: lem-weil-pbc-proj-graded-module-chart-principal-localization)
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace
open LocalizedModule HomogeneousLocalization

namespace AlgebraicGeometry.Proj

variable {S M : Type u} [CommRing S] [AddCommGroup M] [Module S M]
variable (𝒜 : ℕ → AddSubgroup S) [GradedRing 𝒜]

/-- Restrict the ordinary localized module action along the inclusion of the homogeneous
localization. This changes only scalars, not the localization or its operations.
Source: Stacks, Algebra, Section 00JM.
(blueprint: lem-weil-pbc-proj-graded-module-chart-principal-localization) -/
local instance localizedModuleHomogeneousScalarsPrincipalLocalization (T : Submonoid S) :
    Module (HomogeneousLocalization 𝒜 T) (LocalizedModule T M) :=
  Module.compHom (LocalizedModule T M)
    (algebraMap (HomogeneousLocalization 𝒜 T) (Localization T))

set_option quotPrecheck false
set_option linter.unusedVariables false

local notation "Fidx" => {p : S × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2}
local notation "R[" f "]" => HomogeneousLocalization.Away 𝒜 (f).val.1
local notation "N[" f "]" => LocalizedModule.Away (f).val.1 M
local notation "D[" f "]" => basicOpen 𝒜 (f).val.1
local notation "ModX" => (Proj 𝒜).Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Sections of the given graded-module sheaf on each principal chart open are
its chart module localized at the defining element, with canonical scalars and
normalization on restrictions of whole-chart sections.

Source: Stacks Project, Constructions, Lemmas 01M4 (1)(e),(h), 01M7 and 01MB,
last paragraph. (blueprint: lem-weil-pbc-proj-graded-module-chart-principal-localization)

Proof:
Identify whole-chart sections with Z f by restriction along the chart inclusion
and alpha f; this gives b. Write r as a homogeneous fraction a/f^n with a of
degree n*deg(f). Put g=f*a of degree (n+1)*deg(f)>0. The chart-intersection
formula identifies the image of V in Proj with D_+(g), because U f g = r^deg(f)
and D(r^deg(f))=D(r). Transport sections through restrictAppIso and alpha g,
then theta f g inverse. Localization at r^deg(f) and at r have the same
universal property, so obtain c with c(restrict(s))=b(s)/1 from hrestriction
and htheta. For scalars, hcanonical and uniqueness of maps from S_f identify
rhoS with the actual restriction of the structure sheaf. The chart ring on V
is the localization of R[f] at r. The supplied t agrees with its canonical
identification on R[f], hence on all fractions by uniqueness of localization
maps. The scalar compatibility of alpha and theta now proves c(x*s)=t(x)*c(s).
If r=0, V is empty and both localized modules and section modules are zero;
if r is a unit, the same construction is the whole-chart identification.
No comparison with tilde and no compatibility between proper opens is used. -/
theorem gradedModuleChart_principalLocalization
    (Z : ∀ f : Fidx, Submodule R[f] N[f])
    (rhoS : ∀ (f g : Fidx), D[g] ≤ D[f] → R[f] →+* R[g])
    (rho : ∀ (f g : Fidx), D[g] ≤ D[f] → Z f →+ Z g)
    (U : ∀ (f g : Fidx), R[f])
    (hU : ∀ (f g : Fidx), (U f g).val = Localization.mk (g.val.1 ^ f.val.2)
      (⟨f.val.1 ^ g.val.2, ⟨g.val.2, rfl⟩⟩ : Submonoid.powers f.val.1))
    (theta : ∀ (f g : Fidx), D[g] ≤ D[f] →
      LocalizedModule.Away (U f g) (Z f) ≃+ Z g)
    (thetaS : ∀ (f g : Fidx), D[g] ≤ D[f] → Localization.Away (U f g) ≃+* R[g])
    (htheta : ∀ (f g : Fidx) (i : D[g] ≤ D[f]),
      (∀ r : R[f], thetaS f g i (algebraMap R[f] (Localization.Away (U f g)) r) =
        rhoS f g i r) ∧
      (∀ q : Z f, theta f g i (mk q 1) = rho f g i q) ∧
      (∀ (r : Localization.Away (U f g)) (q : LocalizedModule.Away (U f g) (Z f)),
        theta f g i (r • q) = thetaS f g i r • theta f g i q))
    (hcanonical : ∀ (f g : Fidx) (i : D[g] ≤ D[f]),
      ∃ l : Localization.Away f.val.1 →+* Localization.Away g.val.1,
        (∀ a : S, l (algebraMap S (Localization.Away f.val.1) a) =
          algebraMap S (Localization.Away g.val.1) a) ∧
        ∀ r : R[f], (rhoS f g i r).val = l r.val)
    (F : ModX) (alpha : ∀ f : Fidx, F.val.obj (op D[f]) ≃+ Z f)
    (hscalar : ∀ (f : Fidx) (r : R[f]) (s : F.val.obj (op D[f])),
      alpha f ((awayToSection 𝒜 f.val.1 r) • s) = r • alpha f s)
    (hrestriction : ∀ (f g : Fidx) (i : D[g] ≤ D[f])
      (s : F.val.obj (op D[f])),
      alpha g (F.val.map (homOfLE i).op s) = rho f g i (alpha f s))
    (f : Fidx) :
      let e := basicOpenIsoSpec 𝒜 f.val.1 f.property.2 f.property.1
      let E := Scheme.Modules.restrict F D[f].ι
      ∃ b : E.val.obj (op ⊤) ≃+ Z f,
        ∀ (r : R[f]),
          let V := e.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r
          ∀ t : D[f].toScheme.ringCatSheaf.obj.obj (op V) ≃+* Localization.Away r,
            (∀ x : R[f], t ((e.hom.appLE ⊤ V (by simp))
              ((Scheme.ΓSpecIso (CommRingCat.of R[f])).inv x)) =
                algebraMap R[f] (Localization.Away r) x) →
            ∃ c : E.val.obj (op V) ≃+ LocalizedModule.Away r (Z f),
              (∀ (x : D[f].toScheme.ringCatSheaf.obj.obj (op V))
                (s : E.val.obj (op V)), c (x • s) = t x • c s) ∧
              ∀ s : E.val.obj (op ⊤),
                c (E.val.map V.leTop.op s) = mk (b s) 1 := by
  classical
  dsimp only
  let E := Scheme.Modules.restrict F D[f].ι
  let htop := D[f].ι_image_top
  let b := ((F.restrictAppIso D[f].ι ⊤) ≪≫
    F.presheaf.mapIso (eqToIso htop.symm).op).addCommGroupIsoToAddEquiv.trans (alpha f)
  refine ⟨b, ?_⟩
  intro r
  let e := basicOpenIsoSpec 𝒜 f.val.1 f.property.2 f.property.1
  let V := e.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r
  intro t ht
  let K : Type u := D[f].toScheme.presheaf.obj (op V)
  let k : R[f] →+* K := (e.hom.appLE ⊤ V (by simp)).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of R[f])).inv.hom
  let P : Type u := E.val.obj (op V)
  let : Module R[f] P := Module.compHom P k
  let L : Z f →+ P := (E.val.map V.leTop.op).hom.toAddMonoidHom.comp b.symm.toAddMonoidHom
  have hlinear : ∀ (x : R[f]) (q : Z f), L (x • q) = k x • L q := by
    intro x q
    let ktop := (e.hom.appLE ⊤ ⊤ (by simp)).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of R[f])).inv.hom
    have hk : k x = D[f].toScheme.presheaf.map V.leTop.op (ktop x) := by
      exact congr($(e.hom.appLE_map (U := ⊤) (V := ⊤) (by simp) V.leTop.op).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R[f])).inv x)).symm
    have hb : b (ktop x • b.symm q) = x • q := by
      change alpha f (F.presheaf.map (eqToIso htop.symm).op.hom
        ((F.restrictAppIso D[f].ι ⊤).hom (ktop x • b.symm q))) = x • q
      rw [Scheme.Modules.smul_restrictAppIso_hom_apply]
      have hkTop : ktop x = D[f].topIso.inv (awayToSection 𝒜 f.val.1 x) := by
        change (basicOpenToSpec 𝒜 f.val.1).app ⊤
          ((Scheme.ΓSpecIso (CommRingCat.of R[f])).inv x) = _
        rw [basicOpenToSpec_app_top]
        simp
      rw [hkTop]
      have hm := Scheme.Modules.map_smul F (eqToHom htop.symm)
        ((D[f].ι.appIso ⊤).inv (D[f].topIso.inv (awayToSection 𝒜 f.val.1 x)))
        ((F.restrictAppIso D[f].ι ⊤).hom (b.symm q))
      have hr : (Proj 𝒜).presheaf.map (eqToHom htop.symm).op
          ((D[f].ι.appIso ⊤).inv (D[f].topIso.inv (awayToSection 𝒜 f.val.1 x))) =
          awayToSection 𝒜 f.val.1 x := by
        simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
        exact D[f].topIso.inv_hom_id_apply (awayToSection 𝒜 f.val.1 x)
      have hm' := congrArg (alpha f) hm
      rw [hr, hscalar] at hm'
      exact hm'.trans (congrArg (x • ·) (b.apply_symm_apply q))
    have hbinv : b.symm (x • q) = ktop x • b.symm q :=
      b.injective (by simpa using hb.symm)
    change E.val.restrictₛₗ V.leTop.op (b.symm (x • q)) = k x • _
    rw [hbinv]
    exact (Scheme.Modules.map_smul E V.leTop (ktop x) (b.symm q)).trans
      (by rw [← hk]; rfl)
  let l : Z f →ₗ[R[f]] P := { L with map_smul' := hlinear }
  have hl : IsLocalizedModule (Submonoid.powers r) l :=
    gradedModuleChart_restriction_isLocalized 𝒜 Z rhoS rho U hU theta thetaS htheta
      hcanonical F alpha hscalar hrestriction f r l (fun _ ↦ rfl)
  let c := (IsLocalizedModule.iso (Submonoid.powers r) l).symm
  refine ⟨c.toAddEquiv, ?_, ?_⟩
  · let : Algebra R[f] K := k.toAlgebra
    let σ : K ≃ₐ[R[f]] Localization.Away r := { t with commutes' := ht }
    have : IsLocalization (Submonoid.powers r) K :=
      IsLocalization.isLocalization_of_algEquiv (Submonoid.powers r) σ.symm
    let : Module K (LocalizedModule.Away r (Z f)) :=
      Module.compHom (LocalizedModule.Away r (Z f)) t.toRingHom
    have : IsScalarTower R[f] K P :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    have : IsScalarTower R[f] K (LocalizedModule.Away r (Z f)) :=
      IsScalarTower.of_algebraMap_smul fun x s ↦ by
        change t (k x) • s = x • s
        exact (congrArg (fun a : Localization.Away r ↦ a • s) (ht x)).trans
          (IsScalarTower.algebraMap_smul (Localization.Away r) x s)
    intro x s
    exact (IsLocalization.linearMap_compatibleSMul (Submonoid.powers r) K P
      (LocalizedModule.Away r (Z f))).map_smul c.toLinearMap x s
  · intro s
    have hn : l (b s) = E.val.map V.leTop.op s := by
      change E.val.map V.leTop.op (b.symm (b s)) = _
      rw [b.symm_apply_apply]
    rw [← hn]
    exact IsLocalizedModule.iso_symm_apply (Submonoid.powers r) l (b s)

end AlgebraicGeometry.Proj
