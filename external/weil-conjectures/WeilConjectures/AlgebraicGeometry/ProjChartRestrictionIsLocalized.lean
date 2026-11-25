/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Universal property of principal-chart restriction

Source: Stacks Project, Constructions, Section 01M3 and Lemmas 01M4, 01M7 and 01MB.
(blueprint: lem-weil-pbc-proj-chart-restriction-is-localized)
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
(blueprint: lem-weil-pbc-proj-chart-restriction-is-localized) -/
local instance localizedModuleHomogeneousScalarsRestrictionLocalization (T : Submonoid S) :
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
private theorem canonical_chart_constants
    (f g : Fidx) (i : D[g] ≤ D[f]) (rhoS : R[f] →+* R[g])
    (l : Localization.Away f.val.1 →+* Localization.Away g.val.1)
    (hl : ∀ a : S, l (algebraMap S (Localization.Away f.val.1) a) =
      algebraMap S (Localization.Away g.val.1) a)
    (hrho : ∀ x : R[f], (rhoS x).val = l x.val) (x : R[f]) :
    (Proj 𝒜).presheaf.map (homOfLE i).op (awayToSection 𝒜 f.val.1 x) =
      awayToSection 𝒜 g.val.1 (rhoS x) := by
  apply Subtype.ext
  ext p
  change (((ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.map (homOfLE i).op
    (ProjectiveSpectrum.Proj.awayToSection 𝒜 f.val.1 x)).val p).val =
    ((ProjectiveSpectrum.Proj.awayToSection 𝒜 g.val.1 (rhoS x)).val p).val
  rw [AlgebraicGeometry.Proj.res_apply]
  erw [ProjectiveSpectrum.Proj.awayToSection_apply,
    ProjectiveSpectrum.Proj.awayToSection_apply]
  rw [hrho]
  let mf : Localization.Away f.val.1 →+* Localization p.val.asHomogeneousIdeal.toIdeal.primeCompl :=
    IsLocalization.map (M := Submonoid.powers f.val.1)
      (T := p.val.asHomogeneousIdeal.toIdeal.primeCompl) _ (RingHom.id S)
      (Submonoid.powers_le.mpr (show f.val.1 ∈
        p.val.asHomogeneousIdeal.toIdeal.primeCompl from i p.property))
  let mg : Localization.Away g.val.1 →+* Localization p.val.asHomogeneousIdeal.toIdeal.primeCompl :=
    IsLocalization.map (M := Submonoid.powers g.val.1)
      (T := p.val.asHomogeneousIdeal.toIdeal.primeCompl) _ (RingHom.id S)
      (Submonoid.powers_le.mpr (show g.val.1 ∈
        p.val.asHomogeneousIdeal.toIdeal.primeCompl from p.property))
  have hm : mf = mg.comp l := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f.val.1)
    ext a
    change mf (algebraMap S (Localization.Away f.val.1) a) =
      mg (l (algebraMap S (Localization.Away f.val.1) a))
    rw [hl]
    simp only [mf, mg, IsLocalization.map_eq, RingHom.id_apply]
  exact congrArg (fun h : Localization.Away f.val.1 →+*
    Localization p.val.asHomogeneousIdeal.toIdeal.primeCompl ↦ h x.val) hm

/-- Pulled-back affine constants agree with the canonical homogeneous-chart restriction.

Source: Stacks Project, Constructions, Tag 01M4 (1)(h) and Tag 01MB.
(blueprint: lem-weil-pbc-proj-chart-restriction-is-localized)

Proof: The canonical affine chart isomorphism is induced by awayToSection,
so a constant x pulled back from Spec R[f] is awayToSection f x, restricted
to the image of V. Write x=a/f^n using homogeneous fraction surjectivity.
The S-algebra map supplied by hcanonical fixes the image of a and of f.
Since f is invertible in S_f, its image is invertible in S_g and the map
sends a/f^n to a times the inverse of f^n in S_g. This is exactly the
restriction of the fraction section awayToSection f x to D[g]: both have
at every point the same homogeneous-localization germ. Equality of germs
implies equality of sections. Injectivity of the homogeneous localization
in S_g identifies this expression with rhoS f g i x. Finally appIso for
the open immersion and transport along hg identify the image-open section
with its pulled-back section on V. This argument uses no nonzero or domain
hypothesis; the zero ring and empty chart satisfy the same identities. -/
private theorem gradedModuleChart_restriction_constants
    (rhoS : ∀ (f g : Fidx), D[g] ≤ D[f] → R[f] →+* R[g])
    (hcanonical : ∀ (f g : Fidx) (i : D[g] ≤ D[f]),
      ∃ l : Localization.Away f.val.1 →+* Localization.Away g.val.1,
        (∀ a : S, l (algebraMap S (Localization.Away f.val.1) a) =
          algebraMap S (Localization.Away g.val.1) a) ∧
        ∀ r : R[f], (rhoS f g i r).val = l r.val)
    (f : Fidx) (r : R[f]) (g : Fidx)
    (hg : D[f].ι ''ᵁ
      ((basicOpenIsoSpec 𝒜 f.val.1 f.property.2 f.property.1).hom ⁻¹ᵁ
        PrimeSpectrum.basicOpen r) = D[g]) :
    let e := basicOpenIsoSpec 𝒜 f.val.1 f.property.2 f.property.1
    let V := e.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r
    let k := (e.hom.appLE ⊤ V (by simp)).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of R[f])).inv.hom
    ∀ x : R[f],
      (Proj 𝒜).presheaf.map (eqToHom hg.symm).op
        ((D[f].ι.appIso V).inv (k x)) =
      awayToSection 𝒜 g.val.1 (rhoS f g (hg ▸ D[f].ι_image_le V) x) := by
  classical
  let e := basicOpenIsoSpec 𝒜 f.val.1 f.property.2 f.property.1
  let V := e.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r
  dsimp only
  intro x
  obtain ⟨l, hl, hrho⟩ := hcanonical f g (hg ▸ D[f].ι_image_le V)
  have htop : e.hom.appLE ⊤ ⊤ (by simp) = e.hom.appTop :=
    e.hom.appLE_eq_app
  have hV := e.hom.appLE_map (show (⊤ : D[f].toScheme.Opens) ≤ e.hom ⁻¹ᵁ ⊤ by simp)
    V.leTop.op
  rw [htop] at hV
  have hbase : e.hom.appTop = (Scheme.ΓSpecIso (CommRingCat.of R[f])).hom ≫
      awayToSection 𝒜 f.val.1 ≫ D[f].topIso.inv := basicOpenToSpec_app_top 𝒜 f.val.1
  have hk : e.hom.appLE ⊤ V (by simp)
      ((Scheme.ΓSpecIso (CommRingCat.of R[f])).inv x) =
      D[f].toScheme.presheaf.map V.leTop.op (D[f].topIso.inv
        (awayToSection 𝒜 f.val.1 x)) := by
    rw [← hV, hbase]
    simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
    rfl
  change (Proj 𝒜).presheaf.map (eqToHom hg.symm).op
    ((D[f].ι.appIso V).inv (e.hom.appLE ⊤ V (by simp)
      ((Scheme.ΓSpecIso (CommRingCat.of R[f])).inv x))) = _
  rw [hk, Scheme.Opens.ι_appIso]
  change (Proj 𝒜).presheaf.map (eqToHom hg.symm).op
    ((Proj 𝒜).presheaf.map
      (homOfLE (D[f].ι.image_mono (show V ≤ ⊤ from le_top))).op
      ((Proj 𝒜).presheaf.map (eqToHom D[f].ι_image_top).op
        (awayToSection 𝒜 f.val.1 x))) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  have hi : (eqToHom D[f].ι_image_top).op ≫
      (homOfLE (D[f].ι.image_mono (show V ≤ ⊤ from le_top))).op ≫
      (eqToHom hg.symm).op = (homOfLE (hg ▸ D[f].ι_image_le V)).op :=
    Subsingleton.elim _ _
  rw [hi]
  exact canonical_chart_constants 𝒜 f g (hg ▸ D[f].ι_image_le V) _ l hl hrho x

private theorem principalOpen_chart_power (U : ∀ (f g : Fidx), R[f])
    (hU : ∀ (f g : Fidx), (U f g).val = Localization.mk (g.val.1 ^ f.val.2)
      (⟨f.val.1 ^ g.val.2, ⟨g.val.2, rfl⟩⟩ : Submonoid.powers f.val.1))
    (f : Fidx) (r : R[f]) :
    ∃ g : Fidx, D[f].ι ''ᵁ
      ((basicOpenIsoSpec 𝒜 f.val.1 f.property.2 f.property.1).hom ⁻¹ᵁ
        PrimeSpectrum.basicOpen r) = D[g] ∧ U f g = r ^ f.val.2 := by
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 f.property.2 r
  let g : Fidx := ⟨(f.val.1 * a, f.val.2 + n * f.val.2),
    ⟨by omega, SetLike.mul_mem_graded f.property.2 ha⟩⟩
  refine ⟨g, ?_, ?_⟩
  · have hbase (x : D[f]) :
        (basicOpenIsoSpec 𝒜 f.val.1 f.property.2 f.property.1).hom x =
          (ProjectiveSpectrum.Proj.toSpec 𝒜 f.val.1).base x := by
      rfl
    have hopen :
        (basicOpenIsoSpec 𝒜 f.val.1 f.property.2 f.property.1).hom ⁻¹ᵁ
          PrimeSpectrum.basicOpen (HomogeneousLocalization.Away.mk 𝒜 f.property.2 n a ha) =
        D[f].ι ⁻¹ᵁ basicOpen 𝒜 a := by
      ext x
      change (HomogeneousLocalization.Away.mk 𝒜 f.property.2 n a ha) ∉
        ((basicOpenIsoSpec 𝒜 f.val.1 f.property.2 f.property.1).hom x).asIdeal ↔
          a ∉ x.val.asHomogeneousIdeal
      rw [hbase]
      exact (ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply 𝒜 x
        ⟨n • f.val.2, ⟨a, ha⟩, ⟨f.val.1 ^ n, SetLike.pow_mem_graded n f.property.2⟩,
          ⟨n, rfl⟩⟩).not
    rw [hopen, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      ← basicOpen_mul]
  · apply HomogeneousLocalization.val_injective
    rw [hU, HomogeneousLocalization.val_pow, HomogeneousLocalization.Away.val_mk]
    change Localization.mk ((f.val.1 * a) ^ f.val.2) _ =
      (Localization.mk a (⟨f.val.1 ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers f.val.1)) ^
        f.val.2
    rw [Localization.mk_pow, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [OneMemClass.coe_one, one_mul]
    dsimp [g]
    simp only [mul_pow, ← pow_mul, pow_add]
    ring

private theorem gradedModuleChart_restriction_transport
    (Z : ∀ f : Fidx, Submodule R[f] N[f])
    (rhoS : ∀ (f g : Fidx), D[g] ≤ D[f] → R[f] →+* R[g])
    (rho : ∀ (f g : Fidx), D[g] ≤ D[f] → Z f →+ Z g)
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
    (f : Fidx) (r : R[f]) (g : Fidx)
    (hg : D[f].ι ''ᵁ
      ((basicOpenIsoSpec 𝒜 f.val.1 f.property.2 f.property.1).hom ⁻¹ᵁ
        PrimeSpectrum.basicOpen r) = D[g]) :
    let e := basicOpenIsoSpec 𝒜 f.val.1 f.property.2 f.property.1
    let E := Scheme.Modules.restrict F D[f].ι
    let V := e.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r
    let k := (e.hom.appLE ⊤ V (by simp)).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of R[f])).inv.hom
    let b := ((F.restrictAppIso D[f].ι ⊤) ≪≫
      F.presheaf.mapIso (eqToIso D[f].ι_image_top.symm).op).addCommGroupIsoToAddEquiv.trans
        (alpha f)
    letI : Module R[f] (E.val.obj (op V)) := Module.compHom (E.val.obj (op V)) k
    ∃ beta : E.val.obj (op V) ≃+ Z g,
      (∀ (x : R[f]) (s : E.val.obj (op V)),
        beta (x • s) = rhoS f g (hg ▸ D[f].ι_image_le V) x • beta s) ∧
      ∀ q : Z f, beta (E.val.map V.leTop.op (b.symm q)) =
        rho f g (hg ▸ D[f].ι_image_le V) q := by
  classical
  let e := basicOpenIsoSpec 𝒜 f.val.1 f.property.2 f.property.1
  let E := Scheme.Modules.restrict F D[f].ι
  let V := e.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r
  let k := (e.hom.appLE ⊤ V (by simp)).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of R[f])).inv.hom
  let : Module R[f] (E.val.obj (op V)) := Module.compHom (E.val.obj (op V)) k
  dsimp only
  let t := (F.restrictAppIso D[f].ι V) ≪≫
    F.presheaf.mapIso (eqToIso hg.symm).op
  let beta := t.addCommGroupIsoToAddEquiv.trans (alpha g)
  refine ⟨beta, ?_, ?_⟩
  · intro x s
    have hc := gradedModuleChart_restriction_constants 𝒜 rhoS hcanonical f r g hg x
    change alpha g (F.presheaf.map (eqToHom hg.symm).op
      ((F.restrictAppIso D[f].ι V).hom (k x • s))) = _
    rw [Scheme.Modules.smul_restrictAppIso_hom_apply]
    rw [F.map_smul, hc, hscalar]
    rfl
  · intro q
    change alpha g (F.presheaf.map (eqToHom hg.symm).op
      (F.presheaf.map (homOfLE (D[f].ι.image_mono (show V ≤ ⊤ from le_top))).op
        (F.presheaf.map (eqToHom D[f].ι_image_top).op ((alpha f).symm q)))) = _
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    have hi : (eqToHom D[f].ι_image_top).op ≫
        (homOfLE (D[f].ι.image_mono (show V ≤ ⊤ from le_top))).op ≫
        (eqToHom hg.symm).op = (homOfLE (hg ▸ D[f].ι_image_le V)).op :=
      Subsingleton.elim _ _
    rw [hi]
    exact (hrestriction f g (hg ▸ D[f].ι_image_le V) ((alpha f).symm q)).trans
      (congrArg (rho f g (hg ▸ D[f].ι_image_le V)) ((alpha f).apply_symm_apply q))


/-- The canonical restriction from a homogeneous chart is a localization map,
with scalars restricted along the pulled-back chart constants.

Source: Stacks Project, Constructions, Tags 01M4 (1)(e),(h), 01M7 and 01MB,
last paragraph. (blueprint: lem-weil-pbc-proj-chart-restriction-is-localized)

Proof:
Write r=a/f^n with a homogeneous of degree n*deg(f), and take the positive-degree
homogeneous element g=f*a. Its chart lies inside the f-chart, and the inverse image
of D(r) has image D_+(g). The intersection formula gives U(f,g)=r^deg(f).
The canonicality assumption identifies rhoS(f,g) with restriction of chart
constants: an S-algebra map out of S_f is determined on each a/f^n by its values
on S and the inverse of f. Transport sections along the open immersion and alpha g.
More precisely, let beta:E(V) ≃+ Z g be this transported alpha g. Naturality of
restrictAppIso and hrestriction give beta(l(q))=rho(f,g)(q). The canonical ring
comparison and hscalar give beta(k(x) • s)=rhoS(f,g)(x) • beta(s). Hence
psi=theta(f,g) inverse composed with beta is an R[f]-linear equivalence from E(V)
to the localization of Z f at U(f,g): htheta identifies the R[f] action through
thetaS with rhoS, and gives psi(l(q))=q/1. Multiplication by U is invertible on
this localization. Each psi(s) has the form q/U^j, so U^j • s=l(q). If
l(q1)=l(q2), equality of q1/1 and q2/1 supplies j with U^j • q1=U^j • q2.
Transport these three facts along psi. Put d=deg(f)>0. Since U=r^d, the last two
facts already use powers r^(d*j). For invertibility, if A is multiplication by r
and B is the inverse of A^d, then A commutes with B and A^(d-1)*B is an inverse
of A. Thus every power of r acts invertibly and all three localization conditions
hold for powers of r; equivalently one can use IsLocalizedModule.of_exists_mul_mem.
For r=0 the open is empty, both the transported module and its localization
are zero and the three conditions still hold. For r a unit restriction is the
whole-chart identification. This result asserts only the universal property of
restriction; it constructs neither the final comparison nor its scalar action. -/
theorem gradedModuleChart_restriction_isLocalized
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
    (f : Fidx) (r : R[f]) :
    let e := basicOpenIsoSpec 𝒜 f.val.1 f.property.2 f.property.1
    let E := Scheme.Modules.restrict F D[f].ι
    let V := e.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r
    let k := (e.hom.appLE ⊤ V (by simp)).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of R[f])).inv.hom
    let b := ((F.restrictAppIso D[f].ι ⊤) ≪≫
      F.presheaf.mapIso (eqToIso D[f].ι_image_top.symm).op).addCommGroupIsoToAddEquiv.trans
        (alpha f)
    letI : Module R[f] (E.val.obj (op V)) := Module.compHom (E.val.obj (op V)) k
    ∀ l : Z f →ₗ[R[f]] E.val.obj (op V),
      (∀ q : Z f, l q = E.val.map V.leTop.op (b.symm q)) →
      IsLocalizedModule (Submonoid.powers r) l := by
  classical
  let e := basicOpenIsoSpec 𝒜 f.val.1 f.property.2 f.property.1
  let E := Scheme.Modules.restrict F D[f].ι
  let V := e.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r
  let k := (e.hom.appLE ⊤ V (by simp)).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of R[f])).inv.hom
  let : Module R[f] (E.val.obj (op V)) := Module.compHom (E.val.obj (op V)) k
  dsimp only
  intro l hl
  obtain ⟨g, hg, hpower⟩ := principalOpen_chart_power 𝒜 U hU f r
  obtain ⟨beta, hbeta_scalar, hbeta_res⟩ :=
    gradedModuleChart_restriction_transport 𝒜 Z rhoS rho hcanonical F alpha hscalar
      hrestriction f r g hg
  let i : D[g] ≤ D[f] := hg ▸ D[f].ι_image_le _
  let psi : (Scheme.Modules.restrict F D[f].ι).val.obj
      (op ((basicOpenIsoSpec 𝒜 f.val.1 f.property.2 f.property.1).hom ⁻¹ᵁ
        PrimeSpectrum.basicOpen r)) ≃ₗ[R[f]] LocalizedModule.Away (U f g) (Z f) :=
    { beta.trans (theta f g i).symm with
      map_smul' := by
        intro x s
        apply (theta f g i).injective
        change theta f g i ((theta f g i).symm (beta (x • s))) =
          theta f g i (x • (theta f g i).symm (beta s))
        rw [(theta f g i).apply_symm_apply]
        rw [hbeta_scalar]
        rw [← IsScalarTower.algebraMap_smul (Localization.Away (U f g)) x]
        rw [(htheta f g i).2.2, (htheta f g i).1]
        simp }
  have hpsi (q : Z f) : psi (l q) = LocalizedModule.mk q 1 := by
    apply (theta f g i).injective
    change theta f g i ((theta f g i).symm (beta (l q))) =
      theta f g i (LocalizedModule.mk q 1)
    rw [(theta f g i).apply_symm_apply]
    rw [hl, hbeta_res, (htheta f g i).2.1]
  have heq : l = psi.symm.toLinearMap.comp
      (LocalizedModule.mkLinearMap (Submonoid.powers (U f g)) (Z f)) := by
    ext q
    apply psi.injective
    simpa using hpsi q
  have : IsLocalizedModule (Submonoid.powers (U f g)) l := by
    rw [heq]
    infer_instance
  apply IsLocalizedModule.of_exists_mul_mem (Submonoid.powers (U f g))
    (Submonoid.powers r) ?_ ?_ l
  · rw [hpower]
    exact Submonoid.powers_le.mpr (Submonoid.pow_mem _ (Submonoid.mem_powers r) _)
  · rintro ⟨x, n, rfl⟩
    refine ⟨r ^ (n * (f.val.2 - 1)), ?_⟩
    rw [hpower, ← pow_add]
    use n
    change (r ^ f.val.2) ^ n = r ^ (n * (f.val.2 - 1) + n)
    rw [← pow_mul]
    congr 1
    have hd : f.val.2 - 1 + 1 = f.val.2 := Nat.sub_add_cancel f.property.1
    calc
      f.val.2 * n = n * f.val.2 := Nat.mul_comm _ _
      _ = n * (f.val.2 - 1) + n := by
        calc
          n * f.val.2 = n * (f.val.2 - 1 + 1) := congrArg (n * ·) hd.symm
          _ = n * (f.val.2 - 1) + n := by rw [Nat.mul_add, Nat.mul_one]

end AlgebraicGeometry.Proj
