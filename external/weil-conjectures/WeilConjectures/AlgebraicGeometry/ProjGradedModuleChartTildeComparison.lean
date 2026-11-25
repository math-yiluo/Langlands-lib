/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Module.DegreeZeroFractions
public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.ProjGradedModuleChartBasisComparison
import WeilConjectures.Algebra.Module.GradedModuleAwayRestriction
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Tilde comparison on a single graded-module chart

Source: Stacks Project, Constructions, Section 01M3 and Lemmas 01M4, 01M7 and 01MB.
(blueprint: lem-weil-pbc-proj-graded-module-chart-tilde-comparison)
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
(blueprint: lem-weil-pbc-proj-graded-module-chart-tilde-comparison) -/
local instance localizedModuleHomogeneousScalarsChartComparison (T : Submonoid S) :
    Module (HomogeneousLocalization 𝒜 T) (LocalizedModule T M) :=
  Module.compHom (LocalizedModule T M)
    (algebraMap (HomogeneousLocalization 𝒜 T) (Localization T))

set_option quotPrecheck false

local notation "Fidx" => {p : S × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2}
local notation "R[" f "]" => HomogeneousLocalization.Away 𝒜 (f).val.1
local notation "N[" f "]" => LocalizedModule.Away (f).val.1 M
local notation "D[" f "]" => basicOpen 𝒜 (f).val.1
local notation "ModX" => SheafOfModules (moduleRings (Proj 𝒜).toRingedSpace)

private theorem chart_iso_of_basis
    {X : TopCat.{u}} {B : Set (Opens X)} (hB : Opens.IsBasis B)
    {R : TopCat.Sheaf RingCat.{u} X} (E G : SheafOfModules.{u} R)
    (l : ∀ U : B, E.val.obj (op U.val) ≃ₗ[R.obj.obj (op U.val)]
      G.val.obj (op U.val))
    (hl : ∀ (U V : B) (h : V.val ≤ U.val) (s : E.val.obj (op U.val)),
      l V (E.val.map (homOfLE h).op s) = G.val.map (homOfLE h).op (l U s)) :
    Nonempty (E ≅ G) := by
  classical
  let β : (inducedFunctor (fun U : B ↦ U.val)).op ⋙ E.val.presheaf ⟶
      (inducedFunctor (fun U : B ↦ U.val)).op ⋙ G.val.presheaf :=
    { app := fun U ↦ AddCommGrpCat.ofHom (l U.unop).toAddMonoidHom
      naturality := by
        intro U V f
        ext s
        exact hl U.unop V.unop f.unop.hom.le s }
  have hb : Opens.IsBasis (Set.range (fun U : B ↦ U.val)) := by
    simpa only [Subtype.range_coe] using hB
  let γ : E.val.presheaf ⟶ G.val.presheaf := TopCat.Sheaf.restrictHomEquivHom E.val.presheaf
    ((SheafOfModules.toSheaf R).obj G) hb β
  have hγ (U : B) (s : E.val.obj (op U.val)) : γ.app (op U.val) s = l U s := by
    change (TopCat.Sheaf.restrictHomEquivHom E.val.presheaf
      ((SheafOfModules.toSheaf R).obj G) hb β).app (op U.val) s = _
    rw [TopCat.Sheaf.extend_hom_app]
    rfl
  have hlin (W : (Opens X)ᵒᵖ) (a : R.obj.obj W) (s : E.val.obj W) :
      γ.app W (a • s) = a • (γ.app W s : G.val.obj W) := by
    apply TopCat.Presheaf.section_ext ((SheafOfModules.toSheaf R).obj G) W.unop
    intro x hx
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ := hB.exists_subset_of_mem_open hx W.unop.isOpen
    change TopCat.Presheaf.germ G.val.presheaf W.unop x hx (γ.app W (a • s)) =
      TopCat.Presheaf.germ G.val.presheaf W.unop x hx (a • γ.app W s)
    rw [← TopCat.Presheaf.germ_res_apply G.val.presheaf (homOfLE hUW) x hxU,
      ← TopCat.Presheaf.germ_res_apply G.val.presheaf (homOfLE hUW) x hxU]
    congr 1
    have hn (t : E.val.obj W) :
        G.val.map (homOfLE hUW).op (γ.app W t) =
          γ.app (op U) (E.val.map (homOfLE hUW).op t) :=
      (CategoryTheory.congr_fun (γ.naturality (homOfLE hUW).op) t).symm
    change G.val.map (homOfLE hUW).op (γ.app W (a • s)) =
      G.val.map (homOfLE hUW).op (a • γ.app W s)
    rw [hn, E.val.map_smul, G.val.map_smul, hn, hγ ⟨U, hU⟩, hγ ⟨U, hU⟩, map_smul]
  let f : E ⟶ G := ⟨PresheafOfModules.homMk γ hlin⟩
  have : IsIso ((SheafOfModules.toSheaf R).map f) := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis (B := fun U : B ↦ U.val) hb
    intro U
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    change Function.Bijective (fun s : E.val.obj (op U.val) ↦ γ.app (op U.val) s)
    have hh : (fun s : E.val.obj (op U.val) ↦ γ.app (op U.val) s) =
        fun s ↦ l U s := funext (hγ U)
    rw [hh]
    exact (l U).bijective
  have : IsIso f := isIso_of_reflects_iso f (SheafOfModules.toSheaf R)
  exact ⟨asIso f⟩

/-- On each positive homogeneous chart the given sheaf is the tilde of its degree-zero
module, transported along the canonical affine chart isomorphism.
Source: Stacks Project, Constructions, Section 01M3, Lemmas 01M4, 01M7 (2), and 01MB;
Schemes, Lemma 01HV and Section 01I6.
(blueprint: lem-weil-pbc-proj-graded-module-chart-tilde-comparison)

Proof:
Fix a chart f of degree d > 0. For r in S_(f), choose a homogeneous presentation
r = a/f^n, with a of degree n*d, and set h = f*a. Its degree (n+1)*d is positive,
including when a = 0. Under basicOpenIsoSpec, D_+(h) inside D_+(f) is D(r): the
principal localization element h^d/f^((n+1)*d) is r^d. Localization at r^d is the
same as localization at r since d > 0. Conversely these opens cover the principal
basis of Spec S_(f).

Use gradedModuleAwayRestriction for the degree-zero fraction submodules. Its
comparison theta identifies the module on D_+(h) with the localization of Z f
at r^d, and hence at r. Its submodules equal the specified Z by hZ. To compare
its restriction maps to the specified rho, choose a homogeneous relation h^e=b*f
from hlaws. Every element of the ordinary localization is y/f^m; the two maps
have the same image b^m*y/h^(e*m) by their fraction formulas. Equality follows
by injectivity of the inclusions of Z into the ordinary localized modules.
The ring maps agree as well: hcanonical and uniqueness of ring maps out of S_f
identify their ambient maps, and the inclusion of S_(h) into S_h is injective.
Thus the comparisons are linear for the canonical structure-sheaf restrictions.

Compose these comparisons with alpha, using hscalar and hrestriction. The result
identifies sections of the restriction of F on each principal open with those
of tilde (Z f), whose principal-open sections are localized modules by tilde.toOpen.
For nested principal opens, both restrictions agree on Z f and hence agree by
the localization universal property; this also follows from the comparison
composition law in gradedModuleAwayRestriction. These linear equivalences form
an isomorphism on the principal-open basis. Extend it and its inverse to sheaves
using basis-extension uniqueness; their composites are identities because that
holds on the basis. Transport through basicOpenIsoSpec to obtain the stated iso.
For a nilpotent denominator both localizations are zero; for r=0 the principal
open is empty and the same localization comparison holds. No nonemptiness of a
chart, no finite generation, and no degree-one generation of S is used. -/
theorem gradedModuleChart_tildeComparison
    (𝓜 : ℤ → AddSubgroup M) (h𝓜 : DirectSum.IsInternal 𝓜)
    (hsmul : ∀ (n : ℕ) (z : ℤ) (a : S) (y : M),
      a ∈ 𝒜 n → y ∈ 𝓜 z → a • y ∈ 𝓜 (n + z))
    (Z : ∀ f : Fidx, Submodule R[f] N[f])
    (hZ : (∀ f : Fidx, (Z f : Set N[f]) = degreeZeroFractions
        (fun n : ℕ ↦ (𝒜 n : Set S)) (fun n : ℕ ↦ (𝓜 n : Set M))
        (Submonoid.powers f.val.1)))
    (rhoS : ∀ (f g : Fidx), D[g] ≤ D[f] → R[f] →+* R[g])
    (rho : ∀ (f g : Fidx), D[g] ≤ D[f] → Z f →+ Z g)
    (hlaws : (∀ (f g : Fidx) (i : D[g] ≤ D[f]),
        (∃ (e k : ℕ) (a : S), 0 < e ∧ a ∈ 𝒜 k ∧ g.val.1 ^ e = a * f.val.1) ∧
        (∀ (r : R[f]) (q : Z f), rho f g i (r • q) = rhoS f g i r • rho f g i q) ∧
        (∀ (e k : ℕ) (a : S), 0 < e → a ∈ 𝒜 k → g.val.1 ^ e = a * f.val.1 →
          ∀ (m : ℕ) (y : M) (q : Z f),
            (q : N[f]) = mk y (⟨f.val.1 ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f.val.1) →
            (rho f g i q : N[g]) = mk (a ^ m • y)
              (⟨g.val.1 ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g.val.1))) ∧
      (∀ (f : Fidx) (i : D[f] ≤ D[f]) (q : Z f), rho f f i q = q) ∧
      (∀ (f g h : Fidx) (i : D[g] ≤ D[f]) (j : D[h] ≤ D[g]) (q : Z f),
        rho g h j (rho f g i q) = rho f h (j.trans i) q) ∧
      (∀ (f g : Fidx) (i : D[g] ≤ D[f]), D[f] = D[g] →
        Function.Bijective (rho f g i)))
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
      alpha g (F.val.map (homOfLE i).op s) = rho f g i (alpha f s)) :
    ∀ f : Fidx, Nonempty
      (Scheme.Modules.restrict F D[f].ι ≅
        Scheme.Modules.restrict (tilde (ModuleCat.of R[f] (Z f)))
          (basicOpenIsoSpec 𝒜 f.val.1 f.property.2 f.property.1).hom) := by
  intro f
  let e := basicOpenIsoSpec 𝒜 f.val.1 f.property.2 f.property.1
  let B := Set.range (fun r : R[f] ↦ e.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r)
  have hB : Opens.IsBasis B := by
    have hb := PrimeSpectrum.isBasis_basic_opens (R := R[f]) |>.of_isInducing
      (Scheme.homeoOfIso e).isInducing
    convert hb using 1
    ext U
    simp only [B, Set.mem_range, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨PrimeSpectrum.basicOpen r, ⟨r, rfl⟩, rfl⟩
    · rintro ⟨V, ⟨r, rfl⟩, rfl⟩
      exact ⟨r, rfl⟩
  obtain ⟨Z', hZ', lambda, lambdaS, rho', rhoS', U, hU, hpair, _, _, _,
      theta, thetaS, htheta, _⟩ := gradedModuleAwayRestriction 𝒜 𝓜 h𝓜 hsmul
  have hZZ : Z' = Z := by
    funext f
    apply SetLike.coe_injective
    exact (hZ' f).trans (hZ f).symm
  subst Z'
  have hr (f g : Fidx) (i : D[g] ≤ D[f])
      (p : ∃ (e k : ℕ) (a : S), 0 < e ∧ a ∈ 𝒜 k ∧ g.val.1 ^ e = a * f.val.1)
      (q : Z f) : rho' f g p q = rho f g i q := by
    obtain ⟨e, k, a, he, ha, heq⟩ := (hlaws.1 f g i).1
    rcases hpair f g p with ⟨_, _, _, _, _, hformula, _, _, hrestrict, _, _, _⟩
    have hrep : ∃ (y : M) (s : Submonoid.powers f.val.1), (q : N[f]) = mk y s := by
      induction (q : N[f]) using LocalizedModule.induction_on with
      | _ y s => exact ⟨y, s, rfl⟩
    obtain ⟨y, s, hq⟩ := hrep
    obtain ⟨n, hn⟩ := s.property
    have hs : s = (⟨f.val.1 ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers f.val.1) :=
      Subtype.ext hn.symm
    subst s
    apply Subtype.ext
    rw [hrestrict, hq, hformula e k a he ha heq y n]
    exact ((hlaws.1 f g i).2.2 e k a he ha heq n y q hq).symm
  have hrS (f g : Fidx) (i : D[g] ≤ D[f])
      (p : ∃ (e k : ℕ) (a : S), 0 < e ∧ a ∈ 𝒜 k ∧ g.val.1 ^ e = a * f.val.1)
      (r : R[f]) : rhoS' f g p r = rhoS f g i r := by
    rcases hpair f g p with ⟨_, _, _, _, _, _, hS, _, _, hrestrictS, _, _⟩
    obtain ⟨l, hl, hlr⟩ := hcanonical f g i
    have hSl : l = lambdaS f g p := by
      apply IsLocalization.ringHom_ext (Submonoid.powers f.val.1)
      ext a
      exact (hl a).trans (hS a).symm
    apply HomogeneousLocalization.val_injective
    rw [hrestrictS, hlr, hSl]
  let rel (f g : Fidx) (i : D[g] ≤ D[f]) := (hlaws.1 f g i).1
  have ht (f g : Fidx) (i : D[g] ≤ D[f]) :
      (∀ r : R[f], thetaS f g (rel f g i)
        (algebraMap R[f] (Localization.Away (U f g)) r) = rhoS f g i r) ∧
      (∀ q : Z f, theta f g (rel f g i) (mk q 1) = rho f g i q) ∧
      (∀ (r : Localization.Away (U f g)) (q : LocalizedModule.Away (U f g) (Z f)),
        theta f g (rel f g i) (r • q) = thetaS f g (rel f g i) r •
          theta f g (rel f g i) q) := by
    refine ⟨?_, ?_, (htheta f g (rel f g i)).2.2.2⟩
    · intro r
      exact ((htheta f g (rel f g i)).1 r).trans (hrS f g i _ r)
    · intro q
      exact ((htheta f g (rel f g i)).2.1 q).trans (hr f g i _ q)
  obtain ⟨l, hl⟩ := gradedModuleChart_basisComparison 𝒜 Z rhoS rho U hU
    (fun f g i ↦ theta f g (rel f g i)) (fun f g i ↦ thetaS f g (rel f g i)) ht
    hcanonical F alpha hscalar hrestriction f
  exact chart_iso_of_basis hB _ _ l hl


end AlgebraicGeometry.Proj
