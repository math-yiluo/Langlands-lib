/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Module.DegreeZeroFractions
public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import WeilConjectures.AlgebraicGeometry.ProjGradedModuleChartGluing
import WeilConjectures.AlgebraicGeometry.ProjGradedModuleChartQuasicoherent
import WeilConjectures.AlgebraicGeometry.ProjStandardOpenProperties
import WeilConjectures.Topology.SheafOfModulesFromIndexedBasis

/-!
# ProjGradedModuleSheafExtension

Source: Stacks Project, Constructions, Section 01M3, Lemma 01M4, Definition 01M6,
Lemma 01M7 and Lemma 01MB (blueprint: lem-weil-pbc-proj-graded-module-sheaf-extension).

The degree-zero modules are submodules with the already defined `degreeZeroFractions`
as carriers. All choices of fraction representatives occur in the restriction formula.
The section identifications are additive equivalences with explicit scalar compatibility.
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
(blueprint: lem-weil-pbc-proj-graded-module-sheaf-extension) -/
local instance localizedModuleHomogeneousScalarsExtension (T : Submonoid S) :
    Module (HomogeneousLocalization 𝒜 T) (LocalizedModule T M) :=
  Module.compHom (LocalizedModule T M)
    (algebraMap (HomogeneousLocalization 𝒜 T) (Localization T))

set_option quotPrecheck false

local notation "Fidx" => {p : S × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2}
local notation "R[" f "]" => HomogeneousLocalization.Away 𝒜 (f).val.1
local notation "N[" f "]" => LocalizedModule.Away (f).val.1 M
local notation "D[" f "]" => basicOpen 𝒜 (f).val.1
local notation "T[" x "]" => (x).asHomogeneousIdeal.toIdeal.primeCompl
local notation "Rp[" x "]" => HomogeneousLocalization 𝒜 T[x]
local notation "Np[" x "]" => LocalizedModule T[x] M
local notation "ModX" => SheafOfModules (moduleRings (Proj 𝒜).toRingedSpace)

private theorem ringRestriction
    (rhoS : ∀ (f g : Fidx), D[g] ≤ D[f] → R[f] →+* R[g])
    (hcanonical : ∀ (f g : Fidx) (i : D[g] ≤ D[f]),
      ∃ l : Localization.Away f.val.1 →+* Localization.Away g.val.1,
        (∀ a : S, l (algebraMap S (Localization.Away f.val.1) a) =
          algebraMap S (Localization.Away g.val.1) a) ∧
        ∀ r : R[f], (rhoS f g i r).val = l r.val) :
    ∀ (f g : Fidx) (i : D[g] ≤ D[f]) (r : R[f]),
      (Proj 𝒜).presheaf.map (homOfLE i).op (awayToSection 𝒜 f.val.1 r) =
        awayToSection 𝒜 g.val.1 (rhoS f g i r) := by
  intro f g i r
  obtain ⟨l, hl, hr⟩ := hcanonical f g i
  apply Subtype.ext
  funext x
  apply HomogeneousLocalization.val_injective
  change
    (((ProjectiveSpectrum.Proj.awayToSection 𝒜 f.val.1).hom r).val
      ⟨x.1, i x.2⟩).val =
    (((ProjectiveSpectrum.Proj.awayToSection 𝒜 g.val.1).hom (rhoS f g i r)).val x).val
  erw [ProjectiveSpectrum.Proj.awayToSection_apply,
    ProjectiveSpectrum.Proj.awayToSection_apply, hr]
  let pf : Localization.Away f.val.1 →+* Localization T[x.1] :=
    IsLocalization.map (M := Submonoid.powers f.val.1)
    (T := T[x.1]) (Localization T[x.1]) (RingHom.id S)
    (Submonoid.powers_le.mpr (i x.2))
  let pg : Localization.Away g.val.1 →+* Localization T[x.1] :=
    IsLocalization.map (M := Submonoid.powers g.val.1)
    (T := T[x.1]) (Localization T[x.1]) (RingHom.id S)
    (Submonoid.powers_le.mpr x.2)
  have he : pf = pg.comp l := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f.val.1)
    ext a
    simp [pf, pg, hl, IsLocalization.map_eq]
  exact RingHom.congr_fun he r.val


/-- Extension for a graded-module chart system.
Source: Stacks Project, Constructions, Section 01M3 before Definition 01M6;
Lemma 01M7 and Lemma 01MB. (blueprint: lem-weil-pbc-proj-graded-module-sheaf-extension)

Proof:
1. For each distinct positive homogeneous standard open choose one denominator. Identity
   and composition give a presheaf of abelian groups on these opens. For any homogeneous
   fraction y/f^m its given restriction has the canonical ordinary localization formula,
   so it agrees with the restriction supplied by gradedModuleAwayRestriction. The same
   is true of rhoS: an ambient map commuting with S is the unique map out of S_f into
   S_g, and injectivity of the homogeneous localization's inclusion determines rhoS.
2. Identify R[f] with the structure-sheaf sections using basicOpenIsoAway. To check ring
   restriction compatibility, take a germ at x in D[g]. awayToSection_germ identifies
   both ring restrictions with the image of the same fraction in S_(x); the ambient
   localization map preserves that fraction. Sheaf separatedness proves their equality.
   Transport scalar actions along the ring equivalences; semilinearity now gives a
   presheaf of modules over the restriction of the structure sheaf to the basis.
3. For a finite cover D[f] = union D[g_i], standardOpenProperties gives generators
   u_i = g_i^deg(f)/f^deg(g_i) of the unit ideal in R[f]. The principal localization
   comparisons in gradedModuleAwayRestriction identify Z[g_i] with Z[f] localized at
   u_i, and Z[g_i*g_j] with Z[f] localized at u_i*u_j. Indeed its generator for the
   product chart equals u_i*u_j, and the given rho agrees with its maps by step 1.
   The comparison's composition law identifies both overlap maps with canonical
   localization maps. coverModuleExact therefore gives existence and uniqueness of
   gluing, including the empty cover. Intersections and finite refinements are given by
   standardOpenProperties. Apply exists_sheafOfModules_from_basis to obtain F.
4. For a denominator f not chosen for its open, transport the basis identification by
   rho from the chosen denominator to f. Its inverse is the reverse rho: composition
   and identity prove both inverse laws. Semilinearity and the ring compatibility of
   step 2 give the scalar law; composition gives the restriction law for all f,g.
   For another chart system on G, the maps beta_f.symm composed with alpha_f are linear
   and compatible. The basis-extension universal property gives a unique morphism to G;
   the inverse chart maps extend likewise, and uniqueness makes the composites identities.
   Any compatible morphism is this one, so the conclusion is uniqueness of the morphism
   together with its being an isomorphism.
5. On the affine chart D[f] identified with Spec R[f], represent an arbitrary principal
   generator r in R[f] by a homogeneous fraction a/f^n with deg(a)=n*deg(f). Put h=f*a,
   a homogeneous element of positive degree (also if a=0). Its standard open is contained
   in D[f] and corresponds to D(r): its principal generator h^deg(f)/f^deg(h) equals
   r^deg(f), which has the same powers localization as r since deg(f)>0. The principal
   localization comparisons of gradedModuleAwayRestriction thus identify F(D[h]) with
   Z[f] localized at r. For two such opens their comparison maps are the canonical ones
   by the fraction formulas and composition. Mathlib's tilde of the R[f]-module Z[f]
   has these same sections and restrictions on principal opens. Basis uniqueness yields
   a module-sheaf isomorphism on D[f]. The tilde sheaf is quasi-coherent, and these affine
   charts cover X, hence F is quasi-coherent. If a chart is empty, its positive homogeneous
   denominator is nilpotent, so its localized ring and module are zero and empty gluing
   is valid. If X is empty the construction is the unique module sheaf on the empty space.
-/
theorem gradedModuleSheaf_extension
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
        ∀ r : R[f], (rhoS f g i r).val = l r.val) :
    ∃ (F : ModX) (alpha : ∀ f : Fidx, F.val.obj (op D[f]) ≃+ Z f),
      (∀ (f : Fidx) (r : R[f]) (s : F.val.obj (op D[f])),
        alpha f ((awayToSection 𝒜 f.val.1 r) • s) = r • alpha f s) ∧
      (∀ (f g : Fidx) (i : D[g] ≤ D[f]) (s : F.val.obj (op D[f])),
        alpha g (F.val.map (homOfLE i).op s) = rho f g i (alpha f s)) ∧
      (∀ (f g : Fidx) (i : D[g] ≤ D[f]) (r : R[f]),
        (Proj 𝒜).presheaf.map (homOfLE i).op (awayToSection 𝒜 f.val.1 r) =
          awayToSection 𝒜 g.val.1 (rhoS f g i r)) ∧
      (∀ (G : ModX) (beta : ∀ f : Fidx, G.val.obj (op D[f]) ≃+ Z f),
        (∀ (f : Fidx) (r : R[f]) (s : G.val.obj (op D[f])),
          beta f ((awayToSection 𝒜 f.val.1 r) • s) = r • beta f s) →
        (∀ (f g : Fidx) (i : D[g] ≤ D[f]) (s : G.val.obj (op D[f])),
          beta g (G.val.map (homOfLE i).op s) = rho f g i (beta f s)) →
        ∃! phi : F ⟶ G, IsIso phi ∧
          ∀ (f : Fidx) (s : F.val.obj (op D[f])),
            beta f (phi.val.app (op D[f]) s) = alpha f s) ∧
      F.IsQuasicoherent := by
  classical
  have hring := ringRestriction 𝒜 rhoS hcanonical
  let D := fun f : Fidx ↦ basicOpen 𝒜 f.val.1
  let R := moduleRings (Proj 𝒜).toRingedSpace
  let e := fun f : Fidx ↦
    (basicOpenIsoAway 𝒜 f.val.1 f.property.2 f.property.1).commRingCatIsoToRingEquiv
  let chartModule (f : Fidx) : Module (R.obj.obj (op (D f))) (Z f) :=
    Module.compHom (Z f) (e f).symm.toRingHom
  let Q := fun f : Fidx ↦ ModuleCat.of (R.obj.obj (op (D f))) (Z f)
  let cap := fun f g : Fidx ↦
    (⟨(f.val.1 * g.val.1, f.val.2 + g.val.2),
      Nat.add_pos_left f.property.1 g.val.2,
      SetLike.mul_mem_graded f.property.2 g.property.2⟩ : Fidx)
  have hcap (f g : Fidx) : D (cap f g) = D f ⊓ D g := by
    exact basicOpen_mul 𝒜 f.val.1 g.val.1
  have hB : Opens.IsBasis (Set.range D) := by
    have heq : Set.range D =
        {U | ∃ (f : S) (d : ℕ), 0 < d ∧ f ∈ 𝒜 d ∧ U = basicOpen 𝒜 f} := by
      ext U
      constructor
      · rintro ⟨f, rfl⟩
        exact ⟨f.val.1, f.val.2, f.property.1, f.property.2, rfl⟩
      · rintro ⟨f, d, hd, hf, rfl⟩
        exact ⟨⟨(f, d), hd, hf⟩, rfl⟩
    rw [heq]
    exact (standardOpenProperties.{u, u, u} 𝒜).1
  have hrefine (f : Fidx) (J : Type u) (V : J → Fidx)
      (hV : (⨆ j, D (V j)) = D f) :
      ∃ (n : ℕ) (W : Fin n → Fidx), (⨆ k, D (W k)) = D f ∧
        ∀ k, ∃ j, D (W k) ≤ D (V j) := by
    obtain ⟨n, g, k, hk, hc, hr⟩ := (standardOpenProperties 𝒜).2.2.2.1
      f.val.1 f.val.2 f.property.1 f.property.2 J (fun j ↦ D (V j)) hV
    exact ⟨n, (fun i ↦ ⟨(g i, k i), hk i⟩), hc.symm, hr⟩
  have rsmul (f g : Fidx) (i : D g ≤ D f)
      (a : R.obj.obj (op (D f))) (q : Q f) :
      rho f g i (a • q) = R.obj.map (homOfLE i).op a • rho f g i q := by
    obtain ⟨r, rfl⟩ := (e f).surjective a
    change rho f g i ((e f).symm (e f r) • q) =
      (e g).symm ((Proj 𝒜).presheaf.map (homOfLE i).op (e f r)) • rho f g i q
    rw [(e f).symm_apply_apply]
    change rho f g i (r • q) =
      (e g).symm ((Proj 𝒜).presheaf.map (homOfLE i).op
        (awayToSection 𝒜 f.val.1 r)) • rho f g i q
    rw [hring]
    change rho f g i (r • q) = (e g).symm (e g (rhoS f g i r)) • rho f g i q
    rw [(e g).symm_apply_apply]
    exact (hlaws.1 f g i).2.1 r q
  have hglue := gradedModuleChart_gluing 𝒜 𝓜 h𝓜 hsmul Z hZ rhoS rho hlaws hcanonical
  obtain ⟨F, iota, hiota, hmap⟩ := Opens.exists_sheafOfModules_from_indexed_basis
    (Proj 𝒜).toTopCat Fidx D hB cap hcap hrefine R Q rho
    (fun f q ↦ hlaws.2.1 f le_rfl q)
    (fun f g h i j q ↦ hlaws.2.2.1 f g h i j q) rsmul hglue
  let alpha := fun f : Fidx ↦ (iota f).toAddEquiv
  have hscalar (f : Fidx) (r : HomogeneousLocalization.Away 𝒜 f.val.1)
      (s : F.val.obj (op (D f))) :
      alpha f ((awayToSection 𝒜 f.val.1 r) • s) = r • alpha f s := by
    have hh := (iota f).map_smul (e f r) s
    change alpha f ((awayToSection 𝒜 f.val.1 r) • s) =
      (e f).symm (e f r) • alpha f s at hh
    simpa only [RingEquiv.symm_apply_apply] using hh
  refine ⟨F, alpha, hscalar, hiota, hring, ?_, ?_⟩
  · intro G beta hbscalar hbrestrict
    let psi : ∀ f : Fidx, Q f →ₗ[R.obj.obj (op (D f))] G.val.obj (op (D f)) :=
      fun f ↦
        { toAddHom := (beta f).symm.toAddMonoidHom
          map_smul' := by
            intro a q
            obtain ⟨r, rfl⟩ := (e f).surjective a
            apply (beta f).injective
            change beta f ((beta f).symm ((e f).symm (e f r) • q)) =
              beta f ((awayToSection 𝒜 f.val.1 r) • (beta f).symm q)
            rw [AddEquiv.apply_symm_apply, hbscalar,
              AddEquiv.apply_symm_apply, RingEquiv.symm_apply_apply] }
    have hpsi (f g : Fidx) (i : D g ≤ D f) (q : Q f) :
        psi g (rho f g i q) = G.val.map (homOfLE i).op (psi f q) := by
      apply (beta g).injective
      change beta g ((beta g).symm (rho f g i q)) =
        beta g (G.val.map (homOfLE i).op ((beta f).symm q))
      rw [AddEquiv.apply_symm_apply, hbrestrict, AddEquiv.apply_symm_apply]
    obtain ⟨hunique, hiso⟩ := hmap G psi hpsi
    obtain ⟨phi, hphi, huniq⟩ := hunique
    have hcompat : ∀ (f : Fidx) (s : F.val.obj (op (D f))),
        beta f (phi.val.app (op (D f)) s) = alpha f s := by
      intro f s
      rw [hphi]
      exact (beta f).apply_symm_apply (alpha f s)
    refine ⟨phi, ⟨hiso phi hphi (fun f ↦ (beta f).symm.bijective), hcompat⟩, ?_⟩
    intro phi' hphi'
    apply huniq phi'
    intro f s
    apply (beta f).injective
    change beta f (phi'.val.app (op (D f)) s) = beta f ((beta f).symm (alpha f s))
    rw [hphi'.2, AddEquiv.apply_symm_apply]
  · exact gradedModuleChart_quasicoherent 𝒜 𝓜 h𝓜 hsmul Z hZ rhoS rho hlaws
      hcanonical F alpha hscalar hiota

end AlgebraicGeometry.Proj
