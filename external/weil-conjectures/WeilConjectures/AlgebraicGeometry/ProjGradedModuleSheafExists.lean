/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Module.DegreeZeroFractions
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import WeilConjectures.Algebra.Module.GradedModuleAwayRestriction
import WeilConjectures.AlgebraicGeometry.ProjStandardOpenProperties
import WeilConjectures.AlgebraicGeometry.ProjGradedModuleSheafExtension
import WeilConjectures.AlgebraicGeometry.ProjGradedModuleSheafStalks
import WeilConjectures.AlgebraicGeometry.ProjGradedModuleSheafGlobalSections
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# The module sheaf associated to a graded module on Proj

Source: Stacks Project, Constructions, Section 01M3, Lemma 01M4, Definition 01M6,
Lemma 01M7 and Lemma 01MB (blueprint: lem-weil-pbc-proj-graded-module-sheaf-exists).

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
(blueprint: lem-weil-pbc-proj-graded-module-sheaf-exists) -/
local instance localizedModuleHomogeneousScalars (T : Submonoid S) :
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

/-- The associated sheaf exists, with the canonical restrictions, chart and stalk
identifications, uniqueness, quasi-coherence, and the degree-zero global-section map.
Source: Stacks, Constructions, Section 01M3 before Definition 01M6; Lemmas 01M4,
01M7 and 01MB. (blueprint: lem-weil-pbc-proj-graded-module-sheaf-exists)

Proof (implemented reduction below):
The chart restriction laws are obtained directly from gradedModuleAwayRestriction and
standardOpenProperties. Basis extension and quasi-coherence, and the stalk identification,
are split into their own named theorems. The global-section gluing theorem is proved;
compatibility and global uniqueness are proved here by composition and separatedness.

The source argument for the remaining geometric steps is:
1. By `lem-weil-pbc-proj-standard-open-inclusion`, positive homogeneous standard opens
   form an intersection-stable basis covering Proj. An inclusion is equivalent to
   a homogeneous relation `g^e = a*f`, and standard covers refine to finite ones.
2. `lem-weil-pbc-graded-module-away-restriction` gives the restriction formula by
   localization, independence of the witnesses, scalar compatibility, identities,
   composition and inverse maps when the standard opens coincide.
3. Choose one denominator for each basis open. The maps of step 2 give a presheaf
   on this basis. `lem-weil-pbc-proj-structure-sheaf-standard-sections` identifies
   its coefficient rings with the structure sheaf, compatibly with restrictions:
   the two restricted fractions have the same germ in every homogeneous prime.
4. For a finite standard cover, the elements `g_i^deg(f)/f^deg(g_i)` generate the
   unit ideal. The principal localization comparisons of step 2 turn the sheaf
   sequence into the module localization sequence, exact by
   `lem-weil-pbc-cover-module-exact`. Thus the basis presheaf is a sheaf on the basis.
5. Apply `lem-weil-pbc-sheaf-of-modules-from-basis` to extend it to all opens.
   Compatible basis identifications induce a unique morphism, which is an
   isomorphism when the identifications are; this gives the asserted uniqueness.
6. On Spec of a chart ring, a principal open is another positive homogeneous
   standard open by `lem-weil-pbc-proj-basic-open-intersection`. Step 2 identifies
   its sections with the corresponding localized chart module. By
   `lem-weil-pbc-spec-module-tilde-sections` and uniqueness of basis extension this
   is the tilde of the chart module. Hence the sheaf is quasi-coherent.
7. Its stalk is the filtered colimit of these chart modules. Fractions map to
   equal-degree fractions with denominators outside the prime. For surjectivity,
   multiply numerator and denominator by a positive homogeneous element outside
   the prime; for injectivity a homogeneous denominator outside the prime killing
   the numerator also kills the germ on a smaller standard open. Germs respect
   scalar multiplication, so the stalk identification respects `stalkIso`.
8. The fractions `m/1` for `m` of degree zero are compatible on the covering basis.
   Sheaf gluing gives a unique global section. Uniqueness makes this assignment
   additive and compatible with the coefficient map from degree-zero scalars.
-/
theorem gradedModuleSheaf_exists
    (𝓜 : ℤ → AddSubgroup M) (h𝓜 : DirectSum.IsInternal 𝓜)
    (hsmul : ∀ (n : ℕ) (z : ℤ) (a : S) (y : M),
      a ∈ 𝒜 n → y ∈ 𝓜 z → a • y ∈ 𝓜 (n + z)) :
    ∃ (Z : ∀ f : Fidx, Submodule R[f] N[f]),
      (∀ f : Fidx, (Z f : Set N[f]) = degreeZeroFractions
        (fun n : ℕ ↦ (𝒜 n : Set S)) (fun n : ℕ ↦ (𝓜 n : Set M))
        (Submonoid.powers f.val.1)) ∧
    ∃ (rhoS : ∀ (f g : Fidx), D[g] ≤ D[f] → R[f] →+* R[g])
      (rho : ∀ (f g : Fidx), D[g] ≤ D[f] → Z f →+ Z g),
      (∀ (f g : Fidx) (i : D[g] ≤ D[f]),
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
        Function.Bijective (rho f g i)) ∧
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
      F.IsQuasicoherent ∧
    ∃ (Zp : ∀ x : Proj 𝒜, Submodule Rp[x] Np[x]),
      (∀ x : Proj 𝒜, (Zp x : Set Np[x]) = degreeZeroFractions
        (fun n : ℕ ↦ (𝒜 n : Set S)) (fun n : ℕ ↦ (𝓜 n : Set M)) T[x]) ∧
    ∃ (mu : ∀ x : Proj 𝒜,
      (RingedSpace.moduleStalkFunctor (Proj 𝒜).toRingedSpace x).obj F ≃+ Zp x),
      (∀ (x : Proj 𝒜) (r : (Proj 𝒜).presheaf.stalk x)
        (s : (RingedSpace.moduleStalkFunctor (Proj 𝒜).toRingedSpace x).obj F),
        mu x (r • s) = (stalkIso 𝒜 x).hom r • mu x s) ∧
      (∀ (x : Proj 𝒜) (f : Fidx) (hx : x ∈ D[f]) (m : ℕ) (y : M)
        (q : Z f) (t : T[x]),
        (q : N[f]) = mk y (⟨f.val.1 ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f.val.1) →
        (t : S) = f.val.1 ^ m →
        (mu x (TopCat.Presheaf.germ F.val.presheaf D[f] x hx
          ((alpha f).symm q)) : Np[x]) = mk y t) ∧
    ∃ (eta : 𝒜 0 →+* (Proj 𝒜).presheaf.obj (op ⊤))
      (gamma : 𝓜 0 →+ F.val.obj (op ⊤)),
      (∀ (r : 𝒜 0) (f : Fidx),
        (Proj 𝒜).presheaf.map (homOfLE (le_top : D[f] ≤ ⊤)).op (eta r) =
          awayToSection 𝒜 f.val.1 (fromZeroRingHom 𝒜 _ r)) ∧
      (∀ (r : 𝒜 0) (m : 𝓜 0),
        gamma ⟨(r : S) • (m : M), hsmul 0 0 r m r.property m.property⟩ =
          eta r • gamma m) ∧
      (∀ (m : 𝓜 0) (f : Fidx),
        (alpha f (F.val.map (homOfLE (le_top : D[f] ≤ ⊤)).op (gamma m)) : N[f]) =
          mk (m : M) 1) ∧
      (∀ (m : 𝓜 0) (f g : Fidx) (i : D[g] ≤ D[f]),
        rho f g i
          (alpha f (F.val.map (homOfLE (le_top : D[f] ≤ ⊤)).op (gamma m))) =
          alpha g (F.val.map (homOfLE (le_top : D[g] ≤ ⊤)).op (gamma m))) ∧
      (∀ (m : 𝓜 0) (s : F.val.obj (op ⊤)),
        (∀ f : Fidx,
          (alpha f (F.val.map (homOfLE (le_top : D[f] ≤ ⊤)).op s) : N[f]) =
            mk (m : M) 1) → s = gamma m) := by
  classical
  obtain ⟨Z, hZ, haway⟩ := gradedModuleAwayRestriction 𝒜 𝓜 h𝓜 hsmul
  refine ⟨Z, hZ, ?_⟩
  obtain ⟨lambda, lambdaS, rhoRel, rhoSRel, U, hdata⟩ := haway
  have hmaps := hdata.2.1
  have hid := hdata.2.2.1
  have hcomp := hdata.2.2.2.2.1
  have hRel (f g : Fidx) (i : D[g] ≤ D[f]) :
      ∃ (e k : ℕ) (a : S), 0 < e ∧ a ∈ 𝒜 k ∧ g.val.1 ^ e = a * f.val.1 :=
    ((standardOpenProperties.{u, u, u} 𝒜).2.2.1 f.val.1 g.val.1 f.val.2 g.val.2
      f.property.1 g.property.1 f.property.2 g.property.2).1.mp i
  let rhoS := fun (f g : Fidx) (i : D[g] ≤ D[f]) ↦ rhoSRel f g (hRel f g i)
  let rho := fun (f g : Fidx) (i : D[g] ≤ D[f]) ↦ rhoRel f g (hRel f g i)
  have hmap (f g : Fidx) (i : D[g] ≤ D[f]) :
      (∃ (e k : ℕ) (a : S), 0 < e ∧ a ∈ 𝒜 k ∧ g.val.1 ^ e = a * f.val.1) ∧
      (∀ (r : R[f]) (q : Z f), rho f g i (r • q) = rhoS f g i r • rho f g i q) ∧
      (∀ (e k : ℕ) (a : S), 0 < e → a ∈ 𝒜 k → g.val.1 ^ e = a * f.val.1 →
        ∀ (m : ℕ) (y : M) (q : Z f),
          (q : N[f]) = mk y (⟨f.val.1 ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f.val.1) →
          (rho f g i q : N[g]) = mk (a ^ m • y)
            (⟨g.val.1 ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g.val.1)) := by
    have hm := hmaps f g (hRel f g i)
    refine ⟨hRel f g i, hm.2.2.2.2.2.2.2.2.2.2.1, ?_⟩
    intro e k a he ha hrel m y q hq
    change (rhoRel f g (hRel f g i) q : N[g]) = _
    rw [hm.2.2.2.2.2.2.2.2.1, hq]
    exact hm.2.2.2.2.2.1 e k a he ha hrel y m
  have hid' (f : Fidx) (i : D[f] ≤ D[f]) (q : Z f) : rho f f i q = q :=
    (hid f (hRel f f i)).1 q
  have hcomp' (f g h : Fidx) (i : D[g] ≤ D[f]) (j : D[h] ≤ D[g]) (q : Z f) :
      rho g h j (rho f g i q) = rho f h (j.trans i) q :=
    ((hcomp f g h (hRel f g i) (hRel g h j)).2 (hRel f h (j.trans i))).1 q
  have hbij (f g : Fidx) (i : D[g] ≤ D[f]) (heq : D[f] = D[g]) :
      Function.Bijective (rho f g i) := by
    have j : D[f] ≤ D[g] := le_of_eq heq
    have hleft : Function.LeftInverse (rho g f j) (rho f g i) := by
      intro q
      exact (hcomp' f g f i j q).trans (hid' f (j.trans i) q)
    have hright : Function.RightInverse (rho g f j) (rho f g i) := by
      intro q
      exact (hcomp' g f g j i q).trans (hid' g (i.trans j) q)
    exact ⟨hleft.injective, hright.surjective⟩
  refine ⟨rhoS, rho, hmap, hid', hcomp', hbij, ?_⟩
  have hcanonical (f g : Fidx) (i : D[g] ≤ D[f]) :
      ∃ l : Localization.Away f.val.1 →+* Localization.Away g.val.1,
        (∀ a : S, l (algebraMap S (Localization.Away f.val.1) a) =
          algebraMap S (Localization.Away g.val.1) a) ∧
        ∀ r : R[f], (rhoS f g i r).val = l r.val := by
    have hm := hmaps f g (hRel f g i)
    exact ⟨lambdaS f g (hRel f g i), hm.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.1⟩
  obtain ⟨F, alpha, hscalar, hres, hring, hunique, hqc⟩ :=
    gradedModuleSheaf_extension 𝒜 𝓜 h𝓜 hsmul Z hZ rhoS rho
      ⟨hmap, hid', hcomp', hbij⟩ hcanonical
  refine ⟨F, alpha, hscalar, hres, hring, hunique, hqc, ?_⟩
  obtain ⟨Zp, hZp, mu, hmuScalar, hmuGerm⟩ :=
    gradedModuleSheaf_stalks 𝒜 𝓜 h𝓜 hsmul Z hZ rhoS rho
      ⟨hmap, hid', hcomp', hbij⟩ F alpha ⟨hscalar, hres⟩
  refine ⟨Zp, hZp, mu, hmuScalar, hmuGerm, ?_⟩
  obtain ⟨eta, gamma, heta, hgammaScalar, hgammaRes⟩ :=
    gradedModuleSheaf_globalSections 𝒜 𝓜 h𝓜 hsmul Z hZ rhoS rho
      ⟨hmap, hid', hcomp', hbij⟩ F alpha ⟨hscalar, hres⟩ hcanonical hring
  refine ⟨eta, gamma, heta, hgammaScalar, hgammaRes, ?_, ?_⟩
  · intro m f g i
    rw [← hres f g i]
    congr 1
    rw [← F.val.map_comp_apply]
    rfl
  · have hcover : (⊤ : (Proj 𝒜).Opens) ≤ ⨆ f : Fidx, D[f] := by
      intro x hx
      obtain ⟨V, ⟨f, d, hd, hf, rfl⟩, hxV, _⟩ :=
        TopologicalSpace.Opens.isBasis_iff_nbhd.mp
          (standardOpenProperties.{u, u, u} 𝒜).1 hx
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨(f, d), hd, hf⟩, hxV⟩
    intro m s hs
    let E : TopCat.Sheaf AddCommGrpCat (Proj 𝒜) := ⟨F.val.presheaf, F.isSheaf⟩
    apply E.eq_of_locally_eq' (fun f : Fidx ↦ D[f]) ⊤
      (fun _ ↦ homOfLE le_top) hcover s (gamma m)
    intro f
    apply (alpha f).injective
    apply Subtype.ext
    exact (hs f).trans (hgammaRes m f).symm

end AlgebraicGeometry.Proj
