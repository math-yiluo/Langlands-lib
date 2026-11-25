/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Module.DegreeZeroFractions
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
/-!
# ProjGradedModuleSheafGlobalSections

Source: Stacks Project, Constructions, Section 01M3, Lemma 01M4, Definition 01M6,
Lemma 01M7 and Lemma 01MB (blueprint: lem-weil-pbc-proj-graded-module-sheaf-global-sections).

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
(blueprint: lem-weil-pbc-proj-graded-module-sheaf-global-sections) -/
local instance localizedModuleHomogeneousScalarsGlobalSections (T : Submonoid S) :
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

/-- GlobalSections for a graded-module chart system.
Source: Stacks Project, Constructions, Section 01M3 before Definition 01M6;
Lemma 01M7 and Lemma 01MB. (blueprint: lem-weil-pbc-proj-graded-module-sheaf-global-sections)

Proof: For m in M_0 the fraction m/1 lies in every Z f. The fraction restriction
formula with exponent zero shows that these fractions are compatible on every inclusion
and hence on intersections D_+(fg). The standard opens cover Proj, so the sheaf property
glues their inverse images under alpha uniquely to a global section. Unique gluing of
zero and sums makes this an additive map gamma. Apply the same construction to degree-zero
scalars in the structure sheaf, using fromZeroRingHom and awayToSection; uniqueness of
gluing proves zero, one, addition and multiplication, giving eta. The chart scalar law
shows that gamma(r • m) and eta(r) • gamma(m) agree on all charts, proving the scalar
identity. Naturality and the chart restriction law give compatibility of restrictions.
Any other section with these fraction restrictions agrees chartwise and hence globally.
If Proj is empty, both sheaves have a unique global section; the same gluing proof works.
-/
theorem gradedModuleSheaf_globalSections
    (𝓜 : ℤ → AddSubgroup M) (_h𝓜 : DirectSum.IsInternal 𝓜)
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
    (F : SheafOfModules.{u} (moduleRings (Proj 𝒜).toRingedSpace))
    (alpha : ∀ f : Fidx, F.val.obj (op D[f]) ≃+ Z f)
    (hchart : (∀ (f : Fidx) (r : R[f]) (s : F.val.obj (op D[f])),
        alpha f ((awayToSection 𝒜 f.val.1 r) • s) = r • alpha f s) ∧
      (∀ (f g : Fidx) (i : D[g] ≤ D[f]) (s : F.val.obj (op D[f])),
        alpha g (F.val.map (homOfLE i).op s) = rho f g i (alpha f s)))
    (hcanonical : ∀ (f g : Fidx) (i : D[g] ≤ D[f]),
      ∃ l : Localization.Away f.val.1 →+* Localization.Away g.val.1,
        (∀ a : S, l (algebraMap S (Localization.Away f.val.1) a) =
          algebraMap S (Localization.Away g.val.1) a) ∧
        ∀ r : R[f], (rhoS f g i r).val = l r.val)
    (hring : ∀ (f g : Fidx) (i : D[g] ≤ D[f]) (r : R[f]),
      (Proj 𝒜).presheaf.map (homOfLE i).op (awayToSection 𝒜 f.val.1 r) =
        awayToSection 𝒜 g.val.1 (rhoS f g i r)) :
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
          mk (m : M) 1) := by
  classical
  have hcover : (⊤ : (Proj 𝒜).Opens) ≤ ⨆ f : Fidx, D[f] := by
    intro x hx
    let C := affineOpenCover 𝒜
    let i := C.idx x
    have hxV := C.covers x
    change x ∈ (awayι 𝒜 (i.2 : S) i.2.property i.1.property).opensRange at hxV
    rw [opensRange_awayι] at hxV
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨⟨((i.2 : S), i.1.val), i.1.property, i.2.property⟩, hxV⟩
  let E : TopCat.Sheaf AddCommGrpCat.{u} (Proj 𝒜) := ⟨F.val.presheaf, F.isSheaf⟩
  have hext (s t : F.val.obj (op ⊤))
      (h : ∀ f : Fidx, alpha f (F.val.map (homOfLE le_top).op s) =
        alpha f (F.val.map (homOfLE le_top).op t)) : s = t := by
    apply E.eq_of_locally_eq' (fun f : Fidx ↦ D[f]) ⊤
      (fun _ ↦ homOfLE le_top) hcover s t
    intro f
    exact (alpha f).injective (h f)
  let q (m : 𝓜 0) (f : Fidx) : Z f := ⟨mk (m : M) 1, by
    change mk (m : M) 1 ∈ (Z f : Set N[f])
    rw [hZ f]
    exact ⟨0, m, 1, m.property, SetLike.one_mem_graded 𝒜, rfl⟩⟩
  have hq (m : 𝓜 0) (f g : Fidx) (i : D[g] ≤ D[f]) :
      rho f g i (q m f) = q m g := by
    obtain ⟨e, k, a, he, ha, heq⟩ := (hlaws.1 f g i).1
    apply Subtype.ext
    have hfrac := (hlaws.1 f g i).2.2 e k a he ha heq 0 m (q m f) (by
      dsimp [q]
      congr 1
      apply Subtype.ext
      simp)
    convert hfrac using 1
    · simp only [q, mul_zero, pow_zero, one_smul]
      congr 1
  let sf (m : 𝓜 0) (f : Fidx) := (alpha f).symm (q m f)
  have hsres (m : 𝓜 0) (f g : Fidx) (i : D[g] ≤ D[f]) :
      F.val.map (homOfLE i).op (sf m f) = sf m g := by
    apply (alpha g).injective
    simpa [sf] using (hchart.2 f g i (sf m f)).trans (by simp [sf, hq])
  have hscompat (m : 𝓜 0) :
      TopCat.Presheaf.IsCompatible E.obj (fun f : Fidx ↦ D[f]) (sf m) := by
    intro f g
    let h : Fidx := ⟨(f.val.1 * g.val.1, f.val.2 + g.val.2),
      Nat.add_pos_left f.property.1 _, SetLike.mul_mem_graded f.property.2 g.property.2⟩
    have heq : D[h] = D[f] ⊓ D[g] := basicOpen_mul 𝒜 f.val.1 g.val.1
    have hi : D[h] ≤ D[f] := heq.le.trans inf_le_left
    have hj : D[h] ≤ D[g] := heq.le.trans inf_le_right
    have hh := (hsres m f h hi).trans (hsres m g h hj).symm
    have transfer (V : (Proj 𝒜).Opens) (hv : V = D[f] ⊓ D[g])
        (hi : V ≤ D[f]) (hj : V ≤ D[g])
        (hh : F.val.map (homOfLE hi).op (sf m f) =
          F.val.map (homOfLE hj).op (sf m g)) :
        F.val.map (homOfLE inf_le_left : D[f] ⊓ D[g] ⟶ D[f]).op (sf m f) =
          F.val.map (homOfLE inf_le_right : D[f] ⊓ D[g] ⟶ D[g]).op (sf m g) := by
      subst V
      exact hh
    exact transfer D[h] heq hi hj hh
  have hglue (m : 𝓜 0) : ∃! s : F.val.obj (op ⊤),
      ∀ f : Fidx, alpha f (F.val.map (homOfLE le_top).op s) = q m f := by
    obtain ⟨s, hs, hu⟩ := E.existsUnique_gluing' (fun f : Fidx ↦ D[f]) ⊤
      (fun _ ↦ homOfLE le_top) hcover (sf m) (hscompat m)
    refine ⟨s, ?_, ?_⟩
    · intro f
      change ∀ f, F.val.map (homOfLE (le_top : D[f] ≤ ⊤)).op s = sf m f at hs
      rw [hs f]
      exact (alpha f).apply_symm_apply _
    · intro t ht
      apply hu t
      intro f
      exact (alpha f).injective ((ht f).trans (by simp [sf]))
  let gam : 𝓜 0 → F.val.obj (op ⊤) := fun m ↦ (hglue m).choose
  have hgam (m : 𝓜 0) (f : Fidx) :
      alpha f (F.val.map (homOfLE le_top).op (gam m)) = q m f :=
    (hglue m).choose_spec.1 f
  let gamma : 𝓜 0 →+ F.val.obj (op ⊤) :=
    { toFun := gam
      map_zero' := by
        apply hext
        intro f
        rw [hgam]
        apply Subtype.ext
        simp [q]
      map_add' := by
        intro m n
        apply hext
        intro f
        rw [hgam]
        simp only [map_add, hgam]
        apply Subtype.ext
        change mk ((m : M) + (n : M)) 1 = mk (m : M) 1 + mk (n : M) 1
        exact (mkLinearMap (Submonoid.powers f.val.1) M).map_add m n }
  let O : TopCat.Sheaf CommRingCat.{u} (Proj 𝒜) := (Proj 𝒜).sheaf
  let rf (r : 𝒜 0) (f : Fidx) :=
    awayToSection 𝒜 f.val.1 (fromZeroRingHom 𝒜 _ r)
  have hrres (r : 𝒜 0) (f g : Fidx) (i : D[g] ≤ D[f]) :
      (Proj 𝒜).presheaf.map (homOfLE i).op (rf r f) = rf r g := by
    dsimp [rf]
    rw [hring f g i]
    congr 1
    obtain ⟨l, hbase, hl⟩ := hcanonical f g i
    apply HomogeneousLocalization.val_injective
    rw [hl]
    change l (algebraMap S (Localization.Away f.val.1) (r : S)) =
      algebraMap S (Localization.Away g.val.1) (r : S)
    exact hbase r
  have hrcompat (r : 𝒜 0) :
      TopCat.Presheaf.IsCompatible O.obj (fun f : Fidx ↦ D[f]) (rf r) := by
    intro f g
    let h : Fidx := ⟨(f.val.1 * g.val.1, f.val.2 + g.val.2),
      Nat.add_pos_left f.property.1 _, SetLike.mul_mem_graded f.property.2 g.property.2⟩
    have heq : D[h] = D[f] ⊓ D[g] := basicOpen_mul 𝒜 f.val.1 g.val.1
    have hi : D[h] ≤ D[f] := heq.le.trans inf_le_left
    have hj : D[h] ≤ D[g] := heq.le.trans inf_le_right
    have hh := (hrres r f h hi).trans (hrres r g h hj).symm
    have transfer (V : (Proj 𝒜).Opens) (hv : V = D[f] ⊓ D[g])
        (hi : V ≤ D[f]) (hj : V ≤ D[g])
        (hh : (Proj 𝒜).presheaf.map (homOfLE hi).op (rf r f) =
          (Proj 𝒜).presheaf.map (homOfLE hj).op (rf r g)) :
        (Proj 𝒜).presheaf.map (homOfLE inf_le_left : D[f] ⊓ D[g] ⟶ D[f]).op (rf r f) =
          (Proj 𝒜).presheaf.map (homOfLE inf_le_right : D[f] ⊓ D[g] ⟶ D[g]).op (rf r g) := by
      subst V
      exact hh
    exact transfer D[h] heq hi hj hh
  have hrglue (r : 𝒜 0) : ∃! s : (Proj 𝒜).presheaf.obj (op ⊤),
      ∀ f : Fidx, (Proj 𝒜).presheaf.map (homOfLE le_top).op s = rf r f :=
    O.existsUnique_gluing' (fun f : Fidx ↦ D[f]) ⊤
      (fun _ ↦ homOfLE le_top) hcover (rf r) (hrcompat r)
  let et : 𝒜 0 → (Proj 𝒜).presheaf.obj (op ⊤) := fun r ↦ (hrglue r).choose
  have het (r : 𝒜 0) (f : Fidx) :
      (Proj 𝒜).presheaf.map (homOfLE le_top).op (et r) = rf r f :=
    (hrglue r).choose_spec.1 f
  have hrext (s t : (Proj 𝒜).presheaf.obj (op ⊤))
      (h : ∀ f : Fidx, (Proj 𝒜).presheaf.map (homOfLE le_top).op s =
        (Proj 𝒜).presheaf.map (homOfLE le_top).op t) : s = t :=
    O.eq_of_locally_eq' (fun f : Fidx ↦ D[f]) ⊤
      (fun _ ↦ homOfLE le_top) hcover s t h
  let eta : 𝒜 0 →+* (Proj 𝒜).presheaf.obj (op ⊤) :=
    { toFun := et
      map_zero' := by
        apply hrext
        intro f
        rw [het]
        simp [rf]
      map_one' := by
        apply hrext
        intro f
        rw [het]
        simp [rf]
      map_add' := by
        intro r t
        apply hrext
        intro f
        rw [het]
        simp [rf, het]
      map_mul' := by
        intro r t
        apply hrext
        intro f
        rw [het]
        simp [rf, het] }
  refine ⟨eta, gamma, het, ?_, ?_⟩
  · intro r m
    apply hext
    intro f
    change alpha f (F.val.map (homOfLE le_top).op (gam _)) =
      alpha f (F.val.map (homOfLE le_top).op (et r • gam m))
    rw [hgam, F.val.map_smul]
    change q _ f = alpha f
      ((Proj 𝒜).presheaf.map (homOfLE le_top).op (et r) •
        (show F.val.obj (op D[f]) from F.val.map (homOfLE le_top).op (gam m)))
    rw [het, hchart.1 f, hgam]
    apply Subtype.ext
    dsimp only [q, Submodule.coe_smul]
    change mk ((r : S) • (m : M)) 1 =
      algebraMap (HomogeneousLocalization.Away 𝒜 f.val.1)
        (Localization.Away f.val.1) (fromZeroRingHom 𝒜 _ r) • (mk (m : M) 1 : N[f])
    change mk ((r : S) • (m : M)) 1 =
      (Localization.mk (r : S) (1 : Submonoid.powers f.val.1) :
        Localization.Away f.val.1) • (mk (m : M) 1 : N[f])
    simpa using (mk_smul_mk (r : S) (m : M)
      (1 : Submonoid.powers f.val.1) (1 : Submonoid.powers f.val.1)).symm
  · intro m f
    exact congrArg Subtype.val (hgam m f)


end AlgebraicGeometry.Proj
