/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Module.DegreeZeroFractions
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import WeilConjectures.AlgebraicGeometry.ProjStandardOpenProperties
import Mathlib.Topology.Sheaves.Stalks
import WeilConjectures.AlgebraicGeometry.ProjGradedModuleStalkMap
import WeilConjectures.AlgebraicGeometry.HomogeneousVectorAnnihilator

/-!
# ProjGradedModuleSheafStalks

Source: Stacks Project, Constructions, Section 01M3, Lemma 01M4, Definition 01M6,
Lemma 01M7 and Lemma 01MB (blueprint: lem-weil-pbc-proj-graded-module-sheaf-stalks).

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
(blueprint: lem-weil-pbc-proj-graded-module-sheaf-stalks) -/
local instance localizedModuleHomogeneousScalarsStalks (T : Submonoid S) :
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

private noncomputable def primeDegreeZeroSubmodule
    (𝓜 : ℤ → AddSubgroup M)
    (hsmul : ∀ (n : ℕ) (z : ℤ) (a : S) (y : M),
      a ∈ 𝒜 n → y ∈ 𝓜 z → a • y ∈ 𝓜 (n + z))
    (x : Proj 𝒜) : Submodule Rp[x] Np[x] where
  carrier := degreeZeroFractions (fun n : ℕ ↦ (𝒜 n : Set S))
    (fun n : ℕ ↦ (𝓜 n : Set M)) T[x]
  zero_mem' := ⟨0, 0, 1, (𝓜 0).zero_mem, SetLike.GradedOne.one_mem, zero_mk 1⟩
  add_mem' := by
    rintro _ _ ⟨d, y, t, hy, ht, rfl⟩ ⟨e, z, v, hz, hv, rfl⟩
    refine ⟨d + e, (v : S) • y + (t : S) • z, t * v, ?_,
      SetLike.mul_mem_graded ht hv, (mk_add_mk).symm⟩
    apply (𝓜 ((d + e : ℕ) : ℤ)).add_mem
    · simpa only [Nat.cast_add, add_comm] using hsmul e d v y hv hy
    · simpa only [Nat.cast_add] using hsmul d e t z ht hz
  smul_mem' := by
    intro r q hq
    obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective r
    rcases hq with ⟨d, y, t, hy, ht, rfl⟩
    refine ⟨c.deg + d, (c.num : S) • y, ⟨c.den, c.den_mem⟩ * t, ?_,
      SetLike.mul_mem_graded c.den.prop ht, ?_⟩
    · change (c.num : S) • y ∈ 𝓜 ((c.deg + d : ℕ) : ℤ)
      simpa only [Nat.cast_add] using hsmul c.deg d c.num y c.num.prop hy
    · change LocalizedModule.mk _ _ = (algebraMap Rp[x] (Localization T[x])
        (HomogeneousLocalization.mk c)) • mk y t
      rw [HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.val_mk,
        mk_smul_mk]

/-- Stalks for a graded-module chart system.
Source: Stacks Project, Constructions, Section 01M3 before Definition 01M6;
Lemma 01M7 and Lemma 01MB. (blueprint: lem-weil-pbc-proj-graded-module-sheaf-stalks)

Proof:
1. Positive homogeneous standard opens containing x form a cofinal system of
   neighbourhoods by standardOpenProperties, directed by multiplying denominators.
   Sending y/f^m to the same fraction in the prime localization is the ordinary
   localization map, restricted to Z[f]. This does not depend on a representative,
   preserves addition, and lands in equal-degree fractions. The given rho commutes
   with this map by its fraction formula. Germ representatives and equality after
   shrinking (exists_mem_germ_eq_of_isBasis and germ_eq_of_isBasis) therefore define
   an additive map on F_x.
2. Equal-degree fractions at the prime form a submodule over S_(x). For sums of y/t
   and y'/t', use the numerator t' • y + t • y' and denominator t*t', of equal degrees.
   Negatives and zero are immediate. For a homogeneous scalar a/b of degree zero use
   numerator a • y and denominator b*t; the graded scalar law gives the required degree.
3. For surjectivity choose a positive homogeneous f0 outside the prime, which exists
   since the prime avoids the irrelevant ideal. Any y/t of equal degree is the image
   of (f0 • y)/(t*f0) on D_+(t*f0), whose positive degree is deg(t)+deg(f0).
4. For injectivity choose a representative y/f^m with homogeneous y; hZ ensures every
   chart element admits such a representative. If it is zero in the prime localization,
   some c outside the prime annihilates y. Decompose c into homogeneous components.
   The terms c_k • y lie in distinct graded pieces, so internality of the grading of M
   forces every c_k • y to be zero. Since the prime is homogeneous and c is outside it,
   one component c_k is outside it. Write b=c_k and shrink to D_+(f*b), which contains x
   and has positive degree even when deg(b)=0. The relation f*b=b*f gives restriction
   b^m • y/(f*b)^m. If m>0 this is zero because b • y=0. If m=0 its fraction y/1 is
   also zero: the first power of the new denominator f*b annihilates y. Thus the germ
   is zero. Bijectivity packages the additive map as an additive equivalence.
5. Represent a scalar and a section germ on a common standard neighbourhood. The chart
   scalar law and awayToSection_germ identify their product with multiplication of the
   corresponding prime-localized fractions; this is semilinearity over stalkIso. The
   defining map sends a homogeneous chart representative to its unchanged fraction.
   For any other representative of the same chart element, the ordinary localization
   map also has that formula, so the germ formula holds for every y,f,m and denominator
   witness appearing in the conclusion, not just for the homogeneous representative
   used in step 4. If M is zero the equivalence is between zero modules; if X is empty
   all stalk conclusions are vacuous.
-/
theorem gradedModuleSheaf_stalks
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
    (F : ModX) (alpha : ∀ f : Fidx, F.val.obj (op D[f]) ≃+ Z f)
    (hchart : (∀ (f : Fidx) (r : R[f]) (s : F.val.obj (op D[f])),
        alpha f ((awayToSection 𝒜 f.val.1 r) • s) = r • alpha f s) ∧
      (∀ (f g : Fidx) (i : D[g] ≤ D[f]) (s : F.val.obj (op D[f])),
        alpha g (F.val.map (homOfLE i).op s) = rho f g i (alpha f s))) :
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
          ((alpha f).symm q)) : Np[x]) = mk y t) := by
  classical
  let Zp := primeDegreeZeroSubmodule 𝒜 𝓜 hsmul
  have hZp : ∀ x : Proj 𝒜, (Zp x : Set Np[x]) = degreeZeroFractions
      (fun n : ℕ ↦ (𝒜 n : Set S)) (fun n : ℕ ↦ (𝓜 n : Set M)) T[x] :=
    fun _ ↦ rfl
  obtain ⟨tau, hscalar, hformula⟩ := gradedModuleStalkMap 𝒜 𝓜 hsmul
    Z hZ rhoS rho hlaws F alpha hchart Zp hZp
  have hB := (standardOpenProperties.{u, u, u} 𝒜).1
  have hsurj (x : Proj 𝒜) : Function.Surjective (tau x) := by
    intro q
    have hq : (q : Np[x]) ∈ degreeZeroFractions
        (fun n : ℕ ↦ (𝒜 n : Set S)) (fun n : ℕ ↦ (𝓜 n : Set M)) T[x] := by
      rw [← hZp x]
      exact q.prop
    rcases hq with ⟨d, y, t, hy, ht, heq⟩
    obtain ⟨_, ⟨a, e, he, ha, rfl⟩, hxa, _⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp hB (show x ∈ (⊤ : (Proj 𝒜).Opens) from
        trivial)
    let f : Fidx := ⟨⟨(t : S) * a, d + e⟩,
      Nat.add_pos_right d he, SetLike.mul_mem_graded ht ha⟩
    have hx : x ∈ D[f] := by
      change x ∈ basicOpen 𝒜 ((t : S) * a)
      rw [basicOpen_mul]
      exact ⟨t.prop, hxa⟩
    let v : T[x] := ⟨f.val.1, hx⟩
    let w : Submonoid.powers f.val.1 := ⟨f.val.1 ^ 1, ⟨1, rfl⟩⟩
    have hw : mk (a • y) w ∈ Z f := by
      change mk (a • y) w ∈ (Z f : Set N[f])
      rw [hZ f]
      refine ⟨d + e, a • y, w, ?_, ?_, rfl⟩
      · change a • y ∈ 𝓜 ((d + e : ℕ) : ℤ)
        simpa only [Nat.cast_add, add_comm] using hsmul e d a y ha hy
      · change f.val.1 ^ 1 ∈ 𝒜 (d + e)
        simpa only [pow_one] using f.prop.2
    let qf : Z f := ⟨mk (a • y) w, hw⟩
    refine ⟨TopCat.Presheaf.germ F.val.presheaf D[f] x hx ((alpha f).symm qf), ?_⟩
    apply Subtype.ext
    rw [hformula x f hx 1 (a • y) qf v rfl (pow_one _).symm]
    rw [← heq]
    change mk (a • y) (t * (⟨a, hxa⟩ : T[x])) = mk y t
    exact mk_cancel_common_right t ⟨a, hxa⟩ y
  have hinj (x : Proj 𝒜) : Function.Injective (tau x) := by
    apply (injective_iff_map_eq_zero (tau x)).mpr
    intro s hs
    obtain ⟨_, hx, ⟨a, d, hd, ha, rfl⟩, v, hv⟩ :=
      TopCat.Presheaf.exists_mem_germ_eq_of_isBasis hB F.val.presheaf x s
    let f : Fidx := ⟨⟨a, d⟩, hd, ha⟩
    let q : Z f := alpha f v
    have hq : (q : N[f]) ∈ degreeZeroFractions
        (fun n : ℕ ↦ (𝒜 n : Set S)) (fun n : ℕ ↦ (𝓜 n : Set M))
        (Submonoid.powers a) := by
      rw [← hZ f]
      exact q.prop
    rcases hq with ⟨n, y, t, hy, ht, hrep⟩
    obtain ⟨m, hm⟩ := t.prop
    have hrep' : (q : N[f]) = mk y
        (⟨a ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers a) := by
      have ht_eq : t = (⟨a ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers a) :=
        Subtype.ext hm.symm
      simpa only [ht_eq] using hrep.symm
    let tp : T[x] := ⟨a ^ m, pow_mem (show a ∈ T[x] from hx) m⟩
    have hz : mk y tp = (0 : Np[x]) := by
      have hf := hformula x f hx m y q tp hrep' rfl
      have hg : (alpha f).symm q = v := (alpha f).symm_apply_apply v
      rw [hg, hv, hs] at hf
      exact hf.symm
    obtain ⟨c, hc⟩ := mk_eq.mp (hz.trans (zero_mk 1).symm)
    have hcy : (c : S) • y = 0 := by
      change (c : S) • (1 : S) • y = (c : S) • (tp : S) • (0 : M) at hc
      simpa only [one_smul, smul_zero] using hc
    obtain ⟨k, b, hb, hbx, hby⟩ :=
      homogeneousVectorAnnihilator 𝒜 𝓜 h𝓜 hsmul x n y hy c c.prop hcy
    let g : Fidx := ⟨⟨a * b, d + k⟩,
      Nat.add_pos_left hd k, SetLike.mul_mem_graded ha hb⟩
    have hxg : x ∈ D[g] := by
      change x ∈ basicOpen 𝒜 (a * b)
      rw [basicOpen_mul]
      exact ⟨hx, hbx⟩
    have i : D[g] ≤ D[f] := by
      change basicOpen 𝒜 (a * b) ≤ basicOpen 𝒜 a
      rw [basicOpen_mul]
      exact inf_le_left
    have hrho := (hlaws.1 f g i).2.2 1 k b (by decide) hb
      (by change (a * b) ^ 1 = b * a; simp [mul_comm]) m y q hrep'
    have hzero : rho f g i q = 0 := by
      apply Subtype.ext
      rw [hrho]
      change LocalizedModule.mk _ _ = (0 : N[g])
      rw [← zero_mk (1 : Submonoid.powers g.val.1)]
      apply (mk_eq).mpr
      refine ⟨⟨g.val.1, ⟨1, pow_one _⟩⟩, ?_⟩
      change g.val.1 • (1 : S) • (b ^ m • y) = g.val.1 • _ • (0 : M)
      simp only [one_smul, smul_zero]
      change (a * b) • (b ^ m • y) = 0
      rw [mul_smul, smul_comm b (b ^ m), hby, smul_zero, smul_zero]
    have hvzero : F.val.map (homOfLE i).op v = 0 := by
      apply (alpha g).injective
      rw [hchart.2 f g i v]
      exact hzero.trans (map_zero _).symm
    rw [← hv]
    rw [← TopCat.Presheaf.germ_res_apply F.val.presheaf (homOfLE i) x hxg v]
    change TopCat.Presheaf.germ F.val.presheaf D[g] x hxg
      (F.val.map (homOfLE i).op v) = 0
    rw [hvzero, map_zero]
  let mu := fun x ↦ AddEquiv.ofBijective (tau x) ⟨hinj x, hsurj x⟩
  exact ⟨Zp, hZp, mu, hscalar, hformula⟩

end AlgebraicGeometry.Proj
