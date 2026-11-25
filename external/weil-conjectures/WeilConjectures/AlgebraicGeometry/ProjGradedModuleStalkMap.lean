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

/-!
# ProjGradedModuleStalkMap

Source: Stacks Project, Constructions, Section 01M3, stalk computation before
Definition 01M6 (blueprint: lem-weil-pbc-proj-graded-module-stalk-map).
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace
open LocalizedModule HomogeneousLocalization

set_option backward.isDefEq.respectTransparency false in
/-- Descend compatible additive maps on a basis by choosing germ representatives.
The comparison lemma makes the resulting value independent of the representative;
addition is checked on a common basic neighbourhood. -/
private theorem basisStalkLift
    {X : TopCat.{u}} (P : X.Presheaf AddCommGrpCat.{u})
    {I : Type u} (B : I → Opens X) (hB : Opens.IsBasis (Set.range B))
    (x : X) {A : Type u} [AddCommGroup A]
    (c : ∀ i, x ∈ B i → P.obj (op (B i)) →+ A)
    (hc : ∀ i j (hi : x ∈ B i) (hj : x ∈ B j) (hji : B j ≤ B i)
      (s : P.obj (op (B i))),
      c j hj (P.map (homOfLE hji).op s) = c i hi s) :
    ∃ t : P.stalk x →+ A, ∀ i (hi : x ∈ B i) (s : P.obj (op (B i))),
      t (P.germ (B i) x hi s) = c i hi s := by
  classical
  have reps (s : P.stalk x) :
      ∃ (i : I) (hi : x ∈ B i) (a : P.obj (op (B i))), P.germ (B i) x hi a = s := by
    obtain ⟨U, hxU, ⟨i, rfl⟩, a, ha⟩ :=
      TopCat.Presheaf.exists_mem_germ_eq_of_isBasis hB P x s
    exact ⟨i, hxU, a, ha⟩
  have reps' := reps
  choose i hi a ha using reps
  let t : P.stalk x → A := fun s ↦ c (i s) (hi s) (a s)
  have ht (j : I) (hj : x ∈ B j) (b : P.obj (op (B j))) :
      t (P.germ (B j) x hj b) = c j hj b := by
    obtain ⟨W, hxW, ⟨k, rfl⟩, hWi, hWj, heq⟩ :=
      TopCat.Presheaf.germ_eq_of_isBasis hB P x (hi _) hj (ha _)
    exact (hc (i _) k (hi _) hxW hWi (a _)).symm.trans
      ((congrArg (c k hxW) heq).trans (hc j k hj hxW hWj b))
  have hadd (s t' : P.stalk x) : t (s + t') = t s + t t' := by
    obtain ⟨j, hj, b, rfl⟩ := reps' s
    obtain ⟨k, hk, d, rfl⟩ := reps' t'
    obtain ⟨W, ⟨l, rfl⟩, hl, hW⟩ :=
      Opens.isBasis_iff_nbhd.mp hB (show x ∈ B j ⊓ B k from ⟨hj, hk⟩)
    have hWj : B l ≤ B j := hW.trans inf_le_left
    have hWk : B l ≤ B k := hW.trans inf_le_right
    rw [← P.germ_res_apply (homOfLE hWj) x hl b,
      ← P.germ_res_apply (homOfLE hWk) x hl d, ← map_add]
    rw [ht, ht, ht, map_add]
  exact ⟨AddMonoidHom.mk' t hadd, ht⟩

namespace AlgebraicGeometry.Proj

variable {S M : Type u} [CommRing S] [AddCommGroup M] [Module S M]
variable (𝒜 : ℕ → AddSubgroup S) [GradedRing 𝒜]

/-- Restrict the ordinary localized module action along the inclusion of the homogeneous
localization. This changes only scalars, not the localization or its operations.
Source: Stacks, Algebra, Section 00JM.
(blueprint: lem-weil-pbc-proj-graded-module-sheaf-stalks) -/
local instance localizedScalarsProjGradedModuleStalkMap (T : Submonoid S) :
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

/-- A chart denominator outside the prime has all its powers outside the prime. -/
private theorem primePowers (x : Proj 𝒜) (f : Fidx) (hx : x ∈ D[f]) :
    Submonoid.powers f.val.1 ≤ T[x] :=
  Submonoid.powers_le.mpr hx

set_option backward.isDefEq.respectTransparency false in
/-- The ordinary localization map preserves the numerator and denominator. -/
private theorem liftOfLE_mk {T U : Submonoid S} (h : T ≤ U) (y : M) (t : T) :
    LocalizedModule.liftOfLE T U h (mk y t) = mk y ⟨t.val, h t.property⟩ := by
  rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.liftOfLE_mk',
    ← IsLocalizedModule.mk_eq_mk']

set_option backward.isDefEq.respectTransparency false in
/-- Restrict the ordinary localization map to the given equal-degree submodules. -/
private noncomputable def chartToPrime
    (𝓜 : ℤ → AddSubgroup M) (Z : ∀ f : Fidx, Submodule R[f] N[f])
    (hZ : ∀ f : Fidx, (Z f : Set N[f]) = degreeZeroFractions
      (fun n : ℕ ↦ (𝒜 n : Set S)) (fun n : ℕ ↦ (𝓜 n : Set M))
      (Submonoid.powers f.val.1))
    (Zp : ∀ x : Proj 𝒜, Submodule Rp[x] Np[x])
    (hZp : ∀ x : Proj 𝒜, (Zp x : Set Np[x]) = degreeZeroFractions
      (fun n : ℕ ↦ (𝒜 n : Set S)) (fun n : ℕ ↦ (𝓜 n : Set M)) T[x])
    (x : Proj 𝒜) (f : Fidx) (hx : x ∈ D[f]) : Z f →+ Zp x where
  toFun q := ⟨LocalizedModule.liftOfLE _ _ (primePowers 𝒜 x f hx) q, by
    have hq : (q : N[f]) ∈ (Z f : Set N[f]) := q.property
    rw [hZ] at hq
    obtain ⟨d, y, t, hy, ht, heq⟩ := hq
    change _ ∈ (Zp x : Set Np[x])
    rw [hZp]
    refine ⟨d, y, ⟨t.val, primePowers 𝒜 x f hx t.property⟩, hy, ht, ?_⟩
    rw [← heq, liftOfLE_mk]⟩
  map_zero' := by apply Subtype.ext; exact map_zero _
  map_add' a b := by
    apply Subtype.ext
    exact (LocalizedModule.liftOfLE _ _ (primePowers 𝒜 x f hx)).map_add
      (a : N[f]) (b : N[f])

set_option backward.isDefEq.respectTransparency false in
/-- Localization respects the homogeneous scalar action, by the fraction formula. -/
private theorem liftOfLE_homogeneous_smul {T U : Submonoid S} (h : T ≤ U)
    (r : HomogeneousLocalization 𝒜 T) (q : LocalizedModule T M) :
    LocalizedModule.liftOfLE T U h (r • q) =
      HomogeneousLocalization.mapId 𝒜 h r • LocalizedModule.liftOfLE T U h q := by
  obtain ⟨r, rfl⟩ := HomogeneousLocalization.mk_surjective r
  induction q using LocalizedModule.induction_on with
  | _ y t =>
    change LocalizedModule.liftOfLE T U h
      ((HomogeneousLocalization.mk r).val • mk y t) =
      (HomogeneousLocalization.mapId 𝒜 h (HomogeneousLocalization.mk r)).val •
        LocalizedModule.liftOfLE T U h (mk y t)
    rw [HomogeneousLocalization.val_mk, LocalizedModule.mk_smul_mk,
      liftOfLE_mk, liftOfLE_mk]
    change _ = (HomogeneousLocalization.mk _).val • _
    rw [HomogeneousLocalization.val_mk, LocalizedModule.mk_smul_mk]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The Proj structure-sheaf stalk comparison sends a chart scalar germ to its
prime-localized scalar. -/
private theorem primeScalarGerm (x : Proj 𝒜) (f : Fidx) (hx : x ∈ D[f])
    (r : R[f]) :
    (stalkIso 𝒜 x).hom
      ((Proj 𝒜).presheaf.germ D[f] x hx (awayToSection 𝒜 f.val.1 r)) =
      HomogeneousLocalization.mapId 𝒜 (primePowers 𝒜 x f hx) r := by
  have h := ConcreteCategory.congr_hom
    (ProjectiveSpectrum.Proj.awayToSection_germ 𝒜 f.val.1 x hx) r
  change (Proj 𝒜).presheaf.germ D[f] x hx (awayToSection 𝒜 f.val.1 r) =
    (stalkIso 𝒜 x).inv (HomogeneousLocalization.mapId 𝒜 (primePowers 𝒜 x f hx) r) at h
  rw [h]
  exact ConcreteCategory.congr_hom ((stalkIso 𝒜 x).inv_hom_id) _

set_option backward.isDefEq.respectTransparency false in
/-- The canonical additive map from chart germs to equal-degree prime-localized fractions.
No injectivity or surjectivity is asserted here.
Source: Stacks Project, Constructions, Section 01M3, stalk computation before
Definition 01M6 (definition-structure-sheaf-proj).
(blueprint: lem-weil-pbc-proj-graded-module-stalk-map)

Proof:
1. On a positive homogeneous chart containing x, include powers of its denominator into
   the prime complement and apply the ordinary localized-module map. Equal-degree
   representatives show that its restriction lands in Zp, using hZ and hZp.
2. Each rho agrees with this map: write a fraction as y/f^m and use the given relation
   g^e=a*f. The image of a^m*y/g^(e*m) equals y/f^m by clearing denominators in the
   prime localization. This holds for every representative by localization equality.
3. Positive standard opens form a basis. Every stalk element has a chart representative;
   two representatives of the same germ agree on a smaller positive standard open.
   The compatibility in step 2 makes the value independent of both choices. Addition
   is checked after restricting two sections to their common product chart. This
   constructs an additive map, not a choice of an arbitrary existence witness.
4. Represent the scalar and section germ on a common positive standard open. A scalar
   section there is awayToSection of a homogeneous localized scalar. The chart scalar
   law and awayToSection_germ identify its image under stalkIso with that scalar's
   prime localization, proving semilinearity. Step 1 gives the formula for every chart
   fraction, without requiring its numerator itself to be homogeneous.
-/
theorem gradedModuleStalkMap
    (𝓜 : ℤ → AddSubgroup M)
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
        alpha g (F.val.map (homOfLE i).op s) = rho f g i (alpha f s)))
    (Zp : ∀ x : Proj 𝒜, Submodule Rp[x] Np[x])
    (hZp : ∀ x : Proj 𝒜, (Zp x : Set Np[x]) = degreeZeroFractions
      (fun n : ℕ ↦ (𝒜 n : Set S)) (fun n : ℕ ↦ (𝓜 n : Set M)) T[x]) :
    ∃ (tau : ∀ x : Proj 𝒜,
      (RingedSpace.moduleStalkFunctor (Proj 𝒜).toRingedSpace x).obj F →+ Zp x),
      (∀ (x : Proj 𝒜) (r : (Proj 𝒜).presheaf.stalk x)
        (s : (RingedSpace.moduleStalkFunctor (Proj 𝒜).toRingedSpace x).obj F),
        tau x (r • s) = (stalkIso 𝒜 x).hom r • tau x s) ∧
      (∀ (x : Proj 𝒜) (f : Fidx) (hx : x ∈ D[f]) (m : ℕ) (y : M)
        (q : Z f) (t : T[x]),
        (q : N[f]) = mk y (⟨f.val.1 ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f.val.1) →
        (t : S) = f.val.1 ^ m →
        (tau x (TopCat.Presheaf.germ F.val.presheaf D[f] x hx
          ((alpha f).symm q)) : Np[x]) = mk y t) := by
  classical
  have _hsmul := hsmul
  let c := chartToPrime 𝒜 𝓜 Z hZ Zp hZp
  have hc (x : Proj 𝒜) (f g : Fidx) (hf : x ∈ D[f]) (hg : x ∈ D[g])
      (i : D[g] ≤ D[f]) (q : Z f) : c x g hg (rho f g i q) = c x f hf q := by
    apply Subtype.ext
    obtain ⟨y, t, ht⟩ : ∃ (y : M) (t : Submonoid.powers f.val.1), mk y t = (q : N[f]) := by
      induction (q : N[f]) using LocalizedModule.induction_on with
      | _ y t => exact ⟨y, t, rfl⟩
    obtain ⟨m, hm⟩ := t.property
    have ht' : t = ⟨f.val.1 ^ m, ⟨m, rfl⟩⟩ := Subtype.ext hm.symm
    subst t
    obtain ⟨⟨e, k, a, he, ha, hrel⟩, _, hformula⟩ := hlaws.1 f g i
    change LocalizedModule.liftOfLE _ _ (primePowers 𝒜 x g hg) _ =
      LocalizedModule.liftOfLE _ _ (primePowers 𝒜 x f hf) _
    rw [hformula e k a he ha hrel m y q ht.symm, ← ht, liftOfLE_mk, liftOfLE_mk]
    apply LocalizedModule.mk_eq.mpr
    refine ⟨1, ?_⟩
    simp only [one_smul, Submonoid.mk_smul]
    rw [← mul_smul, ← mul_pow, mul_comm f.val.1 a, ← hrel, ← pow_mul]
  have hB : Opens.IsBasis (Set.range (fun f : Fidx ↦ D[f])) := by
    convert (standardOpenProperties.{u, u, u} 𝒜).1 using 1
    ext U
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨f.val.1, f.val.2, f.property.1, f.property.2, rfl⟩
    · rintro ⟨f, d, hd, hf, rfl⟩
      exact ⟨⟨(f, d), hd, hf⟩, rfl⟩
  have htau (x : Proj 𝒜) :
      ∃ t : (RingedSpace.moduleStalkFunctor (Proj 𝒜).toRingedSpace x).obj F →+ Zp x,
      ∀ (f : Fidx) (hx : x ∈ D[f]) (s : F.val.obj (op D[f])),
        t (TopCat.Presheaf.germ F.val.presheaf D[f] x hx s) = c x f hx (alpha f s) := by
    apply basisStalkLift F.val.presheaf (fun f : Fidx ↦ D[f]) hB x
      (fun f hx ↦ (c x f hx).comp (alpha f).toAddMonoidHom)
    intro f g hf hg i s
    dsimp only [AddMonoidHom.comp_apply, AddEquiv.toAddMonoidHom_eq_coe]
    change c x g hg (alpha g (F.val.map (homOfLE i).op s)) = c x f hf (alpha f s)
    rw [hchart.2 f g i s]
    exact hc x f g hf hg i (alpha f s)
  choose tau htau using htau
  refine ⟨tau, ?_, ?_⟩
  · intro x r s
    obtain ⟨U, hxU, r, rfl⟩ := (Proj 𝒜).presheaf.exists_germ_eq r
    obtain ⟨V, hxV, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.val.presheaf s
    obtain ⟨W, ⟨f, rfl⟩, hx, hW⟩ :=
      Opens.isBasis_iff_nbhd.mp hB (show x ∈ U ⊓ V from ⟨hxU, hxV⟩)
    have hU : D[f] ≤ U := hW.trans inf_le_left
    have hV : D[f] ≤ V := hW.trans inf_le_right
    rw [← (Proj 𝒜).presheaf.germ_res_apply (homOfLE hU) x hx r,
      ← TopCat.Presheaf.germ_res_apply F.val.presheaf (homOfLE hV) x hx s]
    let r' := (Proj 𝒜).presheaf.map (homOfLE hU).op r
    let s' := F.val.map (homOfLE hV).op s
    change tau x ((Proj 𝒜).presheaf.germ D[f] x hx r' •
      TopCat.Presheaf.germ F.val.presheaf D[f] x hx s') = _
    obtain ⟨a, ha⟩ := ConcreteCategory.bijective_of_isIso
      (basicOpenIsoAway 𝒜 f.val.1 f.property.2 f.property.1).hom |>.surjective r'
    change awayToSection 𝒜 f.val.1 a = r' at ha
    rw [← ha, ← PresheafOfModules.germ_smul (R := (Proj 𝒜).presheaf) F.val]
    rw [htau, htau, hchart.1 f a s']
    change c x f hx (a • alpha f s') =
      (stalkIso 𝒜 x).hom ((Proj 𝒜).presheaf.germ D[f] x hx r') •
        c x f hx (alpha f s')
    rw [← ha, primeScalarGerm]
    apply Subtype.ext
    exact liftOfLE_homogeneous_smul 𝒜 (primePowers 𝒜 x f hx) a (alpha f s' : N[f])
  · intro x f hx m y q t hq ht
    rw [htau, AddEquiv.apply_symm_apply]
    change LocalizedModule.liftOfLE _ _ (primePowers 𝒜 x f hx) (q : N[f]) = _
    rw [hq, liftOfLE_mk]
    congr 1
    exact Subtype.ext ht.symm

end AlgebraicGeometry.Proj
