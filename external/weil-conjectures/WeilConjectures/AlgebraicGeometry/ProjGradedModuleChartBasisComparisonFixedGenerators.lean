/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Principal-open section comparison for a graded-module chart

Source: Stacks Project, Constructions, Section 01M3 and Lemmas 01M4, 01M7 and 01MB.
(blueprint: lem-weil-pbc-proj-graded-module-chart-basis-comparison-fixed-generators)
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
(blueprint: lem-weil-pbc-proj-graded-module-chart-basis-comparison-fixed-generators) -/
local instance localizedModuleHomogeneousScalarsBasisComparisonFixedGenerators (T : Submonoid S) :
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

private noncomputable local instance restrictedSectionModule {X : Scheme.{u}}
    (F : X.Modules) {U V : X.Opens} (i : U ⟶ V) :
    Module Γ(X, U)
      ((ModuleCat.restrictScalars (X.ringCatSheaf.obj.map i.op).hom).obj
        (F.val.obj (op U))) :=
  inferInstanceAs (Module Γ(X, U) (F.val.obj (op U)))

private theorem restriction_generators {X Y : Scheme.{u}} (F : Y.Modules)
    (j : X ⟶ Y) [IsOpenImmersion j] (V : X.Opens)
    (h : ∀ s : F.val.obj (op (j ''ᵁ V)),
      ∃ (c : Y.ringCatSheaf.obj.obj (op (j ''ᵁ V)))
        (t : F.val.obj (op (j ''ᵁ ⊤))),
        s = c • F.val.map (homOfLE (j.image_mono (show V ≤ ⊤ from le_top))).op t) :
    Submodule.span (X.ringCatSheaf.obj.obj (op V))
      (Set.range ((Scheme.Modules.restrict F j).val.map V.leTop.op)) = ⊤ := by
  apply top_unique
  intro s hs
  obtain ⟨c, t, ht⟩ := h s
  have hsmul : c • F.val.map (homOfLE (j.image_mono (show V ≤ ⊤ from le_top))).op t =
      (j.appIso V).hom c • (Scheme.Modules.restrict F j).val.map V.leTop.op t := by
    have he := Scheme.Modules.smul_restrictAppIso_inv_apply j F V c
      (F.val.map (homOfLE (j.image_mono (show V ≤ ⊤ from le_top))).op t)
    change c • F.val.map (homOfLE (j.image_mono (show V ≤ ⊤ from le_top))).op t =
      (j.appIso V).hom c • (Scheme.Modules.restrict F j).val.map V.leTop.op t at he
    exact he
  rw [ht, hsmul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)

private theorem restriction_generators_of_image_eq {X Y : Scheme.{u}} (F : Y.Modules)
    (j : X ⟶ Y) [IsOpenImmersion j] (V : X.Opens) {A B : Y.Opens}
    (hA : j ''ᵁ V = A) (hB : j ''ᵁ ⊤ = B) (i : A ≤ B)
    (h : ∀ s : F.val.obj (op A),
      ∃ (c : Y.ringCatSheaf.obj.obj (op A)) (t : F.val.obj (op B)),
        s = c • F.val.map (homOfLE i).op t) :
    Submodule.span (X.ringCatSheaf.obj.obj (op V))
      (Set.range ((Scheme.Modules.restrict F j).val.map V.leTop.op)) = ⊤ := by
  subst A B
  exact restriction_generators F j V h

private theorem principalOpen_chart (f : Fidx) (r : R[f]) :
    ∃ g : Fidx, D[f].ι ''ᵁ
      ((basicOpenIsoSpec 𝒜 f.val.1 f.property.2 f.property.1).hom ⁻¹ᵁ
        PrimeSpectrum.basicOpen r) = D[g] := by
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 f.property.2 r
  let g : Fidx := ⟨(f.val.1 * a, f.val.2 + n * f.val.2),
    ⟨by omega, SetLike.mul_mem_graded f.property.2 ha⟩⟩
  refine ⟨g, ?_⟩
  have hbase (x : D[f]) :
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

/-- Restrictions of whole-chart sections generate the sections on each principal open.

Source: Stacks Project, Constructions, Lemma 01M7, and Schemes, Lemma 01HV.
(blueprint: lem-weil-pbc-proj-graded-module-chart-basis-comparison-fixed-generators)

Proof:
For a principal open D(r) of Spec R[f], write r=b/f^n with b homogeneous of
degree n*deg(f), and put g=f*b. The chart intersection formula identifies this
open inside D_+(f) with D_+(g), since U f g=r^deg(f). Transport sections using
alpha f and alpha g. By hrestriction and htheta, restriction from the whole chart
is the canonical map Z f to its localization at U f g. The compatible ring map
is the canonical section restriction by hcanonical. Each localized module
element is a fraction q/(U f g)^k, hence a scalar multiple of the image of q.
Surjectivity of theta supplies this description for every section. Therefore the
image of whole-chart restriction spans over the ring of sections on this open.
Transport back through the chart and restriction identifications. When r=0 the
section module is zero, and the span assertion remains valid. -/
theorem gradedModuleChart_basisComparison_fixed_generators
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
      let B := Set.range (fun r : R[f] ↦ e.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r)
      ∀ V : B, Submodule.span (D[f].toScheme.ringCatSheaf.obj.obj (op V.val))
        (Set.range (E.val.map V.val.leTop.op)) = ⊤ := by
  classical
  dsimp
  intro V
  obtain ⟨r, hr⟩ := V.property
  obtain ⟨g, hg⟩ := principalOpen_chart 𝒜 f r
  have hgV : D[f].ι ''ᵁ V.val = D[g] := by rw [← hr]; exact hg
  have i : D[g] ≤ D[f] := hgV ▸ D[f].ι_image_le V.val
  have hgen (s : F.val.obj (op D[g])) :
      ∃ (c : (Proj 𝒜).ringCatSheaf.obj.obj (op D[g]))
        (t : F.val.obj (op D[f])), s = c • F.val.map (homOfLE i).op t := by
    obtain ⟨x, hx⟩ := (theta f g i).surjective (alpha g s)
    obtain ⟨q, t, hq⟩ :
        ∃ (q : Z f) (t : Submonoid.powers (U f g)), LocalizedModule.mk q t = x := by
      induction x using LocalizedModule.induction_on with
      | h q t => exact ⟨q, t, rfl⟩
    let c : Localization.Away (U f g) := Localization.mk 1 t
    have hc : c • mk q 1 = x := by
      rw [LocalizedModule.mk_smul_mk, one_smul, mul_one]
      exact hq
    have heq : s = (awayToSection 𝒜 g.val.1 (thetaS f g i c)) •
        F.val.map (homOfLE i).op ((alpha f).symm q) := by
      apply (alpha g).injective
      rw [hscalar, hrestriction, (alpha f).apply_symm_apply]
      rw [← (htheta f g i).2.1 q, ← (htheta f g i).2.2 c (mk q 1), hc, hx]
    exact ⟨_, _, heq⟩
  exact restriction_generators_of_image_eq F D[f].ι V.val hgV
    D[f].ι_image_top i hgen

end AlgebraicGeometry.Proj
