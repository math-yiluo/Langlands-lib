/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.ProjGradedModuleChartBasisComparisonFixed

/-!
# Principal-open section comparison for a graded-module chart

Source: Stacks Project, Constructions, Section 01M3 and Lemmas 01M4, 01M7 and 01MB.
(blueprint: lem-weil-pbc-proj-graded-module-chart-basis-comparison)
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
(blueprint: lem-weil-pbc-proj-graded-module-chart-basis-comparison) -/
local instance localizedModuleHomogeneousScalarsBasisComparison (T : Submonoid S) :
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

/-- The fraction-chart descriptions give compatible linear equivalences on the principal
open basis of a fixed affine chart. This asserts only the sectionwise comparison;
extending these maps to a morphism of sheaves is a separate step.

Source: Stacks Project, Constructions, Lemma 01MB (lemma-proj-scheme), last paragraph,
Lemma 01M4 (lemma-standard-open), (1)(e),(g),(h), and Lemma 01M7 (lemma-proj-sheaves).
(blueprint: lem-weil-pbc-proj-graded-module-chart-basis-comparison)

Proof:
Fix f of degree d>0 and write r in R[f] as a/f^n with a homogeneous of degree n*d.
Put h=f*a of degree (n+1)*d. Under basicOpenIsoSpec the preimage of D(r) is D_+(h):
the usual localization element is h^d/f^((n+1)*d)=r^d, and D(r^d)=D(r).
By hU, the principal localization parameter U f h equals r^d. The supplied
comparisons theta and thetaS therefore identify Z h and R[h] with localization
of Z f and R[f] at r^d, hence at r (invert r by r^(d-1)/r^d).
The identities htheta identify the localization maps with rho and rhoS;
hcanonical identifies rhoS with the canonical ambient localization maps.
Compose alpha on D_+(h) with this localized equivalence and the principal-open
section equivalence tilde.toOpen. The restriction section equivalences for the
open immersion D[f].ι and the chart isomorphism identify these groups with E(U)
and G(U). The scalar identities hscalar and localization semilinearity make the
composite linear over O_{D[f]}(U). For nested principal opens, hrestriction and
the localization universal property give naturality: the two localized
maps agree on Z f, so agree everywhere by localization uniqueness.
Choose a principal presentation for each U in the range B. Different presentations
have equal open sets; the preceding compatibility identifies the corresponding maps.
This gives l and its displayed compatibility. If r=0 or f is nilpotent, the open is empty and both
section modules are zero, so the same formulas apply. No finite-generation or
nonempty-chart assumption is needed. -/
theorem gradedModuleChart_basisComparison
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
      alpha g (F.val.map (homOfLE i).op s) = rho f g i (alpha f s)) :
    ∀ f : Fidx,
      let e := basicOpenIsoSpec 𝒜 f.val.1 f.property.2 f.property.1
      let E := Scheme.Modules.restrict F D[f].ι
      let G := Scheme.Modules.restrict (tilde (ModuleCat.of R[f] (Z f))) e.hom
      let B := Set.range (fun r : R[f] ↦ e.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r)
      ∃ l : ∀ U : B, E.val.obj (op U.val) ≃ₗ[
          D[f].toScheme.ringCatSheaf.obj.obj (op U.val)]
          G.val.obj (op U.val),
        ∀ (U V : B) (i : V.val ≤ U.val) (s : E.val.obj (op U.val)),
          l V (E.val.map (homOfLE i).op s) = G.val.map (homOfLE i).op (l U s) := by
  intro f
  exact gradedModuleChart_basisComparison_fixed 𝒜 Z rhoS rho U hU theta thetaS htheta
    hcanonical F alpha hscalar hrestriction f

end AlgebraicGeometry.Proj
