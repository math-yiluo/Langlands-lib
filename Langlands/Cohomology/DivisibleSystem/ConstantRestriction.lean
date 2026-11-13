import Langlands.Cohomology.DivisibleSystem.AnalyticQuasiEtaleConstant
import Langlands.Sheaf.Equivariant.AnalyticQuasiEtaleComparison

/-!
# Restriction of constant equivariant sheaves and the comparison with plain cohomology

Let `G` act on an object `X` of a site. Restricting a sheaf on the twisted site to the site
over `X` forgets the equivariant structure. This module shows that the restriction of the
constant sheaf with value `M` is the constant sheaf with value `M`: restriction commutes with
sheafification, and the restriction of a constant presheaf is constant. The same holds for
constant discrete sheaves of modules.

For `G` acting on an analytic space `X`, Berkovich's `b^*` therefore takes the constant
quasi-étale `G`-sheaf `M` to the constant quasi-étale sheaf `M` of `X`. Composing with the
comparison `H^q_c(X{G}, F) → H^q_c(X, b^*F)` of Berkovich's Corollary 1.5.2(i) gives the
comparison `H^q_c(X{G}, M) → H^q_c(X, M)` for constant coefficients, and composing that with
Harris's (2.3) for the constant system `{R / ℓ ^ m R}` gives the map
`H^n(Γ_{c,X{G}}(G^•_m)) → H^n_c(X, R / ℓ ^ m R)` from the cohomology of Harris's complexes to
the plain compactly supported cohomology of `X`. That these comparison maps are isomorphisms
(Berkovich's Corollary 1.5.2(i)) is not proved.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Sheaf.Equivariant.TwistedOver

universe u v w w' uG

section General

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} [P.RespectsIso] {X : C}
variable {G : Type uG} [Group G] (ρ : G →* Aut X)
variable (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]
variable (A : Type w) [Category.{w'} A]
variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ A, (ι P ρ).op.HasPointwiseRightKanExtension F]
variable [HasWeakSheafify J A] [HasWeakSheafify (twistedTopology ρ J) A]

/-- The restriction of the constant sheaf `M` on the twisted site to the site over `X` is the
constant sheaf `M`. Restriction commutes with sheafification
(`pushforwardContinuousSheafificationCompatibility`), and the restriction of the constant
presheaf `M` is, by definition, the constant presheaf `M`; the component at `M` is the inverse
of the compatibility isomorphism at the constant presheaf `M` on the twisted site. -/
def constantSheafCompRestrictionIso :
    constantSheaf (twistedTopology ρ J) A ⋙ TwistedOver.restriction ρ J A ≅ constantSheaf J A :=
  NatIso.ofComponents
    (fun M => (((ι P ρ).pushforwardContinuousSheafificationCompatibility A J
      (twistedTopology ρ J)).app ((Functor.const (TwistedOver P ρ)ᵒᵖ).obj M)).symm)
    (fun f => ((ι P ρ).pushforwardContinuousSheafificationCompatibility A J
      (twistedTopology ρ J)).inv.naturality ((Functor.const (TwistedOver P ρ)ᵒᵖ).map f))

/-- The inverse of `constantSheafCompRestrictionIso` at `M` is the compatibility isomorphism
between restriction and sheafification at the constant presheaf `M` on the twisted site. -/
theorem constantSheafCompRestrictionIso_inv_app (M : A) :
    (constantSheafCompRestrictionIso ρ J A).inv.app M =
      ((ι P ρ).pushforwardContinuousSheafificationCompatibility A J
        (twistedTopology ρ J)).hom.app ((Functor.const (TwistedOver P ρ)ᵒᵖ).obj M) :=
  rfl

/-- `constantSheafCompRestrictionIso` is characterized by the canonical maps to
sheafifications: the canonical map of the constant presheaf `M` over `X` to its sheafification,
followed by the inverse at `M`, is the restriction of the canonical map of the constant
presheaf `M` on the twisted site to its sheafification. -/
theorem toSheafify_constantSheafCompRestrictionIso_inv_app (M : A) :
    toSheafify J ((Functor.const (P.Over ⊤ X)ᵒᵖ).obj M) ≫
        ((constantSheafCompRestrictionIso ρ J A).inv.app M).hom =
      Functor.whiskerLeft (ι P ρ).op
        (toSheafify (twistedTopology ρ J) ((Functor.const (TwistedOver P ρ)ᵒᵖ).obj M)) :=
  (ι P ρ).toSheafify_pullbackSheafificationCompatibility A J (twistedTopology ρ J)
    ((Functor.const (TwistedOver P ρ)ᵒᵖ).obj M)

end General

section Discrete

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} [P.RespectsIso] {X : C}
variable {G : Type uG} [Group G] {ρ : G →* Aut X}
variable (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]
variable (R : Type w) [CommRing R] [TopologicalSpace G]
variable (L : LocalActionSystem (TwistedOver P ρ) G)
variable [HasSheafify J (ModuleCat.{w} R)]
variable [HasSheafify (twistedTopology ρ J) (ModuleCat.{w} R)]
variable [L.HasFiniteEquivariantRefinements (twistedTopology ρ J)]
variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R, (ι P ρ).op.HasPointwiseRightKanExtension F]

/-- The restriction of the constant discrete sheaf `M` on the twisted site to the site over
`X` is the constant sheaf `M`. -/
def discreteConstantSheafCompRestrictionIso :
    discreteConstantSheaf L (twistedTopology ρ J) R ⋙
        Cohomology.DiscreteSheafDerivedComparison.discreteRestriction J R L ≅
      constantSheaf J (ModuleCat.{w} R) :=
  constantSheafCompRestrictionIso ρ J (ModuleCat.{w} R)

end Discrete

namespace Analytic

open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Cohomology Langlands.Cohomology.DivisibleSystem
open Langlands.Cohomology.DivisibleSystem.Analytic

universe uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Restriction

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [Small.{max u (v + 1) uL} G]
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]

/-- Berkovich's `b^*` takes the constant quasi-étale `G`-sheaf `M` to the constant sheaf `M`
on the quasi-étale site of `X`. -/
def quasiEtaleConstantSheafRestrictionIso :
    haveI := quasiEtale_hasSheafify.{u, v, uL} X R
    quasiEtaleConstantSheaf.{u, v, uL} ρ R ⋙ quasiEtaleGSheafRestriction.{u, v, uL} ρ R ≅
      constantSheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R) :=
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  discreteConstantSheafCompRestrictionIso (quasiEtaleTopology X) R (compactLiftSystem ρ)

end Restriction

section Comparison

variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, QuasiEtaleSite.PointAxioms L x)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]

/-- The comparison `H^q_c(X{G}, M) → H^q_c(X, M)` for the constant sheaves `M`, natural in
the module `M`: Berkovich's comparison `H^q_c(X{G}, F) → H^q_c(X, b^*F)` at the constant
quasi-étale `G`-sheaf `M`, followed by the identification of `b^*M` with the constant sheaf
`M` of `X`. That it is an isomorphism is not proved. -/
def quasiEtaleConstantCompactComparison (q : ℕ) :
    haveI := quasiEtale_hasSheafify.{u, v, uL} X R
    quasiEtaleConstantSheaf.{u, v, uL} ρ R ⋙
        quasiEtaleGSheafCompactCohomology L ρ h R q ⋙ smoothForget R G ⟶
      constantSheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R) ⋙
        quasiEtaleCompactCohomology L h R q :=
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  Functor.whiskerLeft (quasiEtaleConstantSheaf.{u, v, uL} ρ R)
      (quasiEtaleCompactComparison L ρ h R q) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (quasiEtaleConstantSheafRestrictionIso.{u, v, uL} ρ R).hom
      (quasiEtaleCompactCohomology L h R q)

/-- The component of the constant comparison at a module `M` is Berkovich's comparison at
the constant quasi-étale `G`-sheaf `M`, followed by the map induced by `b^*M ≅ M`. -/
theorem quasiEtaleConstantCompactComparison_app (q : ℕ) (M : ModuleCat.{max u (v + 1) uL} R) :
    haveI := quasiEtale_hasSheafify.{u, v, uL} X R
    (quasiEtaleConstantCompactComparison L ρ h R q).app M =
      (quasiEtaleCompactComparison L ρ h R q).app ((quasiEtaleConstantSheaf.{u, v, uL} ρ R).obj M) ≫
        (quasiEtaleCompactCohomology L h R q).map
          ((quasiEtaleConstantSheafRestrictionIso.{u, v, uL} ρ R).hom.app M) := by
  simp [quasiEtaleConstantCompactComparison]

end Comparison

section Harris

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]
variable {ℓ : ℕ} (hℓ : IsSMulRegular R (ℓ : R))
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, QuasiEtaleSite.PointAxioms L x)
variable [PreservesFiniteLimits (quasiEtaleGodementFunctor L ρ h R)]
  [PreservesFiniteColimits (quasiEtaleGodementFunctor L ρ h R)]
variable (hpoints : JointlyFaithful fun x : (localizedFieldPointFunctor L).obj X =>
  (quasiEtalePoints L h x).sheafFiber (A := ModuleCat.{max u (v + 1) uL} R))
variable (D : ℕ)
variable (hF : ∀ (M : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (r : ℕ),
    IsZero ((quasiEtaleGSheafCompactCohomology L ρ h R (r + 1)).obj
      ((quasiEtaleGodementFunctor L ρ h R).obj M)))
  (hC : ∀ m n : ℕ, D < n →
    IsZero ((quasiEtaleGSheafCompactCohomology L ρ h R n).obj
      ((quasiEtaleConstantSheaf.{u, v, uL} ρ R).obj
        (ModuleCat.of R (R ⧸ Ideal.span {(ℓ : R) ^ m})))))

/-- The map `H^n(Γ_{c,X{G}}(G^•_m)) → H^n_c(X, R / ℓ ^ m R)` from the cohomology of
Harris's complex of level `m` for the constant system `{R / ℓ ^ m R}`, with the action of `G`
forgotten, to the plain compactly supported cohomology of `X` with constant coefficients:
Harris's (2.3) followed by the constant comparison. That it is an isomorphism
(Berkovich's Corollary 1.5.2(i)) is not proved. -/
def quasiEtaleConstantCompactHomologyToPlain (m n : ℕ) :
    haveI := quasiEtale_hasSheafify.{u, v, uL} X R
    (smoothForget R G).obj
        (((quasiEtaleConstantCompactSectionsSystem ρ R hℓ L h hpoints D hF hC).obj m).homology n) ⟶
      (quasiEtaleCompactCohomology L h R n).obj
        ((constantSheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R)).obj
          (ModuleCat.of R (R ⧸ Ideal.span {(ℓ : R) ^ m}))) :=
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  (smoothForget R G).map (quasiEtaleConstantCompactHomologyIso ρ R hℓ L h hpoints D hF hC m n).hom ≫
    (quasiEtaleConstantCompactComparison L ρ h R n).app
      (ModuleCat.of R (R ⧸ Ideal.span {(ℓ : R) ^ m}))

end Harris

end Analytic

end Langlands.Sheaf.Equivariant
