import Langlands.Cohomology.DivisibleSystem.TwistedGodement
import Langlands.Cohomology.DivisibleSystem.AcyclicTruncation
import Langlands.Sheaf.Equivariant.TwistedCompactSupport

/-!
# Truncated discrete Godement resolutions and compact cohomology on a twisted site

Harris's Lemma 2.2 bis and (2.3) on Berkovich's equivariant site, in the twisted-site model.
For an `ℓ`-divisible system `T` of discrete sheaves of modules, the discrete Godement
resolution system `F^•` is truncated in degree `D + 1` to `G^• = τ_{≤ D+1}(F^•)`. Each level
`G^•_m` is a finite-length resolution of `T m`. If the discrete Godement sheaves are acyclic
for smooth compactly supported sections (Harris's `RΓ_c`-acyclicity of `F(T)`) and the
compactly supported cohomology of the levels of `T` vanishes above degree `D` (Fact 2), the
complexes of smooth compactly supported sections `Γ_c(G^•_m)` form an `ℓ`-divisible system of
finite-length complexes of smooth representations whose cohomology is the compactly
supported cohomology `H^n_c(T m)` (Harris (2.3)).

Exactness of the discrete Godement functor (Fact 3), the acyclicity of its values and Fact 2
are hypotheses. The constructions are the generic ones of `DivisibleSystem.Truncation` and
`DivisibleSystem.AcyclicTruncation`.
-/

noncomputable section

namespace Langlands.Cohomology.DivisibleSystem

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.TwistedOver

universe w v u uG uI

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} [P.RespectsIso] {X : C}
variable {G : Type uG} [Group G] (ρ : G →* Aut X)
variable (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]
variable [TopologicalSpace G] (L : LocalActionSystem (TwistedOver P ρ) G)
variable {I : Type w} (points : I → GrothendieckTopology.Point.{w} J)
variable (R : Type w) [CommRing R]
variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R, (ι P ρ).op.HasPointwiseRightKanExtension F]
variable [L.HasFiniteEquivariantRefinements (twistedTopology ρ J)]
variable [HasSheafify (twistedTopology ρ J) (ModuleCat.{w} R)]
variable [PreservesFiniteLimits (discreteZeroFunctor ρ J L points R)]
  [PreservesFiniteColimits (discreteZeroFunctor ρ J L points R)]
variable {ℓ : ℕ} (T : DivisibleSystem (L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J)) ℓ)
variable (hpoints : JointlyFaithful (fun i => (points i).sheafFiber (A := ModuleCat.{w} R)))
variable (D : ℕ)

section Truncation

/-- Harris's truncation `G^• = τ_{≤ D+1}(F^•)` of the discrete Godement resolution system: the
term systems `F^q` for `q ≤ D`, the residual system `R (D + 1)` in degree `D + 1`, and zero
above. -/
def discreteGodementTruncatedResolutionSystem :
    DivisibleSystem
      (CochainComplex (L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J)) ℕ) ℓ :=
  haveI := discreteZeroFunctor_additive ρ J L points R
  haveI := mono_discreteCoaugmentation_of_jointlyFaithful ρ J L points R hpoints
  T.truncatedResolutionSystem (discreteZeroFunctor ρ J L points R)
    (discreteCoaugmentation ρ J L points R) D

/-- The inclusion `G^• ⟶ F^•` of the truncation into the discrete Godement resolution
system. -/
def discreteGodementTruncatedResolutionHom :
    discreteGodementTruncatedResolutionSystem ρ J L points R T hpoints D ⟶
      discreteGodementResolutionSystem ρ J L points R T hpoints :=
  haveI := discreteZeroFunctor_additive ρ J L points R
  haveI := mono_discreteCoaugmentation_of_jointlyFaithful ρ J L points R hpoints
  T.truncatedResolutionHom (discreteZeroFunctor ρ J L points R)
    (discreteCoaugmentation ρ J L points R) D

/-- At every level, the inclusion of the truncation is a quasi-isomorphism. -/
theorem quasiIso_discreteGodementTruncatedResolutionHom (m : ℕ) :
    QuasiIso ((discreteGodementTruncatedResolutionHom ρ J L points R T hpoints D).tower.app
      (op m)) :=
  haveI := discreteZeroFunctor_additive ρ J L points R
  haveI := mono_discreteCoaugmentation_of_jointlyFaithful ρ J L points R hpoints
  truncatedResolutionHom_quasiIso (discreteZeroFunctor ρ J L points R)
    (discreteCoaugmentation ρ J L points R) T D m

/-- Every level of the truncation is zero in degrees above `D + 1`. -/
theorem isZero_discreteGodementTruncatedResolutionSystem_obj_X (m : ℕ) {q : ℕ}
    (hq : D + 1 < q) :
    IsZero (((discreteGodementTruncatedResolutionSystem ρ J L points R T hpoints D).obj m).X q) :=
  haveI := discreteZeroFunctor_additive ρ J L points R
  haveI := mono_discreteCoaugmentation_of_jointlyFaithful ρ J L points R hpoints
  T.isZero_truncatedResolutionSystem_obj_X (discreteZeroFunctor ρ J L points R)
    (discreteCoaugmentation ρ J L points R) D m hq

/-- The augmentation `T m ⟶ G^•_m`. -/
def discreteGodementTruncatedAugmentation (m : ℕ) :
    (CochainComplex.single₀ _).obj (T.obj m) ⟶
      (discreteGodementTruncatedResolutionSystem ρ J L points R T hpoints D).obj m :=
  haveI := discreteZeroFunctor_additive ρ J L points R
  haveI := mono_discreteCoaugmentation_of_jointlyFaithful ρ J L points R hpoints
  T.truncatedResolutionAugmentation (discreteZeroFunctor ρ J L points R)
    (discreteCoaugmentation ρ J L points R) D m

/-- Each level of the truncation is a finite-length resolution of the level of `T`. -/
theorem quasiIso_discreteGodementTruncatedAugmentation (m : ℕ) :
    QuasiIso (discreteGodementTruncatedAugmentation ρ J L points R T hpoints D m) :=
  haveI := discreteZeroFunctor_additive ρ J L points R
  haveI := mono_discreteCoaugmentation_of_jointlyFaithful ρ J L points R hpoints
  truncatedResolutionAugmentation_quasiIso (discreteZeroFunctor ρ J L points R)
    (discreteCoaugmentation ρ J L points R) T D m

end Truncation

section Compact

variable [P.ContainsIdentities] [LocallySmall.{w} (P.Over ⊤ X)] [IsTopologicalGroup G]
variable [HasSheafify J (ModuleCat.{w} R)]
variable [EnoughInjectives (Sheaf (twistedTopology ρ J) (ModuleCat.{w} R))]
variable {I' : Type uI} [MulAction G I'] [TopologicalSpace I'] [ContinuousConstSMul G I']
  {Ψ : I' → J.Point.{w}} (E : PointEquivariance ρ Ψ)
variable (hF : ∀ (M : L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J)) (r : ℕ),
    IsZero ((discreteCompactDerived J R L E (r + 1)).obj
      ((discreteZeroFunctor ρ J L points R).obj M)))
  (hT : ∀ m n : ℕ, D < n → IsZero ((discreteCompactDerived J R L E n).obj (T.obj m)))

omit [HasSheafify J (ModuleCat.{w} R)] in
include hF hT in
/-- Every term of every level of the truncation is acyclic for smooth compactly supported
sections. -/
theorem isZero_discreteCompactDerived_truncatedResolutionSystem_obj_X (m i r : ℕ) :
    IsZero ((discreteCompactDerived J R L E (r + 1)).obj
      (((discreteGodementTruncatedResolutionSystem ρ J L points R T hpoints D).obj m).X i)) :=
  haveI := discreteZeroFunctor_additive ρ J L points R
  haveI := mono_discreteCoaugmentation_of_jointlyFaithful ρ J L points R hpoints
  isZero_rightDerived_truncatedResolutionSystem_obj_X (discreteCompactSections J R L E)
    (discreteZeroFunctor ρ J L points R) (discreteCoaugmentation ρ J L points R) T D hF hT m i r

/-- Harris's `ℓ`-divisible system of finite-length complexes `Γ_c(G^•_m)` of smooth
representations, for the twisted site. -/
def discreteGodementTruncatedCompactSectionsSystem :
    DivisibleSystem (CochainComplex (SmoothRep.{w, uG, w} R G) ℕ) ℓ :=
  haveI := discreteZeroFunctor_additive ρ J L points R
  haveI := mono_discreteCoaugmentation_of_jointlyFaithful ρ J L points R hpoints
  acyclicTruncatedSectionsSystem (discreteCompactSections J R L E)
    (discreteZeroFunctor ρ J L points R) (discreteCoaugmentation ρ J L points R) T D hF hT

/-- Level `m` of the section system is the complex of smooth compactly supported sections of
`G^•_m`. -/
theorem discreteGodementTruncatedCompactSectionsSystem_obj (m : ℕ) :
    (discreteGodementTruncatedCompactSectionsSystem ρ J L points R T hpoints D E hF hT).obj m =
      ((discreteCompactSections J R L E).mapHomologicalComplex _).obj
        ((discreteGodementTruncatedResolutionSystem ρ J L points R T hpoints D).obj m) :=
  rfl

/-- Harris (2.3) on the twisted site: the cohomology of level `m` of the compact section
complexes is the compactly supported cohomology `H^n_c` of `T m`. -/
def discreteGodementTruncatedCompactHomologyIso (m n : ℕ) :
    ((discreteGodementTruncatedCompactSectionsSystem ρ J L points R T hpoints D E hF hT).obj
      m).homology n ≅ (discreteCompactDerived J R L E n).obj (T.obj m) :=
  haveI := discreteZeroFunctor_additive ρ J L points R
  haveI := mono_discreteCoaugmentation_of_jointlyFaithful ρ J L points R hpoints
  acyclicTruncatedSectionsHomologyIso (discreteCompactSections J R L E)
    (discreteZeroFunctor ρ J L points R) (discreteCoaugmentation ρ J L points R) T D hF hT m n

/-- The forward map of `discreteGodementTruncatedCompactHomologyIso` is the comparison map of
the acyclic resolution `G^•_m`. -/
theorem discreteGodementTruncatedCompactHomologyIso_hom (m n : ℕ) :
    haveI := quasiIso_discreteGodementTruncatedAugmentation ρ J L points R T hpoints D m
    (discreteGodementTruncatedCompactHomologyIso ρ J L points R T hpoints D E hF hT m n).hom =
      AcyclicResolution.resolutionComparison (discreteCompactSections J R L E)
        (discreteGodementTruncatedAugmentation ρ J L points R T hpoints D m) n :=
  rfl

/-- The cohomology of every level of the compact section complexes vanishes above
degree `D`. -/
theorem isZero_discreteGodementTruncatedCompactSectionsSystem_homology (m : ℕ) {n : ℕ}
    (hn : D < n) :
    IsZero (((discreteGodementTruncatedCompactSectionsSystem ρ J L points R T hpoints D E hF
      hT).obj m).homology n) :=
  (hT m n hn).of_iso (discreteGodementTruncatedCompactHomologyIso ρ J L points R T hpoints D E
    hF hT m n)

end Compact

end Langlands.Cohomology.DivisibleSystem
