import Langlands.Cohomology.DivisibleSystem.AnalyticQuasiEtale
import Langlands.Cohomology.DivisibleSystem.ConstantCoefficients
import Langlands.Sheaf.Equivariant.LocalActionConstant

/-!
# The constant `ℓ`-divisible system of quasi-étale `G`-sheaves

For a local action system with finite equivariant refinements, the constant sheaf functor with
values in discrete sheaves is exact, so it carries the published `ℓ`-divisible system
`scalarSystem R ℓ hℓ = {R / ℓ ^ m R}` to an `ℓ`-divisible system of constant discrete sheaves.

For `G` acting on an analytic space `X`, this gives the constant `ℓ`-divisible system
`{R / ℓ ^ m R}` of quasi-étale `G`-sheaves, the system of constant sheaves `ℤ / ℓ ^ m ℤ`
resolved in Harris's Lemma 2.2 when `R = ℤ`. The module specializes the quasi-étale
Lemma 2.2, Lemma 2.2 bis and (2.3) of `AnalyticQuasiEtale` to this system. The cohomology of
level `m` of the compact section complexes is `H^n_c(X{G}, R / ℓ ^ m R)`. The hypotheses of
those results stay hypotheses here.
-/

noncomputable section

namespace Langlands.Cohomology.DivisibleSystem

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Sheaf.Equivariant

universe u v uL z uG w

section Discrete

variable {T : Type u} [Category.{v} T] {G : Type uG} [Group G] [TopologicalSpace G]
variable (L : LocalActionSystem T G) (J : GrothendieckTopology T) (R : Type w) [CommRing R]
variable [HasSheafify J (ModuleCat.{w} R)] [L.HasFiniteEquivariantRefinements J]
variable {ℓ : ℕ} (hℓ : IsSMulRegular R (ℓ : R))

/-- The constant `ℓ`-divisible system `{R / ℓ ^ m R}` of discrete sheaves: the image of
`scalarSystem R ℓ hℓ` under the exact constant sheaf functor. -/
def discreteConstantSystem : DivisibleSystem (L.DiscreteSheaf (ModuleCat.{w} R) J) ℓ :=
  (scalarSystem R ℓ hℓ).map (discreteConstantSheaf L J R)

/-- Level `m` of the constant system is the constant sheaf `R / ℓ ^ m R`. -/
def discreteConstantSystemObjIso (m : ℕ) :
    (discreteConstantSystem L J R hℓ).obj m ≅
      (discreteConstantSheaf L J R).obj (ModuleCat.of R (R ⧸ Ideal.span {(ℓ : R) ^ m})) :=
  (discreteConstantSheaf L J R).mapIso (scalarSystemObjIso hℓ m)

/-- The maps `j` of the constant system are the constant sheaf maps of those of
`scalarSystem`. -/
theorem discreteConstantSystem_projection {m' m : ℕ} (h : m' ≤ m) :
    (discreteConstantSystem L J R hℓ).projection h =
      (discreteConstantSheaf L J R).map ((scalarSystem R ℓ hℓ).projection h) :=
  rfl

/-- The maps `i` of the constant system are the constant sheaf maps of those of
`scalarSystem`. -/
theorem discreteConstantSystem_inclusion {m' m : ℕ} (h : m' < m) :
    (discreteConstantSystem L J R hℓ).inclusion h =
      (discreteConstantSheaf L J R).map ((scalarSystem R ℓ hℓ).inclusion h) :=
  rfl

end Discrete

namespace Analytic

open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver Langlands.Sheaf.Equivariant.Analytic


variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- In `ULift ℤ`, a nonzero natural number is a non-zero-divisor. -/
theorem isSMulRegular_uLiftInt_natCast {ℓ : ℕ} (hℓ : ℓ ≠ 0) :
    IsSMulRegular (ULift.{w} ℤ) (ℓ : ULift.{w} ℤ) := fun _ _ hab =>
  ULift.ext _ _ (mul_left_cancel₀ (Int.natCast_ne_zero.2 hℓ) (congrArg ULift.down hab))

section Constant

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [Small.{max u (v + 1) uL} G]
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]

/-- The constant quasi-étale `G`-sheaf functor: the sheafification on the twisted quasi-étale
site of the constant presheaf, which is discrete. -/
def quasiEtaleConstantSheaf :
    ModuleCat.{max u (v + 1) uL} R ⥤ QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) :=
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  discreteConstantSheaf (compactLiftSystem ρ) (twistedQuasiEtaleTopology ρ) R

/-- Followed by the inclusion into all sheaves, the constant quasi-étale `G`-sheaf functor is
the constant sheaf functor of the twisted quasi-étale site. -/
theorem quasiEtaleConstantSheaf_comp_inclusion :
    haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
    quasiEtaleConstantSheaf.{u, v, uL} ρ R ⋙
        (compactLiftSystem ρ).discreteSheafInclusion (ModuleCat.{max u (v + 1) uL} R)
          (twistedQuasiEtaleTopology ρ) =
      constantSheaf (twistedQuasiEtaleTopology ρ) (ModuleCat.{max u (v + 1) uL} R) :=
  rfl

variable {ℓ : ℕ} (hℓ : IsSMulRegular R (ℓ : R))

/-- The constant `ℓ`-divisible system `{R / ℓ ^ m R}` of quasi-étale `G`-sheaves; for
`R = ℤ` these are the constant sheaves `ℤ / ℓ ^ m ℤ` of Harris's Lemma 2.2. -/
def quasiEtaleConstantSystem : QuasiEtaleDivisibleSystem.{u, v, uL} ρ R ℓ :=
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  discreteConstantSystem (compactLiftSystem ρ) (twistedQuasiEtaleTopology ρ) R hℓ

/-- Level `m` of the constant system is the constant quasi-étale `G`-sheaf `R / ℓ ^ m R`. -/
def quasiEtaleConstantSystemObjIso (m : ℕ) :
    haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
    (quasiEtaleConstantSystem.{u, v, uL} ρ R hℓ).obj m ≅
      (quasiEtaleConstantSheaf.{u, v, uL} ρ R).obj
        (ModuleCat.of R (R ⧸ Ideal.span {(ℓ : R) ^ m})) :=
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  discreteConstantSystemObjIso (compactLiftSystem ρ) (twistedQuasiEtaleTopology ρ) R hℓ m

/-- The constant system `{ℤ / ℓ ^ m ℤ}` of quasi-étale `G`-sheaves, for `ℓ ≠ 0`, with
integers lifted to the universe of the coefficients. -/
abbrev quasiEtaleIntConstantSystem {ℓ : ℕ} (hℓ : ℓ ≠ 0) :
    QuasiEtaleDivisibleSystem.{u, v, uL} ρ (ULift.{max u (v + 1) uL} ℤ) ℓ :=
  quasiEtaleConstantSystem.{u, v, uL} ρ (ULift.{max u (v + 1) uL} ℤ)
    (isSMulRegular_uLiftInt_natCast.{max u (v + 1) uL} hℓ)

end Constant

section Resolution

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [Small.{max u (v + 1) uL} G]
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]
variable {ℓ : ℕ} (hℓ : IsSMulRegular R (ℓ : R))
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, QuasiEtaleSite.PointAxioms L x)
variable [PreservesFiniteLimits (quasiEtaleGodementFunctor L ρ h R)]
  [PreservesFiniteColimits (quasiEtaleGodementFunctor L ρ h R)]
variable (hpoints : JointlyFaithful fun x : (localizedFieldPointFunctor L).obj X =>
  (quasiEtalePoints L h x).sheafFiber (A := ModuleCat.{max u (v + 1) uL} R))

/-- Harris's Lemma 2.2 for the constant sheaves: the `ℓ`-divisible system of the Godement
resolutions of the constant quasi-étale `G`-sheaves `R / ℓ ^ m R`. -/
abbrev quasiEtaleConstantGodementResolutionSystem :
    QuasiEtaleComplexDivisibleSystem.{u, v, uL} ρ R ℓ :=
  quasiEtaleGodementResolutionSystem ρ R L h (quasiEtaleConstantSystem.{u, v, uL} ρ R hℓ) hpoints

variable (D : ℕ)

/-- Harris's Lemma 2.2 bis for the constant sheaves: the truncation `τ_{≤ D+1}` of the
Godement resolution system of the constant system. -/
abbrev quasiEtaleConstantGodementTruncatedResolutionSystem :
    QuasiEtaleComplexDivisibleSystem.{u, v, uL} ρ R ℓ :=
  quasiEtaleGodementTruncatedResolutionSystem ρ R L h (quasiEtaleConstantSystem.{u, v, uL} ρ R hℓ)
    hpoints D

/-- The augmentation `R / ℓ ^ m R ⟶ G^•_m` of level `m` of the truncated resolution system
of the constant system. -/
def quasiEtaleConstantGodementTruncatedAugmentation (m : ℕ) :
    haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
    (CochainComplex.single₀ _).obj
        ((quasiEtaleConstantSheaf.{u, v, uL} ρ R).obj
          (ModuleCat.of R (R ⧸ Ideal.span {(ℓ : R) ^ m}))) ⟶
      (quasiEtaleConstantGodementTruncatedResolutionSystem ρ R hℓ L h hpoints D).obj m :=
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  (CochainComplex.single₀ _).map (quasiEtaleConstantSystemObjIso.{u, v, uL} ρ R hℓ m).inv ≫
    quasiEtaleGodementTruncatedAugmentation ρ R L h (quasiEtaleConstantSystem.{u, v, uL} ρ R hℓ)
      hpoints D m

/-- Level `m` of the truncated resolution system is a finite-length resolution of the
constant quasi-étale `G`-sheaf `R / ℓ ^ m R`. -/
theorem quasiIso_quasiEtaleConstantGodementTruncatedAugmentation (m : ℕ) :
    haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
    QuasiIso (quasiEtaleConstantGodementTruncatedAugmentation ρ R hℓ L h hpoints D m) := by
  have := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  have := quasiIso_quasiEtaleGodementTruncatedAugmentation ρ R L h
    (quasiEtaleConstantSystem.{u, v, uL} ρ R hℓ) hpoints D m
  exact quasiIso_comp _ _

end Resolution

section Compact

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

omit [PreservesFiniteLimits (quasiEtaleGodementFunctor L ρ h R)]
  [PreservesFiniteColimits (quasiEtaleGodementFunctor L ρ h R)] in
include hC in
/-- The bound on the cohomological dimension of the constant sheaves `R / ℓ ^ m R` transfers
to the levels of the constant system. -/
theorem isZero_quasiEtaleGSheafCompactCohomology_constantSystem_obj (m n : ℕ) (hn : D < n) :
    haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
    IsZero ((quasiEtaleGSheafCompactCohomology L ρ h R n).obj
      ((quasiEtaleConstantSystem.{u, v, uL} ρ R hℓ).obj m)) :=
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  (hC m n hn).of_iso
    ((quasiEtaleGSheafCompactCohomology L ρ h R n).mapIso
      (quasiEtaleConstantSystemObjIso.{u, v, uL} ρ R hℓ m))

/-- Harris's `ℓ`-divisible system of finite-length complexes `Γ_{c,X{G}}(G^•_m)` of smooth
representations of `G`, for the constant sheaves `R / ℓ ^ m R`. -/
abbrev quasiEtaleConstantCompactSectionsSystem :
    DivisibleSystem
      (CochainComplex (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G) ℕ) ℓ :=
  quasiEtaleGodementTruncatedCompactSectionsSystem ρ R L h
    (quasiEtaleConstantSystem.{u, v, uL} ρ R hℓ) hpoints D hF
    (isZero_quasiEtaleGSheafCompactCohomology_constantSystem_obj ρ R hℓ L h D hC)

/-- Harris (2.3) for the constant sheaves: the cohomology of level `m` of the compact section
complexes is `H^n_c(X{G}, R / ℓ ^ m R)`. -/
def quasiEtaleConstantCompactHomologyIso (m n : ℕ) :
    ((quasiEtaleConstantCompactSectionsSystem ρ R hℓ L h hpoints D hF hC).obj m).homology n ≅
      (quasiEtaleGSheafCompactCohomology L ρ h R n).obj
        ((quasiEtaleConstantSheaf.{u, v, uL} ρ R).obj
          (ModuleCat.of R (R ⧸ Ideal.span {(ℓ : R) ^ m}))) :=
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  quasiEtaleGodementTruncatedCompactHomologyIso ρ R L h
      (quasiEtaleConstantSystem.{u, v, uL} ρ R hℓ) hpoints D hF
      (isZero_quasiEtaleGSheafCompactCohomology_constantSystem_obj ρ R hℓ L h D hC) m n ≪≫
    (quasiEtaleGSheafCompactCohomology L ρ h R n).mapIso
      (quasiEtaleConstantSystemObjIso.{u, v, uL} ρ R hℓ m)

end Compact

end Analytic

end Langlands.Cohomology.DivisibleSystem
