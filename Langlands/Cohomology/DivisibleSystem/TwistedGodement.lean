import Langlands.Sheaf.Equivariant.TwistedGodement
import Langlands.Cohomology.DivisibleSystem.Resolution

/-!
# `ℓ`-divisible systems of discrete Godement resolutions on a twisted site

Harris's Lemma 2.2 on Berkovich's equivariant site, in the twisted-site model: for an
`ℓ`-divisible system `T` of discrete sheaves of modules and the discrete Godement functor
`F` with its coaugmentation `T ⟶ F(T)`, the images `F(T_m)` (Fact 4), the iterated
cokernels and the Godement resolutions of the `T_m` form `ℓ`-divisible systems. The
construction assumes that `F` is exact (Harris's Fact 3), which is not proved here, and
that the point fibers are jointly faithful.
-/

noncomputable section

namespace Langlands.Cohomology.DivisibleSystem

open CategoryTheory CategoryTheory.Limits
open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.TwistedOver

universe w v u uG

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} [P.RespectsIso] {X : C}
variable {G : Type uG} [Group G] (ρ : G →* Aut X)
variable (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]
variable [TopologicalSpace G] (L : LocalActionSystem (TwistedOver P ρ) G)
variable {I : Type w} (points : I → GrothendieckTopology.Point.{w} J)
variable (R : Type w) [CommRing R]
variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R, (ι P ρ).op.HasPointwiseRightKanExtension F]
variable [L.HasFiniteEquivariantRefinements (twistedTopology ρ J)]
variable [HasSheafify (twistedTopology ρ J) (ModuleCat.{w} R)]

section LeftExact

variable [PreservesFiniteLimits (discreteZeroFunctor ρ J L points R)]

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts in
/-- A left exact discrete Godement functor is additive. -/
theorem discreteZeroFunctor_additive : (discreteZeroFunctor ρ J L points R).Additive :=
  Functor.additive_of_preservesBinaryBiproducts _

end LeftExact

section Exact

variable [PreservesFiniteLimits (discreteZeroFunctor ρ J L points R)]
  [PreservesFiniteColimits (discreteZeroFunctor ρ J L points R)]
variable {ℓ : ℕ} (T : DivisibleSystem (L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J)) ℓ)

/-- Harris's Fact 4: the images `F(T_m)` under the exact discrete Godement functor form an
`ℓ`-divisible system. -/
def discreteGodementImageSystem :
    DivisibleSystem (L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J)) ℓ :=
  haveI := discreteZeroFunctor_additive ρ J L points R
  T.map (discreteZeroFunctor ρ J L points R)

/-- The embeddings `b_m : T_m ⟶ F(T_m)` as a morphism of `ℓ`-divisible systems. -/
def discreteGodementCoaugmentation : T ⟶ discreteGodementImageSystem ρ J L points R T :=
  haveI := discreteZeroFunctor_additive ρ J L points R
  T.coaugmentation (discreteZeroFunctor ρ J L points R) (discreteCoaugmentation ρ J L points R)

variable (hpoints : JointlyFaithful (fun i => (points i).sheafFiber (A := ModuleCat.{w} R)))

/-- The residual systems: `T` in degree `0`, and in degree `q + 1` the cokernel system of
the coaugmentation of the residual system in degree `q` (`{coker b_m}` for `q = 0`). -/
def discreteGodementResidualSystem (q : ℕ) :
    DivisibleSystem (L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J)) ℓ :=
  haveI := discreteZeroFunctor_additive ρ J L points R
  haveI := mono_discreteCoaugmentation_of_jointlyFaithful ρ J L points R hpoints
  T.residualSystem (discreteZeroFunctor ρ J L points R) (discreteCoaugmentation ρ J L points R) q

/-- The term systems `F^q`: the discrete Godement functor applied to the residual
system in degree `q`. -/
def discreteGodementTermSystem (q : ℕ) :
    DivisibleSystem (L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J)) ℓ :=
  haveI := discreteZeroFunctor_additive ρ J L points R
  haveI := mono_discreteCoaugmentation_of_jointlyFaithful ρ J L points R hpoints
  T.termSystem (discreteZeroFunctor ρ J L points R) (discreteCoaugmentation ρ J L points R) q

/-- Harris's Lemma 2.2 on the twisted site: the `ℓ`-divisible system of the discrete
Godement resolutions `F^0 ⟶ F^1 ⟶ ⋯` of the levels of `T`. -/
def discreteGodementResolutionSystem :
    DivisibleSystem
      (CochainComplex (L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J)) ℕ) ℓ :=
  haveI := discreteZeroFunctor_additive ρ J L points R
  haveI := mono_discreteCoaugmentation_of_jointlyFaithful ρ J L points R hpoints
  resolutionSystem (discreteZeroFunctor ρ J L points R) (discreteCoaugmentation ρ J L points R) T

/-- Degree `q` of the resolution system is the term system `F^q`. -/
def discreteGodementResolutionSystemDegreeIso (q : ℕ) :
    (discreteGodementResolutionSystem ρ J L points R T hpoints).degree q ≅
      discreteGodementTermSystem ρ J L points R T hpoints q :=
  haveI := discreteZeroFunctor_additive ρ J L points R
  haveI := mono_discreteCoaugmentation_of_jointlyFaithful ρ J L points R hpoints
  resolutionSystemDegreeIso (discreteZeroFunctor ρ J L points R)
    (discreteCoaugmentation ρ J L points R) T q

/-- Level `m` of the resolution system is the published discrete Godement complex of
`T_m`. -/
def discreteGodementResolutionSystemObjIso (m : ℕ) :
    (discreteGodementResolutionSystem ρ J L points R T hpoints).obj m ≅
      (discreteComplexFunctor ρ J L points R).obj (T.obj m) :=
  haveI := discreteZeroFunctor_additive ρ J L points R
  haveI := mono_discreteCoaugmentation_of_jointlyFaithful ρ J L points R hpoints
  resolutionSystemObjIso (discreteZeroFunctor ρ J L points R)
    (discreteCoaugmentation ρ J L points R) T m

/-- Every level of the resolution system is exact in positive degrees. -/
theorem discreteGodementResolutionSystem_obj_exactAt (m q : ℕ) :
    ((discreteGodementResolutionSystem ρ J L points R T hpoints).obj m).ExactAt (q + 1) :=
  haveI := discreteZeroFunctor_additive ρ J L points R
  haveI := mono_discreteCoaugmentation_of_jointlyFaithful ρ J L points R hpoints
  resolutionSystem_obj_exactAt (discreteZeroFunctor ρ J L points R)
    (discreteCoaugmentation ρ J L points R) T m q

end Exact

end Langlands.Cohomology.DivisibleSystem
