import Langlands.BruhatTits.IntegralModels.OrderedIntegralOpenCell
import Langlands.BruhatTits.IntegralModels.TorusRootKernelCell

/-! # Ordered fixer factorization in the open cell over the maximal unramified field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

/-- **Fixer factorization in the open cell** (from the displayed equation in the proof of
KP Proposition 8.4.15, together with uniqueness of open-cell decompositions). Let `ν` be a
generic cocharacter of the maximal split torus, and list the negative and the positive
indivisible relative roots injectively and completely. Use the order: negative roots, then
the torus, then positive roots (`TorusRootModelFamilyData.orderedIntegralIndex`). Then, for
every nonempty affine-bounded `Ω'`, if root-group elements and an element of `T(K)⁰` multiply
in this order to an element of `G(K)⁰` fixing `Ω'` pointwise, each root factor lies in
`U_{a,Ω',0}`. The torus is the centralizer of the maximal split torus. -/
def UnramifiedOrderedFixerFactorizationStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G),
    (torusCentralizer C.i).IsRepresentedBy E.i →
    ∀ (ν : cocharacterLattice C.S), IsGenericCocharacter C.i ν →
    ∀ (nneg npos : ℕ) (aneg : Fin nneg → relativeRoots C.i)
      (apos : Fin npos → relativeRoots C.i),
      Function.Injective aneg →
      Set.range (fun j => (aneg j : characterLattice C.S)) =
        RelativeRoot.indivisiblePositiveRoots C.i (-ν) →
      Function.Injective apos →
      Set.range (fun j => (apos j : characterLattice C.S)) =
        RelativeRoot.indivisiblePositiveRoots C.i ν →
      ∀ Ω Ω' : Set C.Apartment, Ω'.Nonempty →
        (∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω')) →
        OrderedFixerFactorization C E
          (TorusRootModelFamilyData.orderedIntegralIndex aneg apos) Ω Ω'

end Langlands.BruhatTits.IntegralModels
