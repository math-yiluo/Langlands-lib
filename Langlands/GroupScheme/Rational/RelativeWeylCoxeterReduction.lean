import Langlands.GroupScheme.Rational.RelativeWeylCoxeterAssembly
import Langlands.GroupScheme.Rational.RootFiniteness
import Langlands.Group.RootPairingCoxeterStatement

/-! # Reduction of the relative Weyl Coxeter theorem to three published statements -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

section Reflection

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] {i : T.toGrp ⟶ G}
  [Mono i.hom.hom.left]

/-- For one torus and one generic cocharacter: the relative root system, kernel-centralizing
reflection data and the abstract Coxeter theorem give the Coxeter realization. -/
theorem RelativeRootReflectionData.hasRelativeWeylCoxeterSystem_of_rootPairingWeylCoxeter
    (hcox : Langlands.Group.RootPairingWeylCoxeterStatement.{u, 0, u, u})
    (D : RelativeRootReflectionData i) (hT : IsSplitTorus T.toGrp)
    (h : HasRelativeRootSystem i) {ν : cocharacterLattice T} (hν : IsGenericCocharacter i ν)
    (hker : ∀ a : relativeRoots i, (D.representative a).val ∈
      (RelativeRoot.kernelCentralizer i a.val).carrier (Over.mk (𝟙 _))) :
    HasRelativeWeylCoxeterSystem i ν := by
  have hfin := h.finite_relativeRoots i hT
  have : Finite (relativeRoots i) := hfin.to_subtype
  have := D.rootPairing_isCrystallographic hT hfin
  obtain ⟨-, Mx, cs, hsimple, hlength, hdescent⟩ :=
    hcox (relativeRoots i) ℚ (relativeRootSpan i) (Module.Dual ℚ (relativeRootSpan i))
      (D.rootPairing hT hfin) (RelativeRootSystem.corootFunctional i ν) (fun β => by
        change RelativeRootSystem.corootFunctional i ν (RelativeRootSystem.rootVector i β) ≠ 0
        rw [RelativeRootSystem.corootFunctional_rootVector]
        exact_mod_cast hν β.1 β.2)
  exact D.hasRelativeWeylCoxeterSystem_of_rootPairing hT hfin h hν hker Mx cs hsimple hlength
    hdescent

end Reflection

/-- The three published statements from which `RelativeWeylCoxeterStatement.{u}` follows: the
relative root system statement, the existence of reflection data whose representatives
centralize the kernels of their roots, and the abstract Coxeter theorem for finite
crystallographic root pairings at the universes used over `ℚ`. -/
def RelativeWeylCoxeterPremises : Prop :=
  RelativeRootSystemStatement.{u} ∧ RelativeRootReflectionExistenceStatement.{u} ∧
    Langlands.Group.RootPairingWeylCoxeterStatement.{u, 0, u, u}

/-- **Reduction of `RelativeWeylCoxeterStatement`.** The relative root system statement,
the existence of kernel-centralizing reflection data and the abstract Coxeter theorem for
finite crystallographic root pairings (applied over `ℚ` to the evaluation pairing on the
actual root span) together imply that `N(k)/Z(k)` is a finite Coxeter group realizing the
relative root action. -/
theorem relativeWeylCoxeterStatement_of_rootPairingWeylCoxeterStatement
    (hroot : RelativeRootSystemStatement.{u})
    (hrefl : RelativeRootReflectionExistenceStatement.{u})
    (hcox : Langlands.Group.RootPairingWeylCoxeterStatement.{u, 0, u, u}) :
    RelativeWeylCoxeterStatement.{u} := by
  intro k _ G hG T i hi ν
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  intro hν
  obtain ⟨D, hker⟩ := hrefl k G hG T i hi
  exact D.hasRelativeWeylCoxeterSystem_of_rootPairingWeylCoxeter hcox hi.isSplitSubtorus.1
    (hroot k G hG T i hi) hν hker

/-- The bundled form of the reduction. -/
theorem RelativeWeylCoxeterPremises.relativeWeylCoxeterStatement
    (h : RelativeWeylCoxeterPremises.{u}) : RelativeWeylCoxeterStatement.{u} :=
  relativeWeylCoxeterStatement_of_rootPairingWeylCoxeterStatement h.1 h.2.1 h.2.2

end Langlands.GroupScheme
