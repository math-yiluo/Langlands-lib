import Langlands.Representation.Plancherel.FiniteSmoothFamilyTransport
import Langlands.Representation.Plancherel.ProductInducedOrbitSections

/-! # Lattice coordinate independence of actual smooth orbit sections -/

noncomputable section

open Langlands.Aubert.General Langlands.Induction
open scoped NNReal

namespace Langlands.Plancherel

universe uG uI uV uJ uJ' uL

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  {M : Subgroup G} {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))
  {J : Type uJ} {J' : Type uJ'} [Fintype J] [Fintype J']
  (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))
  {L : Type uL} [AddCommGroup L] [Module ℤ L]
  (b : Module.Basis J ℤ L) (c : Module.Basis J' ℤ L)

/-- Replace the supplied torus coordinates by a finite integer lattice
basis change, using reconstruction of the same lattice character. -/
def rebaseUnitaryTorusCoordinates :
    unitaryUnramifiedCharacters ν ≃* (J' → Circle) :=
  e.trans (finiteTorusBasisChangeMulEquiv b c)

variable [LocallyCompactSpace G]
  {P U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G)) (K : OpenSubgroup G)
  (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))

/-- Compact restriction of an actual orbit section only reindexes when the
supplied lattice coordinates change. The induced fiber is the same one. -/
theorem productInducedOrbitCompactPullback_rebase
    (q : ProductInducedOrbitSections ν π h hU) :
    productInducedFamilyRestriction ν (rebaseUnitaryTorusCoordinates ν e b c)
        h K hP hK hν hr hU hPK π.obj
        (productInducedOrbitPullback ν π
          (rebaseUnitaryTorusCoordinates ν e b c) h hU q) =
      (productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj
        (productInducedOrbitPullback ν π e h hU q)) ∘ finiteTorusBasisChange c b := rfl

/-- The actual smooth coherent section submodule is unchanged by an integer
lattice basis change of the supplied parameter coordinates. -/
theorem productInducedSmoothOrbitSections_rebase :
    productInducedSmoothOrbitSections ν π (rebaseUnitaryTorusCoordinates ν e b c)
        h hU K hP hK hν hr hPK =
      productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK := by
  apply Submodule.ext
  intro q
  change (_ ∧ productInducedFamilyRestriction ν
      (rebaseUnitaryTorusCoordinates ν e b c) h K hP hK hν hr hU hPK π.obj
      (productInducedOrbitPullback ν π
        (rebaseUnitaryTorusCoordinates ν e b c) h hU q) ∈
      finiteSmoothFamilies J' (ProductInducedCompactPicture h K π.obj)) ↔
    (_ ∧ productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj
      (productInducedOrbitPullback ν π e h hU q) ∈
      finiteSmoothFamilies J (ProductInducedCompactPicture h K π.obj))
  rw [productInducedOrbitCompactPullback_rebase ν π e b c h hU K hP hK hν hr hPK]
  exact and_congr_right fun _ =>
    mem_finiteSmoothFamilies_comp_basisChange_iff c b _

/-- The coordinate comparison is the identity on every actual orbit fiber. -/
def productInducedSmoothOrbitRebaseEquiv :
    productInducedSmoothOrbitSections ν π (rebaseUnitaryTorusCoordinates ν e b c)
        h hU K hP hK hν hr hPK ≃ₗ[ℂ]
      productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK :=
  LinearEquiv.ofEq _ _
    (productInducedSmoothOrbitSections_rebase ν π e b c h hU K hP hK hν hr hPK)

@[simp]
theorem productInducedSmoothOrbitRebaseEquiv_apply
    (q : productInducedSmoothOrbitSections ν π (rebaseUnitaryTorusCoordinates ν e b c)
      h hU K hP hK hν hr hPK) (A : UnitaryOrbitRepresentative ν π) :
    (productInducedSmoothOrbitRebaseEquiv ν π e b c h hU K hP hK hν hr hPK q).val A =
      q.val A := rfl

@[simp]
theorem productInducedSmoothOrbitRebaseEquiv_symm_apply
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (A : UnitaryOrbitRepresentative ν π) :
    ((productInducedSmoothOrbitRebaseEquiv ν π e b c h hU K hP hK hν hr hPK).symm q).val A =
      q.val A := rfl

end Langlands.Plancherel
