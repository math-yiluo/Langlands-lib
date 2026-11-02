import Langlands.AlgebraicGeometry.Modules.FinitePresentationSections
import Langlands.AlgebraicGeometry.Modules.TildeRankOneSpreading

/-! # Rank-one stalk spreading for affine quasi-coherent module sheaves -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Langlands.AlgebraicGeometry.Modules

variable {R : CommRingCat.{u}}

/-- Finite presentation of actual global sections also holds after the canonical
scalar identification with the coordinate ring of an affine spectrum. -/
lemma finitePresentation_moduleSpecΓFunctor (M : (Spec R).Modules)
    [Module.FinitePresentation Γ(Spec R, ⊤) Γ(M, ⊤)] :
    Module.FinitePresentation R (moduleSpecΓFunctor.obj M) := by
  let : Algebra R Γ(Spec R, ⊤) :=
    inferInstanceAs (Algebra R ((Spec.structureSheaf R).obj.obj (.op ⊤)))
  let e : R ≃ₗ[R] Γ(Spec R, ⊤) :=
    LinearEquiv.ofBijective (Algebra.linearMap R Γ(Spec R, ⊤))
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv)
  have : Module.FinitePresentation R Γ(Spec R, ⊤) :=
    Module.FinitePresentation.of_equiv e
  exact Module.FinitePresentation.trans R Γ(M, ⊤) Γ(Spec R, ⊤)

/-- A rank-one actual stalk of a quasi-coherent sheaf on an affine spectrum lies
in its trivializing locus if its global section module is finitely presented. -/
lemma mem_rankOneLocus_spec_of_stalkEquiv (M : (Spec R).Modules) [M.IsQuasicoherent]
    [Module.FinitePresentation Γ(Spec R, ⊤) Γ(M, ⊤)]
    (x : Spec R)
    (e : stalk M x ≃ₗ[(Spec R).presheaf.stalk x] (Spec R).presheaf.stalk x) :
    x ∈ Picard.rankOneLocus M := by
  have : Module.FinitePresentation R (moduleSpecΓFunctor.obj M) :=
    finitePresentation_moduleSpecΓFunctor M
  let t := asIso M.fromTildeΓ
  rw [← Picard.rankOneLocus_eq_of_iso t]
  exact mem_rankOneLocus_tilde_of_stalkEquiv (moduleSpecΓFunctor.obj M) x
    (stalkIso t x ≪≫ₗ e)

/-- Choose an actual trivializing neighbourhood of a rank-one stalk of an affine
quasi-coherent sheaf with finitely presented global sections. -/
def specRankOneTrivializingNeighbourhood (M : (Spec R).Modules) [M.IsQuasicoherent]
    [Module.FinitePresentation Γ(Spec R, ⊤) Γ(M, ⊤)]
    (x : Spec R)
    (e : stalk M x ≃ₗ[(Spec R).presheaf.stalk x] (Spec R).presheaf.stalk x) :
    {U : (Spec R).Opens // x ∈ U ∧
      Nonempty (M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)} :=
  let h := (Picard.mem_rankOneLocus M x).mp
    (mem_rankOneLocus_spec_of_stalkEquiv M x e)
  ⟨h.choose, h.choose_spec⟩

end Langlands.AlgebraicGeometry.Modules
