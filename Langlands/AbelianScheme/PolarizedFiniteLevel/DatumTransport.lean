import Langlands.AbelianScheme.PolarizedFiniteLevel.PolarizationIsoTransport

/-! # Transport of ordinary polarized full-level data along isomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

variable {P : Prerequisites.{u}} {S : Scheme.{u}} {g d n : ℕ}

/-- **Transport of a datum along an isomorphism.** Given a datum `b`, an abelian scheme
`A` with an isomorphism `e : A ≅ b.abelian` and any dual witness `W` of `A`, the
transported polarization, degree, dimension and level structure make a datum on `A`. -/
def Datum.transport (b : Datum P S g d n) {A : AbelianScheme S} (e : A ≅ b.abelian)
    (W : DualWitness A) : Datum P S g d n where
  abelian := A
  dimension := by
    have h1 : A.X.hom = hom e.hom ≫ b.abelian.X.hom :=
      (Over.w (groupHom e.hom).hom.hom).symm
    change SmoothOfRelativeDimension g A.X.hom
    rw [h1, MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension g)]
    exact b.dimension
  dualWitness := W
  polarization := e.hom ≫ b.polarization ≫ W.map P b.dualWitness e.hom
  polarized := DualWitness.isPolarization_iso_transport P e W b.dualWitness _ b.polarized
  degree := HasDegreeSquare.pre_iso
    (b.polarized.1.comp (isIsogeny_of_iso (W.mapIso P b.dualWitness e)))
    (HasDegreeSquare.post_iso b.polarized.1 b.degree (W.mapIso P b.dualWitness e)) e
  level := b.level.mapIso e.symm

/-- The transported datum is polarized isomorphic to the original one. -/
def Datum.transportIso (b : Datum P S g d n) {A : AbelianScheme S} (e : A ≅ b.abelian)
    (W : DualWitness A) : PolarizedIso (b.transport e W) b where
  abelianIso := e
  polarization_eq := rfl
  level_eq i := (levelIsoLinear e (Over.mk (𝟙 S)) n).apply_symm_apply (b.level.sections i)

end Langlands.AbelianScheme.PolarizedFiniteLevel
