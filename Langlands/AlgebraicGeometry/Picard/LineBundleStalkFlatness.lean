import Langlands.AlgebraicGeometry.Picard.LineBundle
import Langlands.AlgebraicGeometry.Modules.RestrictionStalkLinearEquiv
import Langlands.AlgebraicGeometry.Modules.StalkTrivialization
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Stalk bases and relative flatness of actual line bundles -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.AlgebraicGeometry.Modules

variable {X Y : Scheme.{u}}

/-- A chosen rank-one basis of every actual stalk of a locally free
rank-one module sheaf, over its canonical local ring. -/
def IsLocallyFreeRankOne.stalkLinearEquiv {M : X.Modules}
    (hM : IsLocallyFreeRankOne M) (x : X) :
    stalk M x ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x := by
  let U := (hM x).choose
  let hx : x ∈ U := (hM x).choose_spec.1
  let e := (hM x).choose_spec.2.some
  exact ofRestrictStalkRankOneEquiv U.ι M ⟨x, hx⟩
    ((stalkIso e ⟨x, hx⟩).trans (unitStalkLinearEquiv U.toScheme ⟨x, hx⟩))

/-- The stalk basis is also linear over the base local ring through the
actual structure-map stalk homomorphism. -/
def IsLocallyFreeRankOne.relativeStalkLinearEquiv {M : X.Modules}
    (hM : IsLocallyFreeRankOne M) (f : X ⟶ Y) (x : X) :
    letI := relativeStalkModule f M x
    letI := Module.compHom (X.presheaf.stalk x) (f.stalkMap x).hom
    stalk M x ≃ₗ[Y.presheaf.stalk (f x)] X.presheaf.stalk x := by
  letI := relativeStalkModule f M x
  letI := Module.compHom (X.presheaf.stalk x) (f.stalkMap x).hom
  exact {
    __ := (hM.stalkLinearEquiv x).toAddEquiv
    map_smul' := fun r m => (hM.stalkLinearEquiv x).map_smul ((f.stalkMap x) r) m }

/-- A locally free rank-one sheaf on a flat scheme over the base is flat
over that base, with the canonical relative stalk actions. -/
lemma IsLocallyFreeRankOne.isFlatOver {M : X.Modules}
    (hM : IsLocallyFreeRankOne M) (f : X ⟶ Y) [Flat f] :
    IsFlatOver f M := by
  intro x
  let := relativeStalkModule f M x
  let := Module.compHom (X.presheaf.stalk x) (f.stalkMap x).hom
  have : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    Flat.stalkMap f x
  exact Module.Flat.of_linearEquiv (hM.relativeStalkLinearEquiv f x)

/-- The underlying sheaf of an actual line bundle is flat over every base
over which its source scheme is flat. -/
lemma LineBundle.isFlatOver (L : LineBundle X) (f : X ⟶ Y) [Flat f] :
    IsFlatOver f L.obj :=
  L.property.isFlatOver f

end Langlands.AlgebraicGeometry.Picard
