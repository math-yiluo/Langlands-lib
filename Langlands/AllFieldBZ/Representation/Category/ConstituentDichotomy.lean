import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalSupport
import Langlands.Representation.Category.ConstituentDichotomy

/-!
# All-field port of `Langlands.Representation.Category.ConstituentDichotomy`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Category.ConstituentDichotomy` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.SmoothRep
open Langlands.SmoothRep
universe uR uG uV

variable {R : Type uR} [Field R] {G : Type uG} [Group G] [TopologicalSpace G]

/-- An intertwiner vanishing on an invariant submodule descends to the actual
quotient by it. -/
private def _root_.Langlands.SmoothRep.quotientLift {A B : SmoothRep.{uR, uG, uV} R G}
    (S : Subrepresentation A.representation) (f : A ⟶ B)
    (h : S.toSubmodule ≤ (hom f).toLinearMap.ker) : quotient A S ⟶ B :=
  ofHom {
    toLinearMap := S.toSubmodule.liftQ (hom f).toLinearMap h
    isIntertwining' g := by
      apply Submodule.linearMap_qext
      ext v
      exact Representation.IntertwiningMap.isIntertwining _ _ (hom f) g v }

/-- The actual quotient by an intertwiner's kernel is isomorphic to its image. -/
private def _root_.Langlands.SmoothRep.quotientKernelIsoImage {A B : SmoothRep.{uR, uG, uV} R G}
    (f : A ⟶ B) : quotient A (hom f).ker ≅ image f :=
  mkIso <| Representation.Equiv.mk (hom f).toLinearMap.quotKerEquivRange fun g => by
    apply Submodule.linearMap_qext
    ext v
    exact Subtype.ext (Representation.IntertwiningMap.isIntertwining _ _ (hom f) g v)

end Langlands.AllFieldBZ.SmoothRep
