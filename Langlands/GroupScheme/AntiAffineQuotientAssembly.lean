import Langlands.GroupScheme.AntiAffineKernel
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-! # Assembling an anti-affine quotient from a flat affinization -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace FpqcHomDescent

variable {S : Scheme.{u}} {G Q : GroupScheme S}

/-- Smoothness of the full kernel makes an fpqc group homomorphism smooth. -/
theorem smooth_of_smooth_kernel (q : G ⟶ Q)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left] [QuasiCompact q.hom.hom.left]
    [Smooth (kernel q).X.hom] : Smooth q.hom.hom.left := by
  have hp : Smooth (fst G.X (kernel q).X).left := by
    change Smooth (pullback.fst G.X.hom (kernel q).X.hom)
    infer_instance
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (KernelPair.isPullback_scheme q) ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hp

end FpqcHomDescent

namespace AntiAffineQuotient

variable {k : Type u} [Field k]
    {G Q : GroupScheme (Spec (CommRingCat.of k))} (q : G ⟶ Q)
    [Smooth Q.X.hom] [ConnectedSpace Q.X.left]
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left] [QuasiCompact q.hom.hom.left]
    [Smooth (kernel q).X.hom] [ConnectedSpace (kernel q).X.left]

/-- Supply the anti-affineness and smooth projection fields from a flat affinization
with smooth connected target and full kernel. -/
def ofFlatAffinization (hq : IsAffinization q) : AntiAffineQuotient G := by
  have : IsAffine Q.X.left := hq.isAffine
  have : CompactSpace G.X.left :=
    QuasiCompact.compactSpace_of_compactSpace q.hom.hom.left
  exact
    { group := Q
      projection := q
      isAffinization := hq
      smooth := inferInstance
      connectedSpace := inferInstance
      smooth_projection := FpqcHomDescent.smooth_of_smooth_kernel q
      surjective_projection := inferInstance
      quasiCompact_projection := inferInstance
      smooth_kernel := inferInstance
      connectedSpace_kernel := inferInstance
      antiAffine_kernel := hq.antiAffine_kernel }

@[simp]
theorem ofFlatAffinization_group (hq : IsAffinization q) :
    (ofFlatAffinization q hq).group = Q := rfl

@[simp]
theorem ofFlatAffinization_projection (hq : IsAffinization q) :
    (ofFlatAffinization q hq).projection = q := rfl

end AntiAffineQuotient

end Langlands.GroupScheme
