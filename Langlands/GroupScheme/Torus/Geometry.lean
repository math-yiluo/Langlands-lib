import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-! # A splitting extension and intrinsic geometry of a torus -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- An actual field extension over which the given group scheme is split. -/
structure TorusSplittingExtension (T : GroupScheme (Spec (CommRingCat.of k))) where
  carrier : Type u
  [field : Field carrier]
  [algebra : Algebra k carrier]
  isSplitTorus : IsSplitTorus ((GroupScheme.baseChange
    (Spec.map (CommRingCat.ofHom (algebraMap k carrier)))).obj T)

attribute [instance] TorusSplittingExtension.field TorusSplittingExtension.algebra

/-- Choose the splitting extension already asserted by the torus predicate. -/
def IsTorus.splittingExtension {T : GroupScheme (Spec (CommRingCat.of k))}
    (hT : IsTorus T) : TorusSplittingExtension T :=
  Classical.choice (by
    obtain ⟨K, hK, aK, hs⟩ := hT
    exact ⟨{
      carrier := K
      field := hK
      algebra := aK
      isSplitTorus := hs }⟩)

/-- Every torus over a field is smooth. -/
theorem IsTorus.smooth {T : GroupScheme (Spec (CommRingCat.of k))} (hT : IsTorus T) :
    Smooth T.X.hom := by
  let E := hT.splittingExtension
  obtain ⟨hsurj, hflat, hqc⟩ := fieldExtension_fpqc k E.carrier
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (f := T.X.hom) (g := Spec.map (CommRingCat.ofHom (algebraMap k E.carrier)))
    ⟨⟨hsurj, hflat⟩, hqc⟩ E.isSplitTorus.smooth

/-- Every torus over a field has connected underlying space. -/
theorem IsTorus.connectedSpace {T : GroupScheme (Spec (CommRingCat.of k))}
    (hT : IsTorus T) : ConnectedSpace T.X.left := by
  let E := hT.splittingExtension
  let b := Spec.map (CommRingCat.ofHom (algebraMap k E.carrier))
  have : Surjective b := (fieldExtension_fpqc k E.carrier).1
  have : ConnectedSpace (pullback T.X.hom b : Scheme.{u}) :=
    E.isSplitTorus.connectedSpace
  exact (inferInstance : Surjective (pullback.fst T.X.hom b)).surj.connectedSpace
    (pullback.fst T.X.hom b).continuous

/-- A commutative group scheme has solvable geometric points. -/
theorem isSolvableGroupScheme_of_isCommMonObj
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsCommMonObj G.X] :
    IsSolvableGroupScheme G := by
  unfold IsSolvableGroupScheme
  let : IsCommMonObj ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X :=
    Functor.isCommMonObj_obj (F := Over.pullback (toAlgebraicClosure k)) (M := G.X)
  infer_instance

end Langlands.GroupScheme
