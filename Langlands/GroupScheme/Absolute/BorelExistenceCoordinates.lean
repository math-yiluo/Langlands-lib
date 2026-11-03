import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.Rational.CharacterLatticeProof
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-! # Coordinate kernels for maximal connected solvable subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.BorelExistence

variable {k : Type u} [Field k]
  {B B' G : GroupScheme (Spec (CommRingCat.of k))}

/-- The ideal of global functions vanishing on an embedded subgroup scheme. -/
def coordinateKernel (i : B ⟶ G) : Ideal Γ(G.X.left, ⊤) :=
  RingHom.ker i.hom.hom.left.appTop.hom

/-- A smooth connected group scheme over a field has a prime coordinate kernel. -/
theorem coordinateKernel_isPrime (i : B ⟶ G) [Smooth B.X.hom]
    [ConnectedSpace B.X.left] : (coordinateKernel i).IsPrime := by
  have : IsLocallyNoetherian B.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian B.X.hom
  have : IsIntegral B.X.left := CharacterLatticeProof.isIntegral_of_smooth k B.X.hom
  exact RingHom.ker_isPrime _

/-- Coordinate kernels reverse containment of subgroup embeddings. -/
theorem coordinateKernel_le (i : B ⟶ G) (i' : B' ⟶ G) (f : B ⟶ B')
    (h : f ≫ i' = i) : coordinateKernel i' ≤ coordinateKernel i := by
  intro a ha
  have heq : i.hom.hom.left = f.hom.hom.left ≫ i'.hom.hom.left :=
    congrArg (fun j : B ⟶ G => j.hom.hom.left) h.symm
  change i.hom.hom.left.appTop a = 0
  rw [heq, Scheme.Hom.comp_appTop]
  change f.hom.hom.left.appTop (i'.hom.hom.left.appTop a) = 0
  exact (congrArg f.hom.hom.left.appTop ha).trans (map_zero _)

/-- Equal coordinate kernels of two closed embeddings into an affine scheme force any
factorization between them to be an isomorphism of group schemes. -/
theorem isIso_of_coordinateKernel_eq [IsAffineHom G.X.hom]
    (i : B ⟶ G) (i' : B' ⟶ G) (f : B ⟶ B')
    (hi : IsClosedSubgroup i) (hi' : IsClosedSubgroup i')
    (h : f ≫ i' = i) (hker : coordinateKernel i = coordinateKernel i') : IsIso f := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsClosedImmersion i'.hom.hom.left := hi'
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hsheaf : i.hom.hom.left.ker = i'.hom.hom.left.ker :=
    by simpa only [Scheme.ker_of_isAffine, coordinateKernel] using
      congrArg Scheme.IdealSheafData.ofIdealTop hker
  have : IsIso f.hom.hom.left := IsClosedImmersion.isIso_of_ker_eq
    i.hom.hom.left i'.hom.hom.left f.hom.hom.left
    (congrArg (fun j : B ⟶ G => j.hom.hom.left) h) hsheaf
  have : IsIso ((Over.forget _).map f.hom.hom) := ‹IsIso f.hom.hom.left›
  have : IsIso f.hom.hom := isIso_of_reflects_iso _ (Over.forget _)
  have : IsIso ((Mon.forget _).map f.hom) := ‹IsIso f.hom.hom›
  have : IsIso f.hom := isIso_of_reflects_iso _ (Mon.forget _)
  have : IsIso ((Grp.forget₂Mon _).map f) := ‹IsIso f.hom›
  exact isIso_of_reflects_iso f (Grp.forget₂Mon _)

/-- The global coordinate ring of an affine group scheme of finite type over a field is
noetherian. -/
theorem isNoetherianRing_globalSections (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] :
    IsNoetherianRing Γ(G.X.left, ⊤) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsLocallyNoetherian G.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  exact IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top G.X.left⟩

/-- In an affine group scheme of finite type, a smooth connected subgroup has finite
prime-kernel height. -/
theorem coordinateKernel_height_ne_top [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (i : B ⟶ G) [Smooth B.X.hom]
    [ConnectedSpace B.X.left] : (coordinateKernel i).height ≠ ⊤ := by
  have := isNoetherianRing_globalSections G
  have := coordinateKernel_isPrime i
  exact Ideal.height_ne_top_of_isPrime

/-- A closed connected smooth subgroup cannot be properly contained in another one whose
coordinate-kernel height is at least its own. -/
theorem isIso_of_coordinateKernel_height_le [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (i : B ⟶ G) (i' : B' ⟶ G) (f : B ⟶ B')
    (hi : IsClosedSubgroup i) (hi' : IsClosedSubgroup i')
    [Smooth B'.X.hom] [ConnectedSpace B'.X.left]
    (h : f ≫ i' = i) (hheight : (coordinateKernel i).height ≤ (coordinateKernel i').height) :
    IsIso f := by
  have := isNoetherianRing_globalSections G
  have := coordinateKernel_isPrime i'
  have hker := Ideal.eq_of_le_of_height_le (coordinateKernel i')
    (coordinateKernel_le i i' f h) hheight
  exact isIso_of_coordinateKernel_eq i i' f hi hi' h hker.symm

end Langlands.GroupScheme.BorelExistence
