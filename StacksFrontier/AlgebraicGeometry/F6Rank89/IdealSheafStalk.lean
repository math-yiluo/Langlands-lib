module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.Algebra.Module.StablyFree.FreeOfInvertible
public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.CategoryTheory.Abelian.Projective.Extend
public import Mathlib.CategoryTheory.Sites.LocalSite
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.Order.Interval.Finset.Box
public import Mathlib.RingTheory.Finiteness.Lattice
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.RingTheory.Ideal.UFD
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Square
public import Mathlib.RingTheory.Smooth.Quotient
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationPullback
public import StacksFrontier.Algebra.Homology.ProjectiveDimension
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.AffineSections
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.IntegralSchemes
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Comparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Properties.NoetherianClosedPoints
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Properties.Serre
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.FieldTheory.Separable.PerfectField
public import StacksFrontier.RingTheory.CohenMacaulay.FieldExtension
public import StacksFrontier.RingTheory.FinitePresentation.FiniteTypeDescent
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent
public import StacksFrontier.RingTheory.Flat.ShortExact
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.FlatBaseChange
public import StacksFrontier.RingTheory.Ideal.Over.HeightOne
public import StacksFrontier.RingTheory.RegularLocalRing.FlatLocalHom
public import StacksFrontier.RingTheory.Serre.Defs
public import StacksFrontier.RingTheory.Smooth.LocusBaseChange
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# The stalk of an ideal sheaf, and the ideal sheaf of a reduced closed point

`AlgebraicGeometry.IdealSheafData.stalk I x` is the ideal of the local ring `𝒪_{X,x}` generated
by the sections of the quasi-coherent ideal sheaf `I`. At an affine open neighbourhood it is the
image of `I.ideal U` under the germ map, which is
`AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ`; this file computes it further: it is the
unit ideal exactly off the support of `I`, and for a closed immersion it is the kernel of the map
on stalks.

The reduced closed point `x` of a scheme `X` gives such an ideal sheaf,
`Scheme.IdealSheafData.vanishingIdeal {x}`, and the second half of the file identifies it: on an
affine open it is the prime of `x`, its stalk at `x` is the maximal ideal, and its inverse image
along `X.fromSpecStalk x` is the ideal of the closed point of `Spec 𝒪_{X,x}`. The last of these
is what lets a statement about a closed point of a scheme be transported to the local ring at
that point, and the transport needs that `X.fromSpecStalk x` is flat and a monomorphism, both of
which are proved here.

## Main results

* `AlgebraicGeometry.IdealSheafData.stalk_mono`: the stalk is monotone in the ideal sheaf.
* `AlgebraicGeometry.IdealSheafData.stalk_eq_top_iff_not_mem_support`: the stalk is the unit
  ideal exactly off the support.
* `AlgebraicGeometry.IdealSheafData.stalk_ker_of_isClosedImmersion`: for a closed immersion the
  stalk of its kernel ideal sheaf is the kernel of the induced map of local rings.
* `AlgebraicGeometry.vanishingIdeal_singleton_ideal`: the ideal of a reduced closed point on an
  affine open containing it is the corresponding prime.
* `AlgebraicGeometry.IdealSheafData.stalk_vanishingIdeal_singleton`: its stalk at that point is
  the maximal ideal of the local ring.
* `AlgebraicGeometry.vanishingIdeal_singleton_comap_fromSpecStalk`: its inverse image along
  `X.fromSpecStalk x` is the kernel of the residue map.
* `AlgebraicGeometry.isIso_stalkMap_of_flat_preimmersion`: a flat preimmersion is an
  isomorphism on local rings.
* `AlgebraicGeometry.isRegular_of_stalks` and `AlgebraicGeometry.isRegular_of_iso`: regularity
  of a locally Noetherian scheme is a condition on its local rings, hence invariant under
  isomorphism.

## Implementation notes

The stalk is defined as a supremum over all affine opens containing the point, so computing it on
one affine open needs a cofinality argument: two affine opens containing `x` share a basic open
containing `x` (`AlgebraicGeometry.exists_basicOpen_le_affine_inter`), and the ideals of an ideal
sheaf are compatible with restriction, so every term of the supremum is dominated by the one
chosen.

`AlgebraicGeometry.isIso_pullback_snd_of_factorization` is the categorical fact behind both
`AlgebraicGeometry.ker_comap_of_factorization` and
`AlgebraicGeometry.exists_comapIso_of_isPullback_of_factorization`: a base change along a
monomorphism which the other leg factors through is an isomorphism. It is stated for an arbitrary
category with pullbacks rather than for schemes, since nothing about schemes enters.

`AlgebraicGeometry.vanishingIdeal_singleton_ideal` identifies `PrimeSpectrum.vanishingIdeal` of
the preimage of `{x}` in the affine chart with the prime of `x`. The preimage is computed as a
singleton by injectivity of `IsAffineOpen.fromSpec`, and the resulting equality of ideals is then
transported by `congrArg` rather than by `rw`: the two sides are definitionally the ideal of a
`PrimeSpectrum` point but not syntactically so, and a `change` to the `vanishingIdeal` spelling
followed by a rewrite needs reducible unfolding of `IsAffineOpen.primeIdealOf`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace IdealSheafData

end IdealSheafData

/-- A flat preimmersion induces isomorphisms on local rings: the induced map is surjective
because the morphism is a preimmersion, and injective because a flat local homomorphism is
faithfully flat. -/
theorem isIso_stalkMap_of_flat_preimmersion {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [IsPreimmersion f] (x : X) : IsIso (f.stalkMap x) := by
  let : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  have : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (Flat.iff_flat_stalkMap f).mp ‹Flat f› x
  have : IsLocalHom
      (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) := by
    change IsLocalHom (f.stalkMap x).hom
    infer_instance
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hinj : Function.Injective (f.stalkMap x).hom :=
    FaithfulSMul.algebraMap_injective _ _
  have hsurj : Function.Surjective (f.stalkMap x).hom := Scheme.Hom.stalkMap_surjective f x
  exact (ConcreteCategory.isIso_iff_bijective (f.stalkMap x)).mpr ⟨hinj, hsurj⟩

end AlgebraicGeometry

end
