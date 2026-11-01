import Langlands.Cohomology.ExtRightDerived
import Langlands.Cohomology.HyperextSecondPage

/-!
# The second page of the hyperext spectral sequence for smooth representations

For the abelian category of smooth representations, with any derived category, the object in
position `(p, q)` on page 2 of the hyperext spectral sequence of `K` and a smooth
representation `W` placed in degree `0` is the smooth Ext `SmoothExt.ext R G (H^{-q} K) p`
evaluated at `W`, the `p`-th right derived functor of equivariant Hom. This combines the
generic identification `HyperextSpectralSequence.secondPageExtAddEquiv` with Mathlib's `Ext`
and the comparison `ExtRightDerived.smoothExtAddEquiv` of Mathlib's `Ext` with smooth Ext.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite DerivedCategory

namespace Langlands.Cohomology.SmoothHyperext

open HyperextSpectralSequence

universe w u

variable (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [HasDerivedCategory.{w} (SmoothRep.{u, u, u} R G)]

/-- The object in position `(p, q)`, `p : ℕ`, on page 2 of the hyperext spectral sequence of
`K` and the smooth representation `W` placed in degree `0` is additively equivalent to the
smooth Ext `Ext^p(H^{-q}(K), W)`, the `p`-th right derived functor of equivariant Hom out of
`H^{-q}(K)` evaluated at `W`. -/
def secondPageAddEquiv (K : DerivedCategory (SmoothRep.{u, u, u} R G))
    (W : SmoothRep.{u, u, u} R G) (p : ℕ) (q : ℤ) :
    ((hyperextSpectralSequence TStructure.t K ((singleFunctor _ 0).obj W)).page 2).X ⟨p, q⟩ ≃+
      (SmoothExt.ext R G ((homologyFunctor _ (-q)).obj K) p).obj W :=
  letI := ExtRightDerived.hasExt_smoothRep R G
  (secondPageIso TStructure.t K ((singleFunctor _ 0).obj W) p q).addCommGroupIsoToAddEquiv.trans
    ((secondPageExtAddEquiv K W p q).trans
      (ExtRightDerived.smoothExtAddEquiv R G ((homologyFunctor _ (-q)).obj K) W p).symm)

/-- For a cochain complex `L` of smooth representations, the object in position `(p, q)` on
page 2 of the hyperext spectral sequence of the image of `L` in the derived category and `W` is
additively equivalent to the smooth Ext `Ext^p(H^{-q}(L), W)` of the cohomology of `L`. -/
def complexSecondPageAddEquiv (L : CochainComplex (SmoothRep.{u, u, u} R G) ℤ)
    (W : SmoothRep.{u, u, u} R G) (p : ℕ) (q : ℤ) :
    ((hyperextSpectralSequence TStructure.t (Q.obj L) ((singleFunctor _ 0).obj W)).page 2).X
        ⟨p, q⟩ ≃+
      (SmoothExt.ext R G (L.homology (-q)) p).obj W :=
  (secondPageAddEquiv R G (Q.obj L) W p q).trans
    (((SmoothExt.bifunctor R G p).mapIso
      ((homologyFunctorFactors _ (-q)).app L).symm.op).app W).toLinearEquiv.toAddEquiv

/-- In position `(0, q)`, page 2 of the hyperext spectral sequence of `K` and `W` is the group
of equivariant maps `H^{-q}(K) ⟶ W`. -/
def secondPageZeroAddEquiv (K : DerivedCategory (SmoothRep.{u, u, u} R G))
    (W : SmoothRep.{u, u, u} R G) (q : ℤ) :
    ((hyperextSpectralSequence TStructure.t K ((singleFunctor _ 0).obj W)).page 2).X ⟨0, q⟩ ≃+
      ((homologyFunctor _ (-q)).obj K ⟶ W) :=
  (secondPageAddEquiv R G K W 0 q).trans
    ((SmoothExt.extZeroIso R G ((homologyFunctor _ (-q)).obj K)).app W).toLinearEquiv.toAddEquiv

/-- If `W` is injective, page 2 of the hyperext spectral sequence of `K` and `W` is zero in
positions `(p, q)` with `p > 0`. -/
theorem isZero_secondPage_of_injective (K : DerivedCategory (SmoothRep.{u, u, u} R G))
    (W : SmoothRep.{u, u, u} R G) [Injective W] (p q : ℤ) (hp : 0 < p) :
    IsZero (((hyperextSpectralSequence TStructure.t K ((singleFunctor _ 0).obj W)).page 2).X
      ⟨p, q⟩) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = ((n + 1 : ℕ) : ℤ) := ⟨p.toNat - 1, by lia⟩
  have : Subsingleton ((SmoothExt.ext R G ((homologyFunctor _ (-q)).obj K) (n + 1)).obj W) :=
    ModuleCat.subsingleton_of_isZero
      (SmoothExt.isZero_ext_succ_of_injective R G ((homologyFunctor _ (-q)).obj K) W n)
  exact AddCommGrpCat.isZero_of_iff_subsingleton.2
    (secondPageAddEquiv R G K W (n + 1) q).toEquiv.subsingleton

end Langlands.Cohomology.SmoothHyperext
