import Langlands.Geometry.Building.IntegerValuationTitsIndexCartan
import Langlands.Geometry.Building.GaloisFacetAction
import Langlands.Geometry.Building.AnisotropicGaloisFixedTranslations
import Langlands.Geometry.Building.RelativeIrreducibleAffineRoots
import Langlands.GroupScheme.Reductive.SplitRankZeroIsomorphism

/-!
# Affine Cartan extensions for anisotropic groups from a Galois-stable chamber

Let `G` be an anisotropic group over `k` with Tits index `d`, let `K/k` be a Galois extension
inside the separable closure, and let `i : T ⟶ G` be a closed subgroup whose scalar extension
`i_K` is a maximal split torus and a maximal torus of `G_K`. Given a Galois-stable KP apartment
`D` of `i_K` for an integer-valued valuation `v` of `K` with a uniformizer, together with
centralizer and V 6 data, bundle them as `IntegerValuationBuildingData` over `K`. If `G_K` is
almost simple and the Galois action stabilizes the chamber of a regular point `c`, then under the
published statement `RelativeRootSystemIrreducibleStatement` all remaining inputs of
`exists_transitive_titsIndexCartanExtension_of_integerValuation` hold: the affine roots are
nonempty and irreducible, and the chamber is transitive. This gives the integer matrix on
`Option d.Vertex` required by the local anisotropic affine-diagram target (KP Theorem 10.3.1).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

open AffineRootSystem GalleryGeometry RealTorusSpace

/-- A split maximal torus of an almost-simple group has a relative root: otherwise the torus
would be the whole group, which is commutative. -/
private theorem relativeRoots_nonempty_of_isAlmostSimple {L : Type u} [Field L]
    {H : GroupScheme (Spec (CommRingCat.of L))} [IsAffineHom H.X.hom]
    {S : CommGroupScheme (Spec (CommRingCat.of L))}
    (hH : IsAlmostSimple H) (j : S.toGrp ⟶ H) (hS : IsSplitTorus S.toGrp)
    (hj : IsMaximalTorus j) : (relativeRoots j).Nonempty := by
  by_contra hne
  have hempty : roots j = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
  let : IsIso j := hH.isSemisimple.isConnectedReductive.isIso_of_roots_eq_empty hS hj hempty
  apply hH.noncommutative
  intro Z x y
  apply (commute_iff_eq x y).mpr
  apply (cancel_mono (inv j).hom.hom).mp
  simp only [MonObj.mul_comp]
  exact mul_comm _ _

variable (k K : Type u) [Field k] [Field K] [Algebra k K] [IsGalois k K]
  [Algebra K (SeparableClosure k)] [IsScalarTower k K (SeparableClosure k)]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G) (i : T.toGrp ⟶ G)
  [Mono (CategoryTheory.Functor.map
    (GroupScheme.baseChange (algebraBaseMap k K)) i).hom.hom.left]
  {v : Valuation K (WithZero (Multiplicative ℤ))}
  (D : KPApartmentData
    (S := CategoryTheory.Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T)
    (CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k K)) i)
    (IntegerValuation.order v))
  (hD : KPApartmentData.GaloisStable k K i D)
  (hGK : IsConnectedReductive ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
  (hiK : IsMaximalSplitTorus
    (T := CategoryTheory.Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T)
    (CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k K)) i))
  (C : CentralizerDatum
    (S := CategoryTheory.Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T)
    (CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k K)) i))
  (h6 : IntegerValuation.IsOmegaCompatible v D C)
  (hunit : ∃ t : Kˣ, IntegerValuation.order v t = 1)
  (hstmt : RelativeRootSystemIrreducibleStatement.{u})
  (hG : IsAnisotropic G) (hic : IsClosedSubgroup i)
  (hAS : IsAlmostSimple ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
  (hiM : IsMaximalTorus
    (T := CategoryTheory.Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T)
    (CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k K)) i))

local notation "B" => KPApartmentData.integerBuildingData D hGK hiK C h6

include hGK hiK C h6 hunit hstmt hG hic hAS hiM

omit [Algebra K (SeparableClosure k)] [IsScalarTower k K (SeparableClosure k)] in
/-- **The chamber inputs for an anisotropic group.** For the building data over `K` bundled
from a Galois-stable apartment `D` of `i_K`, and a regular point `c` whose chamber is
stabilized by the Galois action, the affine roots are nonempty and irreducible, every simple
affine root of the chamber is carried to every other by a root-preserving automorphism, and the
chamber Cartan matrix is vertex transitive. -/
theorem integerValuationChamberInputs_of_isAnisotropic {c : D.Apartment}
    (hc : IsRegular D.affineRoots c)
    (hC : ∀ σ : K ≃ₐ[k] K,
      KPApartmentData.galoisAffineAction k K i D hD σ '' facet D.affineRoots c =
        facet D.affineRoots c) :
    (B).affineRoots.Nonempty ∧ IsIrreducibleRoots (B).affineRoots ∧
      ∃ _ : Fintype (simpleAffineRoots (B).affineRoots (facet (B).affineRoots c)),
        AffineCartan.IsVertexTransitive
            (chamberCartanMatrix (B).affineRoots (facet (B).affineRoots c)) ∧
          HasTransitiveSimpleRoots (B).affineRoots (facet (B).affineRoots c) := by
  have hΨ : IsAffineRootSystemWithRankZero D.affineRoots :=
    (B).isAffineRootSystemWithRankZero_affineRoots hunit
  have hderiv : derivativeRoots D.affineRoots =
      Set.range (rootForm
        (S := CategoryTheory.Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T)
        (CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k K)) i)) :=
    (B).derivativeRoots_affineRoots_of_maximalTorus hiM
  have hT := hiK.isSplitSubtorus.1
  obtain ⟨hne, hirr⟩ := nonempty_and_isIrreducibleRoots_of_isAlmostSimple hstmt hAS hiK
    (relativeRoots_nonempty_of_isAlmostSimple hAS _ hT hiM) hΨ hderiv
  let := (finite_simpleAffineRoots hΨ hc).fintype
  obtain ⟨htrans, hmat⟩ := KPApartmentData.chamberTransitivity_of_isAnisotropic k K i D hD hG
    hic hT hΨ hirr hc hne hC
  exact ⟨hne, hirr, this, hmat, htrans⟩

/-- **Affine Cartan extension for an anisotropic group.** Under the hypotheses of
`integerValuationChamberInputs_of_isAnisotropic`, there is an integer matrix on
`Option d.Vertex` whose block on the absolute simple vertices is the Cartan matrix of the Tits
index `d`, with diagonal entries `2`, nonpositive off-diagonal entries, symmetric zero pattern,
a positive left kernel vector, and a transitive group of entry-preserving permutations. -/
theorem exists_transitive_titsIndexCartanExtension_of_isAnisotropic {c : D.Apartment}
    (hc : IsRegular D.affineRoots c)
    (hC : ∀ σ : K ≃ₐ[k] K,
      KPApartmentData.galoisAffineAction k K i D hD σ '' facet D.affineRoots c =
        facet D.affineRoots c) :
    ∃ N : Matrix (Option d.Vertex) (Option d.Vertex) ℤ,
      (∀ a b, N (some a) (some b) = d.cartan a b) ∧
      (∀ a, N a a = 2) ∧
      (∀ a b, a ≠ b → N a b ≤ 0) ∧
      (∀ a b, N a b = 0 ↔ N b a = 0) ∧
      (∃ m : Option d.Vertex → ℤ,
        (∀ a, 0 < m a) ∧ Matrix.vecMul m N = 0) ∧
      AffineCartan.IsVertexTransitive N := by
  obtain ⟨hne, hirr, _, hmat, htrans⟩ := integerValuationChamberInputs_of_isAnisotropic k K i D hD
    hGK hiK C h6 hunit hstmt hG hic hAS hiM hc hC
  exact exists_transitive_titsIndexCartanExtension_of_integerValuation d (B) hunit hiM hc hne
    hirr hmat htrans

/-- The integer matrix on `Option d.Vertex` chosen by
`exists_transitive_titsIndexCartanExtension_of_isAnisotropic`. -/
def anisotropicTitsIndexCartanExtension {c : D.Apartment} (hc : IsRegular D.affineRoots c)
    (hC : ∀ σ : K ≃ₐ[k] K,
      KPApartmentData.galoisAffineAction k K i D hD σ '' facet D.affineRoots c =
        facet D.affineRoots c) :
    Matrix (Option d.Vertex) (Option d.Vertex) ℤ :=
  Classical.choose (exists_transitive_titsIndexCartanExtension_of_isAnisotropic k K d i D hD hGK
    hiK C h6 hunit hstmt hG hic hAS hiM hc hC)

/-- The chosen matrix has the Cartan matrix of `d` as its block on the absolute simple vertices
and the remaining five properties of the local anisotropic affine-diagram target. -/
theorem anisotropicTitsIndexCartanExtension_spec {c : D.Apartment}
    (hc : IsRegular D.affineRoots c)
    (hC : ∀ σ : K ≃ₐ[k] K,
      KPApartmentData.galoisAffineAction k K i D hD σ '' facet D.affineRoots c =
        facet D.affineRoots c) :
    let N := anisotropicTitsIndexCartanExtension k K d i D hD hGK hiK C h6 hunit hstmt hG hic
      hAS hiM hc hC
    (∀ a b, N (some a) (some b) = d.cartan a b) ∧
      (∀ a, N a a = 2) ∧
      (∀ a b, a ≠ b → N a b ≤ 0) ∧
      (∀ a b, N a b = 0 ↔ N b a = 0) ∧
      (∃ m : Option d.Vertex → ℤ,
        (∀ a, 0 < m a) ∧ Matrix.vecMul m N = 0) ∧
      AffineCartan.IsVertexTransitive N :=
  Classical.choose_spec (exists_transitive_titsIndexCartanExtension_of_isAnisotropic k K d i D hD
    hGK hiK C h6 hunit hstmt hG hic hAS hiM hc hC)

end Langlands.Geometry.Building
