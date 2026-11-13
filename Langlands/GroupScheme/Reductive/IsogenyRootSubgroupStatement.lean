import Langlands.GroupScheme.Reductive.IsogenyRootDatumStatement
import Langlands.GroupScheme.Rational.RootSubgroup
import Langlands.GroupScheme.SubgroupFunctor.FppfImage
import Langlands.GroupScheme.MatrixRepresentation.TorusEquivariantAdditive

/-! # Statement: root-subgroup images and coordinates of a split group isogeny -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Root subgroups under an isogeny** (the root-image and coordinate assertions of
Milne Proposition 23.5). For any compatible actual-lattice root-datum isogeny, the root
correspondence is exactly the actual fppf-image correspondence. In any whole-root
equivariant additive parametrizations the map is a nonzero scalar times the prescribed
characteristic power, on every test scheme. -/
def IsogenyRootSubgroupStatement : Prop :=
  ∀ (k : Type u) [Field k] (G G' : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    (T T' : CommGroupScheme (Spec (CommRingCat.of k)))
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp),
    haveI := hT.finite_characterLattice
    haveI := hT.finite_cocharacterLattice
    haveI := hT'.finite_characterLattice
    haveI := hT'.finite_cocharacterLattice
    ∀ (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ G'), IsMaximalTorus i → IsMaximalTorus i' →
    ∀ (φ : G ⟶ G') (t : T ⟶ T'), IsIsogeny φ →
      i ≫ φ = CommGroupScheme.groupHom t ≫ i' →
    ∀ (J J' : Type u) [Finite J] [Finite J']
      (P : RootDatum J (characterLattice T) (cocharacterLattice T))
      (P' : RootDatum J' (characterLattice T') (cocharacterLattice T'))
      [P.IsReduced] [P'.IsReduced],
      (haveI := hG.isAffineHom; IsRootDatumOf i P) →
      (haveI := hG'.isAffineHom; IsRootDatumOf i' P') →
    ∀ f : Langlands.LinearAlgebra.RootDatumIsogeny (ringExpChar k) P' P,
      (∀ χ : characterLattice T', f.weightMap χ = t ≫ χ) →
      (∀ ν : cocharacterLattice T, f.coweightMap ν = ν ≫ t) →
    ∀ j' : J',
      (∀ j : J,
        SubgroupFunctor.IsFppfImage
          (RelativeRoot.subgroup i (P.root j))
          (RelativeRoot.subgroup i' (P'.root j')) φ ↔ j = f.indexEquiv j') ∧
      (∀ (x : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G)
        (x' : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G'),
        (RelativeRoot.subgroup i (P.root (f.indexEquiv j'))).IsRepresentedBy x →
        (RelativeRoot.subgroup i' (P'.root j')).IsRepresentedBy x' →
        VectorGroup.IsTorusEquivariant i x (P.root (f.indexEquiv j')) →
        VectorGroup.IsTorusEquivariant i' x' (P'.root j') →
        ∃ c : kˣ,
          ∀ (Z : Over (Spec (CommRingCat.of k))) (a : Γ(Z.left, ⊤)),
            VectorGroup.scalarPoint (CommRingCat.of k) Z a ≫ x.hom.hom ≫ φ.hom.hom =
              VectorGroup.scalarPoint (CommRingCat.of k) Z
                (Z.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv (c : k)) *
                  a ^ f.rootFactor j') ≫ x'.hom.hom)

end Langlands.GroupScheme
