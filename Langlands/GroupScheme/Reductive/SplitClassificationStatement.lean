import Langlands.GroupScheme.Reductive.RootDatumStatement
import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.GroupScheme.CentralIsogeny.Basic
import Mathlib.LinearAlgebra.RootSystem.Hom

/-! # Statements: existence and central isogenies of split reductive groups, and semisimplicity -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Existence Theorem** (Milne Theorem 23.55; over every field also Theorem 23.74). For every
field `k : Type u` and every reduced Mathlib root datum `P`, indexed by a finite type, on a
finitely generated lattice `X` and its dual `Y`, there are a connected reductive group `G` over
`Spec k` and a split maximal torus `i : T ⟶ G` with a root datum `Q` of `i` which is isomorphic
to `P` as a root pairing. -/
def SplitReductiveExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (J X Y : Type u) [Finite J] [AddCommGroup X] [AddCommGroup Y]
    [Module.Finite ℤ X] (P : RootDatum J X Y), P.IsReduced →
      ∃ (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
        (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
        IsSplitTorus T.toGrp ∧ IsMaximalTorus i ∧
          haveI := hG.isAffineHom
          ∃ Q : RootDatum J (characterLattice T) (cocharacterLattice T),
            IsRootDatumOf i Q ∧ Nonempty (RootPairing.Equiv P Q)

/-- **Isogeny Theorem, central case** (Milne Theorem 23.9 with Definitions 23.1, 23.2 and
Proposition 23.5). Let `i : T ⟶ G` and `i' : T' ⟶ G'` be split maximal tori of connected
reductive groups over a field, with root data `P` and `P'`. Every morphism of root pairings
`f : P' ⟶ P` whose weight map `X(T') → X(T)` and coweight map `Y(T) → Y(T')` are injective (a
central isogeny of root data) arises from a central isogeny `φ : G ⟶ G'` and a homomorphism
`t : T ⟶ T'` with `i ≫ φ = t ≫ i'` and `f χ = t ≫ χ` for every character `χ` of `T'`. -/
def SplitCentralIsogenyExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (G G' : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    (T T' : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T.toGrp → IsSplitTorus T'.toGrp →
    ∀ (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ G'), IsMaximalTorus i → IsMaximalTorus i' →
    ∀ (J J' : Type u) (P : RootDatum J (characterLattice T) (cocharacterLattice T))
      (P' : RootDatum J' (characterLattice T') (cocharacterLattice T')),
      (haveI := hG.isAffineHom; IsRootDatumOf i P) →
      (haveI := hG'.isAffineHom; IsRootDatumOf i' P') →
      ∀ f : RootPairing.Hom P' P, Function.Injective f.weightMap →
        Function.Injective f.coweightMap →
          ∃ (φ : G ⟶ G') (t : T ⟶ T'), i ≫ φ = CommGroupScheme.groupHom t ≫ i' ∧
            (∀ χ : characterLattice T', f.weightMap χ = t ≫ χ) ∧ IsCentralIsogeny φ

/-- **Semisimplicity from the root datum** (Milne Proposition 21.48 with Definition C.34, and the
dual form used in the proof of Milne Proposition 21.49(a)). For a connected reductive group `G`
over a field with a split maximal torus `i : T ⟶ G` and a root datum `P` of `i`, `G` is
semisimple exactly when the roots span a subgroup of finite index in the character lattice, and
exactly when the coroots span a subgroup of finite index in the cocharacter lattice. -/
def SplitSemisimpleRootDatumStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T.toGrp → ∀ i : T.toGrp ⟶ G, IsMaximalTorus i →
      haveI := hG.isAffineHom
      ∀ (J : Type u) (P : RootDatum J (characterLattice T) (cocharacterLattice T)),
        IsRootDatumOf i P →
          (IsSemisimple G ↔ Finite (characterLattice T ⧸ P.rootSpan ℤ)) ∧
            (IsSemisimple G ↔ Finite (cocharacterLattice T ⧸ P.corootSpan ℤ))

end Langlands.GroupScheme
