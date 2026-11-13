import Langlands.GroupScheme.Reductive.RootDatum
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Rational.StandardCocharacterFiniteness
import Langlands.GroupScheme.Rational.SplitTorusIsogenyCocharacterLinear
import Langlands.LinearAlgebra.RootDatumIsogeny
import Mathlib.Algebra.CharP.Defs

/-! # Statements: realization and extension of general split reductive isogenies -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Every isogeny of root data is realized** (Milne Theorem 23.9, final assertion).
The root-datum exponent is the field's characteristic exponent. The realizing
homomorphisms induce both specified lattice maps. -/
def SplitIsogenyExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (G G' : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    (T T' : CommGroupScheme (Spec (CommRingCat.of k)))
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp),
    haveI := hT.finite_characterLattice
    haveI := hT.finite_cocharacterLattice
    haveI := hT'.finite_characterLattice
    haveI := hT'.finite_cocharacterLattice
    ∀ (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ G'), IsMaximalTorus i → IsMaximalTorus i' →
    ∀ (J J' : Type u) [Finite J] [Finite J']
      (P : RootDatum J (characterLattice T) (cocharacterLattice T))
      (P' : RootDatum J' (characterLattice T') (cocharacterLattice T'))
      [P.IsReduced] [P'.IsReduced],
      (haveI := hG.isAffineHom; IsRootDatumOf i P) →
      (haveI := hG'.isAffineHom; IsRootDatumOf i' P') →
      ∀ f : Langlands.LinearAlgebra.RootDatumIsogeny (ringExpChar k) P' P,
        ∃ (φ : G ⟶ G') (t : T ⟶ T'), IsIsogeny φ ∧
          IsIsogeny (CommGroupScheme.groupHom t) ∧
          i ≫ φ = CommGroupScheme.groupHom t ≫ i' ∧
          (∀ χ : characterLattice T', f.weightMap χ = t ≫ χ) ∧
          (∀ ν : cocharacterLattice T, f.coweightMap ν = ν ≫ t)

/-- **The isogeny theorem for a fixed torus isogeny** (Milne Theorem 23.9).
An actual torus isogeny extends to the ambient split reductive groups if and only if
its character and cocharacter maps define an isogeny of their root data. -/
def SplitIsogenyExtensionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G G' : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    (T T' : CommGroupScheme (Spec (CommRingCat.of k)))
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp),
    haveI := hT.finite_characterLattice
    haveI := hT.finite_cocharacterLattice
    haveI := hT'.finite_characterLattice
    haveI := hT'.finite_cocharacterLattice
    ∀ (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ G'), IsMaximalTorus i → IsMaximalTorus i' →
    ∀ (J J' : Type u) [Finite J] [Finite J']
      (P : RootDatum J (characterLattice T) (cocharacterLattice T))
      (P' : RootDatum J' (characterLattice T') (cocharacterLattice T'))
      [P.IsReduced] [P'.IsReduced],
      (haveI := hG.isAffineHom; IsRootDatumOf i P) →
      (haveI := hG'.isAffineHom; IsRootDatumOf i' P') →
      ∀ t : T ⟶ T', IsIsogeny (CommGroupScheme.groupHom t) →
        ((∃ φ : G ⟶ G', IsIsogeny φ ∧
            i ≫ φ = CommGroupScheme.groupHom t ≫ i') ↔
          ∃ f : Langlands.LinearAlgebra.RootDatumIsogeny (ringExpChar k) P' P,
            (∀ χ : characterLattice T', f.weightMap χ = t ≫ χ) ∧
            (∀ ν : cocharacterLattice T, f.coweightMap ν = ν ≫ t))

/-- The realization and fixed-torus extension assertions of Milne Theorem 23.9. -/
def SplitIsogenyTheoremStatement : Prop :=
  SplitIsogenyExistenceStatement.{u} ∧ SplitIsogenyExtensionStatement.{u}

end Langlands.GroupScheme
