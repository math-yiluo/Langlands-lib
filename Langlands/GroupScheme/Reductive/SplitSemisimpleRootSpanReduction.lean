import Langlands.GroupScheme.Reductive.SplitClassificationStatement
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Langlands.GroupScheme.Rational.StandardCocharacterFiniteness
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate

/-! # Reduction of the split semisimplicity criterion to its root form

The coroot finite-index form of `SplitSemisimpleRootDatumStatement` follows from the root form
by pure lattice theory (Milne Lemma C.41 and the proof of Proposition 21.49(a)). -/

universe u

open CategoryTheory AlgebraicGeometry

namespace RootPairing

/-- For a root datum with finitely many roots on a finitely generated lattice `X`, the roots span
a subgroup of finite index in `X` exactly when the coroots span a subgroup of finite index in
`Y`: the root and coroot spans have equal rank (Milne Lemma C.41), and so do the perfectly paired
lattices `X` and `Y`. -/
theorem finite_quotient_rootSpan_iff_corootSpan {ι X Y : Type*} [Finite ι] [AddCommGroup X]
    [AddCommGroup Y] [Module.Finite ℤ X] (P : RootDatum ι X Y) :
    Finite (X ⧸ P.rootSpan ℤ) ↔ Finite (Y ⧸ P.corootSpan ℤ) := by
  classical
  have := Fintype.ofFinite ι
  have : Module.IsReflexive ℤ X := .of_isPerfPair P.toLinearMap
  have : Module.Free ℤ X := Module.free_of_finite_type_torsion_free'
  let e : Y ≃ₗ[ℤ] Module.Dual ℤ X := P.flip.toLinearMap.toPerfPair
  have : Module.Finite ℤ Y := Module.Finite.equiv e.symm
  have : Module.Free ℤ Y := Module.Free.of_equiv e.symm
  rw [Submodule.finiteQuotient_iff, Submodule.finiteQuotient_iff, P.finrank_corootSpan_eq',
    Module.finrank_of_isPerfPair P.toLinearMap]

end RootPairing

namespace Langlands.GroupScheme

/-- **Semisimplicity from the root span** (Milne Proposition 21.48 with Definition C.34). The root
form of `SplitSemisimpleRootDatumStatement`: for a connected reductive group `G` over a field
with a split maximal torus `i : T ⟶ G` and a root datum `P` of `i`, `G` is semisimple exactly
when the roots span a subgroup of finite index in the character lattice. -/
def SplitSemisimpleRootSpanStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T.toGrp → ∀ i : T.toGrp ⟶ G, IsMaximalTorus i →
      haveI := hG.isAffineHom
      ∀ (J : Type u) (P : RootDatum J (characterLattice T) (cocharacterLattice T)),
        IsRootDatumOf i P → (IsSemisimple G ↔ Finite (characterLattice T ⧸ P.rootSpan ℤ))

/-- The root datum of a split maximal torus of a smooth affine group has finitely many roots: its
roots are the roots of `i`, which lie in the finite weight support of the Lie algebra. -/
theorem IsRootDatumOf.finite_index {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hT : IsSplitTorus T.toGrp) {i : T.toGrp ⟶ G} {J : Type*}
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)} (hP : IsRootDatumOf i P) :
    Finite J := by
  have hfin : (Set.range P.root).Finite := by
    rw [hP.2.1]
    exact (hT.finite_weightSupport i).subset fun _ hχ => hχ.2
  exact (Set.finite_range_iff P.root.injective).1 hfin

/-- The root form of the split semisimplicity criterion implies both forms: the coroot form
follows from the root form by `RootPairing.finite_quotient_rootSpan_iff_corootSpan`. -/
theorem splitSemisimpleRootDatum_of_rootSpan (h : SplitSemisimpleRootSpanStatement.{u}) :
    SplitSemisimpleRootDatumStatement.{u} := by
  intro k _ G hG T hT i hi J P hP
  have h₁ := h k G hG T hT i hi J P hP
  refine ⟨h₁, h₁.trans ?_⟩
  have := hG.isAffineHom
  have := hG.smooth
  have : Finite J := hP.finite_index hT
  have : Module.Finite ℤ (characterLattice T) := hT.finite_characterLattice
  exact P.finite_quotient_rootSpan_iff_corootSpan

end Langlands.GroupScheme
