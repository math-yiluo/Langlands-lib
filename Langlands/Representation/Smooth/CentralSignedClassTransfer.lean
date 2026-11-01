import Langlands.Representation.Smooth.CentralClassDetection
import Langlands.Representation.Filtration.MultiplicityTransportProof

/-! Signed exact-class transfer of simple quotients and scalar-series pullback. -/

noncomputable section

namespace Langlands.CentralEigenspaceSplitting

universe uK uG uH uV

variable {k : Type uK} [Field k] {G : Type uG} [Group G]
  {H : Type uH} [Group H] {A : Rep.{uV} k G} {n : ℕ}

/-- A group equivalence pulls a scalar-separated simple series back with
the same scalar function. -/
theorem exists_scalarSeries_pullback (e : H ≃* G)
    (s : ObjectRepFiltration A n) (hs : s.HasSimpleFactors)
    (z : G) (c : Fin n → k)
    (hgr : ∀ i v, (s.gradedRepresentation i).ρ z v = c i • v) :
    ∃ t : ObjectRepFiltration (Rep.of (A.ρ.comp e.toMonoidHom)) n,
      t.HasSimpleFactors ∧
        ∀ i v, (t.gradedRepresentation i).ρ (e.symm z) v = c i • v := by
  obtain ⟨t, _, ht, hE, _⟩ :=
    groupEquivFiltrationMultiplicityTransport k G H e A A n s
  refine ⟨t, ht.mp hs, ?_⟩
  intro i v
  obtain ⟨E⟩ := hE i
  apply apply_eq_smul_of_equiv E.symm (e.symm z) (c i) _ v
  intro w
  change (s.gradedRepresentation i).ρ (e (e.symm z)) w = c i • w
  simpa only [e.apply_symm_apply] using hgr i w

/-- The inverse image of a central group element under a group equivalence
is central. -/
theorem groupEquiv_central (e : H ≃* G) (z : G) (hz : ∀ g, z * g = g * z) :
    ∀ h, e.symm z * h = h * e.symm z := by
  intro h
  apply e.injective
  simpa only [map_mul, e.apply_symm_apply] using hz (e h)

end Langlands.CentralEigenspaceSplitting

namespace Langlands.SmoothRep

open IrreducibleGrothendieckProof

universe uK uG uV

variable {k : Type uK} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]

/-- A finite-length class with a nonzero map to an irreducible cannot be
the negative of another actual finite-length class. -/
theorem ofRepresentation_ne_neg_of_nonzero_simple_hom
    (A C τ : SmoothRep.{uK,uG,uV} k G)
    (hA : A.HasFiniteLength) (hC : C.HasFiniteLength) (hτ : τ.IsIrreducible)
    (f : A.representation.IntertwiningMap τ.representation) (hf : f ≠ 0) :
    FiniteLengthGrothendieckGroup.ofRepresentation C hC ≠
      -FiniteLengthGrothendieckGroup.ofRepresentation A hA := by
  intro h
  have hpos := SimpleMapMultiplicityDetectionProof.positive_of_simple_map hτ
    (compositionMultiplicity ⟨A, hA⟩ τ) (compositionMultiplicity_witness ⟨A, hA⟩ τ)
    (Or.inr ⟨f, hf⟩)
  have he := congrArg factorMap h
  simp only [factorMap_ofRepresentation, map_neg] at he
  have hcoord := congrArg
    (fun v : IrreducibleLattice.{uK,uG,uV} k G => v (irreducibleIsoClass τ hτ)) he
  simp only [compositionFactors_apply, Finsupp.neg_apply] at hcoord
  have hApos : (0 : ℤ) < (compositionMultiplicity ⟨A, hA⟩ τ : ℤ) := by
    exact_mod_cast hpos
  have hCnonneg : (0 : ℤ) ≤ (compositionMultiplicity ⟨C, hC⟩ τ : ℤ) := Nat.cast_nonneg _
  omega

/-- A signed equality with a centrally separated actual class, together
with a nonzero simple Hom, forces the positive sign and an actual quotient. -/
theorem signedClass_eq_one_and_exists_surjective
    (A C τ : SmoothRep.{uK,uG,uV} k G)
    (hA : A.HasFiniteLength) (hC : C.HasFiniteLength) (hτ : τ.IsIrreducible)
    {n : ℕ} (s : ObjectRepFiltration A.obj n) (hs : s.HasSimpleFactors)
    (z : G) (hz : ∀ g, z * g = g * z) (c : Fin n → k) (hc : Function.Injective c)
    (hgr : ∀ i v, (s.gradedRepresentation i).ρ z v = c i • v)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hEq : FiniteLengthGrothendieckGroup.ofRepresentation C hC =
      ε • FiniteLengthGrothendieckGroup.ofRepresentation A hA)
    (f : A.representation.IntertwiningMap τ.representation) (hf : f ≠ 0) :
    ε = 1 ∧ ∃ q : C.representation.IntertwiningMap τ.representation, Function.Surjective q := by
  rcases hε with hε | hε
  · subst ε
    refine ⟨rfl, ?_⟩
    apply exists_surjective_to_simple_of_class_eq A C hA hC s hs z hz c hc hgr
      (by simpa only [one_smul] using hEq) τ.obj hτ f hf
  · subst ε
    exact False.elim
      (ofRepresentation_ne_neg_of_nonzero_simple_hom A C τ hA hC hτ f hf
        (by simpa only [neg_one_smul] using hEq))

/-- Choose the actual simple quotient supplied by a signed exact-class
identity with a centrally separated actual representation. -/
def simpleQuotientOfSignedClass
    (A C τ : SmoothRep.{uK,uG,uV} k G)
    (hA : A.HasFiniteLength) (hC : C.HasFiniteLength) (hτ : τ.IsIrreducible)
    {n : ℕ} (s : ObjectRepFiltration A.obj n) (hs : s.HasSimpleFactors)
    (z : G) (hz : ∀ g, z * g = g * z) (c : Fin n → k) (hc : Function.Injective c)
    (hgr : ∀ i v, (s.gradedRepresentation i).ρ z v = c i • v)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hEq : FiniteLengthGrothendieckGroup.ofRepresentation C hC =
      ε • FiniteLengthGrothendieckGroup.ofRepresentation A hA)
    (f : A.representation.IntertwiningMap τ.representation) (hf : f ≠ 0) :
    {q : C.representation.IntertwiningMap τ.representation // Function.Surjective q} :=
  let h := (signedClass_eq_one_and_exists_surjective A C τ hA hC hτ
    s hs z hz c hc hgr ε hε hEq f hf).2
  ⟨Classical.choose h, Classical.choose_spec h⟩

end Langlands.SmoothRep
