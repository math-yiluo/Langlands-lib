import Langlands.GroupScheme.Rational.RootDoubleCommutatorPairing
import Langlands.GroupScheme.Rational.VectorPairingWeightLinearity

/-! # Bilinearity of the commutator pairing of a multipliable relative root

The commutator pairing `U_a / U_{2a} × U_a / U_{2a} ⟶ U_{2a}` is bilinear over every test
scheme's ring of global functions, in weight vector coordinates of weights `a` and `2 • a`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {U U₂ : GroupScheme (Spec (CommRingCat.of k))}
    {i : S.toGrp ⟶ G} {a : characterLattice S}
    {j : U ⟶ G} {hj : (subgroup i a).IsRepresentedBy j}
    {j₂ : U₂ ⟶ G} {hj₂ : (subgroup i (2 • a)).IsRepresentedBy j₂}

/-- The commutator pairing is bilinear in any weight vector coordinates of weight `a` on the
quotient and of weight `2 • a` on the doubled root group. -/
theorem DoubleRootCommutatorPairing.isBilinearVectorPairing
    (C : DoubleRootCommutatorPairing i a hj hj₂) (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0)
    {d m : ℕ}
    {e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ C.V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤))}
    {e' : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ U₂.X) ≃* Multiplicative (Fin m → Γ(T.left, ⊤))}
    (he : IsWeightVectorCoordinates C.action a e)
    (he' : IsWeightVectorCoordinates (subgroupAction i (2 • a) j₂ hj₂) (2 • a) e') :
    IsBilinearVectorPairing e e' C.pairing :=
  isBilinearVectorPairing_of_equivariant hS ha he he' C.lift_mul_pairing C.lift_pairing_mul
    C.lift_pairing_act

variable [IsAffineHom G.X.hom]

/-- If no `n • a` with `n ≥ 3` is a relative root, then `2 • a` has no higher roots. -/
theorem hasNoHigherRoots_two_nsmul (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots i) :
    HasNoHigherRoots i (2 • a) := by
  intro n hn
  rw [smul_smul]
  exact hhigh (n * 2) (by omega)

/-- **Bilinear commutator coordinates.** If no `n • a` with `n ≥ 3` is a relative root, the
quotient and the doubled root group have weight vector coordinates of weights `a` and
`2 • a` in which the commutator pairing is bilinear. -/
theorem DoubleRootCommutatorPairing.exists_bilinear_coordinates [Smooth G.X.hom]
    (C : DoubleRootCommutatorPairing i a hj hj₂) (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0)
    (hhigh : ∀ n : ℕ, 3 ≤ n → n • a ∉ relativeRoots i) :
    ∃ (d m : ℕ)
      (e : ∀ T : Over (Spec (CommRingCat.of k)),
        (T ⟶ C.V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))
      (e' : ∀ T : Over (Spec (CommRingCat.of k)),
        (T ⟶ U₂.X) ≃* Multiplicative (Fin m → Γ(T.left, ⊤))),
      IsWeightVectorCoordinates C.action a e ∧
        IsWeightVectorCoordinates (subgroupAction i (2 • a) j₂ hj₂) (2 • a) e' ∧
        IsBilinearVectorPairing e e' C.pairing := by
  obtain ⟨d, e, he⟩ := C.weightVectorStructure.1
  obtain ⟨m, e', he'⟩ := weightVectorCoordinatesOfNoHigherRoots hS i
    (hS.nsmul_ne_zero ha two_ne_zero) (hasNoHigherRoots_two_nsmul hhigh) hj₂
  exact ⟨d, m, e, e', he, he', C.isBilinearVectorPairing hS ha he he'⟩

end Langlands.GroupScheme.RelativeRoot
