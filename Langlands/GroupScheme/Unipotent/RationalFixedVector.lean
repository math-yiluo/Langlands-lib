import Langlands.GroupScheme.Derived.CentralIntersection.Unipotence

/-! # Fixed vectors from schematically dense rational points -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]

private theorem eq_zero_of_schematicallyDense
    (hdense : ∀ (Z : Scheme.{u}) (z : Z ⟶ G.X.left), IsClosedImmersion z →
      (∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
        ∃ s : Spec (CommRingCat.of k) ⟶ Z, s ≫ z = g.left) → IsIso z)
    (f : Γ(G.X.left, ⊤))
    (hf : ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X, g.left.appTop f = 0) :
    f = 0 := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let I : Ideal Γ(G.X.left, ⊤) := Ideal.span {f}
  let J := Scheme.IdealSheafData.ofIdealTop I
  have hiso : IsIso J.subschemeι := hdense _ _ inferInstance (fun g => by
    have hker : J.subschemeι.ker ≤ g.left.ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.ker_of_isAffine]
      apply Scheme.IdealSheafData.le_of_isAffine
      simpa [J, I, Ideal.span_le, RingHom.mem_ker] using hf g
    exact ⟨IsClosedImmersion.lift _ _ hker, IsClosedImmersion.lift_fac _ _ _⟩)
  have hJ : J = ⊥ := (Scheme.isIso_subschemeι_iff_eq_bot J).1 hiso
  have hI : I = ⊥ := by
    simpa [J] using congrArg
      (fun K : G.X.left.IdealSheafData => K.ideal ⟨⊤, isAffineOpen_top _⟩) hJ
  have hm : f ∈ I := Ideal.subset_span (Set.mem_singleton f)
  simpa [hI] using hm

/-- A vector fixed by all rational points of a schematically dense affine group is fixed
on all test schemes. -/
theorem isFixedVector_of_schematicallyDense {n : Type} [Fintype n] [DecidableEq n]
    (hdense : ∀ (Z : Scheme.{u}) (z : Z ⟶ G.X.left), IsClosedImmersion z →
      (∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
        ∃ s : Spec (CommRingCat.of k) ⟶ Z, s ≫ z = g.left) → IsIso z)
    (ρ : MatrixRepresentation G n) (v : n → k)
    (hfix : ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      (ρ.rationalMatrix g : Matrix n n k) *ᵥ v = v) : ρ.IsFixedVector v := by
  apply (ρ.isFixedVector_iff_universal v).2
  funext i
  rw [← sub_eq_zero]
  apply eq_zero_of_schematicallyDense hdense
  intro g
  let e := Scheme.ΓSpecIso (CommRingCat.of k)
  apply e.commRingCatIsoToRingEquiv.injective
  change CentralIntersection.evalPoint g _ = e.hom 0
  have hv : (CentralIntersection.evalPoint g ∘ fun j => scalarMap G.X (v j)) = v :=
    funext fun j => CentralIntersection.evalPoint_scalarMap g (v j)
  rw [map_sub, RingHom.map_mulVec, CentralIntersection.evalPoint_mapMatrix_pointMatrix,
    hv, hfix, CentralIntersection.evalPoint_scalarMap, sub_self, map_zero]

end Langlands.GroupScheme
