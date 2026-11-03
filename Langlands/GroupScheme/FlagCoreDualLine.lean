import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.MatrixRepresentationRationalPoints

/-! # Semi-invariant linear forms not vanishing on a flag orbit point -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The covering core of the flag step, on rational points.  Let `ρ` be a
finite matrix representation of a smooth connected affine group `G` over an
algebraically closed field whose coordinate line `j` has the Borel subgroup
`B` as unit-scalar stabilizer on all tests, and suppose the `G(k)`-orbit of the
`j`-th basis vector spans the whole coordinate space.  If a subgroup `U` lies in
every Borel subgroup through a maximal torus `T`, then for every rational point
`g` there is a linear form `w` not vanishing on `ρ(g) e_j` whose line is stable
under the rational points of `U`: `w ρ(u) = c w` with `c` a unit. -/
def FlagCoreDualLineStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ G),
    IsMaximalTorus t →
    ∀ (U : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ G),
      (∀ (B' : GroupScheme (Spec (CommRingCat.of k))) (b' : B' ⟶ G),
        IsBorelSubgroup b' → SubgroupFunctor.range t ≤ SubgroupFunctor.range b' →
          SubgroupFunctor.range i ≤ SubgroupFunctor.range b') →
      ∀ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G),
        IsBorelSubgroup b →
        ∀ (n : ℕ) (j : Fin (n + 1)) (ρ : MatrixRepresentation G (Fin (n + 1))),
          (∀ (Z : Over (Spec (CommRingCat.of k))) (x : Z ⟶ G.X),
            x ∈ (SubgroupFunctor.range b).carrier Z ↔
              ∃ c : Γ(Z.left, ⊤)ˣ,
                (ρ.pointMatrix Z x : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) *ᵥ
                    Pi.single j 1 =
                  (c : Γ(Z.left, ⊤)) • (Pi.single j (1 : Γ(Z.left, ⊤)) :
                    Fin (n + 1) → Γ(Z.left, ⊤))) →
          Submodule.span k (Set.range fun g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X =>
              (ρ.rationalMatrix g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ
                (Pi.single j 1 : Fin (n + 1) → k)) = ⊤ →
          ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
            ∃ w : Fin (n + 1) → k,
              w ⬝ᵥ ((ρ.rationalMatrix g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ
                  (Pi.single j 1 : Fin (n + 1) → k)) ≠ 0 ∧
              ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X,
                ∃ c : kˣ,
                  w ᵥ* (ρ.rationalMatrix (x ≫ i.hom.hom) :
                      Matrix (Fin (n + 1)) (Fin (n + 1)) k) = (c : k) • w

end Langlands.GroupScheme
