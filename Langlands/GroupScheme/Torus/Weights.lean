import Langlands.GroupScheme.Torus.Lattice
import Langlands.GroupScheme.Lie.Adjoint

/-! # Weight spaces and roots of a commutative group scheme acting through `Ad` -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {R : CommRingCat.{u}}

namespace Lie

variable {A : Type u} [CommRing A] [Algebra R A]

/-- The value `χ(t) ∈ Aˣ` of a character `χ` at an actual `A`-point `t`, given by the published
identification `Gm.affinePointsEquiv` of the `A`-points of `𝔾_m` with `Aˣ`. -/
def characterValue {T : CommGroupScheme (Spec R)} (χ : characterLattice T)
    (t : AffinePoints T.toGrp A) : Aˣ :=
  Gm.affinePointsEquiv (R := CommRingCat.of A) ((algSpec R).obj (op (CommAlgCat.of R A))).hom
    (t ≫ (CommGroupScheme.groupHom χ).hom.hom)

theorem characterValue_comp {T T' : CommGroupScheme (Spec R)} (f : T ⟶ T')
    (χ : characterLattice T') (t : AffinePoints T.toGrp A) :
    characterValue (f ≫ χ) t = characterValue χ (t ≫ (CommGroupScheme.groupHom f).hom.hom) := by
  rw [characterValue, characterValue, comp_groupHom_comp]

end Lie

/-! ### Instances over bases `Spec (CommRingCat.of k)`

Instance search does not unfold `↑(CommRingCat.of k)` to `k` inside the keys of the generic
instances on `lieKernel`, so they are restated for bases of the form `CommRingCat.of k`. -/

section OfType

variable {k : Type u} [CommRing k] (G : GroupScheme (Spec (CommRingCat.of k)))
  [IsAffineHom G.X.hom] (A : Type u) [CommRing A] [Algebra k A]

instance lieKernelCommGroupOf : CommGroup (lieKernel G A) :=
  lieKernelCommGroup G

instance lieKernelModuleOf : Module A (Additive (lieKernel G A)) :=
  lieKernelModule G

end OfType

variable {T : CommGroupScheme (Spec R)} {G : GroupScheme (Spec R)} [IsAffineHom G.X.hom]

/-- The weight space of a character `χ` of `T` in the actual Lie algebra `Lie(G)(R)`, for a
homomorphism `i : T ⟶ G`: the elements `X` such that for every test algebra `A` and every
`t ∈ T(A)`, `Ad(i(t)) X_A = χ(t) • X_A`, where `X_A` is the image of `X` in `Lie(G)(A)` under the
map induced by `R → A`. -/
def weightSpace (i : T.toGrp ⟶ G) (χ : characterLattice T) :
    Submodule R (Additive (lieKernel G R)) where
  carrier := {X | ∀ (A : Type u) [CommRing A] [Algebra R A] (t : Lie.AffinePoints T.toGrp A),
    adjoint G A (t ≫ i.hom.hom) (lieKernelMapLinear G (Algebra.ofId R A) X) =
      (Lie.characterValue χ t : A) • lieKernelMapLinear G (Algebra.ofId R A) X}
  zero_mem' := by
    intro A _ _ t
    rw [map_zero, map_zero, smul_zero]
  add_mem' := by
    intro X Y hX hY A _ _ t
    rw [map_add, map_add, hX A t, hY A t, smul_add]
  smul_mem' := by
    intro c X hX A _ _ t
    rw [LinearMap.map_smulₛₗ, LinearMap.map_smul, hX A t, smul_comm]

theorem mem_weightSpace {i : T.toGrp ⟶ G} {χ : characterLattice T}
    {X : Additive (lieKernel G R)} :
    X ∈ weightSpace i χ ↔ ∀ (A : Type u) [CommRing A] [Algebra R A]
      (t : Lie.AffinePoints T.toGrp A),
      adjoint G A (t ≫ i.hom.hom) (lieKernelMapLinear G (Algebra.ofId R A) X) =
        (Lie.characterValue χ t : A) • lieKernelMapLinear G (Algebra.ofId R A) X :=
  Iff.rfl

/-- The roots of `T` in `G`: the nonzero characters with a nonzero weight space. -/
def roots (i : T.toGrp ⟶ G) : Set (characterLattice T) :=
  {χ | χ ≠ 0 ∧ weightSpace i χ ≠ ⊥}

theorem mem_roots {i : T.toGrp ⟶ G} {χ : characterLattice T} :
    χ ∈ roots i ↔ χ ≠ 0 ∧ weightSpace i χ ≠ ⊥ :=
  Iff.rfl

end Langlands.GroupScheme
