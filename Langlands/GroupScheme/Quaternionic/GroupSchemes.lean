import Langlands.GroupScheme.Quaternionic.Forms
import Langlands.GroupScheme.Quaternionic.IsometryCut
import Langlands.GroupScheme.CentralSimpleNormOne
import Langlands.GroupScheme.IdentityComponent
import Langlands.GroupScheme.SimplyConnected.Basic

/-!
# The symplectic, orthogonal and spin groups of forms over an algebra with involution

For a finite-dimensional division algebra `D` over a field `K` with an involution of the
first kind `σ`, this module constructs, as affine group schemes over `Spec K`:

* the unitary group `U(h)` of the form with Gram matrix `H ∈ M_n(D)` and its subgroup of
  reduced-norm-one elements, the special unitary ("symplectic") group;
* the isometry group `O(q)` of a `σ`-quadratic form `q` in the sense of Tits, and its
  identity component when `O(q)` is smooth.

It also defines the predicate characterizing a spin group of `q`: a simply connected group
with a central isogeny onto the identity component of `O(q)`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic

namespace FirstKindInvolution

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  (σ : FirstKindInvolution K D) {n : Type} [Fintype n] [DecidableEq n]

/-! ### Unitary and symplectic groups -/

/-- The unitary group `U(h)` of the form with Gram matrix `H`: its points with values in a
commutative `K`-algebra `R` are the units `u` of `R ⊗[K] M_n(D)` with `u H ᵗu^σ = H`. -/
abbrev unitaryGroup (H : Matrix n n D) : GroupScheme (Spec (CommRingCat.of K)) :=
  IsometryCut.groupScheme (τ := σ.matrix n) (M := ⊥) IsometryCut.isStable_bot H

/-- The closed inclusion of `U(h)` into the unit group scheme of `M_n(D)`. -/
def unitaryGroupι (H : Matrix n n D) :
    σ.unitaryGroup H ⟶ FiniteAlgebraUnits.groupScheme (Module.finBasis K (Matrix n n D)) :=
  IsometryCut.inclusion IsometryCut.isStable_bot H

theorem isClosedSubgroup_unitaryGroupι (H : Matrix n n D) :
    IsClosedSubgroup (σ.unitaryGroupι H) :=
  IsometryCut.isClosedSubgroup_inclusion IsometryCut.isStable_bot H

/-- On every test scheme `T` with global sections `R`, a point `u` of the unit group of
`M_n(D)` is a point of `U(h)` exactly when `u H ᵗu^σ = H` in `R ⊗[K] M_n(D)`. -/
theorem mem_range_unitaryGroupι_iff (H : Matrix n n D) {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ (FiniteAlgebraUnits.groupScheme (Module.finBasis K (Matrix n n D))).X) :
    x ∈ (SubgroupFunctor.range (σ.unitaryGroupι H)).carrier T ↔
      (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K (Matrix n n D)) T x :
          ((algΓ (CommRingCat.of K)).obj T).unop ⊗[K] Matrix n n D) * (1 ⊗ₜ[K] H) *
        (σ.matrix n).baseChange ((algΓ (CommRingCat.of K)).obj T).unop
          (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K (Matrix n n D)) T x) =
        1 ⊗ₜ[K] H := by
  rw [unitaryGroupι, IsometryCut.mem_range_inclusion_iff, Submodule.baseChange_bot,
    Submodule.mem_bot, IsometryCut.defect, sub_eq_zero]

/-- The symplectic group of the form with Gram matrix `H`: the special unitary group, the
kernel of the reduced norm of `M_n(D)` restricted to `U(h)`. -/
def symplecticGroup [Algebra.IsCentral K D] [Nonempty n] (H : Matrix n n D) :
    GroupScheme (Spec (CommRingCat.of K)) :=
  kernel (σ.unitaryGroupι H ≫ CentralSimpleUnits.reducedNormHom K (Matrix n n D))

/-- The inclusion of the special unitary group into `U(h)`. -/
def symplecticGroupι [Algebra.IsCentral K D] [Nonempty n] (H : Matrix n n D) :
    σ.symplecticGroup H ⟶ σ.unitaryGroup H :=
  kernelι _

/-! ### Orthogonal and spin groups of quadratic forms -/

/-- The isometry group `O(q)` of a `σ`-quadratic form `q`: for a representative `Q` of `q`,
its points with values in `R` are the units `u` of `R ⊗[K] M_n(D)` with
`u Q ᵗu^σ - Q ∈ R ⊗ {x - ᵗx^σ}`. -/
abbrev isometryGroup (q : σ.QuadraticForms n) : GroupScheme (Spec (CommRingCat.of K)) :=
  IsometryCut.groupScheme (τ := σ.matrix n) (M := σ.quadraticKernel n)
    IsometryCut.isStable_alternatingSubspace (Quotient.out q)

/-- The closed inclusion of `O(q)` into the unit group scheme of `M_n(D)`. -/
def isometryGroupι (q : σ.QuadraticForms n) :
    σ.isometryGroup q ⟶ FiniteAlgebraUnits.groupScheme (Module.finBasis K (Matrix n n D)) :=
  IsometryCut.inclusion IsometryCut.isStable_alternatingSubspace (Quotient.out q)

theorem isClosedSubgroup_isometryGroupι (q : σ.QuadraticForms n) :
    IsClosedSubgroup (σ.isometryGroupι q) :=
  IsometryCut.isClosedSubgroup_inclusion IsometryCut.isStable_alternatingSubspace _

/-- On every test scheme `T` with global sections `R`, and for every representative `Q` of
`q`, a point `u` of the unit group of `M_n(D)` is a point of `O(q)` exactly when
`u Q ᵗu^σ - Q ∈ R ⊗ {x - ᵗx^σ}`; in particular the group does not depend on the chosen
representative. -/
theorem mem_range_isometryGroupι_iff (q : σ.QuadraticForms n) (Q : Matrix n n D)
    (hQ : (Submodule.Quotient.mk Q : σ.QuadraticForms n) = q)
    {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ (FiniteAlgebraUnits.groupScheme (Module.finBasis K (Matrix n n D))).X) :
    x ∈ (SubgroupFunctor.range (σ.isometryGroupι q)).carrier T ↔
      IsometryCut.defect (σ.matrix n) Q
          (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K (Matrix n n D)) T x :
            ((algΓ (CommRingCat.of K)).obj T).unop ⊗[K] Matrix n n D) ∈
        (σ.quadraticKernel n).baseChange ((algΓ (CommRingCat.of K)).obj T).unop := by
  refine (IsometryCut.mem_range_inclusion_iff
    (IsometryCut.isStable_alternatingSubspace (τ := σ.matrix n)) (Quotient.out q) x).trans ?_
  apply IsometryCut.defect_mem_iff_of_sub_mem IsometryCut.isStable_alternatingSubspace
  rw [← Submodule.Quotient.eq]
  exact (Submodule.Quotient.mk_out q).trans hQ.symm

instance isAffineHom_isometryGroup (q : σ.QuadraticForms n) :
    IsAffineHom (σ.isometryGroup q).X.hom := by
  change IsAffineHom (Spec.map _)
  infer_instance

/-- The connected isometry group `O(q)⁰`, the identity component of `O(q)`, defined when
`O(q)` is smooth. -/
abbrev connectedIsometryGroup (q : σ.QuadraticForms n) [Smooth (σ.isometryGroup q).X.hom] :
    GroupScheme (Spec (CommRingCat.of K)) :=
  identityComponent (σ.isometryGroup q)

/-- A homomorphism `π : S ⟶ O(q)` exhibits `S` as a spin group of `q` when `S` is simply
connected, `O(q)` is smooth, and `π` is a central isogeny onto the identity component
`O(q)⁰` followed by the inclusion of `O(q)⁰` into `O(q)`. -/
structure IsSpinCover (q : σ.QuadraticForms n) {S : GroupScheme (Spec (CommRingCat.of K))}
    (π : S ⟶ σ.isometryGroup q) : Prop where
  isSimplyConnected : IsSimplyConnected S
  smooth : Smooth (σ.isometryGroup q).X.hom
  exists_centralIsogeny :
    haveI := smooth
    ∃ p : S ⟶ σ.connectedIsometryGroup q,
      IsCentralIsogeny p ∧ p ≫ identityComponentι (σ.isometryGroup q) = π

end FirstKindInvolution

end Langlands.GroupScheme.Quaternionic
