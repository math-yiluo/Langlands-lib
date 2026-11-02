import Langlands.GroupScheme.MatrixRepresentation
import Langlands.GroupScheme.SubgroupFunctor
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Unipotent, pseudo-reductive and reductive group schemes

Fixed vectors of finite free coefficient representations, unipotent group schemes over a field
(every nonzero finite-dimensional representation has a nonzero fixed vector), closed subgroups,
the triviality of the unipotent radical, connected reductive groups over a field, and reductive
group schemes over an arbitrary base scheme (smooth, affine, with connected reductive geometric
fibres).
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix

namespace Langlands.GroupScheme

section FixedVectors

variable {R : CommRingCat.{u}}

/-- The structure ring map `R → Γ(T, 𝒪_T)` of a scheme `T` over `Spec R`. -/
def scalarMap (T : Over (Spec R)) : R →+* Γ(T.left, ⊤) :=
  ((Scheme.ΓSpecIso R).inv ≫ T.hom.appTop).hom

namespace MatrixRepresentation

variable {G : GroupScheme (Spec R)} {n : Type} [Fintype n] [DecidableEq n]

/-- A coordinate vector `v ∈ Rⁿ` is fixed by `ρ` if, for every scheme `T` over `Spec R` and every
point `g ∈ G(T)`, the matrix `ρ(g)` fixes the image of `v` in `Γ(T, 𝒪_T)ⁿ`. -/
def IsFixedVector (ρ : MatrixRepresentation G n) (v : n → R) : Prop :=
  ∀ (T : Over (Spec R)) (g : T ⟶ G.X),
    (ρ.pointMatrix T g : Matrix n n Γ(T.left, ⊤)) *ᵥ (fun i => scalarMap T (v i)) =
      fun i => scalarMap T (v i)

/-- The submodule `(Rⁿ)^G` of fixed vectors of `ρ`. -/
def fixedSubmodule (ρ : MatrixRepresentation G n) : Submodule R (n → R) where
  carrier := {v | ρ.IsFixedVector v}
  zero_mem' T g := by
    simp only [Pi.zero_apply, map_zero]
    exact Matrix.mulVec_zero _
  add_mem' {v w} hv hw T g := by
    have h : (fun i => scalarMap T ((v + w) i)) =
        (fun i => scalarMap T (v i)) + fun i => scalarMap T (w i) := by
      funext i
      simp only [Pi.add_apply, map_add]
    rw [h, Matrix.mulVec_add, hv T g, hw T g]
  smul_mem' c v hv T g := by
    have h : (fun i => scalarMap T ((c • v) i)) = scalarMap T c • fun i => scalarMap T (v i) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    rw [h, Matrix.mulVec_smul, hv T g]

theorem mem_fixedSubmodule (ρ : MatrixRepresentation G n) (v : n → R) :
    v ∈ ρ.fixedSubmodule ↔ ρ.IsFixedVector v :=
  Iff.rfl

end MatrixRepresentation

end FixedVectors

section ClosedSubgroups

variable {S : Scheme.{u}} {H G : GroupScheme S}

/-- A homomorphism `i : H ⟶ G` exhibits `H` as a closed subgroup of `G` when the underlying
morphism of schemes is a closed immersion. -/
def IsClosedSubgroup (i : H ⟶ G) : Prop :=
  IsClosedImmersion i.hom.hom.left

end ClosedSubgroups

section Field

variable {k : Type u} [Field k]

/-- A group scheme `G` over a field `k` is unipotent if every nonzero finite-dimensional
representation of `G` has a nonzero fixed vector. -/
def IsUnipotent (G : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] [Nonempty n] (ρ : MatrixRepresentation G n),
    ∃ v : n → k, v ≠ 0 ∧ ρ.IsFixedVector v

/-- The `k`-unipotent radical of `G` is trivial: every smooth connected unipotent normal closed
subgroup of `G` (over `k` itself) is trivial. -/
def HasTrivialUnipotentRadical (G : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G), IsClosedSubgroup i →
    Smooth H.X.hom → ConnectedSpace H.X.left → IsUnipotent H →
    (SubgroupFunctor.range i).IsNormal → SubgroupFunctor.range i = ⊥

/-- A pseudo-reductive group over `k`: a smooth connected affine group scheme over `k` whose
`k`-unipotent radical is trivial. Over an algebraically closed field this is exactly a connected
reductive group. -/
structure IsPseudoReductive (G : GroupScheme (Spec (CommRingCat.of k))) : Prop where
  smooth : Smooth G.X.hom
  isAffineHom : IsAffineHom G.X.hom
  connectedSpace : ConnectedSpace G.X.left
  hasTrivialUnipotentRadical : HasTrivialUnipotentRadical G

/-- Base change from `k` to its algebraic closure. -/
abbrev toAlgebraicClosure (k : Type u) [Field k] :
    Spec (CommRingCat.of (AlgebraicClosure k)) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))

/-- A connected reductive group over a field `k`: a smooth connected affine group scheme over `k`
whose geometric unipotent radical, the unipotent radical of the base change to an algebraic
closure of `k`, is trivial. -/
structure IsConnectedReductive (G : GroupScheme (Spec (CommRingCat.of k))) : Prop where
  smooth : Smooth G.X.hom
  isAffineHom : IsAffineHom G.X.hom
  connectedSpace : ConnectedSpace G.X.left
  hasTrivialGeometricUnipotentRadical :
    HasTrivialUnipotentRadical ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G)

end Field

section Base

variable {S : Scheme.{u}}

/-- The geometric point `Spec κ(s)^alg → S` over a point `s` of `S`, through an algebraic closure
of the residue field `κ(s)`. -/
def geometricPoint (S : Scheme.{u}) (s : S) :
    Spec (CommRingCat.of (AlgebraicClosure (S.residueField s))) ⟶ S :=
  toAlgebraicClosure (S.residueField s) ≫ S.fromSpecResidueField s

/-- The geometric fibre `G_{s̄}` of a group scheme `G` over `S` at the geometric point over `s`. -/
abbrev geometricFiber (G : GroupScheme S) (s : S) :
    GroupScheme (Spec (CommRingCat.of (AlgebraicClosure (S.residueField s)))) :=
  (GroupScheme.baseChange (geometricPoint S s)).obj G

/-- A reductive group scheme over `S`: a smooth affine group scheme over `S` whose geometric
fibres are connected reductive groups, that is, smooth connected affine groups over an
algebraically closed field with trivial unipotent radical. -/
structure IsReductive (G : GroupScheme S) : Prop where
  smooth : Smooth G.X.hom
  isAffineHom : IsAffineHom G.X.hom
  geometricFiber : ∀ s : S, IsPseudoReductive (geometricFiber G s)

end Base

end Langlands.GroupScheme
