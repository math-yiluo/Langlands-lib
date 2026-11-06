import Langlands.GroupScheme.Lie.RootOrbitLineCoordinates

/-! # Fixed-field coordinates on invariant actual root-orbit tuples -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u v w

namespace Langlands.LinearAlgebra.OrbitLines

open Langlands.Algebra.FiniteGaloisOrbits

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
    {I : Type v} [MulAction (L ≃ₐ[k] L) I]
    {V : Type w} [AddCommGroup V] [Module L V]
    [DistribMulAction (L ≃ₐ[k] L) V]
    (i : I) (W : I → Submodule L V)

/-- Dependent tuples of vectors in orbit lines that respect the ambient action. -/
def invariantSections : AddSubgroup (Π j : MulAction.orbit (L ≃ₐ[k] L) i, W j.val) where
  carrier := {f | ∀ (σ : L ≃ₐ[k] L) j,
    σ • (f j : V) = (f (σ • j) : V)}
  zero_mem' := by intro σ j; exact smul_zero σ
  add_mem' := by
    intro f g hf hg σ j
    change σ • ((f j : V) + (g j : V)) = (f (σ • j) : V) + (g (σ • j) : V)
    rw [smul_add, hf, hg]
  neg_mem' := by
    intro f hf σ j
    change σ • (-(f j : V)) = -(f (σ • j) : V)
    rw [smul_neg, hf]

@[simp] theorem mem_invariantSections
    (f : Π j : MulAction.orbit (L ≃ₐ[k] L) i, W j.val) :
    f ∈ invariantSections (k := k) (L := L) (V := V) i W ↔
      ∀ (σ : L ≃ₐ[k] L) j, σ • (f j : V) = (f (σ • j) : V) := Iff.rfl

variable (e : ∀ j : MulAction.orbit (L ≃ₐ[k] L) i, L ≃ₗ[L] W j.val)
    (he : ∀ (σ : L ≃ₐ[k] L) j x,
      σ • (e j x : V) = (e (σ • j) (σ x) : V))

/-- Coherent line coordinates identify invariant vector tuples with
semilinear-equivariant scalar functions. -/
def sectionCoordinateEquiv :
    invariantSections (k := k) (L := L) (V := V) i W ≃+ orbitCoordinateAlgebra k L i where
  toFun f := ⟨fun j => (e j).symm (f.val j), by
    intro σ j
    apply (e (σ • j)).injective
    apply Subtype.ext
    rw [LinearEquiv.apply_symm_apply]
    have h := he σ j ((e j).symm (f.val j))
    rw [LinearEquiv.apply_symm_apply] at h
    exact (f.property σ j).symm.trans h⟩
  invFun f := ⟨fun j => e j (f.val j), by
    intro σ j
    change σ • (e j (f.val j) : V) = (e (σ • j) (f.val (σ • j)) : V)
    rw [he, f.property σ j]⟩
  left_inv f := by
    apply Subtype.ext
    funext j
    exact (e j).apply_symm_apply (f.val j)
  right_inv f := by
    apply Subtype.ext
    funext j
    exact (e j).symm_apply_apply (f.val j)
  map_add' f g := by
    apply Subtype.ext
    funext j
    exact (e j).symm.map_add (f.val j) (g.val j)

@[simp] theorem sectionCoordinateEquiv_apply
    (f : invariantSections (k := k) (L := L) (V := V) i W) (j : MulAction.orbit (L ≃ₐ[k] L) i) :
    (sectionCoordinateEquiv (k := k) (L := L) (V := V) i W e he f).val j = (e j).symm (f.val j) := rfl

@[simp] theorem sectionCoordinateEquiv_symm_apply
    (f : orbitCoordinateAlgebra k L i) (j : MulAction.orbit (L ≃ₐ[k] L) i) :
    ((sectionCoordinateEquiv (k := k) (L := L) (V := V) i W e he).symm f).val j = e j (f.val j) := rfl

variable [FiniteDimensional k L] [IsGalois k L]

/-- The stabilizer fixed field gives exactly the invariant orbit-line tuples. -/
def fixedFieldSectionEquiv :
    stabilizerField k L i ≃+ invariantSections (k := k) (L := L) (V := V) i W :=
  (orbitEvaluationEquiv k L i).symm.toAddEquiv.trans
    (sectionCoordinateEquiv (k := k) (L := L) (V := V) i W e he).symm

@[simp] theorem fixedFieldSectionEquiv_apply
    (x : stabilizerField k L i) (j : MulAction.orbit (L ≃ₐ[k] L) i) :
    (fixedFieldSectionEquiv (k := k) (L := L) (V := V) i W e he x).val j =
      e j (orbitEmbeddingEquiv k L i j x) := rfl

end Langlands.LinearAlgebra.OrbitLines

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (j : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k L
local notation "j_L" => CategoryTheory.Functor.map (GroupScheme.baseChange b) j
local notation "T_L" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_L" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G

local instance : IsAffineHom (G_L).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

attribute [local instance] rootsGaloisAction Lie.baseChangeGaloisAction

/-- Actual Lie-root tuples fixed by canonical transport along a Galois orbit. -/
def rootOrbitInvariantSections
    (β : roots
      (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
      (G := (GroupScheme.baseChange (algebraBaseMap k L)).obj G)
      ((GroupScheme.baseChange (algebraBaseMap k L)).map j)) :
    AddSubgroup (Π γ : MulAction.orbit (L ≃ₐ[k] L) β,
      weightSpace (T := T_L) j_L γ.val.val) :=
  Langlands.LinearAlgebra.OrbitLines.invariantSections
    (k := k) (L := L) (V := Additive (lieKernel G_L L)) β
    (fun δ => weightSpace (T := T_L) j_L δ.val)

variable [FiniteDimensional k L] [IsGalois k L]

/-- For actual split maximal-torus roots, a finite separable stabilizer field
parametrizes all invariant Lie-root tuples, with no supplied coordinates. -/
def rootOrbitFieldSectionEquiv
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j)
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp)
    (β : roots
      (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
      (G := (GroupScheme.baseChange (algebraBaseMap k L)).obj G)
      ((GroupScheme.baseChange (algebraBaseMap k L)).map j)) :
    rootOrbitField k L j β ≃+ rootOrbitInvariantSections k L j β :=
  Langlands.LinearAlgebra.OrbitLines.fixedFieldSectionEquiv
    (k := k) (L := L) (V := Additive (lieKernel G_L L)) β
    (fun δ => weightSpace (T := T_L) j_L δ.val)
    (rootOrbitLineEquiv k L j hG hj hT β)
    (fun σ γ x => rootOrbitLineEquiv_galois k L j hG hj hT β σ γ x)

/-- The field parameter is evaluated by the embedding corresponding to the
root, then inserted into the same coherent root-line coordinate. -/
@[simp] theorem rootOrbitFieldSectionEquiv_apply
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j)
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp)
    (β : roots
      (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
      (G := (GroupScheme.baseChange (algebraBaseMap k L)).obj G)
      ((GroupScheme.baseChange (algebraBaseMap k L)).map j))
    (x : rootOrbitField k L j β)
    (γ : MulAction.orbit (L ≃ₐ[k] L) β) :
    (rootOrbitFieldSectionEquiv k L j hG hj hT β x).val γ =
      rootOrbitLineEquiv k L j hG hj hT β γ (rootOrbitEmbeddingEquiv k L j β γ x) := rfl

end Langlands.GroupScheme
