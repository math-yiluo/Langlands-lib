import Langlands.Group.GL.Blocks
import Langlands.Group.GL.Maps
import Mathlib.GroupTheory.DoubleCoset

/-! Actual permutation and intersection data for the GL geometric lemma. -/

namespace Langlands.Geometric

open GeneralLinear

universe u

variable {n : ℕ}

/-- The block containing a standard coordinate. -/
def blockIndex (B : BlockShape n) (a : Fin n) : Fin B.length :=
  (B.indexEquiv.symm a).1

@[simp] theorem blockIndex_index (B : BlockShape n) (i : Fin B.length)
    (a : Fin (B.size i)) : blockIndex B (B.index i a) = i := by
  exact congrArg Sigma.fst (B.indexEquiv.symm_apply_apply ⟨i, a⟩)

/-- The actual Weyl subgroup of a standard Levi: permutations preserving blocks. -/
def blockWeyl (B : BlockShape n) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {w | ∀ a, blockIndex B (w a) = blockIndex B a}
  one_mem' _ := rfl
  mul_mem' := by
    intro w v hw hv a
    exact (hw (v a)).trans (hv a)
  inv_mem' := by
    intro w hw a
    have h := (hw (w⁻¹ a)).symm
    simpa only [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply] using h

/-- The positive-root condition on an actual permutation, in consecutive blocks.
The first clause preserves the order in every source block and the second
preserves the order in every target block under the inverse permutation. -/
def IsMinimalRepresentative (B C : BlockShape n) (w : Equiv.Perm (Fin n)) : Prop :=
  (∀ i, StrictMono (fun a : Fin (B.size i) => w (B.index i a))) ∧
    (∀ j, StrictMono (fun a : Fin (C.size j) => w.symm (C.index j a)))

/-- The finite set `W^{M,N}` as an actual subtype of the symmetric group. -/
abbrev MinimalRepresentatives (B C : BlockShape n) :=
  {w : Equiv.Perm (Fin n) // IsMinimalRepresentative B C w}

instance (B C : BlockShape n) : Finite (MinimalRepresentatives B C) :=
  inferInstanceAs (Finite {w : Equiv.Perm (Fin n) // IsMinimalRepresentative B C w})

/-- The Weyl double-coset map has target `W_C \ W / W_B`. -/
def weylDoubleCoset (B C : BlockShape n) (w : MinimalRepresentatives B C) :
    DoubleCoset.Quotient (blockWeyl C : Set (Equiv.Perm (Fin n)))
      (blockWeyl B : Set (Equiv.Perm (Fin n))) :=
  DoubleCoset.mk (blockWeyl C) (blockWeyl B) w.val

variable (R : Type u) [CommRing R]

/-- The actual matrix double coset corresponding to BZ's representative `P w⁻¹`. -/
def parabolicDoubleCoset (B C : BlockShape n) (w : MinimalRepresentatives B C) :
    DoubleCoset.Quotient (B.parabolic R : Set (GeneralLinear n R))
      (C.parabolic R : Set (GeneralLinear n R)) :=
  DoubleCoset.mk (B.parabolic R) (C.parabolic R) (permutation n R w.val)⁻¹

/-- Conjugation of the source Levi into the ambient matrix group. -/
def conjugatedLeviMap (B : BlockShape n) (w : Equiv.Perm (Fin n)) :
    B.Levi R →* GeneralLinear n R :=
  (MulAut.conj (permutation n R w)).toMonoidHom.comp (B.leviEmbedding R)

/-- The parabolic intersection in the source Levi `M ∩ w⁻¹(Q)`. -/
def sourceParabolic (B C : BlockShape n) (w : Equiv.Perm (Fin n)) :
    Subgroup (B.Levi R) :=
  (C.parabolic R).comap (conjugatedLeviMap R B w)

/-- The Levi intersection in the source Levi `M ∩ w⁻¹(N)`. -/
def sourceLevi (B C : BlockShape n) (w : Equiv.Perm (Fin n)) :
    Subgroup (B.Levi R) :=
  (C.leviSubgroup R).comap (conjugatedLeviMap R B w)

/-- The radical intersection in the source Levi `M ∩ w⁻¹(V)`. -/
def sourceUnipotent (B C : BlockShape n) (w : Equiv.Perm (Fin n)) :
    Subgroup (B.Levi R) :=
  (C.unipotentSubgroup R).comap (conjugatedLeviMap R B w)

/-- An actual ordered refinement in each individual Levi block. -/
abbrev BlockRefinement (B : BlockShape n) :=
  ∀ i : Fin B.length, BlockShape (B.size i)

/-- The standard parabolic of an actual product Levi, given block refinements. -/
def refinedParabolic (B : BlockShape n) (S : BlockRefinement B) :
    Subgroup (B.Levi R) :=
  Subgroup.pi Set.univ (fun i => (S i).parabolic R)

/-- Its actual block diagonal Levi subgroup. -/
def refinedLevi (B : BlockShape n) (S : BlockRefinement B) :
    Subgroup (B.Levi R) :=
  Subgroup.pi Set.univ (fun i => (S i).leviSubgroup R)

/-- Its actual product unipotent radical. -/
def refinedUnipotent (B : BlockShape n) (S : BlockRefinement B) :
    Subgroup (B.Levi R) :=
  Subgroup.pi Set.univ (fun i => (S i).unipotentSubgroup R)

section ConjugateIntersection

variable {G : Type*} [Group G]

/-- The actual ambient intersection `M ∩ w⁻¹(N)`. -/
def intersectionSource (M N : Subgroup G) (w : G) : Subgroup G :=
  M ⊓ N.comap (MulAut.conj w).toMonoidHom

/-- The actual ambient intersection `N ∩ w(M)`. -/
def intersectionTarget (M N : Subgroup G) (w : G) : Subgroup G :=
  N ⊓ M.comap (MulAut.conj w⁻¹).toMonoidHom

/-- Conjugation identifies the two actual intersections, with intrinsic laws proved. -/
def intersectionConjugation (M N : Subgroup G) (w : G) :
    intersectionSource M N w ≃* intersectionTarget M N w where
  toFun g := ⟨MulAut.conj w g.val, g.property.2, by
    change MulAut.conj w⁻¹ (MulAut.conj w g.val) ∈ M
    simpa [MulAut.conj_apply, mul_assoc] using g.property.1⟩
  invFun g := ⟨MulAut.conj w⁻¹ g.val, g.property.2, by
    change MulAut.conj w (MulAut.conj w⁻¹ g.val) ∈ N
    simpa [MulAut.conj_apply, mul_assoc] using g.property.1⟩
  left_inv g := by
    apply Subtype.ext
    simp [MulAut.conj_apply, mul_assoc]
  right_inv g := by
    apply Subtype.ext
    simp [MulAut.conj_apply, mul_assoc]
  map_mul' g h := Subtype.ext ((MulAut.conj w).map_mul g.val h.val)

@[simp]
theorem intersectionConjugation_apply (M N : Subgroup G) (w : G)
    (g : intersectionSource M N w) :
    (intersectionConjugation M N w g : G) = w * g.val * w⁻¹ :=
  rfl

end ConjugateIntersection

end Langlands.Geometric
