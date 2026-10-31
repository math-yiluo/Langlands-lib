import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.Abelian

/-! # Stalk support and finite closed support of scheme modules

For a scheme `X` and an `𝒪_X`-module `M : X.Modules`, `stalkSupport M` is the set of points
at which the stalk of `M` is nonzero (Stacks Project, Tag 01AT). The stalk used is the stalk of
the underlying presheaf of abelian groups `M.presheaf`, computed by Mathlib's
`TopCat.Presheaf.stalkFunctor AddCommGrpCat x`. `HasFiniteClosedSupport M` says that this set is
finite and consists of closed points.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.AlgebraicGeometry.Modules

open _root_.AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The support of an `𝒪_X`-module `M`: the points `x` at which the stalk of the underlying
abelian presheaf `M.presheaf` is not a zero object. -/
def stalkSupport (M : X.Modules) : Set X :=
  {x | ¬ IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj M.presheaf)}

/-- An `𝒪_X`-module has finite closed support if its stalk support is a finite set and each of
its points is closed in `X`. -/
def HasFiniteClosedSupport (M : X.Modules) : Prop :=
  (stalkSupport M).Finite ∧ ∀ x ∈ stalkSupport M, IsClosed ({x} : Set X)

variable {M N : X.Modules}

/-- Membership in the stalk support is nonvanishing of the abelian stalk. -/
theorem mem_stalkSupport {x : X} :
    x ∈ stalkSupport M ↔
      ¬ IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj M.presheaf) :=
  Iff.rfl

/-- Membership in the stalk support means that the abelian stalk has a nonzero element. -/
theorem mem_stalkSupport_iff_nontrivial {x : X} :
    x ∈ stalkSupport M ↔ Nontrivial (M.presheaf.stalk x) := by
  rw [mem_stalkSupport, AddCommGrpCat.isZero_iff_subsingleton, not_subsingleton_iff_nontrivial]
  rfl

/-- Isomorphic `𝒪_X`-modules have the same stalk support. -/
theorem stalkSupport_eq_of_iso (e : M ≅ N) : stalkSupport M = stalkSupport N := by
  ext x
  exact not_congr
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso
      ((Scheme.Modules.toPresheaf X).mapIso e)).isZero_iff

/-- An `𝒪_X`-module is zero if and only if all its abelian stalks are zero. -/
theorem isZero_iff_forall_isZero_stalk :
    IsZero M ↔ ∀ x : X, IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
      M.presheaf) := by
  let F : X.Modules ⥤ TopCat.Sheaf AddCommGrpCat.{u} X := SheafOfModules.toSheaf X.ringCatSheaf
  have : F.Faithful := inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).Faithful
  have : F.PreservesZeroMorphisms :=
    inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).PreservesZeroMorphisms
  have h : IsZero M ↔ IsZero (F.obj M) := by
    refine ⟨F.map_isZero, fun h => ?_⟩
    rw [IsZero.iff_id_eq_zero] at h ⊢
    exact F.zero_of_map_zero _ (by rw [F.map_id]; exact h)
  rw [h]
  exact TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero (F.obj M)

/-- The stalk support is empty if and only if the module is zero. -/
theorem stalkSupport_eq_empty_iff : stalkSupport M = ∅ ↔ IsZero M := by
  rw [isZero_iff_forall_isZero_stalk, Set.eq_empty_iff_forall_notMem]
  simp only [mem_stalkSupport, not_not]

/-- Finite closed support is equivalent to containment of the support in a finite set of
closed points. -/
theorem hasFiniteClosedSupport_iff_exists_subset :
    HasFiniteClosedSupport M ↔
      ∃ S : Set X, S.Finite ∧ (∀ x ∈ S, IsClosed ({x} : Set X)) ∧ stalkSupport M ⊆ S :=
  ⟨fun h => ⟨stalkSupport M, h.1, h.2, subset_rfl⟩,
    fun ⟨_, hS, hcl, hsub⟩ => ⟨hS.subset hsub, fun x hx => hcl x (hsub hx)⟩⟩

/-- If the stalk support is contained in a finite set of closed points, the module has finite
closed support. -/
theorem HasFiniteClosedSupport.of_subset {S : Set X} (hS : S.Finite)
    (hcl : ∀ x ∈ S, IsClosed ({x} : Set X)) (hsub : stalkSupport M ⊆ S) :
    HasFiniteClosedSupport M :=
  hasFiniteClosedSupport_iff_exists_subset.2 ⟨S, hS, hcl, hsub⟩

/-- Finite closed support is invariant under isomorphism of `𝒪_X`-modules. -/
theorem hasFiniteClosedSupport_iff_of_iso (e : M ≅ N) :
    HasFiniteClosedSupport M ↔ HasFiniteClosedSupport N := by
  rw [HasFiniteClosedSupport, HasFiniteClosedSupport, stalkSupport_eq_of_iso e]

/-- A zero module has finite closed support. -/
theorem HasFiniteClosedSupport.of_isZero (h : IsZero M) : HasFiniteClosedSupport M := by
  rw [HasFiniteClosedSupport, stalkSupport_eq_empty_iff.2 h]
  exact ⟨Set.finite_empty, fun _ hx => hx.elim⟩

end Langlands.AlgebraicGeometry.Modules
