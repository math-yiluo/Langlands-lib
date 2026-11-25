/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSplitEtaleHypercover
public import WeilConjectures.AlgebraicGeometry.EtaleHypercover
import WeilConjectures.AlgebraicGeometry.FiniteSplitReplacementStageZero
import WeilConjectures.AlgebraicGeometry.FiniteSplitReplacementStageExtension
import WeilConjectures.AlgebraicGeometry.FiniteSplitReplacementStageAssembly

/-! Intermediate construction for finite split hypercover refinement. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

/-- Source: Stacks Project, Hypercoverings, Tags 0DAV, 094K, 01GS.

Proof: Inductively construct a split V and a map to K in every degree. In degree zero
refine the cover K_0 to X by finitely many affine pieces. Suppose V and its map have
been constructed below n. Finite limits of qcqs etale X-schemes are qcqs etale, so
M_n(V) is qcqs, and the matching limits are universal among all schemes over X.
The relative target is M_n(V) times_{M_n(K)} K_n. Its projection to M_n(V) is a base
change of the surjective etale matching arrow of K. Cover M_n(V) by finitely many
affine opens and refine this relative cover over each by affine opens of its members.
Their images are open and cover a quasi-compact space, so finitely many suffice. These
pieces are qcqs and of finite presentation over X with quasi-compact, quasi-separated
structure maps. No quasi-compactness of K_n is needed.
Let N_n be their finite disjoint union. Adjoin to N_n the prescribed copies of earlier
nondegenerate summands indexed by surjections [n] to [m], m < n. On N_n the map to the
relative target supplies both matching faces in V and the map to K_n; on a degenerate
copy the latter is the old map followed by the corresponding degeneracy of K. The
pullback equation gives compatibility of all proper faces with the map to K. Define
simplicial operators by factoring composites as a surjection followed by an injection.
Uniqueness of this factorization and the matching face equations give the simplicial
identities and naturality of V to K. The canonical degeneracy cofans are coproduct
cofans, giving the required splitting. N_n covers the entire matching object, so V's
matching arrow is surjective. Repeat without a degree bound; dependent choice gives
compatible skeletons in all degrees and hence the stated full refinement.
(auxiliary; not a blueprint node) -/
theorem exists_finite_split_replacement
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (K : SimplicialObject X.Etale) (hK : IsEtaleHypercover K) :
    ∃ V : FiniteSplitEtaleHypercover X, Nonempty (V.simplicial ⟶ K) := by
  classical
  obtain ⟨A₀⟩ := exists_replacement_stage_zero K hK
  have hstep (n : ℕ) (A : FiniteSplitReplacementStage K n) :=
    exists_replacement_stage_extension K hK n A
  choose next hnext using hstep
  let A : ∀ n, FiniteSplitReplacementStage K n :=
    Nat.rec A₀ (fun n B ↦ next n B)
  exact exists_replacement_of_stage_tower K A (fun n ↦ hnext n (A n))

end AlgebraicGeometry.FiniteSplitEtaleHypercover
