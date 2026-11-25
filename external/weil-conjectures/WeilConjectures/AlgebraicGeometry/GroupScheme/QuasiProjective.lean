/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.GroupScheme.AmpleFamily
public import WeilConjectures.AlgebraicGeometry.GroupScheme.AmpleFamilySmooth
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Reduced
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Separated
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfAmple
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.QuasiProjective

/-!
# Group schemes of finite type over a field are quasi-projective

A group scheme of finite type over a field `k` is quasi-projective over `k` (Stacks 0BF7).
Over a field, quasi-projectivity amounts to an immersion into a projective space `ℙ(α; Spec k)`
with finitely many homogeneous coordinates, and this is the form in which it is stated here.

Following Stacks 0BF7, the statement is reduced to the case of an algebraically closed field:
the base change of `G` to an algebraic closure `K` of `k` is again a group scheme of finite type,
and quasi-projectivity descends from `K` to `k`
(`AlgebraicGeometry.exists_isImmersion_projectiveSpace_of_pullback`, Stacks 0BDE).

## Main statements

- `AlgebraicGeometry.GrpObj.exists_isImmersion_projectiveSpace_of_isAlgClosed`: the case of an
  algebraically closed field.
- `AlgebraicGeometry.GrpObj.exists_isImmersion_projectiveSpace`: a group scheme of finite type
  over a field admits an immersion into a projective space over the field.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- The identity component of a group scheme of finite type over a field is quasi-compact over
the field: it is a connected component, hence closed in the quasi-compact scheme `G`. -/
instance GrpObj.quasiCompact_identityComponent_hom (G : Over (Spec (.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] :
    QuasiCompact (GrpObj.identityComponent G).hom := by
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have hc : IsCompact (GrpObj.identityComponentOpens G : Set G.left) :=
    isClosed_connectedComponent.isCompact
  have : CompactSpace (GrpObj.identityComponent G).left := isCompact_iff_compactSpace.mp hc
  exact quasiCompact_of_compactSpace _

/-- **Group schemes of finite type over an algebraically closed field carry an ample invertible
module.** A group scheme `G` of finite type over an algebraically closed field `k` carries an
invertible module `ℒ` with finitely many global sections `s i` whose non-vanishing loci `G_{s i}`
are affine and cover `G`; that is, `ℒ` is ample in the sense of Stacks 01PS.

This is the geometric core of Stacks 0BF7. One reduces to `G` smooth
(`AlgebraicGeometry.GrpObj.exists_isAffineOpen_compl_support_zeroLocus_of_smooth`: Cartier's
theorem in characteristic zero, `G_red` and Frobenius in characteristic `p`), then to the
identity component (`AlgebraicGeometry.GrpObj.hasAmpleFamily_of_identityComponent`), and treats
the smooth irreducible case with translates of a divisor with affine complement
(`AlgebraicGeometry.GrpObj.hasAmpleFamily_of_smooth_of_irreducibleSpace`). -/
theorem GrpObj.exists_isAffineOpen_compl_support_zeroLocus [IsAlgClosed k]
    (G : Over (Spec (.of k))) [GrpObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] :
    ∃ (L : G.left.Modules) (_ : SheafOfModules.IsInvertible.{u, u, u} L) (ι : Type u)
      (_ : Finite ι) (s : ι → (𝟙_ G.left.Modules ⟶ L)),
      (∀ i, IsAffineOpen (Scheme.Modules.Hom.zeroLocus (s i)).support.compl) ∧
        ⨆ i, (Scheme.Modules.Hom.zeroLocus (s i)).support.compl = ⊤ := by
  refine GrpObj.exists_isAffineOpen_compl_support_zeroLocus_of_smooth (fun H _ _ _ _ ↦ ?_) G
  refine GrpObj.hasAmpleFamily_of_identityComponent H ?_
  have := GrpObj.irreducibleSpace_identityComponent H
  have : LocallyOfFiniteType (GrpObj.identityComponent H).hom :=
    inferInstanceAs (LocallyOfFiniteType ((GrpObj.identityComponentOpens H).ι ≫ H.hom))
  have : Smooth (GrpObj.identityComponent H).hom :=
    inferInstanceAs (Smooth ((GrpObj.identityComponentOpens H).ι ≫ H.hom))
  exact GrpObj.hasAmpleFamily_of_smooth_of_irreducibleSpace (GrpObj.identityComponent H)

/-- **Group schemes of finite type over an algebraically closed field are quasi-projective.**
A group scheme `G` of finite type over an algebraically closed field `k` admits an immersion
`G ⟶ ℙ(α; Spec k)` over `Spec k` into a projective space with finitely many homogeneous
coordinates.

`G` is separated over `k` (`AlgebraicGeometry.GrpObj.isSeparated_hom`, Stacks 047L) and carries
an ample invertible module
(`AlgebraicGeometry.GrpObj.exists_isAffineOpen_compl_support_zeroLocus`), whose sections give the
immersion (`AlgebraicGeometry.exists_isImmersion_projectiveSpace_of_isAffineOpen`). It is the
input of `AlgebraicGeometry.GrpObj.exists_isImmersion_projectiveSpace`, used for blueprint
`lemma-symmetric-ample-sheaf--1` and the subsection `lemma-symmetric-ample-sheaf--1`. -/
theorem GrpObj.exists_isImmersion_projectiveSpace_of_isAlgClosed [IsAlgClosed k]
    (G : Over (Spec (.of k))) [GrpObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] :
    ∃ (α : Type u) (_ : Finite α) (j : G.left ⟶ ℙ(α; Spec (.of k))),
      IsImmersion j ∧ j ≫ ℙ(α; Spec (.of k)) ↘ Spec (.of k) = G.hom := by
  obtain ⟨L, _, ι, _, s, hs, hcov⟩ := GrpObj.exists_isAffineOpen_compl_support_zeroLocus G
  exact exists_isImmersion_projectiveSpace_of_isAffineOpen G.hom L s hs hcov

/-- **Group schemes of finite type over a field are quasi-projective.** A group scheme `G` of
finite type over a field `k` admits an immersion `G ⟶ ℙ(α; Spec k)` over `Spec k` into a
projective space with finitely many homogeneous coordinates.

The base change of `G` to an algebraic closure of `k` is a group scheme of finite type over an
algebraically closed field, hence quasi-projective
(`AlgebraicGeometry.GrpObj.exists_isImmersion_projectiveSpace_of_isAlgClosed`), and
quasi-projectivity descends along field extensions (Stacks 0BDE).

This is the input (Stacks 0BF7) used in the proof of blueprint `lemma-symmetric-ample-sheaf--1`
and of the subsection `lemma-symmetric-ample-sheaf--1`. -/
@[stacks 0BF7]
theorem GrpObj.exists_isImmersion_projectiveSpace (G : Over (Spec (.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] :
    ∃ (α : Type u) (_ : Finite α) (j : G.left ⟶ ℙ(α; Spec (.of k))),
      IsImmersion j ∧ j ≫ ℙ(α; Spec (.of k)) ↘ Spec (.of k) = G.hom := by
  let g : Spec (.of (AlgebraicClosure k)) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  let : GrpObj (Over.mk G.hom) := inferInstanceAs (GrpObj G)
  let : GrpObj (Over.mk (Limits.pullback.snd G.hom g)) := Over.grpObjMkPullbackSnd
  have : LocallyOfFiniteType (Over.mk (Limits.pullback.snd G.hom g)).hom :=
    inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd G.hom g))
  have : QuasiCompact (Over.mk (Limits.pullback.snd G.hom g)).hom :=
    inferInstanceAs (QuasiCompact (Limits.pullback.snd G.hom g))
  obtain ⟨α, _, j, hj, hjG⟩ :=
    exists_isImmersion_projectiveSpace_of_isAlgClosed (Over.mk (Limits.pullback.snd G.hom g))
  exact exists_isImmersion_projectiveSpace_of_pullback G.hom j hjG

end AlgebraicGeometry
