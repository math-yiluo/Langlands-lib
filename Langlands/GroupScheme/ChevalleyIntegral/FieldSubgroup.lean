import Langlands.GroupScheme.SplitExistence.Centralizer

/-! # Minimality of the field Chevalley group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitExistence.ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum J X Y} {b : P.Base} (D : ChevalleyData P b)
  {k : Type u} [Field k]
  {M : GroupScheme (Spec (CommRingCat.of k))} (i : M ⟶ D.GLk k)

/-- A subgroup functor containing the torus and root maps contains all abstract
Chevalley matrices on every test scheme. -/
theorem chevPoints_le_range
    (ht : SubgroupFunctor.range (D.torusToGL k) ≤ SubgroupFunctor.range i)
    (hr : ∀ j, SubgroupFunctor.range (D.rootToGL k j) ≤ SubgroupFunctor.range i)
    (T : Over (Spec (CommRingCat.of k))) :
    D.chevPoints k T ≤ (SubgroupFunctor.range i).carrier T := by
  let e := GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of k) T
  let S := ((SubgroupFunctor.range i).carrier T).map e.toMonoidHom
  have htor (χ : Multiplicative X →* Γ(T.left, ⊤)ˣ) : D.torusHom χ ∈ S := by
    let y := (torusPointsEquiv k T).symm χ
    have hy : y ≫ (D.torusToGL k).hom.hom ∈ (SubgroupFunctor.range i).carrier T :=
      ht T (SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩)
    refine ⟨_, hy, ?_⟩
    exact (D.pointsEquiv_torusToGL k T y).trans
      (congrArg D.torusHom ((torusPointsEquiv k T).apply_symm_apply χ))
  have hroot (j : J) (s : Γ(T.left, ⊤)) : D.x j s ∈ S := by
    let y := (VectorGroup.coordinates (CommRingCat.of k) 1 T).symm
      (Multiplicative.ofAdd fun _ => s)
    have hy : y ≫ (D.rootToGL k j).hom.hom ∈ (SubgroupFunctor.range i).carrier T :=
      hr j T (SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩)
    refine ⟨_, hy, ?_⟩
    change GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of k) T
      (y ≫ (D.rootToGL k j).hom.hom) = D.x j s
    rw [D.pointsEquiv_rootToGL]
    congr 1
    simp only [gaCoord, y, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
      Function.comp_apply, MulEquiv.apply_symm_apply]
    rfl
  have hgen : D.chevSub Γ(T.left, ⊤) ≤ S := by
    refine sup_le ?_ ?_
    · rintro _ ⟨χ, rfl⟩
      exact htor χ
    · refine (Subgroup.closure_le _).2 ?_
      intro g hg
      obtain ⟨j, -, hj⟩ := Set.mem_iUnion₂.1 hg
      obtain ⟨s, rfl⟩ := mem_rootSub.1 hj
      exact hroot j s
  intro x hx
  obtain ⟨y, hy, he⟩ := hgen hx
  exact e.injective he ▸ hy

namespace ChevGroup

variable {D} (H : D.ChevGroup k)

/-- A field Chevalley group is contained scheme-theoretically in every closed
matrix subgroup containing its torus and root maps. -/
theorem range_le_of_generators (hi : IsClosedSubgroup i)
    (ht : SubgroupFunctor.range (D.torusToGL k) ≤ SubgroupFunctor.range i)
    (hr : ∀ j, SubgroupFunctor.range (D.rootToGL k j) ≤ SubgroupFunctor.range i) :
    SubgroupFunctor.range H.i ≤ SubgroupFunctor.range i := by
  have := H.smooth
  have : IsReduced H.H.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k _ H.H.X.hom
  apply range_le_of_extPoints (AlgebraicClosure k) hi
  intro x
  exact SubgroupFunctor.mem_range.mp
    (D.chevPoints_le_range i ht hr _ (H.points (AlgebraicClosure k) x))

/-- The actual homomorphism into a closed matrix subgroup containing all the
Chevalley generators. -/
def factorOfGenerators (hi : IsClosedSubgroup i)
    (ht : SubgroupFunctor.range (D.torusToGL k) ≤ SubgroupFunctor.range i)
    (hr : ∀ j, SubgroupFunctor.range (D.rootToGL k j) ≤ SubgroupFunctor.range i) :
    H.H ⟶ M := by
  have : IsClosedImmersion i.hom.hom.left := hi
  exact (show (SubgroupFunctor.range i).IsRepresentedBy i from
    ⟨Over.mono_of_mono_left _, rfl⟩).factorHom H.i
      (H.range_le_of_generators i hi ht hr)

@[reassoc (attr := simp)]
theorem factorOfGenerators_comp (hi : IsClosedSubgroup i)
    (ht : SubgroupFunctor.range (D.torusToGL k) ≤ SubgroupFunctor.range i)
    (hr : ∀ j, SubgroupFunctor.range (D.rootToGL k j) ≤ SubgroupFunctor.range i) :
    H.factorOfGenerators i hi ht hr ≫ i = H.i := by
  have : IsClosedImmersion i.hom.hom.left := hi
  exact SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

/-- The factor is itself a closed immersion, even when the receiving subgroup
has not been shown smooth or reduced. -/
theorem factorOfGenerators_closed (hi : IsClosedSubgroup i)
    (ht : SubgroupFunctor.range (D.torusToGL k) ≤ SubgroupFunctor.range i)
    (hr : ∀ j, SubgroupFunctor.range (D.rootToGL k j) ≤ SubgroupFunctor.range i) :
    IsClosedSubgroup (H.factorOfGenerators i hi ht hr) := by
  apply IsClosedSubgroup.of_comp hi
  rw [factorOfGenerators_comp]
  exact H.closed

end ChevGroup

end Langlands.GroupScheme.SplitExistence.ChevalleyData
