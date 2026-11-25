/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.SplitExists

/-!
# Étale splitting of a finite morphism

Let `f : X ⟶ Y` be a finite morphism and `y : Spec Ω ⟶ Y` a geometric point with `Ω`
algebraically closed. The geometric fibre `f.GeometricFiber y` is the set of `Ω`-points of the
scheme-theoretic fibre `X ×_Y Spec Ω` (`AlgebraicGeometry.Scheme.Hom.geometricFiberEquiv`), and
it is finite.

There is a pointed étale neighbourhood `(U, u)` of `y` over which `U ×_Y X` splits as a disjoint
union of open and closed pieces indexed by the geometric fibre, each finite over `U` and with a
single geometric point over `u` (`AlgebraicGeometry.Scheme.Hom.SplitNbhd.exists_splitting`).
This is the split neighbourhood of `AlgebraicGeometry.Scheme.Hom.SplitNbhd.exists_hom`, together
with the finiteness and the connectedness of the geometric fibres of its pieces.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {Ω : Type u} [Field Ω] (y : Spec (.of Ω) ⟶ Y)

/-- the geometric fibre of `f` over `y`, the set of
geometric points `x: Spec Ω ⟶ X` with `x ≫ f = y` (`AlgebraicGeometry.Scheme.Hom.GeometricFiber`),
is the set of `Ω`-points of the scheme-theoretic fibre `X ×_Y Spec Ω` over `Spec Ω`. When `f` is
finite it is finite (`AlgebraicGeometry.Scheme.Hom.GeometricFiber.finite`). -/
noncomputable def geometricFiberEquiv :
    f.GeometricFiber y ≃ (pullback.snd f y).GeometricFiber (𝟙 _) :=
  (Equiv.subtypeEquivRight fun _ ↦ by rw [Category.id_comp]).trans
    (GeometricFiber.pullbackEquiv f y (𝟙 _)).symm

namespace SplitNbhd

variable {f y}

/-- The pieces of a split neighbourhood are finite over the neighbourhood: they are open and
closed in `U ×_Y X`, which is finite over `U`. -/
instance isFinite_pieceIncl_fst [IsSepClosed Ω] [IsFinite f] (s : SplitNbhd f y)
    (t : GeometricFiber f y) :
    IsFinite ((s.piece t).ι ≫ pullback.fst s.obj.1.hom f) := by
  have : IsClosedImmersion (s.piece t).ι :=
    .of_isPreimmersion _ (by simpa using (s.isClopen t).isClosed)
  infer_instance

/-- The only geometric point of the `t`-th piece of a split neighbourhood `(U, u)` lying over `u`
is the point `(u, t)`. -/
lemma eq_basePt_of_comp_eq [IsSepClosed Ω] (s : SplitNbhd f y) (t : GeometricFiber f y)
    (z : Spec (.of Ω) ⟶ s.piece t)
    (hz : z ≫ (s.piece t).ι ≫ pullback.fst s.obj.1.hom f = s.obj.2.left) :
    z ≫ (s.piece t).ι = basePt f s.obj t := by
  set z' := z ≫ (s.piece t).ι
  have hz' : z' ≫ pullback.fst s.obj.1.hom f = s.obj.2.left := by
    simpa [z'] using hz
  let t' : GeometricFiber f y := ⟨z' ≫ pullback.snd s.obj.1.hom f, by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hz']
    exact CategoryTheory.Over.w s.obj.2⟩
  have he : basePt f s.obj t' = z' := basePt_eq_of_comp_fst_eq f s.obj z' hz'
  have ht : t' = t := by
    by_contra hne
    have h₁ : basePt f s.obj t' default ∈ s.piece t := by
      rw [he]
      exact (Scheme.Opens.range_ι (s.piece t)).subset ⟨z default, rfl⟩
    exact (s.disjoint t' t hne).le_bot ⟨s.mem t', h₁⟩
  rw [← ht, he]

end SplitNbhd

/-- étale splitting of a finite morphism. For a finite
`f: X ⟶ Y` and a geometric point `y` of `Y` with algebraically closed residue field, there is
a pointed étale neighbourhood `(U, u)` of `y` and a decomposition of `U ×_Y X` into pairwise
disjoint open and closed pieces `X_t` indexed by the (finite) geometric fibre of `f` over `y`
(the structure `AlgebraicGeometry.Scheme.Hom.SplitNbhd`) such that every `X_t ⟶ U` is finite and
the geometric fibre of `X_t` over `u` is a single point, hence connected. -/
theorem SplitNbhd.exists_splitting [IsAlgClosed Ω] [IsFinite f] :
    ∃ s : SplitNbhd f y, ∀ t : GeometricFiber f y,
      IsFinite ((s.piece t).ι ≫ pullback.fst s.obj.1.hom f) ∧
      Nonempty (Unique (GeometricFiber ((s.piece t).ι ≫ pullback.fst s.obj.1.hom f)
        s.obj.2.left)) := by
  obtain ⟨s, -⟩ := SplitNbhd.exists_hom f y (IsCofiltered.nonempty (C := Nbhd y)).some
  refine ⟨s, fun t ↦ ⟨inferInstance, ⟨?_⟩⟩⟩
  let p : GeometricFiber ((s.piece t).ι ≫ pullback.fst s.obj.1.hom f) s.obj.2.left :=
    ⟨(s.piecePt t).left, by rw [piecePt_left_ι_assoc, basePt_fst]⟩
  refine { default := p, uniq := fun z ↦ GeometricFiber.ext ?_ }
  rw [← cancel_mono (s.piece t).ι]
  exact (SplitNbhd.eq_basePt_of_comp_eq s t z.1 z.2).trans (piecePt_left_ι s t).symm

end AlgebraicGeometry.Scheme.Hom
