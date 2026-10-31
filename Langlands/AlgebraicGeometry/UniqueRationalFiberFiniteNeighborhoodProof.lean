import Langlands.AlgebraicGeometry.UniqueRationalFiberFiniteNeighborhoodStatement

/-!
# A unique rational fiber of a proper map has a finite neighborhood

Closed points of a scheme locally of finite type over an algebraically closed field `K` are
exactly the images of rational points. A closed point of the closed fiber over `f z` therefore
comes from a rational point in the same rational fiber as `x`, so it equals `z`. Closed points
are dense in every closed subset of the Jacobson space `X`, hence the whole fiber is `{z}`.
Zariski's main theorem in the form of
`exists_isFinite_morphismRestrict_of_finite_preimage_singleton` then gives a target
neighborhood over which `f` is finite.
-/

universe u

open CategoryTheory AlgebraicGeometry Topology

namespace Langlands.AlgebraicGeometry

/-- A unique rational fiber of a proper morphism between schemes locally of finite type over
an algebraically closed field is a topological singleton, and the morphism is finite over a
neighborhood of its image. -/
theorem uniqueRationalFiber_finiteNeighborhood :
    UniqueRationalFiberFiniteNeighborhoodStatement.{u} := by
  intro K _ _ X Y p q _ _ f _ hfq x hx huniq
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  -- `x ≫ f` is a rational point of `Y`.
  have hxf : (x ≫ f) ≫ q = 𝟙 _ := by rw [Category.assoc, hfq]; exact hx
  have hz : IsClosed {x (IsLocalRing.closedPoint K)} :=
    ((pointEquivClosedPoint p) ⟨x, hx⟩).2
  have hy : IsClosed {f (x (IsLocalRing.closedPoint K))} := by
    have : IsClosed {(x ≫ f) (IsLocalRing.closedPoint K)} :=
      ((pointEquivClosedPoint q) ⟨x ≫ f, hxf⟩).2
    exact this
  have hF : f ⁻¹' {f (x (IsLocalRing.closedPoint K))} = {x (IsLocalRing.closedPoint K)} := by
    refine Set.Subset.antisymm ?_ (by simp)
    rw [← closure_inter_closedPoints (hy.preimage f.continuous)]
    refine closure_minimal ?_ hz
    rintro z' ⟨hz'f, hz'⟩
    replace hz' : IsClosed {z'} := hz'
    -- The closed point `z'` of the fiber comes from a rational point `x'` of `X`.
    have hx' : pointOfClosedPoint p z' hz' ≫ p = 𝟙 _ := pointOfClosedPoint_comp p z' hz'
    have hx'f : (pointOfClosedPoint p z' hz' ≫ f) ≫ q = 𝟙 _ := by
      rw [Category.assoc, hfq]; exact hx'
    have heq : pointOfClosedPoint p z' hz' ≫ f = x ≫ f :=
      ext_of_apply_closedPoint_eq q hx'f hxf (by
        show f (pointOfClosedPoint p z' hz' (IsLocalRing.closedPoint K)) =
          f (x (IsLocalRing.closedPoint K))
        rw [pointOfClosedPoint_apply p z' hz' (IsLocalRing.closedPoint K)]
        exact hz'f)
    have hxx := huniq _ hx' heq
    rw [Set.mem_singleton_iff, ← hxx]
    exact (pointOfClosedPoint_apply p z' hz' _).symm
  refine ⟨hF, exists_isFinite_morphismRestrict_of_finite_preimage_singleton f _ ?_⟩
  rw [hF]
  exact Set.finite_singleton _

end Langlands.AlgebraicGeometry
