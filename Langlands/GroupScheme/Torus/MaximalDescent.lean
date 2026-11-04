import Langlands.GroupScheme.Descent.ClosedSubgroups
import Langlands.GroupScheme.Torus.MaximalAmbient
import Langlands.GroupScheme.Torus.MaximalBaseChangeReflection

/-! # Descent of overlap-invariant tori and maximal tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open Descent

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
variable {T : CommGroupScheme (Spec (CommRingCat.of K))}
variable {i : T.toGrp ⟶ (GroupScheme.baseChange
  (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G}

/-- An actual closed torus over the original field, together with recovery of
the prescribed field-extension inclusion. -/
structure TorusDescent (i : T.toGrp ⟶ (GroupScheme.baseChange
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G) where
  torus : CommGroupScheme (Spec (CommRingCat.of k))
  inclusion : torus.toGrp ⟶ G
  recovery : (GroupScheme.baseChange
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj torus.toGrp ≅ T.toGrp
  isTorus : IsTorus torus.toGrp
  isClosedSubgroup : IsClosedSubgroup inclusion
  comparison : (GroupScheme.baseChange
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map inclusion = recovery.hom ≫ i

/-- An overlap-invariant closed torus in a field-extension pullback descends to an
actual closed torus with an isomorphism recovering its given inclusion. -/
theorem IsTorus.exists_descent_of_overlap_range_eq
    (hT : IsTorus T.toGrp) (hi : IsClosedSubgroup i)
    (h : SubgroupFunctor.range
        ((GroupScheme.baseChange
          (fst (Spec.map (CommRingCat.ofHom (algebraMap k K))))).map i ≫
          (canonicalOverlap (Spec.map (CommRingCat.ofHom (algebraMap k K))) G).hom) =
      SubgroupFunctor.range ((GroupScheme.baseChange
        (snd (Spec.map (CommRingCat.ofHom (algebraMap k K))))).map i)) :
    ∃ (T₀ : CommGroupScheme (Spec (CommRingCat.of k))) (j : T₀.toGrp ⟶ G)
      (e : (GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T₀.toGrp ≅ T.toGrp),
      IsTorus T₀.toGrp ∧ IsClosedSubgroup j ∧
        (GroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map j = e.hom ≫ i := by
  let p := Spec.map (CommRingCat.ofHom (algebraMap k K))
  obtain ⟨hsurj, hflat, _⟩ := fieldExtension_fpqc k K
  let : Surjective p := hsurj
  let : Flat p := hflat
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨H₀, j, e, _, hj, he⟩ := hi.exists_descent_of_overlap_range_eq p h
  have hH : IsTorus H₀ := IsTorus.of_baseChange (IsTorus.of_iso e hT)
  let T₀ : CommGroupScheme (Spec (CommRingCat.of k)) :=
    { H₀ with comm := hH.isCommMonObj }
  exact ⟨T₀, j, e, hH, hj, he⟩

/-- Choose the actual descended torus and its recovery data from overlap
invariance. -/
def IsTorus.descentOfOverlapRangeEq
    (hT : IsTorus T.toGrp) (hi : IsClosedSubgroup i)
    (h : SubgroupFunctor.range
        ((GroupScheme.baseChange
          (fst (Spec.map (CommRingCat.ofHom (algebraMap k K))))).map i ≫
          (canonicalOverlap (Spec.map (CommRingCat.ofHom (algebraMap k K))) G).hom) =
      SubgroupFunctor.range ((GroupScheme.baseChange
        (snd (Spec.map (CommRingCat.ofHom (algebraMap k K))))).map i)) :
    TorusDescent i :=
  Classical.choice <| by
    obtain ⟨T₀, j, e, hT₀, hj, he⟩ := hT.exists_descent_of_overlap_range_eq hi h
    exact ⟨⟨T₀, j, e, hT₀, hj, he⟩⟩

omit [IsAffineHom G.X.hom] in
/-- The recovery equation preserves maximality of the specified input torus
on the actual pullback of any descended datum. -/
theorem TorusDescent.isMaximalTorus_baseChange (D : TorusDescent i)
    (hi : IsMaximalTorus i) :
    IsMaximalTorus (T := (CommGroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj D.torus)
      ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map D.inclusion) := by
  rw [D.comparison]
  exact hi.iso_comp (T' := (CommGroupScheme.baseChange
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj D.torus) D.recovery

omit [IsAffineHom G.X.hom] in
/-- Maximality over the original field follows by the independent
field-extension reflection theorem. -/
theorem TorusDescent.isMaximalTorus (D : TorusDescent i) (hi : IsMaximalTorus i) :
    IsMaximalTorus D.inclusion :=
  IsMaximalTorus.of_baseChange D.isClosedSubgroup (D.isMaximalTorus_baseChange hi)

/-- An overlap-invariant geometric maximal torus descends to a maximal torus
whose actual field-extension pullback is still maximal. -/
theorem IsMaximalTorus.exists_descent_of_overlap_range_eq
    (hi : IsMaximalTorus i)
    (h : SubgroupFunctor.range
        ((GroupScheme.baseChange
          (fst (Spec.map (CommRingCat.ofHom (algebraMap k K))))).map i ≫
          (canonicalOverlap (Spec.map (CommRingCat.ofHom (algebraMap k K))) G).hom) =
      SubgroupFunctor.range ((GroupScheme.baseChange
        (snd (Spec.map (CommRingCat.ofHom (algebraMap k K))))).map i)) :
    ∃ (T₀ : CommGroupScheme (Spec (CommRingCat.of k))) (j : T₀.toGrp ⟶ G)
      (e : (GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T₀.toGrp ≅ T.toGrp),
      IsMaximalTorus j ∧
        IsMaximalTorus (T := (CommGroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T₀)
          ((GroupScheme.baseChange
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map j) ∧
        (GroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map j = e.hom ≫ i := by
  obtain ⟨T₀, j, e, _, hj, he⟩ := hi.1.exists_descent_of_overlap_range_eq hi.2.1 h
  have hmax : IsMaximalTorus (T := (CommGroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T₀)
      ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map j) := by
    rw [he]
    exact hi.iso_comp (T' := (CommGroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T₀) e
  exact ⟨T₀, j, e, IsMaximalTorus.of_baseChange hj hmax, hmax, he⟩

end Langlands.GroupScheme
