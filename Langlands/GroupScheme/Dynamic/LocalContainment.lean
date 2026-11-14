import Langlands.GroupScheme.Dynamic.FiberwiseContainment
import Langlands.GroupScheme.SmoothMonoLocalIso

/-! # Persistence of dynamic containment near a residue fibre -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.Dynamic

/-- If a dynamic parabolic in a smooth affine group with geometrically
connected fibres is the whole group at one residue fibre, it is the whole
group on an open neighbourhood. -/
theorem exists_parabolic_eq_top_near
    {S : Scheme.{u}} {H : GroupScheme S}
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [GeometricallyConnected H.X.hom]
    (χ : (Gm S).toGrp ⟶ H) (s : S)
    (hs : parabolic (baseChangeCocharacter (S.fromSpecResidueField s) χ) = ⊤) :
    ∃ V : S.Opens, s ∈ V ∧ parabolic (baseChangeCocharacter V.ι χ) = ⊤ := by
  obtain ⟨K, κ, hκc, hκL, hκ⟩ :=
    (dynamicBaseRepresentability S H χ).1
  let : IsClosedImmersion κ.hom.hom.left := hκc
  let : Mono κ.hom.hom := hκ.1
  let : Smooth K.X.hom := (dynamicBaseSmoothConnected S H χ K κ).2.1 hκ |>.1
  have hf : IsIso (((baseChange (S.fromSpecResidueField s)).map κ).hom.hom.left) := by
    let b := S.fromSpecResidueField s
    have hκb := hκ.baseChange b
    have hr : SubgroupFunctor.range ((baseChange b).map κ) = ⊤ := by
      rw [hκb.2, ← parabolic_baseChange]
      exact hs
    let : Mono ((baseChange b).map κ).hom.hom := hκb.1
    let : IsIso ((baseChange b).map κ).hom.hom :=
      DynamicContainment.isIso_of_range_eq_top _ hr
    change IsIso ((Over.forget _).map ((baseChange b).map κ).hom.hom)
    infer_instance
  obtain ⟨V, hsV, hV⟩ := SmoothMonoLocalIso.isIsoNear_of_residueFiber κ s hf
  refine ⟨V, hsV, ?_⟩
  let : IsIso (((baseChange V.ι).map κ).hom.hom.left) := hV
  let : IsIso ((Over.forget _).map ((baseChange V.ι).map κ).hom.hom) :=
    inferInstanceAs (IsIso (((baseChange V.ι).map κ).hom.hom.left))
  let : IsIso ((baseChange V.ι).map κ).hom.hom :=
    isIso_of_reflects_iso _ (Over.forget _)
  rw [parabolic_baseChange, ← (hκ.baseChange V.ι).2]
  ext U x
  refine ⟨fun _ => Subgroup.mem_top _, fun _ => ?_⟩
  exact SubgroupFunctor.mem_range.mpr
    ⟨x ≫ inv ((baseChange V.ι).map κ).hom.hom, by simp⟩

/-- A homomorphism maps the whole source into the ambient parabolic when
the source dynamic parabolic is full. -/
theorem range_le_parabolic_comp_of_top
    {S : Scheme.{u}} {H G : GroupScheme S}
    (i : H ⟶ G) (χ : (Gm S).toGrp ⟶ H) (hχ : parabolic χ = ⊤) :
    SubgroupFunctor.range i ≤ parabolic (χ ≫ i) := by
  intro U x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  have hy : y ∈ (parabolic χ).carrier U := by
    rw [hχ]
    exact Subgroup.mem_top y
  exact parabolic_le_comap χ i U hy

/-- A homomorphism carries a locally full dynamic parabolic into the
corresponding ambient dynamic parabolic. -/
theorem exists_range_le_parabolic_near_of_top
    {S : Scheme.{u}} {H G : GroupScheme S}
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [GeometricallyConnected H.X.hom]
    (i : H ⟶ G) (χ : (Gm S).toGrp ⟶ H) (s : S)
    (hs : parabolic (baseChangeCocharacter (S.fromSpecResidueField s) χ) = ⊤) :
    ∃ V : S.Opens, s ∈ V ∧
      SubgroupFunctor.range ((baseChange V.ι).map i) ≤
        parabolic (baseChangeCocharacter V.ι (χ ≫ i)) := by
  obtain ⟨V, hsV, hV⟩ := exists_parabolic_eq_top_near χ s hs
  refine ⟨V, hsV, ?_⟩
  have hcomp : baseChangeCocharacter V.ι (χ ≫ i) =
      baseChangeCocharacter V.ι χ ≫ (baseChange V.ι).map i := by
    simp only [baseChangeCocharacter, Functor.map_comp, Category.assoc]
  rw [hcomp]
  exact range_le_parabolic_comp_of_top ((baseChange V.ι).map i)
    (baseChangeCocharacter V.ι χ) hV

/-- Containment at a residue fibre persists when the cocharacter belongs to
the source group and the source has smooth affine geometrically connected
fibres. Closedness is required only for the distinguished fibre inclusion. -/
theorem exists_range_le_parabolic_near_of_residueFiber
    {S : Scheme.{u}} {H G : GroupScheme S}
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [GeometricallyConnected H.X.hom]
    (i : H ⟶ G) (χ : (Gm S).toGrp ⟶ H) (s : S)
    (hi : IsClosedSubgroup ((baseChange (S.fromSpecResidueField s)).map i))
    (hs : SubgroupFunctor.range ((baseChange (S.fromSpecResidueField s)).map i) ≤
      parabolic (baseChangeCocharacter (S.fromSpecResidueField s) (χ ≫ i))) :
    ∃ V : S.Opens, s ∈ V ∧
      SubgroupFunctor.range ((baseChange V.ι).map i) ≤
        parabolic (baseChangeCocharacter V.ι (χ ≫ i)) := by
  apply exists_range_le_parabolic_near_of_top i χ s
  let b := S.fromSpecResidueField s
  have hcomp : baseChangeCocharacter b (χ ≫ i) =
      baseChangeCocharacter b χ ≫ (baseChange b).map i := by
    simp only [baseChangeCocharacter, Functor.map_comp, Category.assoc]
  ext U x
  refine ⟨fun _ => Subgroup.mem_top _, fun _ => ?_⟩
  rw [parabolic_eq_comap_of_isClosedSubgroup _ _ hi, SubgroupFunctor.mem_comap]
  rw [← hcomp]
  exact hs U (SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩)

/-- An actual open neighbourhood carrying the proved containment. -/
def parabolicContainmentNeighbourhood
    {S : Scheme.{u}} {H G : GroupScheme S}
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [GeometricallyConnected H.X.hom]
    (i : H ⟶ G) (χ : (Gm S).toGrp ⟶ H) (s : S)
    (hi : IsClosedSubgroup ((baseChange (S.fromSpecResidueField s)).map i))
    (hs : SubgroupFunctor.range ((baseChange (S.fromSpecResidueField s)).map i) ≤
      parabolic (baseChangeCocharacter (S.fromSpecResidueField s) (χ ≫ i))) :
    {V : S.Opens // s ∈ V ∧
      SubgroupFunctor.range ((baseChange V.ι).map i) ≤
        parabolic (baseChangeCocharacter V.ι (χ ≫ i))} :=
  ⟨(exists_range_le_parabolic_near_of_residueFiber i χ s hi hs).choose,
    (exists_range_le_parabolic_near_of_residueFiber i χ s hi hs).choose_spec⟩

end Langlands.GroupScheme.Dynamic
