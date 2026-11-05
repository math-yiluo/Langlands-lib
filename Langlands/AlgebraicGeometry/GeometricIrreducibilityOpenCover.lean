import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import Mathlib.AlgebraicGeometry.Cover.Open

universe u v

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- An open cover by pairwise intersecting irreducible subsets is irreducible. -/
theorem irreducibleSpace_of_open_cover {T : Type u} [TopologicalSpace T]
    {ι : Type v} [Nonempty ι] (U : ι → Set T) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (hirr : ∀ i, IsIrreducible (U i))
    (hmeet : ∀ i j, (U i ∩ U j).Nonempty) : IrreducibleSpace T := by
  let : PreirreducibleSpace T := .of_forall_nonempty_inter fun V W hV hW hVne hWne => by
    obtain ⟨x, hx⟩ := hVne
    obtain ⟨i, hxi⟩ := hcover x
    obtain ⟨y, hy⟩ := hWne
    obtain ⟨j, hyj⟩ := hcover y
    obtain ⟨z, hzi, hzV, hzj⟩ :=
      (hirr i).isPreirreducible V (U j) hV (hU j) ⟨x, hxi, hx⟩ (hmeet i j)
    obtain ⟨t, -, htV, htW⟩ :=
      (hirr j).isPreirreducible V W hV hW ⟨z, hzj, hzV⟩ ⟨y, hyj, hy⟩
    exact ⟨t, htV, htW⟩
  exact ⟨⟨(hirr (Classical.choice ‹Nonempty ι›)).nonempty.some⟩⟩

/-- Open-cover form of the pairwise intersection criterion. -/
theorem irreducibleSpace_of_scheme_openCover {X : Scheme.{u}}
    (𝒰 : Scheme.OpenCover.{v} X) [Nonempty 𝒰.I₀]
    (hirr : ∀ i, IrreducibleSpace (𝒰.X i))
    (hmeet : ∀ i j, (Set.range (𝒰.f i) ∩ Set.range (𝒰.f j)).Nonempty) :
    IrreducibleSpace X := by
  apply irreducibleSpace_of_open_cover (fun i => Set.range (𝒰.f i))
    (fun i => IsOpenImmersion.isOpen_range (𝒰.f i))
    (fun x => by simpa only [Set.mem_range] using 𝒰.exists_eq x)
    (fun i => ?_) hmeet
  let := hirr i
  simpa only [Set.image_univ] using
    (IrreducibleSpace.isIrreducible_univ (𝒰.X i)).image (𝒰.f i)
      (𝒰.f i).continuous.continuousOn

/-- Geometrically irreducible members glue when every pairwise overlap meets
all fibres. This criterion needs no finiteness or separation hypothesis. -/
theorem geometricallyIrreducible_of_openCover {X S : Scheme.{u}} (f : X ⟶ S)
    (𝒰 : Scheme.OpenCover.{v} X) [Nonempty 𝒰.I₀]
    (hgeom : ∀ i, GeometricallyIrreducible (𝒰.f i ≫ f))
    (hmeet : ∀ i j (s : S), ∃ x : X,
      f x = s ∧ x ∈ Set.range (𝒰.f i) ∧ x ∈ Set.range (𝒰.f j)) :
    GeometricallyIrreducible f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y => ?_⟩
  let 𝒱 := 𝒰.pullback₁ (pullback.fst f y)
  have : Nonempty 𝒱.I₀ := inferInstanceAs (Nonempty 𝒰.I₀)
  apply irreducibleSpace_of_scheme_openCover 𝒱
  · intro i
    let := hgeom i
    have : IrreducibleSpace ↥(pullback (𝒰.f i ≫ f) y) :=
      GeometricallyIrreducible.geometrically_irreducibleSpace y _ _ (.of_hasPullback _ _)
    let e : 𝒱.X i ≅ pullback (𝒰.f i ≫ f) y :=
      pullbackSymmetry _ _ ≪≫ pullbackRightPullbackFstIso f y (𝒰.f i)
    exact e.hom.homeomorph.irreducibleSpace_iff.mpr inferInstance
  · intro i j
    obtain ⟨s⟩ := (inferInstance : Nonempty (Spec (.of K)))
    obtain ⟨x, hxs, hxi, hxj⟩ := hmeet i j (y s)
    obtain ⟨z, hzx, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := y) x s hxs
    refine ⟨z, ?_, ?_⟩
    · change z ∈ Set.range (pullback.fst (pullback.fst f y) (𝒰.f i))
      rw [Scheme.Pullback.range_fst]
      simpa only [Set.mem_preimage, hzx] using hxi
    · change z ∈ Set.range (pullback.fst (pullback.fst f y) (𝒰.f j))
      rw [Scheme.Pullback.range_fst]
      simpa only [Set.mem_preimage, hzx] using hxj

/-- The gluing criterion also applies to a family of open immersions whose
images cover the source, without an already bundled open cover. -/
theorem geometricallyIrreducible_of_openImmersions
    {X S : Scheme.{u}} {ι : Type v} [Nonempty ι]
    (U : ι → Scheme.{u}) (i : ∀ a, U a ⟶ X) [∀ a, IsOpenImmersion (i a)]
    (f : X ⟶ S) (hcover : ∀ x : X, ∃ a, x ∈ Set.range (i a))
    (hgeom : ∀ a, GeometricallyIrreducible (i a ≫ f))
    (hmeet : ∀ a b (s : S), ∃ x : X,
      f x = s ∧ x ∈ Set.range (i a) ∧ x ∈ Set.range (i b)) :
    GeometricallyIrreducible f := by
  let 𝒰 : Scheme.OpenCover.{v} X :=
    { I₀ := ι
      X := U
      f := i
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨hcover, inferInstance⟩ }
  exact geometricallyIrreducible_of_openCover f 𝒰 hgeom hmeet

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
