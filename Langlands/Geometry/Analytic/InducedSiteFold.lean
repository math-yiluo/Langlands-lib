import Langlands.Geometry.Analytic.InducedSpacePoints
import Langlands.Geometry.Analytic.InducedSiteFaithful
import Langlands.Geometry.Analytic.OpenPartitionCoproductStatement

/-! # The fold morphism of an induced space on the copies -/

noncomputable section

universe u v z

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {G : Type z} [Group G] (H : Subgroup G)
  (X : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) H)

/-- The unit `X → X_{G/H}` is a split monomorphism, with retraction `foldHom ≫ ρ(r)`, where
`r` is the chosen representative of the coset `H`. -/
@[reassoc (attr := simp)]
theorem unitHom_foldHom : unitHom H X ≫ foldHom H X ≫ X.ρ (baseRep H) = 𝟙 X.V := by
  rw [unitHom, Category.assoc, copy_foldHom_assoc, ρ_comp, mul_inv_cancel, Action.ρ_one]

instance mono_unitHom : Mono (unitHom H X) :=
  ⟨fun _ _ h => by simpa using h =≫ (foldHom H X ≫ X.ρ (baseRep H))⟩

/-- The open domain of `X_{G/H}` given by the copy indexed by `c`. -/
def copyDomain (c : G ⧸ H) : (presentationOf (copies H X).pt).AnalyticDomain :=
  (presentationOf (copies H X).pt).openDomain
    (Set.range (localizedSpaceFunctor.map (copy H X c))) (isOpen_range_copy_space H X c)

theorem mem_copyDomain_iff (c : G ⧸ H) (p : localizedSpaceFunctor.obj (copies H X).pt) :
    p ∈ (copyDomain H X c).carrier ↔ pointCoset H X p = c :=
  mem_range_copy_space_iff H X c p

/-- The copy indexed by `c` lands in its open domain. -/
theorem copy_mem_copyDomain (c : G ⧸ H) (x : localizedSpaceFunctor.obj X.V) :
    localizedSpaceFunctor.map (copy H X c) x ∈ (copyDomain H X c).carrier :=
  ⟨x, rfl⟩

variable (hP : OpenPartitionCoproductStatement.{u, v, z})

include hP in
/-- The open domains of the copies exhibit `X_{G/H}` as their coproduct. -/
theorem nonempty_isColimit_copyDomain :
    Nonempty (IsColimit (Cofan.mk (copies H X).pt fun c =>
      domainι (copies H X).pt (copyDomain H X c))) :=
  hP K (copies H X).pt (fun c => Set.range (localizedSpaceFunctor.map (copy H X c)))
    (isOpen_range_copy_space H X)
    (fun i j hij => Set.disjoint_left.2 fun p hi hj =>
      hij (((mem_range_copy_space_iff H X i p).1 hi).symm.trans
        ((mem_range_copy_space_iff H X j p).1 hj)))
    (fun p => ⟨pointCoset H X p, (mem_range_copy_space_iff H X _ p).2 rfl⟩)

include hP in
/-- On the open domain of the copy `c`, the fold morphism followed by the inclusion of the
copy `c` is the canonical morphism of the domain. -/
theorem domainι_copyDomain_foldHom_copy (c : G ⧸ H) :
    domainι _ (copyDomain H X c) ≫ foldHom H X ≫ copy H X c = domainι _ (copyDomain H X c) := by
  obtain ⟨hc⟩ := nonempty_isColimit_copyDomain H X hP
  let φ : ∀ d, domainObj (copies H X).pt (copyDomain H X d) ⟶ (copies H X).pt := fun d =>
    domainι _ (copyDomain H X d) ≫ foldHom H X ≫ copy H X d
  have hfac : ∀ d, domainι _ (copyDomain H X d) ≫ Cofan.IsColimit.desc hc φ = φ d :=
    fun d => Cofan.IsColimit.fac hc φ d
  have hψ : Cofan.IsColimit.desc hc φ = 𝟙 _ := by
    refine copies_hom_ext H X fun d => ?_
    have hl := domainLift_comp (copyDomain H X d) (copy H X d) (copy_mem_copyDomain H X d)
    calc copy H X d ≫ Cofan.IsColimit.desc hc φ
        = domainLift (copyDomain H X d) (copy H X d) (copy_mem_copyDomain H X d) ≫
            domainι _ (copyDomain H X d) ≫ Cofan.IsColimit.desc hc φ := by
          rw [← Category.assoc, hl]
      _ = domainLift (copyDomain H X d) (copy H X d) (copy_mem_copyDomain H X d) ≫ φ d := by
          rw [hfac]
      _ = copy H X d ≫ 𝟙 _ := by
          simp only [φ]
          rw [← Category.assoc, hl, copy_foldHom_assoc, Category.comp_id]
  have h := hfac c
  rw [hψ] at h
  exact (h.symm.trans (Category.comp_id _) :)

include hP in
/-- A morphism to `X_{G/H}` with image in the copy `c` factors through that copy, by the fold
morphism. -/
theorem foldHom_copy_of_pointCoset {T : LocalizedCategory.{u, max z v, max z v} (K := K)}
    (f : T ⟶ (copies H X).pt) (c : G ⧸ H)
    (hf : ∀ t, pointCoset H X (localizedSpaceFunctor.map f t) = c) :
    f ≫ foldHom H X ≫ copy H X c = f := by
  have hf' : ∀ t, localizedSpaceFunctor.map f t ∈ (copyDomain H X c).carrier := fun t =>
    (mem_copyDomain_iff H X c _).2 (hf t)
  rw [← domainLift_comp (copyDomain H X c) f hf', Category.assoc,
    domainι_copyDomain_foldHom_copy H X hP c]

end Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace
