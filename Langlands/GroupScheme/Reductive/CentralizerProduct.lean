import Langlands.GroupScheme.Reductive.NormalCentralizer
import Langlands.GroupScheme.Reductive.CommutingMultiplication
import Langlands.GroupScheme.Reductive.Semisimple

/-! # Multiplication in the full centralizer as a pullback -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G H C Z K : GroupScheme S}

/-- A point of a subgroup centralizes that subgroup exactly when it is central
in the subgroup. This uses the full all-refinement conditions. -/
theorem mem_center_iff_comp_mem_conjugation_fixedSubgroup
    (j : H ⟶ G) [Mono j.hom.hom] {T : Over S} (x : T ⟶ H.X) :
    x ∈ (center H).carrier T ↔
      x ≫ j.hom.hom ∈ (AutomorphicAction.conjugation j).fixedSubgroup.carrier T := by
  rw [mem_conjugation_fixedSubgroup_iff]
  constructor
  · intro hx U b h
    have he := congrArg (fun y => y ≫ j.hom.hom) (hx U b h).eq.symm
    change _ = _
    simpa only [MonObj.mul_comp, Category.assoc] using he
  · intro hx U b h
    apply (cancel_mono j.hom.hom).mp
    rw [MonObj.mul_comp, MonObj.mul_comp, Category.assoc]
    exact (hx U b h).eq.symm

namespace CentralizerProduct

variable (j : H ⟶ G) (c : C ⟶ G)
    (hc : (AutomorphicAction.conjugation j).fixedSubgroup.IsRepresentedBy c)
    (z : Z ⟶ H) (hz : IsSchemeTheoreticCenter z)

/-- The full centre of a subgroup factors through its full centralizer. -/
def centerMap : Z ⟶ C :=
  hc.factorHom (z ≫ j) (by
    apply (range_le_conjugation_fixedSubgroup_iff j (z ≫ j)).mpr
    intro T h x
    have he := congrArg (fun y => y ≫ j.hom.hom)
      (commute_of_mem_center (hz.isCentral T x) h).eq.symm
    change _ = _
    simpa only [Grp.comp_hom_hom, Category.assoc, MonObj.mul_comp] using he)

@[reassoc]
theorem centerMap_comp : centerMap j c hc z hz ≫ c = z ≫ j :=
  hc.factorHom_comp _ _

@[reassoc]
theorem centerMap_hom_comp :
    (centerMap j c hc z hz).hom.hom ≫ c.hom.hom =
      z.hom.hom ≫ j.hom.hom :=
  congrArg (fun f => f.hom.hom) (centerMap_comp j c hc z hz)

/-- The centre of the subgroup is central in its full centralizer. -/
theorem centerMap_isCentral : IsCentral (centerMap j c hc z hz) := by
  intro T x U b y
  apply hc.1.right_cancellation
  rw [MonObj.mul_comp, MonObj.mul_comp]
  have hy : y ≫ c.hom.hom ∈
      (AutomorphicAction.conjugation j).fixedSubgroup.carrier U := by
    rw [← hc.2]
    exact SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩
  have he := (mem_conjugation_fixedSubgroup_iff j _).mp hy U (𝟙 U)
    (b ≫ x ≫ z.hom.hom)
  change _ = _ at he
  simpa only [Category.id_comp, Category.assoc, centerMap_hom_comp]
    using he

variable (d : K ⟶ C)

/-- Actual multiplication of the subgroup centre and a factor in the full
centralizer. -/
def hom : Z ⊗ K ⟶ C :=
  commutingSubgroupMultiplicationHom (centerMap j c hc z hz) d
    (fun T x y => commute_of_mem_center (centerMap_isCentral j c hc z hz T x)
      (y ≫ d.hom.hom))

/-- The multiplication in the centralizer is the restriction of multiplication
in the ambient group. -/
theorem square :
    (z.hom.hom ⊗ₘ 𝟙 K.X) ≫ subgroupMultiplication j (d ≫ c) =
      (hom j c hc z hz d).hom.hom ≫ c.hom.hom := by
  change _ = subgroupMultiplication (centerMap j c hc z hz) d ≫ c.hom.hom
  simp only [subgroupMultiplication, MonObj.comp_mul, MonObj.mul_comp,
    Category.assoc, tensorHom_fst_assoc, tensorHom_snd_assoc, Category.id_comp,
    centerMap_hom_comp, Grp.comp_hom_hom]

include hc in
/-- If a product of a subgroup point and a centralizer point is in the full
centralizer, the subgroup point is central in the subgroup. -/
theorem mem_center_of_product_eq [Mono j.hom.hom]
    {T : Over S} (h : T ⟶ H.X) (x : T ⟶ K.X) (y : T ⟶ C.X)
    (he : (h ≫ j.hom.hom) * (x ≫ (d ≫ c).hom.hom) = y ≫ c.hom.hom) :
    h ∈ (center H).carrier T := by
  apply (mem_center_iff_comp_mem_conjugation_fixedSubgroup j h).mpr
  let F := (AutomorphicAction.conjugation j).fixedSubgroup
  have hx : x ≫ (d ≫ c).hom.hom ∈ F.carrier T := by
    change _ ∈ (AutomorphicAction.conjugation j).fixedSubgroup.carrier T
    rw [← hc.2]
    exact SubgroupFunctor.mem_range.mpr ⟨x ≫ d.hom.hom, Category.assoc _ _ _⟩
  have hy : y ≫ c.hom.hom ∈ F.carrier T := by
    change _ ∈ (AutomorphicAction.conjugation j).fixedSubgroup.carrier T
    rw [← hc.2]
    exact SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩
  have hp : (h ≫ j.hom.hom) * (x ≫ (d ≫ c).hom.hom) ∈ F.carrier T := he.symm ▸ hy
  have hh := (F.carrier T).mul_mem hp ((F.carrier T).inv_mem hx)
  simpa only [mul_inv_cancel_right] using hh

/-- The centre-times-factor multiplication square is a genuine pullback of
schemes over the base, without geometric hypotheses on any factor. -/
theorem isPullback [Mono j.hom.hom] :
    IsPullback (z.hom.hom ⊗ₘ 𝟙 K.X) (hom j c hc z hz d).hom.hom
      (subgroupMultiplication j (d ≫ c)) c.hom.hom := by
  let : Mono z.hom.hom := hz.isRepresentedBy.1
  let : Mono c.hom.hom := hc.1
  have w := square j c hc z hz d
  refine IsPullback.of_isLimit (c := PullbackCone.mk _ _ w) ?_
  let l (s : PullbackCone (subgroupMultiplication j (d ≫ c)) c.hom.hom) :
      s.pt ⟶ Z.X :=
    (hz.isRepresentedBy.pointsEquiv s.pt).symm
      ⟨s.fst ≫ fst H.X K.X,
        mem_center_of_product_eq j c hc d
          (s.fst ≫ fst H.X K.X) (s.fst ≫ snd H.X K.X) s.snd (by
            simpa only [subgroupMultiplication, MonObj.comp_mul, ← Category.assoc,
              tensorHom_fst, tensorHom_snd] using s.condition)⟩
  have hl (s : PullbackCone (subgroupMultiplication j (d ≫ c)) c.hom.hom) :
      l s ≫ z.hom.hom = s.fst ≫ fst H.X K.X :=
    hz.isRepresentedBy.pointsEquiv_symm_comp _
  refine PullbackCone.IsLimit.mk w
    (fun s => lift (l s) (s.fst ≫ snd H.X K.X)) ?_ ?_ ?_
  · intro s
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, tensorHom_fst, lift_fst_assoc, hl]
    · simp only [Category.assoc, tensorHom_snd, Category.comp_id, lift_snd]
  · intro s
    apply (cancel_mono c.hom.hom).mp
    rw [Category.assoc, ← w, ← Category.assoc]
    have he : lift (l s) (s.fst ≫ snd H.X K.X) ≫
        (z.hom.hom ⊗ₘ 𝟙 K.X) = s.fst := by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [Category.assoc, tensorHom_fst, lift_fst_assoc, hl]
      · simp only [Category.assoc, tensorHom_snd, Category.comp_id, lift_snd]
    rw [he, s.condition]
  · intro s m hm _
    apply CartesianMonoidalCategory.hom_ext
    · apply (cancel_mono z.hom.hom).mp
      have he := congrArg (fun f => f ≫ fst H.X K.X) hm
      simpa only [Category.assoc, tensorHom_fst, lift_fst, hl] using he
    · have he := congrArg (fun f => f ≫ snd H.X K.X) hm
      simpa only [Category.assoc, tensorHom_snd, Category.comp_id, lift_snd] using he

/-- An actual isomorphism from the centre product to the pullback of ambient
multiplication along the full centralizer inclusion. -/
def pullbackIso [Mono j.hom.hom] :
    (Z ⊗ K).X ≅ pullback (subgroupMultiplication j (d ≫ c)) c.hom.hom :=
  (isPullback j c hc z hz d).isoIsPullback _ _
    (IsPullback.of_hasPullback _ _)

/-- Faithful flatness and quasi-compactness of ambient multiplication pass to
the multiplication of the subgroup centre and the centralizer factor. -/
theorem fpqc [Mono j.hom.hom]
    [Flat (subgroupMultiplication j (d ≫ c)).left]
    [Surjective (subgroupMultiplication j (d ≫ c)).left]
    [QuasiCompact (subgroupMultiplication j (d ≫ c)).left] :
    Flat (hom j c hc z hz d).hom.hom.left ∧
      Surjective (hom j c hc z hz d).hom.hom.left ∧
      QuasiCompact (hom j c hc z hz d).hom.hom.left := by
  have hp := (isPullback j c hc z hz d).map (Over.forget S)
  change IsPullback (z.hom.hom ⊗ₘ 𝟙 K.X).left (hom j c hc z hz d).hom.hom.left
    (subgroupMultiplication j (d ≫ c)).left c.hom.hom.left at hp
  exact ⟨MorphismProperty.of_isPullback hp inferInstance,
    MorphismProperty.of_isPullback hp inferInstance,
    MorphismProperty.of_isPullback hp inferInstance⟩

end CentralizerProduct

end Langlands.GroupScheme
