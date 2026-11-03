import Langlands.GroupScheme.SubgroupBaseChange
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Fpqc reflection of represented subgroup containment -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S S' : Scheme.{u}} {G H K : GroupScheme S}

/-- A point factors through a monomorphism if it does so after an effective
epimorphism of test schemes. -/
theorem mem_range_of_comp_mem_range (i : H ⟶ G) [Mono i.hom.hom]
    {U V : Over S} (q : V ⟶ U) [EffectiveEpi q.left] {x : U ⟶ G.X}
    (hx : q ≫ x ∈ (range i).carrier V) : x ∈ (range i).carrier U := by
  obtain ⟨y, hy⟩ := mem_range.mp hx
  have hy₀ : y.left ≫ i.hom.hom.left = q.left ≫ x.left :=
    congrArg (fun f => f.left) hy
  let d : U.left ⟶ H.X.left :=
    EffectiveEpi.desc q.left y.left (fun f f' he => by
      apply (cancel_mono i.hom.hom.left).mp
      simpa only [Category.assoc, hy₀] using
        congrArg (fun z => z ≫ x.left) he)
  have hd : q.left ≫ d = y.left := EffectiveEpi.fac _ _ _
  let z : U ⟶ H.X := Over.homMk d (by
    apply (cancel_epi q.left).mp
    simp only [← Category.assoc, hd, Over.w y, Over.w q])
  refine mem_range.mpr ⟨z, ?_⟩
  apply Over.OverMorphism.ext
  apply (cancel_epi q.left).mp
  change q.left ≫ (d ≫ i.hom.hom.left) = q.left ≫ x.left
  rw [← Category.assoc, hd, hy₀]

/-- Base change preserves containment of arbitrary subgroup functors. -/
theorem baseChange_mono (b : S' ⟶ S) {F F' : SubgroupFunctor G}
    (h : F ≤ F') : F.baseChange b ≤ F'.baseChange b := by
  intro U x hx
  exact h _ hx

/-- Fpqc base change reflects containment in a represented subgroup, without
requiring representability of the subgroup on the left. -/
theorem le_range_of_baseChange_le (b : S' ⟶ S)
    [QuasiCompact b] [Flat b] [Surjective b]
    {F : SubgroupFunctor G} (i : H ⟶ G) [Mono i.hom.hom]
    (h : F.baseChange b ≤ (range i).baseChange b) : F ≤ range i := by
  intro U x hx
  let V : Over S' := (Over.pullback b).obj U
  let q : (Over.map b).obj V ⟶ U :=
    Over.homMk (pullback.fst U.hom b) pullback.condition
  have : EffectiveEpi q.left := by
    change EffectiveEpi (pullback.fst U.hom b)
    infer_instance
  apply mem_range_of_comp_mem_range i q
  let x' := (baseChangePointsEquiv b G V).symm (q ≫ x)
  have hx' : x' ∈ (F.baseChange b).carrier V := by
    rw [mem_baseChange]
    change baseChangePointsEquiv b G V
      ((baseChangePointsEquiv b G V).symm (q ≫ x)) ∈ F.carrier _
    rw [MulEquiv.apply_symm_apply]
    exact F.comp_mem q hx
  have hi := h V hx'
  rw [mem_baseChange] at hi
  simpa only [x', MulEquiv.apply_symm_apply] using hi

/-- Containment in a represented subgroup is equivalent to containment after
an fpqc base change. -/
theorem baseChange_le_range_iff (b : S' ⟶ S)
    [QuasiCompact b] [Flat b] [Surjective b]
    {F : SubgroupFunctor G} (i : H ⟶ G) [Mono i.hom.hom] :
    F.baseChange b ≤ (range i).baseChange b ↔ F ≤ range i :=
  ⟨le_range_of_baseChange_le b i, baseChange_mono b⟩

/-- Fpqc base change reflects equality of subgroup functors represented by
monomorphisms. -/
theorem range_eq_of_baseChange_eq (b : S' ⟶ S)
    [QuasiCompact b] [Flat b] [Surjective b]
    (i : H ⟶ G) (j : K ⟶ G) [Mono i.hom.hom] [Mono j.hom.hom]
    (h : (range i).baseChange b = (range j).baseChange b) : range i = range j := by
  apply le_antisymm
  · exact le_range_of_baseChange_le b j h.le
  · exact le_range_of_baseChange_le b i h.ge

/-- The same reflection theorem using explicit representing homomorphisms. -/
theorem eq_of_isRepresentedBy_baseChange_eq (b : S' ⟶ S)
    [QuasiCompact b] [Flat b] [Surjective b]
    {F F' : SubgroupFunctor G} {i : H ⟶ G} {j : K ⟶ G}
    (hi : F.IsRepresentedBy i) (hj : F'.IsRepresentedBy j)
    (h : F.baseChange b = F'.baseChange b) : F = F' := by
  let : Mono i.hom.hom := hi.1
  let : Mono j.hom.hom := hj.1
  rw [← hi.2, ← hj.2] at h ⊢
  exact range_eq_of_baseChange_eq b i j h

/-- Fpqc base change embeds the ordered collection of representable subgroup
functors into the subgroup functors over the new base. -/
def baseChangeOrderEmbedding (b : S' ⟶ S)
    [QuasiCompact b] [Flat b] [Surjective b] :
    {F : SubgroupFunctor G // ∃ (H : GroupScheme S) (i : H ⟶ G),
      F.IsRepresentedBy i} ↪o SubgroupFunctor ((GroupScheme.baseChange b).obj G) where
  toFun F := F.val.baseChange b
  inj' := by
    intro F F' h
    obtain ⟨H, i, hi⟩ := F.property
    obtain ⟨K, j, hj⟩ := F'.property
    exact Subtype.ext (eq_of_isRepresentedBy_baseChange_eq b hi hj h)
  map_rel_iff' := by
    intro F F'
    change F.val.baseChange b ≤ F'.val.baseChange b ↔ F.val ≤ F'.val
    constructor
    · intro h
      obtain ⟨K, j, hj⟩ := F'.property
      let : Mono j.hom.hom := hj.1
      rw [← hj.2] at h ⊢
      exact le_range_of_baseChange_le b j h
    · exact baseChange_mono b

end Langlands.GroupScheme.SubgroupFunctor
