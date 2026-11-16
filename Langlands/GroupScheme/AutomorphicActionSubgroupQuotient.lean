import Langlands.GroupScheme.LocalGroupIsoSubgroup
import Langlands.GroupScheme.RelativeInnerCocycle
import Langlands.GroupScheme.SubgroupFunctor.FppfProductLaws
import Langlands.GroupScheme.SubgroupFunctor.QuotientEmbedding
import Langlands.GroupScheme.RelativeParabolicNormalizerProof
import Langlands.GroupScheme.RelativeLevi.ParabolicClosedProof
import Langlands.GroupScheme.RelativeLevi.BorelTransport

/-! # Subgroup stabilizers under quotient actions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace SubgroupFunctor

variable {S : Scheme.{u}} {G A : GroupScheme S}

/-- Fppf inverse images reflect containment in any subgroup with fppf-local membership. -/
theorem le_of_comap_le_of_isFppfLocal (q : G ⟶ A)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]
    {F E : SubgroupFunctor A} (hE : E.IsFppfLocal)
    (h : F.comap q ≤ E.comap q) : F ≤ E := by
  intro T x hx
  let V : Over S := Over.mk (pullback.fst x.left q.hom.hom.left ≫ T.hom)
  let p : V ⟶ T := Over.homMk (pullback.fst x.left q.hom.hom.left) rfl
  let y : V ⟶ G.X := Over.homMk (pullback.snd x.left q.hom.hom.left) (by
    rw [← Over.w q.hom.hom, ← Category.assoc, ← pullback.condition,
      Category.assoc, Over.w x]
    rfl)
  have hpy : p ≫ x = y ≫ q.hom.hom :=
    Over.OverMorphism.ext pullback.condition
  have hf : Flat p.left := by change Flat (pullback.fst _ _); infer_instance
  have hs : Surjective p.left := by change Surjective (pullback.fst _ _); infer_instance
  have hl : LocallyOfFinitePresentation p.left := by
    change LocallyOfFinitePresentation (pullback.fst _ _)
    infer_instance
  apply hE T V p hf hs hl x
  rw [hpy]
  apply h V
  change y ≫ q.hom.hom ∈ F.carrier V
  rw [← hpy]
  exact F.comp_mem p hx

end SubgroupFunctor

namespace AutomorphicAction

variable {S : Scheme.{u}} {G A K : GroupScheme S}

/-- Restricting the acting group pulls back the full subgroup stabilizer. -/
theorem subgroupStabilizer_restrict (a : AutomorphicAction A G) (q : K ⟶ A)
    (F : SubgroupFunctor G) :
    (a.restrict q).subgroupStabilizer F = (a.subgroupStabilizer F).comap q := by
  apply SubgroupFunctor.ext
  intro T
  ext x
  change (∀ (W : Over S) (t : W ⟶ T) (g : W ⟶ G.X),
      (a.restrict q).act (t ≫ x) g ∈ F.carrier W ↔ g ∈ F.carrier W) ↔
    ∀ (W : Over S) (t : W ⟶ T) (g : W ⟶ G.X),
      a.act (t ≫ (x ≫ q.hom.hom)) g ∈ F.carrier W ↔ g ∈ F.carrier W
  simp only [restrict_act, Category.assoc]

/-- For an action restricting to conjugation, the stabilizer pulls back to the normalizer. -/
theorem subgroupStabilizer_comap_of_restrict_eq_conjugation
    (a : AutomorphicAction A G) (q : G ⟶ A)
    (ha : a.restrict q = conjugation (𝟙 G)) (F : SubgroupFunctor G) :
    (a.subgroupStabilizer F).comap q = F.normalizer := by
  rw [← subgroupStabilizer_restrict, ha, conjugation_subgroupStabilizer]

/-- The stabilizer of an fppf-local subgroup has fppf-local membership. -/
theorem isFppfLocal_subgroupStabilizer (a : AutomorphicAction A G)
    {F : SubgroupFunctor G} (hF : F.IsFppfLocal) :
    (a.subgroupStabilizer F).IsFppfLocal := by
  intro T V p hf hs hl x hx W t g
  let : Flat p.left := hf
  let : Surjective p.left := hs
  let : LocallyOfFinitePresentation p.left := hl
  let Z : Over S := Over.mk (pullback.fst t.left p.left ≫ W.hom)
  let s : Z ⟶ W := Over.homMk (pullback.fst t.left p.left) rfl
  let r : Z ⟶ V := Over.homMk (pullback.snd t.left p.left) (by
    rw [← Over.w p, ← Category.assoc, ← pullback.condition,
      Category.assoc, Over.w t]
    rfl)
  have hst : s ≫ t = r ≫ p := Over.OverMorphism.ext pullback.condition
  have hsf : Flat s.left := by change Flat (pullback.fst _ _); infer_instance
  have hss : Surjective s.left := by change Surjective (pullback.fst _ _); infer_instance
  have hsl : LocallyOfFinitePresentation s.left := by
    change LocallyOfFinitePresentation (pullback.fst _ _)
    infer_instance
  have hlocal := hx Z r (s ≫ g)
  rw [← Category.assoc, ← hst, Category.assoc, ← a.naturality] at hlocal
  constructor
  · intro hg
    apply hF W Z s hsf hss hsl g
    exact hlocal.mp (F.comp_mem s hg)
  · intro hg
    apply hF W Z s hsf hss hsl (a.act (t ≫ x) g)
    exact hlocal.mpr (F.comp_mem s hg)

/-- A quotient subgroup with self-normalizing inverse image is the exact action stabilizer. -/
theorem subgroupStabilizer_eq_range_of_comap
    (a : AutomorphicAction A G) (q : G ⟶ A)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]
    (ha : a.restrict q = conjugation (𝟙 G))
    {F : SubgroupFunctor G} (hF : F.IsFppfLocal) (hn : F.normalizer = F)
    {P : GroupScheme S} (j : P ⟶ A) [Mono j.hom.hom]
    (hj : (SubgroupFunctor.range j).comap q = F) :
    a.subgroupStabilizer F = SubgroupFunctor.range j := by
  apply le_antisymm
  · apply SubgroupFunctor.le_of_comap_le_of_isFppfLocal q
      (SubgroupFunctor.isFppfLocal_range j)
    rw [a.subgroupStabilizer_comap_of_restrict_eq_conjugation q ha, hn, hj]
  · apply SubgroupFunctor.le_of_comap_le_of_isFppfLocal q
      (a.isFppfLocal_subgroupStabilizer hF)
    rw [a.subgroupStabilizer_comap_of_restrict_eq_conjugation q ha, hn, hj]

end AutomorphicAction

section Borel

variable {R : Type u} [CommRing R]
    {G B A P : GroupScheme (Spec (CommRingCat.of R))}
    {i : B ⟶ G} (hi : IsRelativeBorelSubgroup i) (hG : IsReductive G)
    (q : G ⟶ A) (a : AutomorphicAction A G)
    (ha : a.restrict q = AutomorphicAction.conjugation (𝟙 G))

include hi hG in
/-- A relative Borel is its own all-test normalizer over a ring. -/
theorem IsRelativeBorelSubgroup.normalizer_eq :
    (SubgroupFunctor.range i).normalizer = SubgroupFunctor.range i := by
  apply relativeParabolicSelfNormalizer R G B i hG
    hi.isRelativeParabolicSubgroup.smooth
    (relativeParabolicClosed _ G B i hG hi.isRelativeParabolicSubgroup)
  intro k _ _
  exact (hi.fieldPoint hG (Spec.algebraMap R k)).isParabolicSubgroup

include hi hG ha in
/-- Any monic quotient Borel with the specified inverse image represents the adjoint-action
stabilizer of the original Borel subgroup functor. -/
theorem IsRelativeBorelSubgroup.isRepresentedBy_subgroupStabilizer
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]
    (j : P ⟶ A) [Mono j.hom.hom]
    (hj : (SubgroupFunctor.range j).comap q = SubgroupFunctor.range i) :
    (a.subgroupStabilizer (SubgroupFunctor.range i)).IsRepresentedBy j := by
  let : Mono i.hom.hom := hi.isRelativeParabolicSubgroup.mono
  exact ⟨inferInstance, (a.subgroupStabilizer_eq_range_of_comap q ha
    (SubgroupFunctor.isFppfLocal_range i) (hi.normalizer_eq hG) j hj).symm⟩

variable (qB : B ⟶ P)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]
    [Flat qB.hom.hom.left] [Surjective qB.hom.hom.left]
    [QuasiCompact qB.hom.hom.left]
    (hkernel : SubgroupFunctor.range (kernelι qB) ≤
      (SubgroupFunctor.range (kernelι q)).comap i)
    (hkernel' : (SubgroupFunctor.range (kernelι q)).comap i ≤
      SubgroupFunctor.range (kernelι qB))
    (hcontain : SubgroupFunctor.range (kernelι q) ≤ SubgroupFunctor.range i)

include hi hG ha hkernel' hcontain in
/-- The subgroup map induced on supplied quotient groups represents the Borel stabilizer. -/
theorem IsRelativeBorelSubgroup.quotientSubgroupHom_isRepresentedBy :
    (a.subgroupStabilizer (SubgroupFunctor.range i)).IsRepresentedBy
      (SubgroupFunctor.quotientSubgroupHom i q qB hkernel) := by
  let : Mono i.hom.hom := hi.isRelativeParabolicSubgroup.mono
  let : Mono (SubgroupFunctor.quotientSubgroupHom i q qB hkernel).hom.hom :=
    SubgroupFunctor.quotientSubgroupHom_mono i q qB hkernel hkernel'
  exact hi.isRepresentedBy_subgroupStabilizer hG q a ha _
    (SubgroupFunctor.quotientSubgroupHom_comap_range i q qB hkernel hcontain)

/-- Construct the actual stabilizer inclusion from a supplied quotient of the Borel. -/
def IsRelativeBorelSubgroup.quotientStabilizerInclusion :
    {j : P ⟶ A // (a.subgroupStabilizer (SubgroupFunctor.range i)).IsRepresentedBy j} :=
  ⟨SubgroupFunctor.quotientSubgroupHom i q qB hkernel,
    hi.quotientSubgroupHom_isRepresentedBy hG q a ha qB hkernel hkernel' hcontain⟩

/-- The constructed stabilizer inclusion completes the original quotient square. -/
theorem IsRelativeBorelSubgroup.quotientStabilizerInclusion_square :
    i ≫ q = qB ≫
      (hi.quotientStabilizerInclusion hG q a ha qB hkernel hkernel' hcontain).val :=
  SubgroupFunctor.quotientSubgroupHom_square i q qB hkernel

end Borel

end Langlands.GroupScheme
