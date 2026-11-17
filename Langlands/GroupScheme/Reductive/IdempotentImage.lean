import Langlands.GroupScheme.HomImage
import Langlands.GroupScheme.Reductive.AlmostSimple
import Langlands.GroupScheme.SubgroupRangeTransport

/-! # Actual retract images of idempotent field-group endomorphisms -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The actual smooth connected closed retract image of an idempotent. -/
structure IdempotentImage (ψ : G ⟶ G) where
  group : GroupScheme (Spec (CommRingCat.of k))
  inclusion : group ⟶ G
  projection : G ⟶ group
  closed : IsClosedSubgroup inclusion
  factorization : projection ≫ inclusion = ψ
  retraction : inclusion ≫ projection = 𝟙 group
  smooth : Smooth group.X.hom
  connected : ConnectedSpace group.X.left
  affine : IsAffineHom group.X.hom
  range_eq : SubgroupFunctor.range inclusion = SubgroupFunctor.range ψ

/-- Every idempotent of a smooth connected affine field group has an actual
smooth connected closed retract image, equal on all points to its full image. -/
def idempotentImage [Smooth G.X.hom] [ConnectedSpace G.X.left] [IsAffineHom G.X.hom]
    (ψ : G ⟶ G) (hidem : ψ ≫ ψ = ψ) : IdempotentImage ψ := by
  apply Classical.choice
  obtain ⟨H, i, p, hi, hpi, hpf, hps, _, _, hHs, hHc, hHa⟩ := HomImage.exists_image ψ
  let : Flat p.hom.hom.left := hpf
  let : Surjective p.hom.hom.left := hps
  let : Epi p.hom.hom.left := Flat.epi_of_flat_of_surjective _
  let : Epi p.hom.hom := Over.epi_of_epi_left _
  let : Epi p := (Grp.forget _).epi_of_epi_map (inferInstanceAs (Epi p.hom.hom))
  have hfix : i ≫ ψ = i := by
    apply (cancel_epi p).mp
    simpa only [← Category.assoc, hpi] using hidem
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let : Mono i := (Grp.forget _).mono_of_mono_map (inferInstanceAs (Mono i.hom.hom))
  have hret : i ≫ p = 𝟙 H := by
    apply (cancel_mono i).mp
    simpa only [Category.assoc, hpi, Category.id_comp] using hfix
  have hrange : SubgroupFunctor.range i = SubgroupFunctor.range ψ := by
    apply SubgroupFunctor.ext
    intro T
    apply Subgroup.ext
    intro x
    constructor
    · rintro ⟨y, rfl⟩
      refine SubgroupFunctor.mem_range.mpr ⟨y ≫ i.hom.hom, ?_⟩
      rw [Category.assoc, ← Grp.comp_hom_hom, hfix]
      rfl
    · rintro ⟨y, rfl⟩
      refine SubgroupFunctor.mem_range.mpr ⟨y ≫ p.hom.hom, ?_⟩
      rw [Category.assoc, ← Grp.comp_hom_hom, hpi]
      rfl
  exact ⟨⟨H, i, p, hi, hpi, hret, hHs, hHc, hHa, hrange⟩⟩

namespace IdempotentImage
variable {ψ : G ⟶ G} (P : IdempotentImage ψ)

/-- The idempotent fixes every point of its actual image. -/
@[reassoc (attr := simp)] theorem inclusion_comp : P.inclusion ≫ ψ = P.inclusion := by
  calc
    P.inclusion ≫ ψ = P.inclusion ≫ (P.projection ≫ P.inclusion) :=
      congrArg (fun f => P.inclusion ≫ f) P.factorization.symm
    _ = (P.inclusion ≫ P.projection) ≫ P.inclusion := (Category.assoc _ _ _).symm
    _ = P.inclusion := by rw [P.retraction, Category.id_comp]

/-- Full pointwise normality of the idempotent image is exactly normality of
its closed representative. -/
theorem normal (h : (SubgroupFunctor.range ψ).IsNormal) :
    (SubgroupFunctor.range P.inclusion).IsNormal := by
  rw [P.range_eq]
  exact h

end IdempotentImage

/-- Conjugation equivariance makes the full pointwise image normal. -/
theorem isNormal_range_of_conjugation_equivariant (ψ : G ⟶ G)
    (hn : ∀ (T : Over (Spec (CommRingCat.of k))) (h x : T ⟶ G.X),
      (h * x * h⁻¹) ≫ ψ.hom.hom = h * (x ≫ ψ.hom.hom) * h⁻¹) :
    (SubgroupFunctor.range ψ).IsNormal := by
  intro T h z _ hz
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hz
  exact SubgroupFunctor.mem_range.mpr ⟨h * x * h⁻¹, hn T h x⟩

/-- On an almost-simple field group, every idempotent with normal image is
trivial or the identity. No algebraic closedness assumption is needed. -/
theorem IsAlmostSimple.idempotent_eq_zero_or_id (hG : IsAlmostSimple G)
    (ψ : G ⟶ G) (hidem : ψ ≫ ψ = ψ) (hn : (SubgroupFunctor.range ψ).IsNormal) :
    ψ = 0 ∨ ψ = 𝟙 G := by
  let : Smooth G.X.hom := hG.isSemisimple.isConnectedReductive.smooth
  let : ConnectedSpace G.X.left := hG.isSemisimple.isConnectedReductive.connectedSpace
  let : IsAffineHom G.X.hom := hG.isSemisimple.isConnectedReductive.isAffineHom
  let P := idempotentImage ψ hidem
  rcases hG.normalSubgroup_trivial_or_full P.group P.inclusion P.closed
      P.smooth P.connected (P.normal hn) with hbot | htop
  · left
    have hψbot : SubgroupFunctor.range ψ = ⊥ := P.range_eq.symm.trans hbot
    apply Grp.hom_ext
    change ψ.hom.hom = (1 : G.X ⟶ G.X)
    have hz : ψ.hom.hom ∈ (SubgroupFunctor.range ψ).carrier G.X :=
      SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩
    simpa only [hψbot, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] using hz
  · right
    let : IsClosedImmersion P.inclusion.hom.hom.left := P.closed
    have hrep : (⊤ : SubgroupFunctor G).IsRepresentedBy P.inclusion :=
      ⟨Over.mono_of_mono_left _, htop⟩
    let : IsIso P.inclusion := by
      rw [← hrep.topIso_hom]
      infer_instance
    apply (cancel_epi P.inclusion).mp
    simpa only [Category.comp_id] using P.inclusion_comp

/-- In particular the normal, conjugation-equivariant case has the same dichotomy. -/
theorem IsAlmostSimple.normal_idempotent_eq_zero_or_id (hG : IsAlmostSimple G)
    (ψ : G ⟶ G) (hidem : ψ ≫ ψ = ψ)
    (hn : ∀ (T : Over (Spec (CommRingCat.of k))) (h x : T ⟶ G.X),
      (h * x * h⁻¹) ≫ ψ.hom.hom = h * (x ≫ ψ.hom.hom) * h⁻¹) :
    ψ = 0 ∨ ψ = 𝟙 G :=
  hG.idempotent_eq_zero_or_id ψ hidem (isNormal_range_of_conjugation_equivariant ψ hn)

end Langlands.GroupScheme
