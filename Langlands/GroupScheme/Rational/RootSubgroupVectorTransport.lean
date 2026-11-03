import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Rational.WeightSemigroupStatement
import Langlands.GroupScheme.RepresentedSubgroup
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # Actual kernels and transport of natural vector coordinates -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {B : Scheme.{u}} {G H Q : GroupScheme B}

/-- A trivial actual kernel makes the underlying morphism a monomorphism. -/
theorem mono_of_range_kernel_eq_bot (q : H ⟶ Q)
    (hq : range (kernelι q) = ⊥) : Mono q.hom.hom := by
  constructor
  intro T x y hxy
  have hinj : Function.Injective ((yonedaGrp.map q).app (op T)).hom := by
    apply (injective_iff_map_eq_one _).mpr
    intro z hz
    have hz' := (mem_range_kernelι_iff q z).mpr hz
    rw [hq] at hz'
    exact hz'
  exact hinj hxy

/-- The inverse image of the identity functor under a monomorphism is trivial. -/
theorem comap_bot_of_mono (j : H ⟶ G) [Mono j.hom.hom] :
    (⊥ : SubgroupFunctor G).comap j = ⊥ := by
  ext T x
  change x ≫ j.hom.hom = 1 ↔ x = 1
  constructor
  · intro hx
    apply (cancel_mono j.hom.hom).mp
    simpa only [MonObj.one_comp] using hx
  · rintro rfl
    exact MonObj.one_comp _

end SubgroupFunctor

namespace RelativeRoot

variable {B : Scheme.{u}} {H Q : GroupScheme B}

/-- An fppf quotient with trivial actual kernel is an isomorphism on the
underlying schemes over the base. -/
theorem IsFppfQuotient.isIso_of_bot {q : H ⟶ Q}
    (hq : IsFppfQuotient ⊥ q) : IsIso q.hom.hom := by
  let : Flat q.hom.hom.left := hq.1
  let : Surjective q.hom.hom.left := hq.2.1
  let : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  let : Mono q.hom.hom := SubgroupFunctor.mono_of_range_kernel_eq_bot q hq.2.2.2
  let : Mono q.hom.hom.left := Over.mono_left_of_mono _
  let : IsOpenImmersion q.hom.hom.left := IsOpenImmersion.of_flat_of_mono _
  let : IsIso q.hom.hom.left :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  have : IsIso ((Over.forget B).map q.hom.hom) := by
    change IsIso q.hom.hom.left
    infer_instance
  exact isIso_of_reflects_iso q.hom.hom (Over.forget B)

/-- The group-scheme isomorphism underlying an fppf quotient by the actual
trivial subgroup functor. -/
def IsFppfQuotient.isoOfBot {q : H ⟶ Q} (hq : IsFppfQuotient ⊥ q) : H ≅ Q :=
  letI := hq.isIso_of_bot
  Grp.mkIso (asIso q.hom.hom)

/-- Transport natural vector coordinates along a group-scheme isomorphism. -/
theorem IsVectorGroupOfDimension.of_iso_source (e : H ≅ Q) {n : ℕ}
    (hQ : IsVectorGroupOfDimension Q n) : IsVectorGroupOfDimension H n := by
  obtain ⟨c, hc⟩ := hQ
  let p : ∀ T : Over B, (T ⟶ H.X) ≃* (T ⟶ Q.X) :=
    fun T => ((yonedaGrp.mapIso e).app (op T)).groupIsoToMulEquiv
  refine ⟨fun T => (p T).trans (c T), ?_⟩
  intro T V b x
  change (c V ((b ≫ x) ≫ e.hom.hom.hom)).toAdd =
    fun j => b.left.appTop ((c T (x ≫ e.hom.hom.hom)).toAdd j)
  rw [Category.assoc]
  exact hc T V b (x ≫ e.hom.hom.hom)

/-- Being a vector group is independent of a representative. -/
theorem IsVectorGroup.of_iso (e : H ≅ Q) (hQ : IsVectorGroup Q) :
    IsVectorGroup H := by
  obtain ⟨n, hn⟩ := hQ
  exact ⟨n, hn.of_iso_source e⟩

/-- A vector fppf quotient by the actual trivial kernel gives vector coordinates
on the source. -/
theorem IsFppfQuotient.isVectorGroup_of_bot {q : H ⟶ Q}
    (hq : IsFppfQuotient ⊥ q) (hQ : IsVectorGroup Q) : IsVectorGroup H := by
  exact hQ.of_iso hq.isoOfBot

/-- Vector coordinates on one representative transport to every representative
of the same all-test subgroup functor. -/
theorem isVectorGroup_of_isRepresentedBy {G : GroupScheme B} {F : SubgroupFunctor G}
    {i : H ⟶ G} {j : Q ⟶ G} (hi : F.IsRepresentedBy i) (hj : F.IsRepresentedBy j)
    (hQ : IsVectorGroup Q) : IsVectorGroup H :=
  hQ.of_iso (hi.isoOfIsRepresentedBy hj)

/-- Forgetting the equivariant uniqueness part leaves natural vector coordinates. -/
theorem HasUniqueWeightVectorStructure.isVectorGroup {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {V : GroupScheme (Spec (CommRingCat.of k))}
    {b : AutomorphicAction S.toGrp V} {a : characterLattice S}
    (h : HasUniqueWeightVectorStructure b a) : IsVectorGroup V := by
  obtain ⟨n, e, he⟩ := h.1
  exact ⟨n, e, he.1⟩

end RelativeRoot
end Langlands.GroupScheme
