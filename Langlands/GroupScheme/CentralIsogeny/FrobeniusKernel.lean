import Langlands.GroupScheme.Lie.GeneralLinearFrobeniusDifferential
import Langlands.GroupScheme.Lie.SubgroupTangent
import Langlands.GroupScheme.SubgroupIntersection
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Reductive.CenterExistenceProof
import Langlands.GroupScheme.AffineLinearEmbeddingProof

/-! # A finite central subgroup with the full tangent space of the centre -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.CentralFrobeniusKernel

variable (k : Type u) [Field k] (p : ℕ) [ExpChar k p]
    {G Z : GroupScheme (Spec (CommRingCat.of k))}
    {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n) (z : Z ⟶ G)

/-- Intersect the given centre representative with the actual kernel of the
Frobenius of a matrix representation. -/
def subgroup : GroupScheme (Spec (CommRingCat.of k)) :=
  subgroupIntersection z (kernelι (ρ ≫ GeneralLinear.frobeniusHom k p n))

/-- The inclusion of the central Frobenius kernel in the ambient group. -/
def inclusion : subgroup k p ρ z ⟶ G :=
  subgroupIntersectionHom z (kernelι (ρ ≫ GeneralLinear.frobeniusHom k p n))

/-- On all scheme tests, the construction is exactly the indicated intersection. -/
theorem range_eq :
    SubgroupFunctor.range (inclusion k p ρ z) =
      SubgroupFunctor.range z ⊓
        SubgroupFunctor.range (kernelι (ρ ≫ GeneralLinear.frobeniusHom k p n)) :=
  range_subgroupIntersectionHom _ _

/-- If the chosen representative is the full centre, this is the full centre
intersected with the actual Frobenius kernel. -/
theorem range_eq_of_center (hz : IsSchemeTheoreticCenter z) :
    SubgroupFunctor.range (inclusion k p ρ z) =
      center G ⊓
        SubgroupFunctor.range (kernelι (ρ ≫ GeneralLinear.frobeniusHom k p n)) := by
  rw [range_eq, hz.2]

/-- The intersection inclusion is closed whenever the given centre inclusion is closed. -/
theorem isClosedSubgroup (hz : IsClosedSubgroup z) :
    IsClosedSubgroup (inclusion k p ρ z) := by
  let : IsAffineHom (GeneralLinear.groupScheme n (CommRingCat.of k)).X.hom :=
    GeneralLinear.isAffineHom_groupScheme n _
  exact isClosedSubgroup_subgroupIntersectionHom hz
    (inferInstanceAs (IsClosedImmersion
      (kernelι (ρ ≫ GeneralLinear.frobeniusHom k p n)).hom.hom.left))

/-- Every point of the constructed subgroup is central, on every test scheme. -/
theorem isCentral (hz : IsSchemeTheoreticCenter z) :
    IsCentral (inclusion k p ρ z) :=
  hz.isCentral.comp
    (subgroupIntersectionFst z (kernelι (ρ ≫ GeneralLinear.frobeniusHom k p n)))

/-- Its range is normal, without requiring the centre to be smooth. -/
theorem isNormal (hz : IsSchemeTheoreticCenter z) :
    (SubgroupFunctor.range (inclusion k p ρ z)).IsNormal := by
  intro T g x _ hx
  have hc := (isCentral_iff_range_le_center _).mp (isCentral k p ρ z hz) T hx
  have he : g * x * g⁻¹ = x := by
    rw [← (commute_of_mem_center hc g).eq, mul_inv_cancel_right]
  rwa [he]

/-- A closed matrix representation makes the kernel finite over the ground
field, including when the centre and kernel are nonsmooth. -/
theorem isFinite (hz : IsClosedSubgroup z) (hρ : IsClosedSubgroup ρ) :
    IsFinite (subgroup k p ρ z).X.hom := by
  let f := ρ ≫ GeneralLinear.frobeniusHom k p n
  let : IsClosedImmersion ρ.hom.hom.left := hρ
  let : IsFinite (GeneralLinear.frobeniusHom k p n).hom.hom.left :=
    GeneralLinear.isFinite_frobeniusHom k p n
  have hf : IsFinite f.hom.hom.left := by
    change IsFinite (ρ.hom.hom.left ≫ (GeneralLinear.frobeniusHom k p n).hom.hom.left)
    infer_instance
  let : IsFinite (kernel f).X.hom :=
    MorphismProperty.of_isPullback (kernel_isPullback_scheme f) hf
  let : IsClosedImmersion (subgroupIntersectionSnd z (kernelι f)).hom.hom.left :=
    MorphismProperty.of_isPullback
      (subgroupIntersection_isPullback_scheme z (kernelι f)) hz
  change IsFinite (subgroupIntersection z (kernelι f)).X.hom
  rw [← Over.w (subgroupIntersectionSnd z (kernelι f)).hom.hom]
  infer_instance

variable [IsAffineHom G.X.hom]

/-- In positive characteristic, this finite central subgroup contains precisely
all tangent directions of the full centre, on every test algebra. -/
theorem lie_eq_center (hp : 1 < p) (hz : IsSchemeTheoreticCenter z)
    (A : Type u) [CommRing A] [Algebra k A] :
    (SubgroupFunctor.range (inclusion k p ρ z)).lie A = (center G).lie A := by
  rw [range_eq_of_center k p ρ z hz]
  apply SetLike.ext
  intro X
  change (X.toMul.val ∈ (center G).carrier _ ∧
    X.toMul.val ∈ (SubgroupFunctor.range
      (kernelι (ρ ≫ GeneralLinear.frobeniusHom k p n))).carrier _) ↔
      X.toMul.val ∈ (center G).carrier _
  constructor
  · exact And.left
  · intro hX
    refine ⟨hX, (mem_range_kernelι_iff _ _).mpr ?_⟩
    have h := congrArg Subtype.val
      (GeneralLinear.targetMap_frobeniusHom k p n hp A (Lie.targetMap ρ A X.toMul))
    simpa only [lieKernelTarget_val, OneMemClass.coe_one, Grp.comp_hom_hom,
      Category.assoc] using h

/-- Every affine finite-type group in positive characteristic has a finite
central normal closed subgroup with exactly the centre's actual tangent
submodule on every field algebra. -/
theorem exists_subgroup (hp : 1 < p)
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] :
    ∃ (N : GroupScheme (Spec (CommRingCat.of k))) (i : N ⟶ G),
      IsClosedSubgroup i ∧ IsFinite N.X.hom ∧ IsCentral i ∧
        (SubgroupFunctor.range i).IsNormal ∧
        ∀ (A : Type u) [CommRing A] [Algebra k A],
          (SubgroupFunctor.range i).lie A = (center G).lie A := by
  obtain ⟨Z, z, hz, hclosed⟩ :=
    fieldFixedSubgroupRepresentability k G G inferInstance
      (AutomorphicAction.conjugation (𝟙 G))
  have hcenter : IsSchemeTheoreticCenter z :=
    ⟨hclosed, hz.2.trans (conjugation_id_fixedSubgroup_eq_center G)⟩
  obtain ⟨d, ρ, hρ⟩ := affineLinearEmbeddingStatement k G inferInstance inferInstance
  exact ⟨subgroup k p ρ z, inclusion k p ρ z, isClosedSubgroup k p ρ z hclosed,
    isFinite k p ρ z hclosed hρ, isCentral k p ρ z hcenter,
    isNormal k p ρ z hcenter, fun A _ _ => lie_eq_center k p ρ z hp hcenter A⟩

end Langlands.GroupScheme.CentralFrobeniusKernel
