import Langlands.GroupScheme.Rational.RootSubgroup
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.Rational.TorusNormalizer

/-! # Normalizer conjugation of the actual relative root subgroup functors -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {B : Scheme.{u}} {S : CommGroupScheme B} {G H : GroupScheme B}
  (i : S.toGrp ⟶ G) (a : characterLattice S)

/-- Applying a group homomorphism carries the full torus orbit to the image orbit. -/
theorem orbit_comp_hom (f : G ⟶ H) {U : Over B} (g : U ⟶ G.X) :
    orbit (i ≫ f) (g ≫ f.hom.hom) = orbit i g ≫ f.hom.hom := by
  simp only [orbit, AutomorphicAction.conjugation_act, Grp.comp_hom_hom,
    MonObj.mul_comp, GrpObj.inv_comp, Category.assoc]

/-- An extension through the actual character remains an extension after a group map. -/
theorem IsOrbitExtension.comp_hom (f : G ⟶ H) {U : Over B} {g : U ⟶ G.X}
    {e : U ⊗ AffineLine.scheme B ⟶ G.X} (he : IsOrbitExtension i a g e) :
    IsOrbitExtension (i ≫ f) a (g ≫ f.hom.hom) (e ≫ f.hom.hom) := by
  rw [IsOrbitExtension, ← Category.assoc, he, orbit_comp_hom]

/-- Root subgroup membership is preserved by a group homomorphism. -/
theorem comp_mem_subgroup (f : G ⟶ H) {U : Over B} {g : U ⟶ G.X}
    (hg : g ∈ (subgroup i a).carrier U) :
    g ≫ f.hom.hom ∈ (subgroup (i ≫ f) a).carrier U := by
  obtain ⟨e, he, he0⟩ := hg
  refine ⟨e ≫ f.hom.hom, he.comp_hom i a f, ?_⟩
  rw [Dynamic.evalZero_comp, he0, MonObj.one_comp]

/-- Reparametrizing the torus reparametrizes its full orbit. -/
theorem orbit_precomp_torus (τ : S ⟶ S) {U : Over B} (g : U ⟶ G.X) :
    orbit (CommGroupScheme.groupHom τ ≫ i) g =
      U ◁ (CommGroupScheme.groupHom τ).hom.hom ≫ orbit i g := by
  simp only [orbit, AutomorphicAction.conjugation_act, Grp.comp_hom_hom,
    MonObj.comp_mul, GrpObj.comp_inv, whiskerLeft_snd_assoc,
    whiskerLeft_fst_assoc]

/-- Reparametrizing both the torus map and the character preserves an extension. -/
theorem IsOrbitExtension.precomp_torus (τ : S ⟶ S) {U : Over B} {g : U ⟶ G.X}
    {e : U ⊗ AffineLine.scheme B ⟶ G.X} (he : IsOrbitExtension i a g e) :
    IsOrbitExtension (CommGroupScheme.groupHom τ ≫ i) (τ ≫ a) g e := by
  rw [IsOrbitExtension, orbit_precomp_torus]
  change U ◁ ((CommGroupScheme.groupHom τ).hom.hom ≫
    (CommGroupScheme.groupHom a).hom.hom ≫ AffineLine.unitInclusion B) ≫ e = _
  rw [whiskerLeft_comp, Category.assoc, he]

/-- Root subgroup membership is preserved when both torus and character are reparametrized. -/
theorem mem_subgroup_precomp_torus (τ : S ⟶ S) {U : Over B} {g : U ⟶ G.X}
    (hg : g ∈ (subgroup i a).carrier U) :
    g ∈ (subgroup (CommGroupScheme.groupHom τ ≫ i) (τ ≫ a)).carrier U := by
  obtain ⟨e, he, he0⟩ := hg
  exact ⟨e, he.precomp_torus i a τ, he0⟩

variable [Mono i.hom.hom.left]

/-- Conjugation by a normalizing base point carries the actual `a`-root
subgroup into the actual subgroup for its Weyl translate, on every test scheme. -/
theorem normalizer_conj_mem (n : normalizerPoints i) {U : Over B} {g : U ⟶ G.X}
    (hg : g ∈ (subgroup i a).carrier U) :
    G.constantPoint n U * g * (G.constantPoint n U)⁻¹ ∈
      (subgroup i (weylAction i n a)).carrier U := by
  let σ := normalizingAut i n
  have hσ : i ≫ (G.innerIso (n : Over.mk (𝟙 B) ⟶ G.X)).hom =
      CommGroupScheme.groupHom σ.hom ≫ i := isNormalizingPoint_normalizingAut i n
  have hc : CommGroupScheme.groupHom σ.inv ≫
      (i ≫ (G.innerIso (n : Over.mk (𝟙 B) ⟶ G.X)).hom) = i := by
    rw [hσ, ← Category.assoc]
    change CommGroupScheme.groupHom (σ.inv ≫ σ.hom) ≫ i = i
    rw [Iso.inv_hom_id]
    exact Category.id_comp i
  have h := mem_subgroup_precomp_torus
    (i ≫ (G.innerIso (n : Over.mk (𝟙 B) ⟶ G.X)).hom) a σ.inv
    (comp_mem_subgroup i a (G.innerIso (n : Over.mk (𝟙 B) ⟶ G.X)).hom hg)
  rw [hc, comp_innerIso_hom] at h
  exact h

/-- The normalizer conjugation inclusion is an equality on every test scheme. -/
theorem normalizer_conj_mem_iff (n : normalizerPoints i) {U : Over B} (g : U ⟶ G.X) :
    G.constantPoint n U * g * (G.constantPoint n U)⁻¹ ∈
      (subgroup i (weylAction i n a)).carrier U ↔ g ∈ (subgroup i a).carrier U := by
  constructor
  · intro hg
    have h := normalizer_conj_mem i (weylAction i n a) n⁻¹ hg
    have ha : weylAction i n⁻¹ (weylAction i n a) = a := by
      rw [map_inv]
      exact (weylAction i n).symm_apply_apply a
    rw [ha] at h
    simpa [G.constantPoint_inv, mul_assoc] using h
  · exact normalizer_conj_mem i a n

/-- The all-test root subgroup functors are carried into one another by the
actual scheme inner automorphism, with the contravariant preimage convention. -/
theorem subgroup_comap_innerIso (n : normalizerPoints i) :
    (subgroup i (weylAction i n a)).comap
        (G.innerIso (n : Over.mk (𝟙 B) ⟶ G.X)).hom = subgroup i a := by
  apply SubgroupFunctor.ext
  intro U
  apply Subgroup.ext
  intro g
  rw [SubgroupFunctor.mem_comap, comp_innerIso_hom, normalizer_conj_mem_iff]

/-- The actual conjugation equivalence between the groups of points of Weyl-translated
root subgroup functors, over any test scheme. -/
def normalizerConjEquiv (n : normalizerPoints i) (U : Over B) :
    (subgroup i a).carrier U ≃* (subgroup i (weylAction i n a)).carrier U where
  toFun g := ⟨G.constantPoint n U * g * (G.constantPoint n U)⁻¹,
    normalizer_conj_mem i a n g.property⟩
  invFun g := ⟨(G.constantPoint n U)⁻¹ * g * G.constantPoint n U, by
    apply (normalizer_conj_mem_iff i a n _).mp
    simp [mul_assoc]⟩
  left_inv g := Subtype.ext (by simp [mul_assoc])
  right_inv g := Subtype.ext (by simp [mul_assoc])
  map_mul' g h := Subtype.ext (by simp [mul_assoc])

@[simp] theorem normalizerConjEquiv_apply (n : normalizerPoints i) (U : Over B)
    (g : (subgroup i a).carrier U) :
    (normalizerConjEquiv i a n U g : U ⟶ G.X) =
      G.constantPoint n U * g * (G.constantPoint n U)⁻¹ := rfl

end Langlands.GroupScheme.RelativeRoot
