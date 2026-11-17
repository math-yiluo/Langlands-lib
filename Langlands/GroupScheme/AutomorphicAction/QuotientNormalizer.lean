import Langlands.GroupScheme.Adjoint.ActionFaithfulness
import Langlands.GroupScheme.AutomorphicAction.RestrictionImage

/-! # Normalizers induced by quotient actions -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction

/-- A homomorphism intertwines the specified source automorphism with
conjugation by the specified target element. -/
def IntertwinesConjugation {M N : Type*} [Group M] [Group N]
    (φ : M →* N) (e : MulAut M) (x : N) : Prop :=
  ∀ g : M, φ (e g) = x * φ g * x⁻¹

variable {S : Scheme.{u}} {G A : GroupScheme S}
  (a : AutomorphicAction A G) (q : G ⟶ A)

/-- An action lifting conjugation intertwines the quotient homomorphism with
conjugation on the quotient, on every test. -/
theorem act_comp_eq_conjugation
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    (hlift : ∀ {U : Over S} (h g : U ⟶ G.X),
      a.act (h ≫ q.hom.hom) g = h * g * h⁻¹)
    {T : Over S} (x : T ⟶ A.X) (g : T ⟶ G.X) :
    a.act x g ≫ q.hom.hom = x * (g ≫ q.hom.hom) * x⁻¹ := by
  apply hom_ext_of_flat_surjective_local_lift q x
  intro V b h hb
  simp only [← Category.assoc, a.naturality, MonObj.comp_mul, GrpObj.comp_inv]
  rw [hb, hlift]
  simp only [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc]

/-- An acting point preserving a subgroup normalizes its quotient image whenever
the quotient intertwines the action with conjugation. -/
theorem mem_normalizer_map_of_map_pointAut_eq
    {M N : Type*} [Group M] [Group N]
    (φ : M →* N) (e : MulAut M) (x : N) (K : Subgroup M)
    (hK : K.map e.toMonoidHom = K)
    (heq : IntertwinesConjugation φ e x) :
    x ∈ Subgroup.normalizer (K.map φ : Set N) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_map]
  have hc : (MulAut.conj x).toMonoidHom.comp φ = φ.comp e.toMonoidHom := by
    apply MonoidHom.ext
    intro g
    exact (heq g).symm
  change K.map ((MulAut.conj x).toMonoidHom.comp φ) = K.map φ
  rw [hc, ← Subgroup.map_map, hK]

/-- The existential preservation predicate is equality of the corresponding
image subgroup under the point automorphism. -/
theorem PreservesRestrictionImage.map_pointAut_range_eq
    {U T : Over S} (res : T ⟶ U) (x : T ⟶ A.X)
    (hx : a.PreservesRestrictionImage res x) :
    ((G.points.map res.op).hom.range).map (a.pointAut T x).toMonoidHom =
      (G.points.map res.op).hom.range := by
  ext g
  constructor
  · rintro ⟨z, ⟨y, rfl⟩, rfl⟩
    obtain ⟨y, hy⟩ := (hx (a.act x (res ≫ y))).1 ⟨y, rfl⟩
    exact ⟨y, hy.symm⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := (hx (res ≫ y)).2 ⟨y, rfl⟩
    exact ⟨res ≫ z, ⟨z, rfl⟩, hz.symm⟩

end Langlands.GroupScheme.AutomorphicAction
