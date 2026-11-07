import Langlands.GroupScheme.Rational.ParabolicWhiteheadQuotient

/-! # Actual isomorphisms on rational points and parabolic Whitehead quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section RationalPoints

variable {k : Type u} [CommRing k]
  {G G' : GroupScheme (Spec (CommRingCat.of k))}

/-- The actual multiplicative equivalence on rational points induced by a
specified group-scheme isomorphism over the ground ring. -/
def rationalPoints.mapEquiv (e : G ≅ G') : rationalPoints G ≃* rationalPoints G' :=
  { rationalPoints.map e.hom with
    invFun := rationalPoints.map e.inv
    left_inv := by
      intro x
      change (x ≫ e.hom.hom.hom) ≫ e.inv.hom.hom = x
      simp only [Category.assoc, ← Grp.comp_hom_hom,
        e.hom_inv_id, Grp.id_hom_hom, Category.comp_id]
    right_inv := by
      intro x
      change (x ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = x
      simp only [Category.assoc, ← Grp.comp_hom_hom,
        e.inv_hom_id, Grp.id_hom_hom, Category.comp_id] }

@[simp] theorem rationalPoints.mapEquiv_toMonoidHom (e : G ≅ G') :
    (rationalPoints.mapEquiv e).toMonoidHom = rationalPoints.map e.hom := rfl

@[simp] theorem rationalPoints.mapEquiv_apply (e : G ≅ G') (x : rationalPoints G) :
    rationalPoints.mapEquiv e x = rationalPoints.map e.hom x := rfl

@[simp] theorem rationalPoints.mapEquiv_symm (e : G ≅ G') :
    (rationalPoints.mapEquiv e).symm = rationalPoints.mapEquiv e.symm := rfl

end RationalPoints

section Quotient

variable {k : Type u} [Field k]
  {G G' G'' : GroupScheme (Spec (CommRingCat.of k))}

/-- A specified actual group-scheme isomorphism induces an equivalence on the
quotients by all actual rational parabolic radical images. -/
def parabolicWhiteheadQuotientCongr (e : G ≅ G') :
    parabolicWhiteheadQuotient G ≃* parabolicWhiteheadQuotient G' :=
  QuotientGroup.congr _ _ (rationalPoints.mapEquiv e)
    (parabolicElementarySubgroup_map_eq e)

/-- The quotient equivalence is induced by the original rational-point map. -/
@[simp] theorem parabolicWhiteheadQuotientCongr_mk (e : G ≅ G')
    (x : rationalPoints G) :
    parabolicWhiteheadQuotientCongr e (parabolicWhiteheadQuotientMk G x) =
      parabolicWhiteheadQuotientMk G' (rationalPoints.map e.hom x) := rfl

@[simp] theorem parabolicWhiteheadQuotientCongr_refl :
    parabolicWhiteheadQuotientCongr (Iso.refl G) =
      MulEquiv.refl (parabolicWhiteheadQuotient G) := by
  apply MulEquiv.ext
  intro x
  obtain ⟨g, rfl⟩ := parabolicWhiteheadQuotientMk_surjective G x
  simp only [parabolicWhiteheadQuotientCongr_mk, rationalPoints.map_apply,
    Iso.refl_hom, Grp.id_hom_hom, Category.comp_id, MulEquiv.refl_apply]

@[simp] theorem parabolicWhiteheadQuotientCongr_trans (e : G ≅ G') (e' : G' ≅ G'') :
    parabolicWhiteheadQuotientCongr (e ≪≫ e') =
      (parabolicWhiteheadQuotientCongr e).trans (parabolicWhiteheadQuotientCongr e') := by
  apply MulEquiv.ext
  intro x
  obtain ⟨g, rfl⟩ := parabolicWhiteheadQuotientMk_surjective G x
  simp only [parabolicWhiteheadQuotientCongr_mk, MulEquiv.trans_apply,
    rationalPoints.map_apply, Iso.trans_hom, Grp.comp_hom_hom, Category.assoc]

/-- Full generation by actual rational parabolic radicals is invariant under
specified ground-field group-scheme isomorphisms. -/
theorem parabolicElementarySubgroup_eq_top_iff_iso (e : G ≅ G') :
    parabolicElementarySubgroup G = ⊤ ↔ parabolicElementarySubgroup G' = ⊤ := by
  rw [← parabolicWhiteheadQuotient_subsingleton_iff G,
    ← parabolicWhiteheadQuotient_subsingleton_iff G']
  exact (parabolicWhiteheadQuotientCongr e).toEquiv.subsingleton_congr

end Quotient

end Langlands.GroupScheme
