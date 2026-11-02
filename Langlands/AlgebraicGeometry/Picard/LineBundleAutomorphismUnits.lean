import Langlands.AlgebraicGeometry.Modules.UnitAutomorphisms
import Langlands.AlgebraicGeometry.Picard.LineBundleAutomorphismScalarProof

/-! # Global units and actual line-bundle automorphisms -/

universe u

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.LineBundle

variable {X Y : Scheme.{u}}

/-- The actual unit action on any line bundle is bijective. -/
lemma unitAutHom_bijective (L : LineBundle X) : Function.Bijective (unitAutHom L) := by
  constructor
  · intro r s h
    apply Units.ext
    exact Langlands.Scheme.Modules.smul_id_injective_of_isLocallyFreeRankOne L.property
      (congrArg (fun e : Aut L => e.hom.hom) h)
  · intro e
    obtain ⟨r, hr, _⟩ := lineBundleAutomorphismScalar X L.obj L.property
      ((forget X).mapIso e)
    refine ⟨r, ?_⟩
    apply Iso.ext
    apply ObjectProperty.hom_ext
    exact hr.symm

/-- Global units are the actual automorphism group, via scalar multiplication. -/
def unitAutEquiv (L : LineBundle X) : Γ(X, ⊤)ˣ ≃* Aut L :=
  MulEquiv.ofBijective (unitAutHom L) (unitAutHom_bijective L)

@[simp]
lemma unitAutEquiv_apply (L : LineBundle X) (r : Γ(X, ⊤)ˣ) :
    unitAutEquiv L r = unitAut L r := rfl

/-- Pullback of the equivalence is ordinary pullback of the global unit. -/
lemma pullback_mapIso_unitAutEquiv (f : X ⟶ Y) (L : LineBundle Y)
    (r : Γ(Y, ⊤)ˣ) :
    (pullback f).mapIso (unitAutEquiv L r) =
      unitAutEquiv ((pullback f).obj L) (Units.map f.appTop.hom.toMonoidHom r) :=
  pullback_mapIso_unitAut f L r

set_option backward.isDefEq.respectTransparency false in
/-- The inverse equivalence recovers the scalar of an actual pulled-back automorphism. -/
lemma unitAutEquiv_symm_pullback (f : X ⟶ Y) (L : LineBundle Y) (e : Aut L) :
    (unitAutEquiv ((pullback f).obj L)).symm ((pullback f).mapIso e) =
      Units.map f.appTop.hom.toMonoidHom ((unitAutEquiv L).symm e) := by
  apply (unitAutEquiv ((pullback f).obj L)).injective
  rw [MulEquiv.apply_symm_apply, ← pullback_mapIso_unitAutEquiv,
    MulEquiv.apply_symm_apply]

/-- Transport through an arbitrary isomorphism preserves the scalar. -/
lemma unitAutEquiv_conjugate {L M : LineBundle X} (e : L ≅ M) (r : Γ(X, ⊤)ˣ) :
    Aut.autMulEquivOfIso e (unitAutEquiv L r) = unitAutEquiv M r := by
  apply Iso.ext
  apply ObjectProperty.hom_ext
  exact congrArg Iso.hom
    (Langlands.Scheme.Modules.unitAut_conjugate ((forget X).mapIso e) r)

end Langlands.AlgebraicGeometry.Picard.LineBundle
