import Langlands.AlgebraicGeometry.Descent.CompatibleUnitsStatement
import Langlands.GroupScheme.Multiplicative
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Proof of descent of compatible global units -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.Scheme

/-- Global units descend uniquely along any effective epimorphism of schemes. -/
theorem compatibleUnitsDescent_of_effectiveEpi
    {X Y : AlgebraicGeometry.Scheme.{u}} (p : X ⟶ Y) [EffectiveEpi p]
    (s : Γ(X, ⊤)ˣ)
    (hs : ∀ (U : AlgebraicGeometry.Scheme.{u}) (a b : U ⟶ X), a ≫ p = b ≫ p →
      Units.map a.appTop.hom.toMonoidHom s = Units.map b.appTop.hom.toMonoidHom s) :
    ∃! t : Γ(Y, ⊤)ˣ, Units.map p.appTop.hom.toMonoidHom t = s := by
  let e := (Langlands.GroupScheme.Gm.unitsHomEquiv X).symm s
  have he : ∀ {U : AlgebraicGeometry.Scheme.{u}} (a b : U ⟶ X),
      a ≫ p = b ≫ p → a ≫ e = b ≫ e := by
    intro U a b h
    apply (Langlands.GroupScheme.Gm.unitsHomEquiv U).injective
    simpa only [Langlands.GroupScheme.Gm.unitsHomEquiv_comp,
      e, Equiv.apply_symm_apply] using hs U a b h
  let d := EffectiveEpi.desc p e he
  refine ⟨Langlands.GroupScheme.Gm.unitsHomEquiv Y d, ?_, ?_⟩
  · change Units.map p.appTop.hom.toMonoidHom
      (Langlands.GroupScheme.Gm.unitsHomEquiv Y d) = s
    rw [← Langlands.GroupScheme.Gm.unitsHomEquiv_comp]
    change Langlands.GroupScheme.Gm.unitsHomEquiv X (p ≫ EffectiveEpi.desc p e he) = s
    rw [EffectiveEpi.fac]
    exact (Langlands.GroupScheme.Gm.unitsHomEquiv X).apply_symm_apply s
  · intro t ht
    have hcomp : p ≫ (Langlands.GroupScheme.Gm.unitsHomEquiv Y).symm t = p ≫ d := by
      apply (Langlands.GroupScheme.Gm.unitsHomEquiv X).injective
      rw [Langlands.GroupScheme.Gm.unitsHomEquiv_comp, Equiv.apply_symm_apply,
        Langlands.GroupScheme.Gm.unitsHomEquiv_comp]
      rw [ht]
      change s = Langlands.GroupScheme.Gm.unitsHomEquiv X
        (p ≫ EffectiveEpi.desc p e he)
      rw [EffectiveEpi.fac]
      exact ((Langlands.GroupScheme.Gm.unitsHomEquiv X).apply_symm_apply s).symm
    have hd := (cancel_epi p).mp hcomp
    simpa only [Equiv.apply_symm_apply] using
      congrArg (Langlands.GroupScheme.Gm.unitsHomEquiv Y) hd

/-- Compatible global units descend along quasi-compact flat surjections. -/
theorem compatibleUnitsDescent : CompatibleUnitsDescentStatement.{u} := by
  intro X Y p hpqc hpflat hpsurj s hs
  let : QuasiCompact p := hpqc
  let : Flat p := hpflat
  let : Surjective p := hpsurj
  exact compatibleUnitsDescent_of_effectiveEpi p s hs

end Langlands.Scheme
