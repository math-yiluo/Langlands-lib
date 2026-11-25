/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedRootLimitCone
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedRootLimitPunctures

/-! # The pointed etale limit presentation of a punctured root chart

## References

* Stacks Project, Tags 0BSK and 05N9
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Punctured root charts commute with the pointed etale limit defining strict henselization. -/
theorem punctured_root_limit_presentation
    (R : CommRingCat.{u}) (f : R) (n : ℕ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (y : Spec R) (hy : ∀ x : Spec (.of Ω), barY x = y)
    (b : R ⟶ strictHenselization barY)
    (hb : Spec.map b = strictLocalizationToBase barY) :
    let H := strictHenselization barY
    let g := b.hom f
    let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ n - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
    ∃ (I : Type u) (cat : Category.{u} I), letI := cat
      ∃ (_ : IsCofiltered I) (D : I ⥤ Scheme.{u}) (c : Cone D)
        (t : D ⟶ (Functor.const I).obj (Spec R)),
        Nonempty (IsLimit c) ∧ (∀ j, IsAffine (D.obj j)) ∧
        ∃ e : V.toScheme ≅ c.pt,
          (∀ j, e.hom ≫ c.π.app j ≫ t.app j = V.ι ≫ q ≫ Spec.map b) ∧
          ∀ j, ∃ (S : CommRingCat.{u}) (a : R ⟶ S) (z : Spec S),
            Etale (Spec.map a) ∧ (Spec.map a) z = y ∧
            let g := a.hom f
            let A := AdjoinRoot ((Polynomial.X : Polynomial S) ^ n - Polynomial.C g)
            let N := Spec (CommRingCat.of A)
            let q := Spec.map (CommRingCat.ofHom (algebraMap S A))
            let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap S A g)
            ∃ d : V.toScheme ≅ D.obj j,
              d.hom ≫ t.app j = V.ι ≫ q ≫ Spec.map a := by
  classical
  obtain ⟨I, cat, hI, F, c₀, a, e₀, hc₀, ha, hstage⟩ :=
    pointed_etale_ring_colimit R barY y hy b hb
  let := cat
  let := hI
  obtain ⟨D, c, t, hc, hD, e, he, hd⟩ :=
    punctured_root_colimit_continuity R (strictHenselization barY) f n b
      I F c₀ (Classical.choice hc₀) a e₀ ha
  refine ⟨I, cat, hI, D, c, t, hc, hD, e, he, ?_⟩
  intro j
  obtain ⟨het, z, hz⟩ := hstage (Opposite.op j)
  exact ⟨F.obj (Opposite.op j), a.app (Opposite.op j), z, het, hz, hd j⟩

end AlgebraicGeometry.Scheme
