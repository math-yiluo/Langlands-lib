/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.ProEtale.Proper.ProEtaleProperQcOpenCounitSections
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenCounitFiniteSupportDiagram

/-! Epimorphism half of the proper/open pro-etale counit support argument.

## References

* Stacks, Tags 09AE and 09AG
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (A : Type u) [CommRing A] [Finite A]

omit [Finite A] in
private theorem epi_of_surjective_affine {T : Scheme.{u}}
    {F G : proEtaleRingModules T (proEtaleConstantRing T A)} (f : F ⟶ G)
    (hf : ∀ (Q : T.ProEt), IsAffine Q.left →
      Function.Surjective (f.val.app (op Q))) : Epi f := by
  let H := SheafOfModules.toSheaf
    ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing T A))
  suffices he : Epi (H.map f) from H.epi_of_epi_map he
  have hlocal : Presheaf.IsLocallySurjective (ProEt.topology T) (H.map f).hom := by
    constructor
    intro Q y
    let V (j : Q.left.affineCover.I₀) : T.ProEt :=
      ProEt.mk (Q.left.affineCover.f j ≫ Q.hom)
    let a (j : Q.left.affineCover.I₀) : V j ⟶ Q :=
      MorphismProperty.Over.homMk (Q.left.affineCover.f j)
    have hcover : Sieve.ofArrows V a ∈ ProEt.topology T Q := by
      apply Precoverage.generate_mem_toGrothendieck
      change (Presieve.ofArrows V a).map (ProEt.forget T ⋙ Over.forget T) ∈
        proetalePrecoverage Q.left
      rw [Presieve.map_ofArrows]
      exact Scheme.zariskiPrecoverage_le_propQCPrecoverage _ Q.left.affineCover.mem₀
    apply (ProEt.topology T).superset_covering _ hcover
    rw [Sieve.ofArrows, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro j
    have hV : IsAffine (V j).left := inferInstanceAs (IsAffine (Spec _))
    obtain ⟨x, hx⟩ := hf (V j) hV (G.val.map (a j).op y)
    exact ⟨x, hx⟩
  exact Sheaf.epi_of_isLocallySurjective (H.map f)

/-- For `p` proper and `i` an open immersion, the counit of the extension-by-zero adjunction
for `i` at `p_* i'_! M` is an epimorphism, where `i'` is the base change of `i`. -/
theorem sfProperOpenCounit_epi {V W T : Scheme.{u}} (p : V ⟶ T) [IsProper p]
    (i : W ⟶ T) [IsOpenImmersion i] (M :
      proEtaleRingModules (pullback p i)
        (proEtaleConstantRing (pullback p i) A)) :
    Epi ((sfIntrinsicExtensionByZeroAdjunction i A).counit.app
      ((sfIntrinsicExtensionByZero (pullback.fst p i) A ⋙
        proEtaleConstantModuleDirectImage p A).obj M)) := by
  apply epi_of_surjective_affine A
  intro Q hQ y
  let : IsAffine Q.left := hQ
  let : IsAffine ((𝟭 Scheme).obj Q.left) := hQ
  obtain ⟨O, hO, _hOW, M₀, a, b, y₀, hcomm, hy⟩ :=
    sfOpenCounit_finiteSupportDiagram A p i M Q y
  obtain ⟨x, hx⟩ := sfProperQcOpenCounit_sections_surjective A
    (pullback.snd p Q.hom) O hO M₀ y₀
  exact ⟨a x, (hcomm x).trans ((congrArg b hx).trans hy)⟩

end AlgebraicGeometry.Scheme
