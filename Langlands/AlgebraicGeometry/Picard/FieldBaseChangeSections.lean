import Langlands.AlgebraicGeometry.Picard.TrivialLocusComparison
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_twoTermComplex_sectionsEquiv_forall_baseChange
import Langlands.AnthropicFLT.Theorems.Thm_Module_Flat_bijective_kerBaseChangeHom_and_nonempty_homology_baseChange_linearEquiv

/-! # Global functions on base changes of a proper scheme over a field

For a proper scheme `X` over a field `k` there is a natural number `a` such that, for every
`k`-algebra `A`, the global functions on `Spec A ×_k X` form a free `A`-module of rank `a`.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct
open Scheme.TwoAffineOpenCover (moduleSectionsOfHom specMap)
open Langlands.AlgebraicGeometry.AlgebraicSpace (specOver)

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.SectionsComparison

instance {k : Type u} [Field k] : Subsingleton (Spec (.of k)) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum k))

/-- Global functions on the base changes of a proper scheme over a field are free of constant
finite rank. -/
theorem exists_unitSectionsEquiv_of_field {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] :
    ∃ a : ℕ, ∀ (A : Type u) [CommRing A] [Algebra k A] {P : Scheme.{u}} (q : P ⟶ X)
      (p : P ⟶ Spec (.of A)), IsPullback q p f (specMap k A) →
      letI := moduleSectionsOfHom p (SheafOfModules.unit P.ringCatSheaf) ⊤
      Nonempty (Γ(SheafOfModules.unit P.ringCatSheaf, ⊤) ≃ₗ[A] (Fin a → A)) := by
  obtain ⟨G, -, ε, -⟩ := Scheme.Modules.exists_twoTermComplex_sectionsEquiv_forall_baseChange f
    (SheafOfModules.unit X.ringCatSheaf)
    (fun x => ⟨⊤, trivial, ⟨Langlands.Scheme.Modules.pullbackUnitIso _⟩⟩)
  refine ⟨Module.finrank k (LinearMap.ker G.d), fun A _ _ P q p hpb => ?_⟩
  let b := Module.finBasis k (LinearMap.ker G.d)
  have hbij : Function.Bijective (G.kerBaseChangeHom A) :=
    (Module.Flat.bijective_kerBaseChangeHom_and_nonempty_homology_baseChange_linearEquiv A
      (0 : G.C0 →ₗ[k] G.C0) G.d (by simp)).1
  let e₁ : G.H0 A ≃ₗ[A] A ⊗[k] LinearMap.ker G.d := (LinearEquiv.ofBijective _ hbij).symm
  let e₂ : A ⊗[k] LinearMap.ker G.d ≃ₗ[A] (Fin _ → A) :=
    (Algebra.TensorProduct.basis A b).equivFun
  let e₀ := unitSectionsEquivOfIsPullback hpb (IsPullback.of_hasPullback f (specMap k A))
  let e₃ := sectionsEquivOfIso (pullback.snd f (specMap k A))
    (Langlands.Scheme.Modules.pullbackUnitIso (pullback.fst f (specMap k A))).symm
  exact ⟨e₀.trans (e₃.trans ((ε A).trans (e₁.trans e₂)))⟩

end Langlands.AlgebraicGeometry.Picard.SectionsComparison

namespace Langlands.AlgebraicGeometry.Picard.RelativePicard

open SectionsComparison

variable {k : Type u} [Field k] (X : Over (Spec (CommRingCat.of k)))

/-- The projection from `Spec R ×_k X` to `Spec R`. -/
abbrev baseMap (R : Type u) [CommRing R] [Algebra k R] :
    (relativeSpace X.hom).obj (specOver k R) ⟶ Spec (.of R) :=
  pullback.fst (specOver k R).hom X.hom

/-- `SectionsRank X a`: whenever a line bundle `N` on `Spec R ×_k X` becomes trivial along
`Spec A ⟶ Spec R`, the global sections of its pullback to the base change along
`Spec A ⟶ Spec R` form a free `A`-module of rank `a`. -/
def SectionsRank (a : ℕ) : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra k R]
    (N : LineBundle ((relativeSpace X.hom).obj (specOver k R)))
    (A : Type u) [CommRing A] [Algebra R A] [Algebra k A] [IsScalarTower k R A],
    isoLocus X.hom (specOver k R) N (LineBundle.trivial _) (specMap R A) →
    letI := moduleSectionsOfHom (pullback.snd (baseMap X R) (specMap R A))
      ((Scheme.Modules.pullback (pullback.fst (baseMap X R) (specMap R A))).obj N.obj) ⊤
    Nonempty (Γ((Scheme.Modules.pullback (pullback.fst (baseMap X R) (specMap R A))).obj N.obj,
      ⊤) ≃ₗ[A] (Fin a → A))

/-- For proper `X`, the rank of global functions on the base changes of `X` is a
`SectionsRank`. -/
theorem exists_sectionsRank [IsProper X.hom] : ∃ a : ℕ, SectionsRank X a := by
  obtain ⟨a, ha⟩ := exists_unitSectionsEquiv_of_field X.hom
  refine ⟨a, fun R _ _ N A _ _ _ _ hA => ?_⟩
  obtain ⟨e⟩ := nonempty_pullback_iso_trivial_of_mem X.hom hA
    (pullback.fst (baseMap X R) (specMap R A)) (pullback.snd (baseMap X R) (specMap R A))
    pullback.condition
  have hpb : IsPullback (pullback.fst (baseMap X R) (specMap R A) ≫
      pullback.snd (specOver k R).hom X.hom) (pullback.snd (baseMap X R) (specMap R A))
      X.hom (specMap k A) := by
    rw [← FrameCombination.specMap_comp k R A]
    exact (IsPullback.of_hasPullback (baseMap X R) (specMap R A)).paste_horiz
      (IsPullback.of_hasPullback (specOver k R).hom X.hom).flip
  obtain ⟨e'⟩ := ha A _ _ hpb
  exact ⟨(sectionsEquivOfIso _ ((LineBundle.forget _).mapIso e)).trans e'⟩

end Langlands.AlgebraicGeometry.Picard.RelativePicard
