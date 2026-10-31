import Langlands.Cohomology.PerfectResidueAcyclicity
import Langlands.AlgebraicGeometry.Modules.UniversalPerfectSectionsStatement

/-!
# Vanishing of cohomology from a perfect representative and its quotient fibres

If a cochain complex `K` represents the bounded below derived complex
`derivedComplex F X`, then `K` is acyclic exactly when every right-derived
object `(F.rightDerived n).obj X` vanishes: the derived complex has no
cohomology in negative degrees, and its cohomology in degree `n : ℕ` is
`(F.rightDerived n).obj X`.

For a morphism `f : X ⟶ Spec R`, a strictly perfect representative `K` of the
derived `R`-module global sections of `M`, whose ordinary scalar extensions to
every quotient `R ⧸ m` at a maximal ideal `m` represent the derived global
sections of the actual scheme fibre product over `Spec (R ⧸ m)`, this detects
vanishing of all `Hⁿ(X, M)` from vanishing of all cohomology of these fibres,
via `ModuleComplex.acyclic_of_isStrictlyPerfect_of_residue_acyclic`.
The last theorem extracts the representative from
`UniversalPerfectSectionsStatement`, taken as a hypothesis.
-/

universe w w' v v' u u₁ u₂

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.Cohomology.DerivedPlus

variable {C : Type u₁} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [EnoughInjectives C]
variable {D : Type u₂} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
variable (F : C ⥤ D) [F.Additive]

/-- Cohomology of a complex representing `derivedComplex F X` in a degree `n : ℕ` is
`(F.rightDerived n).obj X`. -/
def homologyIsoOfIsoDerivedComplex {K : CochainComplex D ℤ} {X : C}
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Plus.ι.obj ((derivedComplex F).obj X))
    (n : ℕ) :
    K.homology n ≅ (F.rightDerived n).obj X :=
  ((DerivedCategory.homologyFunctorFactors D n).app K).symm ≪≫
    (DerivedCategory.homologyFunctor D n).mapIso e ≪≫
    homologyIso F (injectiveResolution X) n

/-- A complex representing `derivedComplex F X` is acyclic once every right-derived
object `(F.rightDerived n).obj X` vanishes. -/
theorem acyclic_of_iso_derivedComplex {K : CochainComplex D ℤ} {X : C}
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Plus.ι.obj ((derivedComplex F).obj X))
    (h : ∀ n : ℕ, IsZero ((F.rightDerived n).obj X)) :
    K.Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  obtain hn | hn := lt_or_ge n 0
  swap
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact IsZero.of_iso (h m) (homologyIsoOfIsoDerivedComplex F e m)
  · refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctorFactors D n).app K).symm
    exact IsZero.of_iso (isZero_homology_of_neg F X hn)
      ((DerivedCategory.homologyFunctor D n).mapIso e)

/-- If an acyclic complex represents `derivedComplex F X`, then every right-derived
object `(F.rightDerived n).obj X` vanishes. -/
theorem isZero_rightDerived_of_iso_derivedComplex {K : CochainComplex D ℤ} {X : C}
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Plus.ι.obj ((derivedComplex F).obj X))
    (hK : K.Acyclic) (n : ℕ) :
    IsZero ((F.rightDerived n).obj X) :=
  IsZero.of_iso ((hK n).isZero_homology) (homologyIsoOfIsoDerivedComplex F e n).symm

end Langlands.Cohomology.DerivedPlus

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

open Langlands.Cohomology Langlands.Cohomology.DerivedPlus

attribute [local instance] HasDerivedCategory.standard

/-- Additivity of `relativeGlobalSections g` over a base `Spec (CommRingCat.of A)`, whose
coefficient category `ModuleCat A` is not found by the instance for `Spec R`. -/
instance instAdditiveRelativeGlobalSectionsOf {X : Scheme.{u}} {A : Type u} [CommRing A]
    (g : X ⟶ Spec (CommRingCat.of A)) : (relativeGlobalSections g).Additive :=
  (inferInstance : ∀ {R : CommRingCat.{u}} (f : X ⟶ Spec R),
    (relativeGlobalSections f).Additive) g

/-- The quotient map `R ⟶ R ⧸ m` of commutative rings. -/
def idealQuotientHom {R : CommRingCat.{u}} (m : Ideal R) : R ⟶ CommRingCat.of (R ⧸ m) :=
  CommRingCat.ofHom (Ideal.Quotient.mk m)

/-- Let `K` be a strictly perfect complex of `R`-modules representing the derived
`R`-module global sections of `M`, such that for every maximal ideal `m` the ordinary
scalar extension of `K` to `R ⧸ m` represents the derived global sections of the pullback
of `M` to the fibre product `X ×_{Spec R} Spec (R ⧸ m)`. If all cohomology of these fibres
vanishes, then all cohomology `Hⁿ(X, M)` vanishes. -/
theorem isZero_relativeCohomology_of_quotient_fibres
    {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) (M : X.Modules)
    {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : ModuleComplex.IsStrictlyPerfect K)
    (e : DerivedCategory.Q.obj K ≅
      DerivedCategory.Plus.ι.obj ((derivedComplex (relativeGlobalSections f)).obj M))
    (eq : ∀ m : Ideal R, m.IsMaximal →
      Nonempty (DerivedCategory.Q.obj
          ((ModuleComplex.baseChange (idealQuotientHom m).hom).obj K) ≅
        DerivedCategory.Plus.ι.obj
          ((derivedComplex
            (relativeGlobalSections (pullback.snd f (Spec.map (idealQuotientHom m))))).obj
              ((Scheme.Modules.pullback (pullback.fst f (Spec.map (idealQuotientHom m)))).obj
                M))))
    (hfib : ∀ m : Ideal R, m.IsMaximal → ∀ n : ℕ,
      IsZero ((relativeCohomology (pullback.snd f (Spec.map (idealQuotientHom m))) n).obj
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (idealQuotientHom m)))).obj M)))
    (n : ℕ) :
    IsZero ((relativeCohomology f n).obj M) := by
  refine isZero_rightDerived_of_iso_derivedComplex (relativeGlobalSections f) e ?_ n
  refine ModuleComplex.acyclic_of_isStrictlyPerfect_of_residue_acyclic hK fun m hm ↦ ?_
  obtain ⟨e'⟩ := eq m hm
  exact acyclic_of_iso_derivedComplex _ e' (hfib m hm)

/-- Assuming `UniversalPerfectSectionsStatement`, for a smooth proper `f : X ⟶ Spec R` and
a line bundle `L` on `X`, if every cohomology module of the pullback of `L` to every fibre
product `X ×_{Spec R} Spec (R ⧸ m)` at a maximal ideal `m` vanishes, then every
cohomology module `Hⁿ(X, L)` vanishes. -/
theorem isZero_relativeCohomology_of_universalPerfectSections
    (hups : UniversalPerfectSectionsStatement.{u})
    {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) [Smooth f] [IsProper f]
    (L : Picard.LineBundle X)
    (hfib : ∀ m : Ideal R, m.IsMaximal → ∀ n : ℕ,
      IsZero ((relativeCohomology (pullback.snd f (Spec.map (idealQuotientHom m))) n).obj
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (idealQuotientHom m)))).obj L.obj)))
    (n : ℕ) :
    IsZero ((relativeCohomology f n).obj L.obj) := by
  obtain ⟨K, hK, ⟨e⟩, hbc⟩ := hups R X f inferInstance inferInstance L
  exact isZero_relativeCohomology_of_quotient_fibres f L.obj hK e
    (fun m _ ↦ hbc _ (idealQuotientHom m)) hfib n

end Langlands.AlgebraicGeometry.Modules.DerivedSections
