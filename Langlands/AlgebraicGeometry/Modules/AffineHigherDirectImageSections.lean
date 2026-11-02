import Langlands.AlgebraicGeometry.Modules.FiniteClosedSupportLerayProof
import Langlands.AlgebraicGeometry.Modules.HigherDirectImageOpenRestriction
import Langlands.AlgebraicGeometry.Modules.RationalFibreVanishing
import Langlands.AlgebraicGeometry.Modules.ClosedSupportDimension
import Langlands.Cohomology.DerivedPlus

/-! # Sections of finitely supported higher direct images over an affine open -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- The sections over an affine open `V` of a module `N` on `Y`, as a `Γ(Y, V)`-module: the
`Γ(Y, V)`-module global sections of the restriction of `N` to `V ≅ Spec Γ(Y, V)`. -/
abbrev affineSections {Y : Scheme.{u}} {V : Y.Opens} (hV : IsAffineOpen V) (N : Y.Modules) :
    ModuleCat.{u} Γ(Y, V) :=
  (relativeGlobalSections hV.isoSpec.hom).obj ((Scheme.Modules.restrictFunctor V.ι).obj N)

/-- The relative cohomology of the pullback of `M` along a fibre product of `f` with
`t : Spec R ⟶ Y` does not depend on the chosen fibre product. -/
theorem nonempty_relativeCohomology_iso_of_isPullback {X Y P₁ P₂ : Scheme.{u}}
    {R : CommRingCat.{u}} {f : X ⟶ Y} {t : Spec R ⟶ Y} {q₁ : P₁ ⟶ X} {f₁ : P₁ ⟶ Spec R}
    (h₁ : IsPullback q₁ f₁ f t) {q₂ : P₂ ⟶ X} {f₂ : P₂ ⟶ Spec R} (h₂ : IsPullback q₂ f₂ f t)
    (M : X.Modules) (n : ℕ) :
    Nonempty ((relativeCohomology f₁ n).obj ((Scheme.Modules.pullback q₁).obj M) ≅
      (relativeCohomology f₂ n).obj ((Scheme.Modules.pullback q₂).obj M)) := by
  obtain ⟨E, hq, hf⟩ : ∃ E : P₂ ≅ P₁, E.hom ≫ q₁ = q₂ ∧ E.hom ≫ f₁ = f₂ :=
    ⟨h₂.isoIsPullback _ _ h₁, h₂.isoIsPullback_hom_fst _ _ h₁, h₂.isoIsPullback_hom_snd _ _ h₁⟩
  subst hq hf
  exact ⟨(relativeCohomologyPullbackIso E f₁ _ n).symm ≪≫
    (relativeCohomology (E.hom ≫ f₁) n).mapIso ((Scheme.Modules.pullbackComp E.hom q₁).app M)⟩

section AffineSections

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules) {V : Y.Opens} (hV : IsAffineOpen V)

/-- Restricting to an open preserves finite closed support. -/
theorem hasFiniteClosedSupport_restrict {N : Y.Modules} (hN : HasFiniteClosedSupport N) :
    HasFiniteClosedSupport ((Scheme.Modules.restrictFunctor V.ι).obj N) := by
  obtain ⟨hfin, hcl⟩ := hN
  have hinj : Function.Injective V.ι := V.ι.isOpenEmbedding.injective
  refine ⟨(hfin.preimage hinj.injOn).subset fun x hx =>
    (mem_stalkSupport_restrict_iff N V x).1 hx, fun x hx => ?_⟩
  have hx' := hcl _ ((mem_stalkSupport_restrict_iff N V x).1 hx)
  have hpre : ({x} : Set V.toScheme) = V.ι ⁻¹' {V.ι x} := by
    ext z
    simp [hinj.eq_iff]
  rw [hpre]
  exact hx'.preimage V.ι.continuous

/-- If every higher direct image of `M` along `f` has finite closed support, so does every
higher direct image of the restriction of `M` to `f⁻¹ V` along `f ∣_ V`. -/
theorem hasFiniteClosedSupport_higherDirectImage_morphismRestrict
    (hsupp : ∀ q : ℕ, HasFiniteClosedSupport ((higherDirectImage f q).obj M)) (q : ℕ) :
    HasFiniteClosedSupport ((higherDirectImage (f ∣_ V) q).obj
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj M)) :=
  (hasFiniteClosedSupport_iff_of_iso (higherDirectImageRestrictIso f V M q)).2
    (hasFiniteClosedSupport_restrict (hsupp q))

/-- **Sections of finitely supported higher direct images over an affine open.** If every
higher direct image of `M` along `f` has finite closed support, then for every affine open `V`
of `Y` and every fibre product `P` of `f` with `Spec Γ(Y, V) ⟶ Y`, the sections of `Rⁿ f_* M`
over `V` are the cohomology `Hⁿ(P, q^* M)`, as `Γ(Y, V)`-modules. -/
theorem nonempty_affineSections_higherDirectImage_iso
    (hsupp : ∀ q : ℕ, HasFiniteClosedSupport ((higherDirectImage f q).obj M))
    {P : Scheme.{u}} {q : P ⟶ X} {f' : P ⟶ Spec Γ(Y, V)} (h : IsPullback q f' f hV.fromSpec)
    (n : ℕ) :
    Nonempty (affineSections hV ((higherDirectImage f n).obj M) ≅
      (relativeCohomology f' n).obj ((Scheme.Modules.pullback q).obj M)) := by
  obtain ⟨eL⟩ := finiteClosedSupportLeray _ _ _ (f ∣_ V) hV.isoSpec.hom
    ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj M)
    (hasFiniteClosedSupport_higherDirectImage_morphismRestrict f M hsupp) n
  obtain ⟨eP⟩ :=
    nonempty_relativeCohomology_iso_of_isPullback (isPullback_affineRestrict f hV) h M n
  exact ⟨((relativeGlobalSections hV.isoSpec.hom).mapIso
      (higherDirectImageRestrictIso f V M n)).symm ≪≫ eL.symm ≪≫
    (relativeCohomology (affineRestrict f hV) n).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app M) ≪≫ eP⟩

attribute [local instance] HasDerivedCategory.standard in
/-- The sections over an affine open `V` of a finitely supported `Rⁿ f_* M` are the `n`-th
homology of any complex of `Γ(Y, V)`-modules representing the derived sections of the
pullback of `M` to a fibre product of `f` with `Spec Γ(Y, V) ⟶ Y`. -/
theorem nonempty_affineSections_higherDirectImage_iso_homology
    (hsupp : ∀ q : ℕ, HasFiniteClosedSupport ((higherDirectImage f q).obj M))
    {P : Scheme.{u}} {q : P ⟶ X} {f' : P ⟶ Spec Γ(Y, V)} (h : IsPullback q f' f hV.fromSpec)
    (Kc : CochainComplex (ModuleCat.{u} Γ(Y, V)) ℤ)
    (e : DerivedCategory.Q.obj Kc ≅ DerivedCategory.Plus.ι.obj
      ((Cohomology.DerivedPlus.derivedComplex (relativeGlobalSections f')).obj
        ((Scheme.Modules.pullback q).obj M)))
    (n : ℕ) :
    Nonempty (affineSections hV ((higherDirectImage f n).obj M) ≅ Kc.homology n) := by
  obtain ⟨i⟩ := nonempty_affineSections_higherDirectImage_iso f M hV hsupp h n
  exact ⟨i ≪≫ (Cohomology.DerivedPlus.homologyIsoOfIsoDerivedComplex _ e n).symm⟩

end AffineSections

end Langlands.AlgebraicGeometry.Modules.DerivedSections
